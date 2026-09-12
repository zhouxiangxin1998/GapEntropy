import GapEntropy.UniversalProcedure
import GapEntropy.UniversalReadoutFacts

/-!
# Exact call reservations along universal-attempt histories

This trace records every accepted reservation, including a call still in
progress. Its contents are obtained from the actual history parser. No
statistical event is required for the work, sample, count, or confidence caps.
-/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram
variable {n : ℕ}

/-- Accepted calls in chronological order. An unfinished call is included
because its complete budget has already been reserved. -/
def calls (c : Config) : ℕ → (a : Metadata n) → ℝ → {t : ℕ} → History n t → List Reservation.Call
  | 0, _, _, _, _ => []
  | fuel + 1, a, z, t, h =>
    if a.Allowed c then
      let m := (a.call c).samples
      (a.call c) :: (if hm : m ≤ t then
        let r := readout c a z (historyPrefix m hm h)
        if r.2.card = 1 then [] else
          calls c fuel (a.advance c r.2) (retainedReference a r.1 r.2) (historySuffix m hm h)
        else [])
    else []

theorem calls_arms (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    {t : ℕ} (h : History n t) :
    ∀ call ∈ calls c fuel a z h, 2 ≤ call.arms := by
  induction fuel generalizing a z t with
  | zero => simp [calls]
  | succ fuel ih =>
    by_cases ha : a.Allowed c
    · simp only [calls, if_pos ha, List.mem_cons]
      intro call hc
      rcases hc with rfl | hc
      · exact ha.1
      · split_ifs at hc with hm hr
        · simp at hc
        · exact ih _ _ _ call hc
        · simp at hc
    · simp [calls, ha]

theorem calls_reserved (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    {t : ℕ} (h : History n t) :
    ∃ st, Reservation.reserveAll c.workCap c.sampleCap a.counters (calls c fuel a z h) = some st := by
  induction fuel generalizing a z t with
  | zero => exact ⟨a.counters, rfl⟩
  | succ fuel ih =>
    by_cases ha : a.Allowed c
    · simp only [calls, if_pos ha, Reservation.reserveAll, allowed_reservation c a ha,
        Option.bind_some]
      split_ifs with hm hr
      · exact ⟨_, rfl⟩
      · simpa only [advance_counters] using ih
          (a.advance c (readout c a z (historyPrefix (a.call c).samples hm h)).2)
          (retainedReference a (readout c a z (historyPrefix (a.call c).samples hm h)).1
            (readout c a z (historyPrefix (a.call c).samples hm h)).2)
          (historySuffix (a.call c).samples hm h)
      · exact ⟨_, rfl⟩
    · exact ⟨a.counters, by simp only [calls, if_neg ha, Reservation.reserveAll]⟩

theorem terminal_counters (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    {t : ℕ} (h : History n t) (st : State n) (answer : Option (Fin n))
    (hp : parse c fuel a z h = .inr (st, answer)) :
    Reservation.reserveAll c.workCap c.sampleCap a.counters (calls c fuel a z h) =
      some st.1.counters := by
  induction fuel generalizing a z t st answer with
  | zero =>
    simp only [parse, Sum.inr.injEq, Prod.mk.injEq] at hp
    rw [← hp.1]
    rfl
  | succ fuel ih =>
    by_cases ha : a.Allowed c
    · have hr := allowed_reservation c a ha
      simp only [parse, dif_pos ha] at hp
      simp only [calls, if_pos ha, Reservation.reserveAll, hr, Option.bind_some]
      split_ifs at hp ⊢ with hm hs
      · simp only [Sum.inr.injEq, Prod.mk.injEq] at hp
        rw [← hp.1]
        rfl
      · simpa only [advance_counters] using ih _ _ _ st answer hp
    · simp only [parse, dif_neg ha, Sum.inr.injEq, Prod.mk.injEq] at hp
      rw [← hp.1]
      simp only [calls, if_neg ha, Reservation.reserveAll]

/-- The actual accepted trace obeys both D.8 caps and the finite call bound. -/
theorem initial_trace_budgets (c : Config) {t : ℕ} (h : History n t) :
    let cs := calls c c.fuel (initial n) 0 h
    (cs.map Reservation.Call.work).sum ≤ c.workCap ∧
    (cs.map Reservation.Call.samples).sum ≤ c.sampleCap ∧ cs.length ≤ c.workCap / 2 := by
  obtain ⟨st, hr⟩ := calls_reserved c c.fuel (initial n) 0 h
  have hzero : (initial n).counters = Reservation.zero := rfl
  rw [hzero] at hr
  obtain ⟨hw, hs⟩ := Reservation.reserved_path_budgets _ _ _ _ hr
  exact ⟨hw, hs, Reservation.accepted_call_count_le _ _ _ _ hr
    (calls_arms c c.fuel (initial n) 0 h)⟩

theorem initial_trace_confidence (c : Config) (hδ : 0 ≤ c.confidence)
    {t : ℕ} (h : History n t) :
    ((calls c c.fuel (initial n) 0 h).map
      (Reservation.callConfidence c.errorBudget c.workCap c.attempt)).sum ≤ c.errorBudget := by
  obtain ⟨st, hr⟩ := calls_reserved c c.fuel (initial n) 0 h
  have hzero : (initial n).counters = Reservation.zero := rfl
  rw [hzero] at hr
  exact Reservation.reserved_confidence_sum_le
    (div_nonneg hδ (by norm_num)) _ _ _ (by unfold Config.workCap; positivity) _ _ hr

/-- The confidence attached to a recorded call is exactly the fresh-call
confidence recomputed by the controller, including the small-set factor. -/
theorem call_confidence (c : Config) (a : Metadata n) :
    Reservation.callConfidence c.errorBudget c.workCap c.attempt (a.call c) = a.alpha c := rfl

theorem readout_subset (c : Config) (a : Metadata n) (z : ℝ) {t : ℕ} (h : History n t) :
    (readout c a z h).2 ⊆ a.active := by
  unfold readout
  split_ifs
  · exact UniversalCall.entryReadout_subset _ _ _ _ _
  · exact UniversalCall.laterReadout_subset _ _ _ _ _

theorem readout_card_ge_half (c : Config) (a : Metadata n) (z : ℝ)
    {t : ℕ} (h : History n t) :
    (a.active.card + 1) / 2 ≤ (readout c a z h).2.card := by
  unfold readout
  split_ifs
  · exact UniversalCall.entryReadout_card_ge_half _ _ _ _ _
  · exact UniversalCall.laterReadout_card_ge_half _ _ _ _ _

theorem readout_nonempty (c : Config) (a : Metadata n) (z : ℝ)
    {t : ℕ} (h : History n t) (hS : a.active.Nonempty) :
    (readout c a z h).2.Nonempty := by
  unfold readout
  split_ifs
  · exact UniversalCall.entryReadout_nonempty _ hS _ _ _ _
  · exact UniversalCall.laterReadout_nonempty _ hS _ _ _ _

theorem singleton_preceded_by_two (c : Config) (a : Metadata n) (z : ℝ)
    {t : ℕ} (h : History n t) (ha : 2 ≤ a.active.card)
    (hs : (readout c a z h).2.card = 1) : a.active.card = 2 := by
  have hh := readout_card_ge_half c a z h
  rw [hs] at hh
  omega

theorem same_scale_exact_half (c : Config) (a : Metadata n) (z : ℝ)
    {t : ℕ} (h : History n t)
    (hs : (readout c a z h).2.card ≤ (a.active.card + 1) / 2) :
    (readout c a z h).2.card = (a.active.card + 1) / 2 :=
  Nat.le_antisymm hs (readout_card_ge_half c a z h)

end GapEntropy.UniversalAttempt
