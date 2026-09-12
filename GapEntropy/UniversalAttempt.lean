import GapEntropy.UniversalCall
import GapEntropy.ReservationBudget
import GapEntropy.FiniteCallProgram

/-!
# The universal attempt's observed-history controller

The parameters are the arm count, confidence, attempt index, and a fixed
numerical sample-cap constant. No unknown mean is supplied to this controller.
The discrete metadata and the stored numerical reference are separate, so all
uses of the real reference retain their ordinary Borel measurability.
-/

noncomputable section
open MeasureTheory
open scoped Classical
namespace GapEntropy.UniversalAttempt
open UniversalCall FiniteCallProgram
variable {n : ℕ}

structure Config where
  confidence : ℝ
  attempt : ℕ
  sampleConstant : ℝ

def Config.workCap (c : Config) : ℕ := 1024 * 2 ^ c.attempt

def Config.sampleCap (c : Config) : ℕ :=
  ⌈c.sampleConstant * (2 : ℝ) ^ c.attempt * Real.log c.confidence⁻¹⌉₊

def Config.errorBudget (c : Config) : ℝ := c.confidence / 1024

def Config.fuel (c : Config) : ℕ := c.workCap / 2 + 1

/-- Active set, scale, entry flag, used base work, and reserved samples. -/
abbrev Metadata (n : ℕ) := Finset (Fin n) × ℕ × Bool × ℕ × ℕ
namespace Metadata
abbrev active (a : Metadata n) := a.1
abbrev scale (a : Metadata n) := a.2.1
abbrev entry (a : Metadata n) := a.2.2.1
abbrev work (a : Metadata n) := a.2.2.2.1
abbrev samples (a : Metadata n) := a.2.2.2.2

def counters (a : Metadata n) : Reservation.Counters := ⟨a.work, a.samples⟩
def tolerance (a : Metadata n) : ℝ := (2 : ℝ) ^ (-(a.scale : ℤ))
def baseCall (a : Metadata n) : Reservation.Call := ⟨a.active.card, a.scale, 0⟩
def alpha (c : Config) (a : Metadata n) : ℝ :=
  Reservation.callConfidence c.errorBudget c.workCap c.attempt a.baseCall

def beta (c : Config) (a : Metadata n) : ℝ := referenceError c.confidence c.attempt a.scale

def call (c : Config) (a : Metadata n) : Reservation.Call :=
  ⟨a.active.card, a.scale, if a.entry then
    entryBudget a.active.card a.tolerance (a.alpha c) (a.beta c)
    else laterBudget a.active.card a.tolerance (a.alpha c)⟩

/-- Both complete reservations are checked before the next request is issued. -/
def Allowed (c : Config) (a : Metadata n) : Prop :=
  2 ≤ a.active.card ∧ a.work + (a.call c).work ≤ c.workCap ∧
    a.samples + (a.call c).samples ≤ c.sampleCap

/-- A successful halving retains the stored numerical reference. A stall
advances one scale and discards that reference. -/
def advance (c : Config) (a : Metadata n) (R : Finset (Fin n)) : Metadata n :=
  (R, if R.card ≤ (a.active.card + 1) / 2 then a.scale else a.scale + 1,
    !(R.card ≤ (a.active.card + 1) / 2),
    a.work + (a.call c).work, a.samples + (a.call c).samples)
end Metadata

abbrev State (n : ℕ) := Metadata n × ℝ
abbrev Parsed (n : ℕ) := Fin n ⊕ (State n × Option (Fin n))

def initial (n : ℕ) : Metadata n := (Finset.univ, 0, true, 0, 0)

def singletonAnswer (R : Finset (Fin n)) : Option (Fin n) :=
  if h : R.card = 1 then some (R.min' (Finset.card_pos.mp (by omega))) else none

def readout (c : Config) (a : Metadata n) (z : ℝ) {t : ℕ} (h : History n t) :
    ℝ × Finset (Fin n) :=
  if a.entry then entryReadout a.active a.tolerance (a.alpha c) (a.beta c) h
  else (z, laterReadout a.active a.tolerance (a.alpha c) z h)

def request (c : Config) (a : Metadata n) (ha : 2 ≤ a.active.card)
    {t : ℕ} (h : History n t) : Fin n :=
  let hS := Finset.card_pos.mp (show 0 < a.active.card by omega)
  if a.entry then entryRequest a.active hS a.tolerance (a.alpha c) (a.beta c) t h
  else laterRequest a.active hS a.tolerance (a.alpha c) t h

def retainedReference (a : Metadata n) (z : ℝ) (R : Finset (Fin n)) : ℝ :=
  if R.card ≤ (a.active.card + 1) / 2 then z else 0

/-- Parse completed calls from the observed history. An unfinished, already
reserved call returns its actual next arm request. Completed calls are read
before the next reservation; singleton return has priority over halving. -/
def parse (c : Config) : ℕ → (a : Metadata n) → ℝ → {t : ℕ} → History n t → Parsed n
  | 0, a, z, _, _ => .inr ((a, z), none)
  | fuel + 1, a, z, t, h =>
    if ha : a.Allowed c then
      let m := (a.call c).samples
      if hm : m ≤ t then
        let r := readout c a z (historyPrefix m hm h)
        let a' := a.advance c r.2
        if r.2.card = 1 then .inr ((a', r.1), singletonAnswer r.2)
        else parse c fuel a' (retainedReference a r.1 r.2) (historySuffix m hm h)
      else .inl (request c a ha.1 h)
    else .inr ((a, z), none)

theorem measurable_readout (c : Config) (a : Metadata n) (t : ℕ) :
    Measurable (fun p : ℝ × History n t => readout c a p.1 p.2) := by
  unfold readout
  split_ifs
  · exact (measurable_entryReadout _ _ _ _).comp measurable_snd
  · exact measurable_fst.prodMk (measurable_laterReadout _ _ _)

theorem measurable_request (c : Config) (a : Metadata n) (ha : 2 ≤ a.active.card) (t : ℕ) :
    Measurable (request c a ha (t := t)) := by
  unfold request
  split_ifs
  · exact measurable_entryRequest _ _ _ _ _ _
  · exact measurable_const

theorem measurable_retainedReference (a : Metadata n) (R : Finset (Fin n)) :
    Measurable (fun z : ℝ => retainedReference a z R) := by
  unfold retainedReference
  split_ifs <;> fun_prop

/-- Measurability is joint in the real reference and the observed history.
Only the returned finite set is handled by a discrete choice argument. -/
theorem measurable_parse (c : Config) (fuel : ℕ) (a : Metadata n) (t : ℕ) :
    Measurable (fun p : ℝ × History n t => parse c fuel a p.1 p.2) := by
  induction fuel generalizing a t with
  | zero => exact measurable_inr.comp ((measurable_const.prodMk measurable_fst).prodMk measurable_const)
  | succ fuel ih =>
    by_cases ha : a.Allowed c
    · let m := (a.call c).samples
      by_cases hm : m ≤ t
      · let rr := fun p : ℝ × History n t => readout c a p.1 (historyPrefix m hm p.2)
        have hr : Measurable rr := (measurable_readout c a m).comp
          (measurable_fst.prodMk ((historyPrefix_measurable m hm).comp measurable_snd))
        have hnext : Measurable (fun p : ℝ × History n t =>
            if (rr p).2.card = 1 then
              Sum.inr (((a.advance c (rr p).2), (rr p).1), singletonAnswer (rr p).2)
            else parse c fuel (a.advance c (rr p).2)
              (retainedReference a (rr p).1 (rr p).2) (historySuffix m hm p.2)) := by
          apply measurable_finite_choice
            (F := fun p R => if R.card = 1 then
              Sum.inr ((a.advance c R, (rr p).1), singletonAnswer R)
            else parse c fuel (a.advance c R)
              (retainedReference a (rr p).1 R) (historySuffix m hm p.2)) hr.snd
          intro R
          split_ifs
          · exact measurable_inr.comp ((measurable_const.prodMk hr.fst).prodMk measurable_const)
          · exact (ih (a.advance c R) (t - m)).comp
              (((measurable_retainedReference a R).comp hr.fst).prodMk
                ((historySuffix_measurable m hm).comp measurable_snd))
        simpa only [parse, dif_pos ha, dif_pos hm, rr, m] using hnext
      · simpa only [parse, dif_pos ha, dif_neg hm, m, Function.comp_def] using
          measurable_inl.comp ((measurable_request c a ha.1 t).comp measurable_snd)
    · simpa only [parse, dif_neg ha, Function.comp_def] using
        measurable_inr.comp ((measurable_const.prodMk measurable_fst).prodMk
          (measurable_const : Measurable (fun _ : ℝ × History n t => (none : Option (Fin n)))))

/-- A full sample-cap history always reaches a terminal state. The strict fuel
invariant rules out exhaustion while a further two-unit reservation is possible. -/
theorem parse_complete (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    {t : ℕ} (h : History n t) (hw : a.work ≤ c.workCap)
    (hs : a.samples ≤ c.sampleCap) (hf : c.workCap < a.work + 2 * fuel)
    (ht : c.sampleCap ≤ a.samples + t) :
    ∃ st answer, parse c fuel a z h = .inr (st, answer) := by
  induction fuel generalizing a z t with
  | zero => simp only [Nat.mul_zero, Nat.add_zero] at hf; omega
  | succ fuel ih =>
    by_cases ha : a.Allowed c
    · have hcw : 2 ≤ (a.call c).work := Reservation.two_le_call_work _ ha.1
      have hm : (a.call c).samples ≤ t := by have := ha.2.2; omega
      let r := readout c a z (historyPrefix (a.call c).samples hm h)
      by_cases hr : r.2.card = 1
      · exact ⟨(a.advance c r.2, r.1), singletonAnswer r.2,
          by simp only [parse, dif_pos ha, dif_pos hm, r, if_pos hr]⟩
      · have hwork : (a.advance c r.2).work = a.work + (a.call c).work := rfl
        have hsamples : (a.advance c r.2).samples = a.samples + (a.call c).samples := rfl
        obtain ⟨st, ans, heq⟩ := ih (a.advance c r.2) (retainedReference a r.1 r.2)
          (historySuffix (a.call c).samples hm h)
          (by rw [hwork]; exact ha.2.1) (by rw [hsamples]; exact ha.2.2)
          (by rw [hwork]; omega) (by rw [hsamples]; omega)
        exact ⟨st, ans, by simpa only [parse, dif_pos ha, dif_pos hm, r, if_neg hr] using heq⟩
    · exact ⟨(a, z), none, by simp only [parse, dif_neg ha]⟩

theorem initial_parse_complete (c : Config) {t : ℕ} (h : History n t)
    (ht : c.sampleCap ≤ t) :
    ∃ st answer, parse c c.fuel (initial n) 0 h = .inr (st, answer) := by
  apply parse_complete
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · change c.workCap < 0 + 2 * (c.workCap / 2 + 1)
    omega
  · simpa [initial, Metadata.samples] using ht

theorem allowed_reservation (c : Config) (a : Metadata n) (ha : a.Allowed c) :
    Reservation.reserve c.workCap c.sampleCap a.counters (a.call c) =
      some (Reservation.charge a.counters (a.call c)) :=
  (Reservation.reserve_eq_some_iff _ _ _ _ _).2 ⟨ha.2.1, ha.2.2, rfl⟩

theorem advance_counters (c : Config) (a : Metadata n) (R : Finset (Fin n)) :
    (a.advance c R).counters = Reservation.charge a.counters (a.call c) := rfl

theorem advance_reuses_reference (c : Config) (a : Metadata n) (z : ℝ)
    (R : Finset (Fin n)) (hhalf : R.card ≤ (a.active.card + 1) / 2) :
    (a.advance c R).scale = a.scale ∧ (a.advance c R).entry = false ∧
      retainedReference a z R = z := by simp [Metadata.advance, retainedReference, hhalf]

theorem advance_stall (c : Config) (a : Metadata n) (z : ℝ)
    (R : Finset (Fin n)) (hstall : (a.active.card + 1) / 2 < R.card) :
    (a.advance c R).scale = a.scale + 1 ∧ (a.advance c R).entry = true ∧
      retainedReference a z R = 0 := by
  simp [Metadata.advance, retainedReference, Nat.not_le.mpr hstall]

end GapEntropy.UniversalAttempt
