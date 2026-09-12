import GapEntropy.FixedCapRetryPolicy

/-! Actual observed histories of fixed-cap retries agree with their private finite simulations. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace GapEntropy.FixedCapRetry
variable {n : ℕ} (R : ℕ → BoundedProcedure n (Option (Fin n)))
  (hpos : ∀ j, 0 < (R j).budget)

theorem currentIndex_start_add (j s : ℕ) (hs : s < (R j).budget) :
    currentIndex R hpos ((schedule R hpos).start j + s) = j :=
  (schedule R hpos).index_start_add j ⟨s, hs⟩

theorem currentRequest_at (j s : ℕ) (hs : s < (R j).budget)
    (h : History n ((schedule R hpos).start j + s)) :
    currentRequest R hpos ((schedule R hpos).start j + s) h =
      (R j).request s hs (segment h ((schedule R hpos).start j) s le_rfl) := by
  have hi := currentIndex_start_add R hpos j s hs
  have ho : offset R hpos ((schedule R hpos).start j + s) = s := by
    simp only [offset, hi, Nat.add_sub_cancel_left]
  simp only [currentRequest, hi]
  apply (R j).request_congr_history _ hs ho
  intro i
  simp only [currentHistory, hi, segment]

/-- The whole global observed history induces exactly the private procedure's
simulation on every reached prefix of each attempt. -/
theorem segment_eq_simulate (hn : 2 ≤ n) (ω : SampleSpace n) {t : ℕ}
    (h : History n t) (hc : (policy R hpos).historyConsistent hn ω t h)
    (j m : ℕ) (hm : m ≤ (R j).budget)
    (hcut : (schedule R hpos).start j + m ≤ t) :
    segment h ((schedule R hpos).start j) m hcut =
      (R j).simulate (blocks R hpos ω j) m hm := by
  symm
  apply (R j).simulate_eq_of_decisions
  intro s hs
  have hsbudget : s < (R j).budget := hs.trans_le hm
  have hu : (schedule R hpos).start j + s < t := by omega
  have hd := (policy R hpos).historyConsistent_decision hn ω h hc
    ((schedule R hpos).start j + s) hu
  have hr := (choose_sample_imp R hpos hn _ ω.1 _ _ hd.1).2
  rw [currentRequest_at R hpos j s hsbudget] at hr
  exact ⟨hr, hd.2⟩

theorem previousOutput_eq_answer (hn : 2 ≤ n) (ω : SampleSpace n) {t : ℕ}
    (h : History n t) (hc : (policy R hpos).historyConsistent hn ω t h)
    (hj : 0 < currentIndex R hpos t) :
    previousOutput R hpos t hj h = answer R hpos (currentIndex R hpos t - 1) ω := by
  unfold previousOutput
  rw [segment_eq_simulate R hpos hn ω h hc _ _ le_rfl]
  rfl

theorem pendingOutput_eq_answer (hn : 2 ≤ n) (ω : SampleSpace n) {t : ℕ}
    (h : History n t) (hc : (policy R hpos).historyConsistent hn ω t h)
    (hj : 0 < currentIndex R hpos t) :
    pendingOutput R hpos t h = answer R hpos (currentIndex R hpos t - 1) ω := by
  rw [pendingOutput, dif_pos hj, previousOutput_eq_answer R hpos hn ω h hc hj]

/-- If execution continues past an attempt's boundary, that attempt really aborted. -/
theorem answer_none_of_consistent_after_end (hn : 2 ≤ n) (ω : SampleSpace n) {t : ℕ}
    (h : History n t) (hc : (policy R hpos).historyConsistent hn ω t h)
    (j : ℕ) (hj : (schedule R hpos).start (j + 1) < t) : answer R hpos j ω = none := by
  let u := (schedule R hpos).start (j + 1)
  have hu : u < t := hj
  have hi : currentIndex R hpos u = j + 1 := (schedule R hpos).index_start _
  have hcp := (policy R hpos).historyConsistent_prefix hn ω h hc u hu.le
  have hd := (policy R hpos).historyConsistent_decision hn ω h hc u hu
  have hn := (choose_sample_imp R hpos hn u ω.1 _ _ hd.1).1
  rw [pendingOutput_eq_answer R hpos _ ω _ hcp (by omega), hi, Nat.add_sub_cancel] at hn
  exact hn

/-- Every actual returned arm is the readout of one of the actual finite attempts. -/
theorem returned_imp_answer (hn : 2 ≤ n) (ω : SampleSpace n) (i : Fin n)
    (hret : ∃ t, (policy R hpos).returnedAt hn t ω = some i) :
    ∃ j, answer R hpos j ω = some i := by
  obtain ⟨t, ht⟩ := hret
  have hr := ((policy R hpos).returnedAt_eq_some_iff hn t ω i).mp ht
  obtain ⟨s, h, hs, hret⟩ := (policy R hpos).exists_active_return_transition hn ω t i hr
  have hc := ((policy R hpos).run_eq_active_iff_historyConsistent hn ω s h).mp hs
  have hchoose : (policy R hpos).choose hn s (ω.1, h) = Sum.inr i := by
    cases he : (policy R hpos).choose hn s (ω.1, h) with
    | inl a => simp [Policy.run_succ, Policy.step, hs, he] at hret
    | inr a =>
        have ha : a = i := by simpa [Policy.run_succ, Policy.step, hs, he] using hret
        simp only [ha]
  have hp := choose_return_imp R hpos hn s ω.1 h i hchoose
  have hj : 0 < currentIndex R hpos s := by
    by_contra hj
    simp [pendingOutput, hj] at hp
  exact ⟨currentIndex R hpos s - 1,
    (pendingOutput_eq_answer R hpos hn ω h hc hj).symm.trans hp⟩

end GapEntropy.FixedCapRetry
