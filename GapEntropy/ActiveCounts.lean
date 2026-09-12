import GapEntropy.HistoryConsistency
import GapEntropy.ReturnedCounts

/-! Pathwise sample counts before and at the first return. -/

open scoped ENNReal

namespace GapEntropy.Policy

variable {n : ℕ} (A : Policy n)

theorem truncatedSamples_eq_time_of_active (hn : 2 ≤ n) (ω : SampleSpace n)
    (t : ℕ) (h : History n t) (hr : A.run hn ω t = Sum.inr h) :
    A.truncatedSamples hn t ω = t := by
  have hc := (A.run_eq_active_iff_historyConsistent hn ω t h).1 hr
  have hi (s : ℕ) (hs : s < t) : A.sampleIndicator hn s ω = 1 := by
    have hp := A.historyConsistent_prefix hn ω h hc s hs.le
    have hrp := (A.run_eq_active_iff_historyConsistent hn ω s _).2 hp
    have hd := (A.historyConsistent_decision hn ω h hc s hs).1
    simp [sampleIndicator, sampleRequested, requestedArm, hrp, hd]
  simp only [truncatedSamples]
  calc
    (∑ s ∈ Finset.range t, A.sampleIndicator hn s ω) = ∑ _s ∈ Finset.range t, (1 : ℝ≥0∞) :=
      Finset.sum_congr rfl (fun s hs => hi s (Finset.mem_range.1 hs))
    _ = t := by simp

theorem time_le_sampleCount_of_active (hn : 2 ≤ n) (ω : SampleSpace n)
    (t : ℕ) (h : History n t) (hr : A.run hn ω t = Sum.inr h) :
    (t : ℝ≥0∞) ≤ A.sampleCount hn ω := by
  rw [← A.truncatedSamples_eq_time_of_active hn ω t h hr]
  exact A.truncatedSamples_le_sampleCount hn t ω

theorem exists_active_return_transition (hn : 2 ≤ n) (ω : SampleSpace n)
    (t : ℕ) (i : Fin n) (hret : A.run hn ω t = Sum.inl i) :
    ∃ (s : ℕ) (h : History n s), A.run hn ω s = Sum.inr h ∧
      A.run hn ω (s + 1) = Sum.inl i := by
  induction t with
  | zero => simp [run] at hret
  | succ t ih =>
      cases hr : A.run hn ω t with
      | inr h => exact ⟨t, h, hr, hret⟩
      | inl j =>
          have hji : j = i := by simpa [run_succ, step, hr] using hret
          subst j
          exact ih hr

theorem sampleCount_eq_time_of_return_transition (hn : 2 ≤ n) (ω : SampleSpace n)
    (t : ℕ) (h : History n t) (hr : A.run hn ω t = Sum.inr h) (i : Fin n)
    (hret : A.run hn ω (t + 1) = Sum.inl i) : A.sampleCount hn ω = t := by
  have hi : A.sampleIndicator hn t ω = 0 := by
    cases hc : A.choose hn t (ω.1, h) with
    | inl j => simp [run_succ, step, hr, hc] at hret
    | inr j => simp [sampleIndicator, sampleRequested, requestedArm, hr, hc]
  rw [A.sampleCount_eq_truncatedSamples_of_returned hn ω (t + 1)
    ((A.returnedAt_eq_some_iff hn (t + 1) ω i).2 hret),
    A.truncatedSamples_succ, hi, add_zero]
  exact A.truncatedSamples_eq_time_of_active hn ω t h hr

end GapEntropy.Policy
