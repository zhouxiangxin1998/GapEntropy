import GapEntropy.Model
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Nontermination and unconditional sample cost

These lemmas check the connection between the operational semantics and the
extended runtime used in the benchmark. A path that never returns requests
infinitely many observations. Finite expectation therefore implies almost-sure
termination, independently of any correctness assumption.
-/

open MeasureTheory
open scoped ENNReal

namespace GapEntropy.Policy

variable {n : ℕ} (A : Policy n)

theorem sampleIndicator_eq_one_of_never_returns (hn : 2 ≤ n) (ω : SampleSpace n)
    (h : ∀ t i, A.returnedAt hn t ω ≠ some i) (t : ℕ) :
    A.sampleIndicator hn t ω = 1 := by
  classical
  cases hr : A.run hn ω t with
  | inl i =>
    exact False.elim (h t i (by simp [returnedAt, hr]))
  | inr history =>
    cases hc : A.choose hn t (ω.1, history) with
    | inl i => simp [sampleIndicator, sampleRequested, requestedArm, hr, hc]
    | inr i =>
      exact False.elim (h (t + 1) i (by simp [returnedAt, run_succ, step, hr, hc]))

theorem sampleCount_eq_top_of_never_returns (hn : 2 ≤ n) (ω : SampleSpace n)
    (h : ∀ t i, A.returnedAt hn t ω ≠ some i) : A.sampleCount hn ω = ⊤ := by
  simp only [sampleCount, A.sampleIndicator_eq_one_of_never_returns hn ω h]
  simp

theorem returns_of_sampleCount_ne_top (hn : 2 ≤ n) (ω : SampleSpace n)
    (h : A.sampleCount hn ω ≠ ⊤) : ∃ t i, A.returnedAt hn t ω = some i := by
  by_contra! hnot
  exact h (A.sampleCount_eq_top_of_never_returns hn ω hnot)

theorem almostSurelyTerminates_of_expectedSamples_ne_top (I : Instance n)
    (h : A.expectedSamples I ≠ ⊤) : A.AlmostSurelyTerminates I := by
  have hf := ae_lt_top (A.measurable_sampleCount I.two_le) h
  filter_upwards [hf] with ω hω
  exact A.returns_of_sampleCount_ne_top I.two_le ω hω.ne

end GapEntropy.Policy
