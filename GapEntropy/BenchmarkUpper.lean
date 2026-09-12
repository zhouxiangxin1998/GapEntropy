import GapEntropy.Problem

/-! Passing a uniform labeling cost bound to the actual permutation benchmark. -/
open scoped ENNReal BigOperators
namespace GapEntropy

theorem permutationAverage_le_of_each (A : Algorithm) {n : ℕ} (I : Instance n)
    (q : ℝ≥0∞) (hq : ∀ π : Equiv.Perm (Fin n), (A n).expectedSamples (I.permute π) ≤ q) :
    permutationAverage A I ≤ q := by
  unfold permutationAverage
  apply (show (∑ π : Equiv.Perm (Fin n), (A n).expectedSamples (I.permute π)) /
      (n.factorial : ℝ≥0∞) ≤ (∑ _π : Equiv.Perm (Fin n), q) / (n.factorial : ℝ≥0∞) from
    mul_le_mul' (Finset.sum_le_sum (fun π _ => hq π)) le_rfl).trans_eq
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_perm, Fintype.card_fin]
  rw [mul_comm]
  exact ENNReal.mul_div_cancel_right (by simp [Nat.factorial_ne_zero]) (by simp)

theorem benchmark_le_of_each (A : Algorithm) {δ : ℝ} (hA : DeltaCorrect A δ)
    {n : ℕ} (I : Instance n) (q : ℝ≥0∞)
    (hq : ∀ π : Equiv.Perm (Fin n), (A n).expectedSamples (I.permute π) ≤ q) :
    benchmark I δ ≤ q :=
  (benchmark_le_permutationAverage A hA I).trans (permutationAverage_le_of_each A I q hq)

end GapEntropy
