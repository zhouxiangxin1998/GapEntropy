import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

/-!
# Finite entropy and the deterministic conclusion of Appendix B

The definitions and proofs in this file concern finite real-valued distributions.
They do not assume or assert any statistical lower bound for a bandit algorithm.
The required probabilistic Kraft bound is an explicit hypothesis of the theorem
`finiteEntropy_le_of_kraft`.
-/

noncomputable section

open scoped BigOperators

namespace GapEntropy

variable {ι : Type*}

/-- Shannon entropy, with natural logarithms. At zero the summand is zero. -/
def finiteEntropy (s : Finset ι) (p : ι → ℝ) : ℝ :=
  ∑ i ∈ s, p i * Real.log (p i)⁻¹

/-- Finite relative entropy; nonnegativity requires appropriate mass/support hypotheses. -/
def finiteRelativeEntropy (s : Finset ι) (p q : ι → ℝ) : ℝ :=
  ∑ i ∈ s, p i * Real.log (p i / q i)

theorem finiteEntropy_eq_sum_negMulLog (s : Finset ι) (p : ι → ℝ) :
    finiteEntropy s p = ∑ i ∈ s, Real.negMulLog (p i) := by
  simp [finiteEntropy, Real.negMulLog, Real.log_inv]

theorem finiteEntropy_nonneg_of_le_one (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hp1 : ∀ i ∈ s, p i ≤ 1) :
    0 ≤ finiteEntropy s p := by
  rw [finiteEntropy_eq_sum_negMulLog]
  exact Finset.sum_nonneg fun i hi ↦ Real.negMulLog_nonneg (hp i hi) (hp1 i hi)

theorem finiteEntropy_nonneg (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    0 ≤ finiteEntropy s p := by
  apply finiteEntropy_nonneg_of_le_one s p hp
  intro i hi
  calc
    p i ≤ ∑ j ∈ s, p j := Finset.single_le_sum hp hi
    _ = 1 := hsum

/-- Scalar Gibbs inequality, including the zero source-mass case. -/
theorem entropy_term_le_cross_term {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p * Real.log p⁻¹ ≤ p * Real.log q⁻¹ + q - p := by
  by_cases hp0 : p = 0
  · simpa [hp0] using hq.le
  have hp_pos : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hq hp_pos)) hp
  rw [Real.log_div hq.ne' hp0] at h
  have hcancel : p * (q / p - 1) = q - p := by
    field_simp
  rw [hcancel] at h
  simp only [Real.log_inv]
  nlinarith

/-- Finite log-sum inequality in its mass-corrected Gibbs form. -/
theorem finiteEntropy_le_cross_add_mass (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i) :
    finiteEntropy s p ≤ (∑ i ∈ s, p i * Real.log (q i)⁻¹) +
      (∑ i ∈ s, q i) - ∑ i ∈ s, p i := by
  have h := Finset.sum_le_sum fun i hi ↦ entropy_term_le_cross_term (hp i hi) (hq i hi)
  simpa only [finiteEntropy, Finset.sum_sub_distrib, Finset.sum_add_distrib] using h

theorem finiteEntropy_le_cross (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (hq : ∀ i ∈ s, 0 < q i) (hqsum : ∑ i ∈ s, q i ≤ 1) :
    finiteEntropy s p ≤ ∑ i ∈ s, p i * Real.log (q i)⁻¹ := by
  have h := finiteEntropy_le_cross_add_mass s p q hp hq
  linarith

theorem finiteRelativeEntropy_eq_cross_sub (s : Finset ι) (p q : ι → ℝ)
    (hq : ∀ i ∈ s, q i ≠ 0) :
    finiteRelativeEntropy s p q =
      (∑ i ∈ s, p i * Real.log (q i)⁻¹) - finiteEntropy s p := by
  rw [finiteRelativeEntropy, finiteEntropy, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpi : p i = 0
  · simp [hpi]
  rw [Real.log_div hpi (hq i hi), Real.log_inv, Real.log_inv]
  ring

/-- Gibbs' inequality for a probability distribution and positive subprobability weights. -/
theorem finiteRelativeEntropy_nonneg (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (hq : ∀ i ∈ s, 0 < q i) (hqsum : ∑ i ∈ s, q i ≤ 1) :
    0 ≤ finiteRelativeEntropy s p q := by
  rw [finiteRelativeEntropy_eq_cross_sub s p q (fun i hi ↦ (hq i hi).ne')]
  exact sub_nonneg.mpr (finiteEntropy_le_cross s p q hp hsum hq hqsum)

/-- The log-sum inequality for nonnegative source masses and positive comparison masses.
The two total masses are required to be positive so that the displayed logarithm is meaningful. -/
theorem finite_log_sum (s : Finset ι) (p q : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hq : ∀ i ∈ s, 0 < q i)
    (hP : 0 < ∑ i ∈ s, p i) (hQ : 0 < ∑ i ∈ s, q i) :
    (∑ i ∈ s, p i) * Real.log ((∑ i ∈ s, p i) / ∑ i ∈ s, q i) ≤
      finiteRelativeEntropy s p q := by
  let P := ∑ i ∈ s, p i
  let Q := ∑ i ∈ s, q i
  have hp_sum : ∑ i ∈ s, p i / P = 1 := by
    rw [← Finset.sum_div]
    exact div_self hP.ne'
  have hq_sum : ∑ i ∈ s, q i / Q = 1 := by
    rw [← Finset.sum_div]
    exact div_self hQ.ne'
  have hG := finiteRelativeEntropy_nonneg s (fun i ↦ p i / P) (fun i ↦ q i / Q)
    (fun i hi ↦ div_nonneg (hp i hi) hP.le) hp_sum
    (fun i hi ↦ div_pos (hq i hi) hQ) hq_sum.le
  have hterms :
      (∑ i ∈ s, (p i * Real.log (p i / q i) - p i * Real.log (P / Q))) =
        P * finiteRelativeEntropy s (fun i ↦ p i / P) (fun i ↦ q i / Q) := by
    rw [finiteRelativeEntropy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hpi : p i = 0
    · simp [hpi]
    have hratio : p i / P / (q i / Q) = (p i / q i) / (P / Q) := by
      field_simp
    rw [hratio, Real.log_div (div_ne_zero hpi (hq i hi).ne')
      (div_ne_zero hP.ne' hQ.ne')]
    have hcancel : P * (p i / P) = p i := by
      field_simp [show P ≠ 0 from hP.ne']
    rw [← mul_assoc, hcancel]
    ring
  have hnonneg := mul_nonneg hP.le hG
  rw [← hterms, Finset.sum_sub_distrib, ← Finset.sum_mul] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- The Kraft-to-entropy step used in manuscript equation (B.15).
No sign hypothesis on `c` or `a` is needed once the Kraft bound is known. -/
theorem finiteEntropy_le_of_kraft (s : Finset ι) (p a : ι → ℝ) (c : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1)
    (hkraft : ∑ i ∈ s, Real.exp (-(c * a i)) ≤ 1) :
    finiteEntropy s p ≤ c * ∑ i ∈ s, p i * a i := by
  have h := finiteEntropy_le_cross s p (fun i ↦ Real.exp (-(c * a i)))
    hp hsum (fun i _ ↦ Real.exp_pos _) hkraft
  simpa only [Real.log_inv, Real.log_exp, neg_neg, mul_left_comm,
    ← Finset.mul_sum] using h

/-- The final scalar combination in Appendix B: one confidence cost and four entropy costs. -/
theorem confidence_entropy_fifth {T H L E : ℝ}
    (hL : H * L ≤ T) (hE : H * E ≤ 4 * T) :
    H * (L + E) / 5 ≤ T := by
  nlinarith

/-- Uniform weights attain the logarithm of the support cardinality.
The empty case is also valid with Lean's convention `Real.log 0 = 0`. -/
theorem finiteEntropy_uniform (s : Finset ι) :
    finiteEntropy s (fun _ ↦ (s.card : ℝ)⁻¹) = Real.log (s.card : ℝ) := by
  by_cases hs : s.Nonempty
  · have hc : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
    simp [finiteEntropy, nsmul_eq_mul, hc]
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [hs0, finiteEntropy]

/-- A probability distribution on a finite set has entropy at most the uniform entropy. -/
theorem finiteEntropy_le_log_card (s : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : ∑ i ∈ s, p i = 1) :
    finiteEntropy s p ≤ Real.log (s.card : ℝ) := by
  have hs : s.Nonempty := by
    by_contra h
    have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [hs0] at hsum
  have hc : 0 < (s.card : ℝ) := by exact_mod_cast hs.card_pos
  have hqsum : ∑ _i ∈ s, (s.card : ℝ)⁻¹ = 1 := by
    simp [nsmul_eq_mul, hc.ne']
  have h := finiteEntropy_le_cross s p (fun _ ↦ (s.card : ℝ)⁻¹) hp hsum
    (fun _ _ ↦ inv_pos.mpr hc) hqsum.le
  simpa only [inv_inv, ← Finset.sum_mul, hsum, one_mul] using h

/-- Normalizing weights with nonzero total mass gives total mass one. -/
theorem normalized_weights_sum (s : Finset ι) (w : ι → ℝ)
    (hH : (∑ i ∈ s, w i) ≠ 0) :
    ∑ i ∈ s, w i / (∑ j ∈ s, w j) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hH

/-- The proportional allocation spends exactly the prescribed total confidence budget. -/
theorem proportional_allocation_sum (s : Finset ι) (w : ι → ℝ) (δ : ℝ)
    (hH : (∑ i ∈ s, w i) ≠ 0) :
    ∑ i ∈ s, δ * w i / (∑ j ∈ s, w j) = δ := by
  rw [← Finset.sum_div, ← Finset.mul_sum, mul_div_cancel_right₀ _ hH]

/-- Entropy is the exact additional logarithmic cost of a proportional allocation.
Zero probability weights cause no exception because their cost summand is zero. -/
theorem probability_allocation_cost_identity (s : Finset ι) (p : ι → ℝ) (δ : ℝ)
    (hsum : ∑ i ∈ s, p i = 1) (hδ : δ ≠ 0) :
    (∑ i ∈ s, p i * Real.log (δ * p i)⁻¹) =
      Real.log δ⁻¹ + finiteEntropy s p := by
  calc
    (∑ i ∈ s, p i * Real.log (δ * p i)⁻¹) =
        ∑ i ∈ s, (p i * Real.log δ⁻¹ + p i * Real.log (p i)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hpi : p i = 0
      · simp [hpi]
      rw [Real.log_inv, Real.log_mul hδ hpi, Real.log_inv, Real.log_inv]
      ring
    _ = Real.log δ⁻¹ + finiteEntropy s p := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
      rfl

/-- Exact weighted cost of `αᵢ = δ wᵢ/H`, where `H` is the sum of the weights. -/
theorem weighted_allocation_cost_identity (s : Finset ι) (w : ι → ℝ) (δ : ℝ)
    (hH : (∑ i ∈ s, w i) ≠ 0) (hδ : δ ≠ 0) :
    (∑ i ∈ s, w i * Real.log (δ * w i / (∑ j ∈ s, w j))⁻¹) =
      (∑ i ∈ s, w i) *
        (Real.log δ⁻¹ + finiteEntropy s (fun i ↦ w i / (∑ j ∈ s, w j))) := by
  let H := ∑ i ∈ s, w i
  have hcost := probability_allocation_cost_identity s (fun i ↦ w i / H) δ
    (normalized_weights_sum s w hH) hδ
  calc
    (∑ i ∈ s, w i * Real.log (δ * w i / (∑ j ∈ s, w j))⁻¹) =
        H * ∑ i ∈ s, (w i / H) * Real.log (δ * (w i / H))⁻¹ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hc : H * (w i / H) = w i := by field_simp [show H ≠ 0 from hH]
      rw [← mul_assoc, hc, mul_div_assoc]
    _ = _ := congrArg (H * ·) hcost

/-- Splitting the logarithmic confidence cost into a common budget cost and
the cross entropy with the normalized allocation. -/
theorem weighted_allocation_cost_decomposition (s : Finset ι) (w α : ι → ℝ) (δ : ℝ)
    (hH : (∑ i ∈ s, w i) ≠ 0) (hδ : δ ≠ 0) (hα : ∀ i ∈ s, α i ≠ 0) :
    (∑ i ∈ s, w i * Real.log (α i)⁻¹) =
      (∑ i ∈ s, w i) * (Real.log δ⁻¹ +
        ∑ i ∈ s, (w i / (∑ j ∈ s, w j)) * Real.log (α i / δ)⁻¹) := by
  let H := ∑ i ∈ s, w i
  calc
    (∑ i ∈ s, w i * Real.log (α i)⁻¹) =
        ∑ i ∈ s, (w i * Real.log δ⁻¹ + w i * Real.log (α i / δ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Real.log_inv, Real.log_inv, Real.log_inv, Real.log_div (hα i hi) hδ]
      ring
    _ = H * Real.log δ⁻¹ + ∑ i ∈ s, w i * Real.log (α i / δ)⁻¹ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
    _ = H * (Real.log δ⁻¹ +
        ∑ i ∈ s, (w i / H) * Real.log (α i / δ)⁻¹) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hc : H * (w i / H) = w i := by field_simp [show H ≠ 0 from hH]
      rw [← mul_assoc, hc]

/-- Every positive allocation of total confidence at most `δ` has cost at least
the entropy formula. This is a deterministic consequence of finite Gibbs. -/
theorem weighted_allocation_cost_lower_bound (s : Finset ι) (w α : ι → ℝ) (δ : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hH : 0 < ∑ i ∈ s, w i) (hδ : 0 < δ)
    (hα : ∀ i ∈ s, 0 < α i) (hαsum : ∑ i ∈ s, α i ≤ δ) :
    (∑ i ∈ s, w i) *
        (Real.log δ⁻¹ + finiteEntropy s (fun i ↦ w i / (∑ j ∈ s, w j))) ≤
      ∑ i ∈ s, w i * Real.log (α i)⁻¹ := by
  have hqsum : ∑ i ∈ s, α i / δ ≤ 1 := by
    rw [← Finset.sum_div]
    exact (div_le_iff₀ hδ).mpr (by simpa using hαsum)
  have hG := finiteEntropy_le_cross s (fun i ↦ w i / (∑ j ∈ s, w j))
    (fun i ↦ α i / δ) (fun i hi ↦ div_nonneg (hw i hi) hH.le)
    (normalized_weights_sum s w hH.ne') (fun i hi ↦ div_pos (hα i hi) hδ) hqsum
  rw [weighted_allocation_cost_decomposition s w α δ hH.ne' hδ.ne'
    (fun i hi ↦ (hα i hi).ne')]
  exact mul_le_mul_of_nonneg_left (by linarith) hH.le

/-- With positive weights, the proportional allocation is itself feasible. -/
theorem proportional_allocation_feasible (s : Finset ι) (w : ι → ℝ) (δ : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hH : 0 < ∑ i ∈ s, w i) (hδ : 0 < δ) :
    (∀ i ∈ s, 0 < δ * w i / (∑ j ∈ s, w j)) ∧
      (∑ i ∈ s, δ * w i / (∑ j ∈ s, w j)) = δ := by
  exact ⟨fun i hi ↦ div_pos (mul_pos hδ (hw i hi)) hH,
    proportional_allocation_sum s w δ hH.ne'⟩

/-- Proportional allocation minimizes the weighted confidence cost over all
positive allocations with total mass at most `δ`. -/
theorem proportional_allocation_optimal (s : Finset ι) (w α : ι → ℝ) (δ : ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hH : 0 < ∑ i ∈ s, w i) (hδ : 0 < δ)
    (hα : ∀ i ∈ s, 0 < α i) (hαsum : ∑ i ∈ s, α i ≤ δ) :
    (∑ i ∈ s, w i * Real.log (δ * w i / (∑ j ∈ s, w j))⁻¹) ≤
      ∑ i ∈ s, w i * Real.log (α i)⁻¹ := by
  rw [weighted_allocation_cost_identity s w δ hH.ne' hδ.ne']
  exact weighted_allocation_cost_lower_bound s w α δ (fun i hi ↦ (hw i hi).le)
    hH hδ hα hαsum

end GapEntropy
