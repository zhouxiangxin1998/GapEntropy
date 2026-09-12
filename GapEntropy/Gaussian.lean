import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gaussian sample-mean concentration

This module proves the fixed-block Gaussian inequalities used in manuscript (A.1).
The hypotheses are genuine Gaussian laws and independence on a probability space.
The proof uses mathlib's Gaussian MGF formula and its independent-sum Chernoff bound;
it does not assume concentration as an input.
-/

namespace GapEntropy.Gaussian

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A zero-mean Gaussian has sub-Gaussian parameter equal to its variance. -/
theorem subgaussian_of_gaussian_zero {X : Ω → ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal 0 v) P) : HasSubgaussianMGF X v P := by
  constructor
  · intro t
    rw [← mgf_pos_iff, mgf_gaussianReal hX.map_eq]
    exact Real.exp_pos _
  · intro t
    rw [mgf_gaussianReal hX.map_eq]
    simp

/-- Centering a Gaussian produces the sub-Gaussian MGF bound with the original variance. -/
theorem subgaussian_centered {X : Ω → ℝ} {a : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal a v) P) :
    HasSubgaussianMGF (fun ω => X ω - a) v P := by
  apply subgaussian_of_gaussian_zero
  simpa using gaussianReal_sub_const hX a

/-- The empirical mean of a nonempty block indexed by `Fin m`. -/
def sampleMean {m : ℕ} (X : Fin m → Ω → ℝ) (ω : Ω) : ℝ :=
  (∑ i, X i ω) / (m : ℝ)

omit [MeasurableSpace Ω] in
theorem sampleMean_centered_eq {m : ℕ} (hm : 0 < m) (X : Fin m → Ω → ℝ)
    (a : ℝ) (ω : Ω) :
    sampleMean X ω - a = (m : ℝ)⁻¹ * ∑ i, (X i ω - a) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [sampleMean, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- For independent unit-variance Gaussian observations with common mean `a`,
the centered empirical mean has sub-Gaussian variance parameter `1/m`. -/
theorem sampleMean_subgaussian {m : ℕ} (hm : 0 < m) {X : Fin m → Ω → ℝ}
    {a : ℝ} (hind : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal a 1) P) :
    HasSubgaussianMGF (fun ω => sampleMean X ω - a) (m : ℝ≥0)⁻¹ P := by
  have hind' : iIndepFun (fun i ω => X i ω - a) P :=
    hind.comp (fun _ y => y - a) (fun _ => by fun_prop)
  have hsum : HasSubgaussianMGF (fun ω => ∑ i, (X i ω - a)) (m : ℝ≥0) P := by
    simpa using HasSubgaussianMGF.sum_of_iIndepFun hind'
      (s := Finset.univ) (c := fun _ => 1)
      (fun i _ => subgaussian_centered (hlaw i))
  have hscaled := hsum.const_mul (m : ℝ)⁻¹
  have hparam : (NNReal.mk (((m : ℝ)⁻¹) ^ 2) (sq_nonneg _)) * (m : NNReal) =
      (m : ℝ≥0)⁻¹ := by
    apply NNReal.coe_injective
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_natCast, NNReal.coe_inv]
    field_simp
  change HasSubgaussianMGF _ (NNReal.mk (((m : ℝ)⁻¹) ^ 2) (sq_nonneg _) *
    (m : NNReal)) P at hscaled
  rw [hparam] at hscaled
  exact hscaled.congr (ae_of_all P fun ω => (sampleMean_centered_eq hm X a ω).symm)

omit [IsProbabilityMeasure P] in
/-- A two-sided Chernoff bound derived from the right-tail bound and reflection. -/
theorem subgaussian_abs_tail {Y : Ω → ℝ} {c : ℝ≥0}
    (hY : HasSubgaussianMGF Y c P) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ |Y ω|} ≤ 2 * Real.exp (-t ^ 2 / (2 * c)) := by
  have hevent : {ω | t ≤ |Y ω|} = {ω | t ≤ Y ω} ∪ {ω | t ≤ -Y ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hevent]
  calc
    _ ≤ P.real {ω | t ≤ Y ω} + P.real {ω | t ≤ -Y ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-t ^ 2 / (2 * c)) + Real.exp (-t ^ 2 / (2 * c)) :=
      add_le_add (hY.measure_ge_le ht) (hY.neg.measure_ge_le ht)
    _ = 2 * Real.exp (-t ^ 2 / (2 * c)) := by ring

private theorem mean_exponent {m : ℕ} (hm : 0 < m) (t : ℝ) :
    -t ^ 2 / (2 * (↑((m : ℝ≥0)⁻¹) : ℝ)) = -((m : ℝ) * t ^ 2) / 2 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [NNReal.coe_inv, NNReal.coe_natCast]
  field_simp

/-- The upper one-sided Gaussian sample-mean bound in (D.9), with exact constant `1/2`. -/
theorem sampleMean_upper_tail {m : ℕ} (hm : 0 < m) {X : Fin m → Ω → ℝ}
    {a t : ℝ} (hind : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal a 1) P) (ht : 0 ≤ t) :
    P.real {ω | t ≤ sampleMean X ω - a} ≤ Real.exp (-((m : ℝ) * t ^ 2) / 2) := by
  have h := (sampleMean_subgaussian hm hind hlaw).measure_ge_le ht
  rwa [mean_exponent hm t] at h

/-- The lower one-sided Gaussian sample-mean bound in (D.9). -/
theorem sampleMean_lower_tail {m : ℕ} (hm : 0 < m) {X : Fin m → Ω → ℝ}
    {a t : ℝ} (hind : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal a 1) P) (ht : 0 ≤ t) :
    P.real {ω | sampleMean X ω - a ≤ -t} ≤ Real.exp (-((m : ℝ) * t ^ 2) / 2) := by
  have h := (sampleMean_subgaussian hm hind hlaw).neg.measure_ge_le ht
  rw [mean_exponent hm t] at h
  convert h using 1
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, Pi.neg_apply]
  constructor <;> intro hω <;> linarith

/-- The two-sided Gaussian sample-mean concentration inequality (A.1). -/
theorem sampleMean_two_sided {m : ℕ} (hm : 0 < m) {X : Fin m → Ω → ℝ}
    {a t : ℝ} (hind : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal a 1) P) (ht : 0 ≤ t) :
    P.real {ω | t ≤ |sampleMean X ω - a|} ≤
      2 * Real.exp (-((m : ℝ) * t ^ 2) / 2) := by
  have h := subgaussian_abs_tail (sampleMean_subgaussian hm hind hlaw) ht
  rwa [mean_exponent hm t] at h

end

end GapEntropy.Gaussian
