import GapEntropy.Gaussian
import Mathlib.Probability.Independence.InfinitePi

/-!
# Sample-mean tails of independent standard Gaussian noise

`law m` is the product of `m` standard Gaussians and `mean` is the coordinate average. Any
measure-preserving map into this law has independent standard Gaussian coordinates, so the
two-sided sample-mean tail of `Gaussian` applies. The A.3 budget arithmetic then shows that
`512 · d⁻² · log(C/α)` samples make a deviation of at least `d/16` occur with probability at
most `2α/C`, with the manuscript's coefficient `512`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MeasureTheory.Measure
open scoped BigOperators

namespace GapEntropy.GaussianNoise

def law (m : ℕ) : Measure (Fin m → ℝ) := infinitePi (fun _ => gaussianReal 0 1)

instance (m : ℕ) : IsProbabilityMeasure (law m) := by unfold law; infer_instance

def mean {m : ℕ} (x : Fin m → ℝ) : ℝ := (∑ j, x j) / (m : ℝ)

theorem mean_measurable (m : ℕ) : Measurable (mean (m := m)) := by
  unfold mean
  fun_prop

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem mean_tail {m : ℕ} (hm : 0 < m) {F : Ω → Fin m → ℝ}
    (hF : MeasurePreserving F P (law m)) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ |mean (F ω)|} ≤ 2 * Real.exp (-((m : ℝ) * t ^ 2) / 2) := by
  have hlaw (j : Fin m) : HasLaw (fun ω => F ω j) (gaussianReal 0 1) P := by
    have h := (measurePreserving_eval_infinitePi (fun _ : Fin m => gaussianReal 0 1) j).comp hF
    exact ⟨h.measurable.aemeasurable, h.map_eq⟩
  have hind : iIndepFun (fun j ω => F ω j) P := by
    apply (iIndepFun_iff_hasLaw_Pi_infinitePi hlaw hF.measurable.aemeasurable).mpr
    exact ⟨hF.measurable.aemeasurable, hF.map_eq⟩
  simpa only [GapEntropy.Gaussian.sampleMean, sub_zero, mean] using
    GapEntropy.Gaussian.sampleMean_two_sided hm hind hlaw ht

/-- Exact A.3 Gaussian tail arithmetic, including the manuscript's coefficient 512. -/
theorem two_tail_of_budget {m : ℕ} {d α C : ℝ} (hd : 0 < d) (hα : 0 < α) (hC : 0 < C)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (C / α) ≤ (m : ℝ)) :
    2 * Real.exp (-((m : ℝ) * (d / 16) ^ 2) / 2) ≤ 2 * α / C := by
  have hmul := mul_le_mul_of_nonneg_right hbudget (sq_nonneg d)
  have heq : (512 * (d ^ 2)⁻¹ * Real.log (C / α)) * d ^ 2 =
      512 * Real.log (C / α) := by field_simp [hd.ne']
  rw [heq] at hmul
  have hexp : -((m : ℝ) * (d / 16) ^ 2) / 2 ≤ -Real.log (C / α) := by
    nlinarith
  have hexpbound := Real.exp_le_exp.mpr hexp
  rw [Real.exp_neg, Real.exp_log (div_pos hC hα)] at hexpbound
  simp only [inv_div] at hexpbound
  calc
    _ ≤ 2 * (α / C) := mul_le_mul_of_nonneg_left hexpbound (by norm_num)
    _ = _ := by ring

theorem mean_tail_of_budget {m : ℕ} (hm : 0 < m) {F : Ω → Fin m → ℝ}
    (hF : MeasurePreserving F P (law m)) {d α C : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hC : 0 < C)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (C / α) ≤ (m : ℝ)) :
    P.real {ω | d / 16 ≤ |mean (F ω)|} ≤ 2 * α / C :=
  (mean_tail hm hF (by positivity)).trans (two_tail_of_budget hd hα hC hbudget)

end GapEntropy.GaussianNoise
