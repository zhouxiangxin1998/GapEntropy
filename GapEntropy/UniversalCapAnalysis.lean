import GapEntropy.Problem
import GapEntropy.TargetEntropyBudget
import GapEntropy.FixedCapRetryTail

/-!
# Noncircular universal sample-cap analysis

These are the numerical steps F.10–F.14. The favorable-path declared sample
cost is an input to this module, not an assumed actual runtime conclusion.
All threshold indices depend on the instance only in the analysis.
-/
noncomputable section
open scoped BigOperators ENNReal

namespace GapEntropy.UniversalCapAnalysis

/-- The fixed positive truncation dominates the logarithm needed to count scales. -/
theorem log_one_add_log_le_iteratedLog {D : ℝ} (hD : 1 ≤ D) :
    Real.log (1 + Real.log D) ≤ iteratedLog D := by
  have hD0 : 0 < D := by linarith
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hlog' : Real.log D ≤ Real.log (Real.exp 1 + D) :=
    Real.log_le_log hD0 (by linarith [Real.exp_pos 1])
  exact Real.log_le_log (by linarith) (by linarith)

/-- F.11 with an explicit constant 1, valid for every later dyadic guess. -/
theorem log_index_le (j : ℕ) {D : ℝ} (hD : 1 ≤ D) (hDj : D ≤ (2 : ℝ) ^ j) :
    Real.log (j + 1 : ℝ) ≤ 1 + iteratedLog D + Real.log ((2 : ℝ) ^ j / D) := by
  have hD0 : 0 < D := by linarith
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hy : 0 ≤ Real.log ((2 : ℝ) ^ j / D) :=
    Real.log_nonneg ((one_le_div hD0).mpr hDj)
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have htwo1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have heq : Real.log ((2 : ℝ) ^ j / D) = j * Real.log 2 - Real.log D := by
    rw [Real.log_div (by positivity) hD0.ne', Real.log_pow]
  have harg : (j + 1 : ℝ) ≤ 2 * ((1 + Real.log D) *
      (1 + Real.log ((2 : ℝ) ^ j / D))) := by
    nlinarith [mul_nonneg hlogD hy]
  have h := Real.log_le_log (by positivity : (0 : ℝ) < j + 1) harg
  rw [Real.log_mul (by norm_num) (mul_pos (by linarith) (by linarith)).ne',
    Real.log_mul (by linarith : 1 + Real.log D ≠ 0)
      (by linarith : 1 + Real.log ((2 : ℝ) ^ j / D) ≠ 0)] at h
  have hylog := Real.log_le_sub_one_of_pos (show 0 <
    1 + Real.log ((2 : ℝ) ^ j / D) by linarith)
  linarith [log_one_add_log_le_iteratedLog hD]

theorem weight_log_ratio_le {a h : ℝ} (ha : 0 < a) (hah : a ≤ h) :
    a * Real.log (h / a) ≤ h := by
  have hratio : 0 < h / a := div_pos (lt_of_lt_of_le ha hah) ha
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio) ha.le
  have he : a * (h / a) = h := by field_simp
  nlinarith

/-- Analysis-only target scale Ψ from F.10. -/
def complexityTarget {n : ℕ} (I : Instance n) (δ : ℝ) : ℝ :=
  I.hardness * (confidenceCost δ + I.gapEntropy + 1) + twoArmCost I

theorem complexityTarget_eq {n : ℕ} (I : Instance n) (δ : ℝ) :
    complexityTarget I δ = entropyCost I δ + twoArmCost I + I.hardness := by
  unfold complexityTarget entropyCost
  ring

theorem complexityTarget_pos {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) : 0 < complexityTarget I δ := by
  rw [complexityTarget_eq]
  have h₁ := entropyCost_pos hδ I
  have h₂ := twoArmCost_pos I
  have h₃ := I.hardness_pos
  positivity

theorem one_le_confidenceCost {δ : ℝ} (hδ : ValidConfidence δ) : 1 ≤ confidenceCost δ :=
  TargetAttempt.one_le_log_inv hδ.1 (by linarith [hδ.2])

theorem hardness_le_target_div {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) : I.hardness ≤ complexityTarget I δ / confidenceCost δ := by
  apply (le_div_iff₀ (confidenceCost_pos hδ)).mpr
  unfold complexityTarget
  have hH := I.hardness_pos
  have hE := I.gapEntropy_nonneg
  have hD := twoArmCost_pos I
  nlinarith

theorem complexityTarget_le_twice_cost {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) : complexityTarget I δ ≤
      2 * (entropyCost I δ + twoArmCost I) := by
  rw [complexityTarget_eq]
  have hH := I.hardness_pos
  have hE := I.gapEntropy_nonneg
  have hD := twoArmCost_pos I
  have hL := one_le_confidenceCost hδ
  unfold entropyCost
  nlinarith

/-- A dyadic threshold within factor two. Choosing one step above a dyadic
endpoint is harmless; no integer-ceiling convention is silently substituted. -/
theorem exists_dyadic_threshold {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) : ∃ j₀ : ℕ,
      complexityTarget I δ ≤ (2 : ℝ) ^ j₀ * confidenceCost δ ∧
      (2 : ℝ) ^ j₀ * confidenceCost δ ≤ 2 * complexityTarget I δ ∧
      I.hardness ≤ (2 : ℝ) ^ j₀ := by
  have hL := confidenceCost_pos hδ
  have hH := hardness_le_target_div I hδ
  have h1 : 1 ≤ complexityTarget I δ / confidenceCost δ :=
    (I.one_le_twoArmHardness.trans I.twoArmHardness_le_hardness).trans hH
  obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near h1 (show (1 : ℝ) < 2 by norm_num)
  refine ⟨j + 1, (div_le_iff₀ hL).mp hj'.le, ?_, hH.trans hj'.le⟩
  have hb := mul_le_mul_of_nonneg_right ((le_div_iff₀ hL).mp hj) (show (0 : ℝ) ≤ 2 by norm_num)
  rw [pow_succ]
  nlinarith

/-- The declared favorable sample-cost expression of F.9 before its universal
sampling constant is applied. -/
def favorableCost {n : ℕ} (I : Instance n) (δ : ℝ) (j : ℕ) : ℝ :=
  I.hardness * (confidenceCost δ + I.gapEntropy + 1 + Real.log ((2 : ℝ) ^ j / I.hardness)) +
    I.twoArmHardness * (confidenceCost δ + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness)

/-- F.12: a fixed factor 5 suffices for the F.9 expression after the threshold. -/
theorem favorableCost_le {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) (j : ℕ)
    (hfit : complexityTarget I δ ≤ (2 : ℝ) ^ j * confidenceCost δ) :
    favorableCost I δ j ≤ 5 * (2 : ℝ) ^ j * confidenceCost δ := by
  have hL := one_le_confidenceCost hδ
  have hL0 := confidenceCost_pos hδ
  have hHj : I.hardness ≤ (2 : ℝ) ^ j :=
    (hardness_le_target_div I hδ).trans ((div_le_iff₀ hL0).mpr hfit)
  have hDj := I.twoArmHardness_le_hardness.trans hHj
  have hD0 : 0 < I.twoArmHardness := by linarith [I.one_le_twoArmHardness]
  have hlogj := mul_le_mul_of_nonneg_left (log_index_le j I.one_le_twoArmHardness hDj) hD0.le
  have hlogH := weight_log_ratio_le I.hardness_pos hHj
  have hlogD := weight_log_ratio_le hD0 hDj
  have hDL := mul_le_mul_of_nonneg_right I.twoArmHardness_le_hardness hL0.le
  have hh : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ j * confidenceCost δ :=
    le_mul_of_one_le_right (by positivity) hL
  have hH := I.hardness_pos
  have hE := I.gapEntropy_nonneg
  have hHE : 0 ≤ I.hardness * (I.gapEntropy + 1) := by positivity
  unfold favorableCost complexityTarget twoArmCost at *
  nlinarith

/-- Ceilings in Q_j can be charged to the same dyadic factor on every path. -/
theorem sampleCap_le {C L : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (j : ℕ) :
    (⌈C * (2 : ℝ) ^ j * L⌉₊ : ℝ) ≤ (C * L + 1) * 2 ^ j := by
  have hc := (Nat.ceil_lt_add_one (show 0 ≤ C * (2 : ℝ) ^ j * L by positivity)).le
  have hpow : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
  nlinarith

/-- Numerical F.14 applied to the actual retry policy. Only the large-attempt
abort guarantee remains statistical; caps and the infinite-path accounting are
fully discharged here. -/
theorem expectedSamples_le_entropy_of_abort_bound {n : ℕ}
    (R : ℕ → BoundedProcedure n (Option (Fin n))) (hpos : ∀ j, 0 < (R j).budget)
    (I : Instance n) {δ C : ℝ} (hδ : ValidConfidence δ) (hC : 0 ≤ C)
    (hcap : ∀ j, (R j).budget = ⌈C * (2 : ℝ) ^ j * confidenceCost δ⌉₊)
    (habort : ∀ j, complexityTarget I δ ≤ (2 : ℝ) ^ j * confidenceCost δ →
      GaussianBlocks.blockLaw I.mean (R j).budget {x | (R j).evaluate x = none} ≤ 1 / 4) :
    (FixedCapRetry.policy R hpos).expectedSamples I ≤
      ENNReal.ofReal (12 * (C + 1) * (entropyCost I δ + twoArmCost I)) := by
  obtain ⟨j₀, hj₀, hj₀upper, _⟩ := exists_dyadic_threshold I hδ
  have hL := one_le_confidenceCost hδ
  have hL0 := confidenceCost_pos hδ
  have ht := FixedCapRetry.expectedSamples_le_dyadic_tail R hpos I j₀
    (K := C * confidenceCost δ + 1) (by positivity)
    (fun j => by rw [hcap]; exact sampleCap_le hC hL0.le j)
    (fun j hj => habort j (hj₀.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hL0.le)))
  apply ht.trans (ENNReal.ofReal_le_ofReal ?_)
  have hK : C * confidenceCost δ + 1 ≤ (C + 1) * confidenceCost δ := by nlinarith
  have ha := mul_le_mul_of_nonneg_right hK (show 0 ≤ 3 * (2 : ℝ) ^ j₀ by positivity)
  have hb := mul_le_mul_of_nonneg_left hj₀upper (show 0 ≤ 3 * (C + 1) by positivity)
  have hc := mul_le_mul_of_nonneg_left (complexityTarget_le_twice_cost I hδ)
    (show 0 ≤ 6 * (C + 1) by positivity)
  nlinarith

/-- F.2's generous base-work reservation is strictly sufficient whenever the
prospective favorable envelope is at most 171H and the guess exceeds H. -/
theorem prospective_work_fits {H h w : ℝ} (hH : 0 < H) (hHh : H ≤ h)
    (hw : w ≤ 171 * H) : w < 1024 * h := by
  nlinarith

end GapEntropy.UniversalCapAnalysis
