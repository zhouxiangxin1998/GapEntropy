import GapEntropy.Problem
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Explicit comparison of positive iterated-log conventions

The source's untruncated expression is undefined in ordinary analysis at gap one
and can be negative nearby. This module compares an explicitly *positive*
max-with-one convention with the manuscript's smooth truncation. It makes no
identification with `SourceConjecture32Literal`.
-/
noncomputable section
namespace GapEntropy

/-- A precise conventional positive truncation of log log(1/gap), where D=gap⁻². -/
def positiveSourceIteratedLog (D : ℝ) : ℝ :=
  max 1 (Real.log (Real.log (Real.sqrt D)))

theorem one_le_iteratedLog {D : ℝ} (hD : 0 ≤ D) : 1 ≤ iteratedLog D := by
  have he := Real.exp_pos 1
  have he1 := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
  have hlog := Real.log_nonneg (show 1 ≤ Real.exp 1 + D by linarith)
  have h := Real.log_le_log he (show Real.exp 1 ≤ Real.exp 1 + Real.log (Real.exp 1 + D) by linarith)
  simpa only [Real.log_exp, iteratedLog] using h

theorem positiveSourceIteratedLog_le {D : ℝ} (hD : 1 ≤ D) :
    positiveSourceIteratedLog D ≤ iteratedLog D := by
  have hD0 : 0 < D := by linarith
  have hlogD := Real.log_nonneg hD
  rw [positiveSourceIteratedLog, Real.log_sqrt hD0.le]
  apply max_le (one_le_iteratedLog hD0.le)
  by_cases hx : Real.log D / 2 ≤ 1
  · exact (Real.log_nonpos (by positivity) hx).trans
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_iteratedLog hD0.le))
  · have hlog : Real.log D ≤ Real.log (Real.exp 1 + D) :=
      Real.log_le_log hD0 (by linarith [Real.exp_pos 1])
    exact Real.log_le_log (by linarith) (by linarith [Real.exp_pos 1])

/-- Uniform comparison on the entire legal gap range, including D=1. -/
theorem iteratedLog_le_seven_positiveSource {D : ℝ} (hD : 1 ≤ D) :
    iteratedLog D ≤ 7 * positiveSourceIteratedLog D := by
  have hD0 : 0 < D := by linarith
  have he := Real.exp_pos 1
  have he3 := Real.exp_one_lt_three
  have hlogD := Real.log_nonneg hD
  have hlog : Real.log (Real.exp 1 + D) ≤ Real.log (4 * D) := by
    apply Real.log_le_log (by positivity)
    nlinarith
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hD0.ne'] at hlog
  have h4 : Real.log (4 : ℝ) ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    norm_num at h
    exact h
  have hinner : Real.exp 1 + Real.log (Real.exp 1 + D) ≤ 6 + Real.log D := by linarith
  have hinner0 : 0 < Real.exp 1 + Real.log (Real.exp 1 + D) := by
    have he1 := Real.one_le_exp (show (0 : ℝ) ≤ 1 by norm_num)
    have hl := Real.log_nonneg (show 1 ≤ Real.exp 1 + D by linarith)
    positivity
  rw [positiveSourceIteratedLog, Real.log_sqrt hD0.le]
  have ht1 : (1 : ℝ) ≤ max 1 (Real.log (Real.log D / 2)) := le_max_left _ _
  have htx : Real.log (Real.log D / 2) ≤ max 1 (Real.log (Real.log D / 2)) := le_max_right _ _
  have h8 : Real.log (8 : ℝ) ≤ 6 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have hpow := Real.log_pow (2 : ℝ) 3
    norm_num at h2 hpow
    linarith
  by_cases hx : Real.log D / 2 ≤ 1
  · have h := Real.log_le_log hinner0 (show
        Real.exp 1 + Real.log (Real.exp 1 + D) ≤ 8 by linarith)
    unfold iteratedLog
    linarith
  · have hx0 : 0 < Real.log D / 2 := by linarith
    have h := Real.log_le_log hinner0 (show
        Real.exp 1 + Real.log (Real.exp 1 + D) ≤ 8 * (Real.log D / 2) by linarith)
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) hx0.ne'] at h
    unfold iteratedLog
    linarith

/-- A new, explicitly truncated source-cost definition; the literal expression
in Problem.lean is preserved unchanged. -/
def positiveSourceTwoArmCost {n : ℕ} (I : Instance n) : ℝ :=
  I.twoArmHardness * positiveSourceIteratedLog I.twoArmHardness

theorem twoArmCost_truncation_comparison {n : ℕ} (I : Instance n) :
    positiveSourceTwoArmCost I ≤ twoArmCost I ∧
      twoArmCost I ≤ 7 * positiveSourceTwoArmCost I := by
  have hD : 0 ≤ I.twoArmHardness := by linarith [I.one_le_twoArmHardness]
  constructor
  · exact mul_le_mul_of_nonneg_left (positiveSourceIteratedLog_le I.one_le_twoArmHardness) hD
  · have h := mul_le_mul_of_nonneg_left
      (iteratedLog_le_seven_positiveSource I.one_le_twoArmHardness) hD
    simpa only [twoArmCost, positiveSourceTwoArmCost, mul_left_comm] using h

/-- The truncated two-arm term is exactly the maximum of D and the totalized
literal source expression; it is a different function near gap one. -/
theorem positiveSourceTwoArmCost_eq_max {n : ℕ} (I : Instance n) :
    positiveSourceTwoArmCost I = max I.twoArmHardness (sourceTwoArmExpression I) := by
  have hD : 0 ≤ I.twoArmHardness := by linarith [I.one_le_twoArmHardness]
  unfold positiveSourceTwoArmCost positiveSourceIteratedLog sourceTwoArmExpression
  rw [mul_max_of_nonneg _ _ hD, mul_one]

/-- Conjecture 3.2 with an explicitly specified max-with-one log-log convention. -/
def PositiveSourceAlmostInstanceWiseOptimality : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ → Algorithm,
    ∀ δ : ℝ, ValidConfidence δ → DeltaCorrect (A δ) δ ∧
      ∀ (n : ℕ) (I : Instance n),
        (A δ n).expectedSamples I ≤ ENNReal.ofReal C *
          (benchmark I δ + ENNReal.ofReal (positiveSourceTwoArmCost I))

/-- Exact equivalence of the two explicitly positive conventions, with the
same algorithms and at most a factor-seven change of the universal constant. -/
theorem almostInstanceWiseOptimality_iff_positiveTruncation :
    AlmostInstanceWiseOptimality ↔ PositiveSourceAlmostInstanceWiseOptimality := by
  constructor
  · rintro ⟨C, hC, A, hA⟩
    refine ⟨7 * C, by positivity, A, ?_⟩
    intro δ hδ
    obtain ⟨hc, ht⟩ := hA δ hδ
    refine ⟨hc, fun n I => (ht n I).trans ?_⟩
    have hterm : ENNReal.ofReal (twoArmCost I) ≤
        7 * ENNReal.ofReal (positiveSourceTwoArmCost I) := by
      have h := ENNReal.ofReal_le_ofReal (twoArmCost_truncation_comparison I).2
      simpa only [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 7 by norm_num), ENNReal.ofReal_ofNat] using h
    have hbench : benchmark I δ ≤ 7 * benchmark I δ :=
      le_mul_of_one_le_left zero_le (by norm_num)
    calc
      ENNReal.ofReal C * (benchmark I δ + ENNReal.ofReal (twoArmCost I)) ≤
          ENNReal.ofReal C * (7 * benchmark I δ +
            7 * ENNReal.ofReal (positiveSourceTwoArmCost I)) :=
        mul_le_mul' le_rfl (add_le_add hbench hterm)
      _ = _ := by
        rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 7 by norm_num), ENNReal.ofReal_ofNat]
        ring
  · rintro ⟨C, hC, A, hA⟩
    refine ⟨C, hC, A, ?_⟩
    intro δ hδ
    obtain ⟨hc, ht⟩ := hA δ hδ
    refine ⟨hc, fun n I => (ht n I).trans ?_⟩
    exact mul_le_mul' le_rfl (add_le_add le_rfl
      (ENNReal.ofReal_le_ofReal (twoArmCost_truncation_comparison I).1))

end GapEntropy
