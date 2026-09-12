import GapEntropy.UniversalTheorem

/-!
# The small-gap and easy-gap iterated-log regimes

This module records the elementary consequences used when comparing the
globally positive iterated-log convention with the source's raw expression.
Above the explicit threshold `exp (2 * exp 1)`, the max-with-one convention is
exactly the raw double logarithm.  Below that threshold, it is exactly one and
the smooth convention is universally bounded.

The final two theorems combine these regime facts with the proved gap-entropy
lower bound.  They give the actual universal policy's raw source bound in the
small-gap regime and its benchmark-only bound in the easy-gap regime.
-/

noncomputable section
open scoped ENNReal

namespace GapEntropy

/-- The hardness threshold corresponding to `log (log (sqrt D)) = 1`. -/
def sourceIteratedLogThreshold : ℝ := Real.exp (2 * Real.exp 1)

/-- Beyond the source threshold, the positive convention is literally the raw
source double logarithm. -/
theorem positiveSourceIteratedLog_eq_raw_of_threshold_le {D : ℝ}
    (hD : sourceIteratedLogThreshold ≤ D) :
    positiveSourceIteratedLog D = Real.log (Real.log (Real.sqrt D)) := by
  have hthreshold_pos : 0 < sourceIteratedLogThreshold := Real.exp_pos _
  have hD_pos : 0 < D := hthreshold_pos.trans_le hD
  have hlogD : 2 * Real.exp 1 ≤ Real.log D := by
    rw [← Real.exp_le_exp]
    simpa only [sourceIteratedLogThreshold, Real.exp_log hD_pos] using hD
  rw [positiveSourceIteratedLog, max_eq_right]
  rw [Real.log_sqrt hD_pos.le]
  have hinner : Real.exp 1 ≤ Real.log D / 2 := by linarith
  calc
    1 = Real.log (Real.exp 1) := by rw [Real.log_exp]
    _ ≤ Real.log (Real.log D / 2) :=
      Real.log_le_log (Real.exp_pos 1) hinner

/-- Up to the source threshold, the positive convention is exactly one. -/
theorem positiveSourceIteratedLog_eq_one_of_le_threshold {D : ℝ}
    (hD_lower : 1 ≤ D) (hD_upper : D ≤ sourceIteratedLogThreshold) :
    positiveSourceIteratedLog D = 1 := by
  have hD_pos : 0 < D := zero_lt_one.trans_le hD_lower
  have hlogD_nonneg : 0 ≤ Real.log D := Real.log_nonneg hD_lower
  have hlogD : Real.log D ≤ 2 * Real.exp 1 := by
    rw [← Real.exp_le_exp, Real.exp_log hD_pos]
    simpa only [sourceIteratedLogThreshold] using hD_upper
  have hinner_nonneg : 0 ≤ Real.log D / 2 := by positivity
  have hinner : Real.log D / 2 ≤ Real.exp 1 := by linarith
  have hraw : Real.log (Real.log (Real.sqrt D)) ≤ 1 := by
    rw [Real.log_sqrt hD_pos.le]
    by_cases hzero : Real.log D / 2 = 0
    · simp [hzero]
    · have hinner_pos : 0 < Real.log D / 2 :=
        lt_of_le_of_ne hinner_nonneg (Ne.symm hzero)
      calc
        Real.log (Real.log D / 2) ≤ Real.log (Real.exp 1) :=
          Real.log_le_log hinner_pos hinner
        _ = 1 := Real.log_exp 1
  exact max_eq_left hraw

/-- In the easy-gap regime the manuscript's smooth iterated logarithm is at
most the universal constant seven. -/
theorem iteratedLog_le_seven_of_le_threshold {D : ℝ}
    (hD_lower : 1 ≤ D) (hD_upper : D ≤ sourceIteratedLogThreshold) :
    iteratedLog D ≤ 7 := by
  calc
    iteratedLog D ≤ 7 * positiveSourceIteratedLog D :=
      iteratedLog_le_seven_positiveSource hD_lower
    _ = 7 := by rw [positiveSourceIteratedLog_eq_one_of_le_threshold hD_lower hD_upper]; norm_num

/-- On easy instances, the universal algorithm is already within an explicit
universal factor of the instance-wise benchmark, with no separate iterated-log
term in the conclusion. -/
theorem UniversalPolicy.expectedSamples_le_benchmark_of_twoArmHardness_le_threshold
    {n : ℕ} (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (hD : I.twoArmHardness ≤ sourceIteratedLogThreshold) :
    (UniversalPolicy.algorithm δ n).expectedSamples I ≤
      ENNReal.ofReal 480000000000480 * benchmark I δ := by
  have hL : 1 ≤ confidenceCost δ := UniversalCapAnalysis.one_le_confidenceCost hδ
  have hE : 0 ≤ I.gapEntropy := I.gapEntropy_nonneg
  have hH : 0 ≤ I.hardness := I.hardness_pos.le
  have hD0 : 0 ≤ I.twoArmHardness := (by norm_num : (0 : ℝ) ≤ 1).trans I.one_le_twoArmHardness
  have hiter : iteratedLog I.twoArmHardness ≤ 7 :=
    iteratedLog_le_seven_of_le_threshold I.one_le_twoArmHardness hD
  have htwo : twoArmCost I ≤ 7 * entropyCost I δ := by
    unfold twoArmCost entropyCost
    have hDH : I.twoArmHardness ≤ I.hardness := I.twoArmHardness_le_hardness
    have hconfEntropy : 1 ≤ confidenceCost δ + I.gapEntropy := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hiter hD0,
      mul_le_mul_of_nonneg_left hconfEntropy hH,
      mul_le_mul_of_nonneg_right hDH (show (0 : ℝ) ≤ 7 by norm_num)]
  have hcost : entropyCost I δ + twoArmCost I ≤ 8 * entropyCost I δ := by
    linarith
  have hentropy : 0 ≤ entropyCost I δ := (entropyCost_pos hδ I).le
  calc
    (UniversalPolicy.algorithm δ n).expectedSamples I ≤
        ENNReal.ofReal (12000000000012 * (entropyCost I δ + twoArmCost I)) :=
      UniversalPolicy.expectedSamples_le I hδ
    _ ≤ ENNReal.ofReal (12000000000012 * (8 * entropyCost I δ)) := by
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left hcost (by norm_num))
    _ = ENNReal.ofReal 480000000000480 *
        ENNReal.ofReal (entropyCost I δ / 5) := by
      rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 480000000000480)]
      congr 1
      ring
    _ ≤ ENNReal.ofReal 480000000000480 * benchmark I δ :=
      mul_le_mul' le_rfl (by
        simpa only [entropyCost, confidenceCost] using
          (benchmark_entropy_lower_bound I hδ))

/-- In the small-gap regime, the universal algorithm satisfies the source's
raw double-logarithm bound with an explicit universal constant. -/
theorem UniversalPolicy.expectedSamples_le_source_of_threshold_le_twoArmHardness
    {n : ℕ} (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (hD : sourceIteratedLogThreshold ≤ I.twoArmHardness) :
    (UniversalPolicy.algorithm δ n).expectedSamples I ≤
      ENNReal.ofReal 84000000000084 *
        (benchmark I δ + ENNReal.ofReal (sourceTwoArmExpression I)) := by
  have hsourceIterated :
      positiveSourceIteratedLog I.twoArmHardness =
        Real.log (Real.log (Real.sqrt I.twoArmHardness)) :=
    positiveSourceIteratedLog_eq_raw_of_threshold_le hD
  have hsourceCost : positiveSourceTwoArmCost I = sourceTwoArmExpression I := by
    unfold positiveSourceTwoArmCost sourceTwoArmExpression
    rw [hsourceIterated]
  have htwo : twoArmCost I ≤ 7 * sourceTwoArmExpression I := by
    calc
      twoArmCost I ≤ 7 * positiveSourceTwoArmCost I :=
        (twoArmCost_truncation_comparison I).2
      _ = 7 * sourceTwoArmExpression I := by rw [hsourceCost]
  have hentropy : 0 ≤ entropyCost I δ := (entropyCost_pos hδ I).le
  have htwo_nonneg : 0 ≤ twoArmCost I := (twoArmCost_pos I).le
  have hentropyENN : ENNReal.ofReal (entropyCost I δ) ≤ 5 * benchmark I δ := by
    calc
      ENNReal.ofReal (entropyCost I δ) =
          5 * ENNReal.ofReal (entropyCost I δ / 5) := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
        congr 1
        ring
      _ ≤ 5 * benchmark I δ :=
        mul_le_mul' le_rfl (by
          simpa only [entropyCost, confidenceCost] using
            (benchmark_entropy_lower_bound I hδ))
  have htwoENN : ENNReal.ofReal (twoArmCost I) ≤
      7 * ENNReal.ofReal (sourceTwoArmExpression I) := by
    have h := ENNReal.ofReal_le_ofReal htwo
    simpa only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7),
      ENNReal.ofReal_ofNat] using h
  calc
    (UniversalPolicy.algorithm δ n).expectedSamples I ≤
        ENNReal.ofReal (12000000000012 * (entropyCost I δ + twoArmCost I)) :=
      UniversalPolicy.expectedSamples_le I hδ
    _ = ENNReal.ofReal 12000000000012 *
        (ENNReal.ofReal (entropyCost I δ) + ENNReal.ofReal (twoArmCost I)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 12000000000012),
        ENNReal.ofReal_add hentropy htwo_nonneg]
    _ ≤ ENNReal.ofReal 12000000000012 *
        (7 * benchmark I δ + 7 * ENNReal.ofReal (sourceTwoArmExpression I)) := by
      apply mul_le_mul' le_rfl
      exact add_le_add
        (hentropyENN.trans (mul_le_mul' (by norm_num : (5 : ℝ≥0∞) ≤ 7) le_rfl))
        htwoENN
    _ = ENNReal.ofReal 84000000000084 *
        (benchmark I δ + ENNReal.ofReal (sourceTwoArmExpression I)) := by
      rw [← ENNReal.ofReal_ofNat 7, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 7)]
      norm_num
      ring

end GapEntropy
