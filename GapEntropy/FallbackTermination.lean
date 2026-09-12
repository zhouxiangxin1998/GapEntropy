import GapEntropy.FallbackAnalysis

/-!
# Finite unconditional sample expectation of the operational fallback

After a returned state all future counts vanish. Each further checkpoint can
therefore be charged only on paths not returned at the previous checkpoint.
The resulting actual-policy budget has finite expectation by the Gaussian tail.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal BigOperators Classical

namespace GapEntropy.Fallback

def noReturnBy {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (r : ℕ) : Set (SampleSpace n) :=
  {ω | ¬ ∃ i, (policy n δ).returnedAt hn (roundTime n r + 1) ω = some i}

theorem measurableSet_noReturnBy {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (r : ℕ) :
    MeasurableSet (noReturnBy hn δ r) :=
  (Measurable.not (Measurable.exists fun i =>
    ((policy n δ).measurable_returnedAt hn (roundTime n r + 1)).eq_const (some i))).setOf

def notReturnedIndicator {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (r : ℕ)
    (ω : SampleSpace n) : ℝ≥0∞ := if ω ∈ noReturnBy hn δ r then 1 else 0

theorem measurable_notReturnedIndicator {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (r : ℕ) :
    Measurable (notReturnedIndicator hn δ r) :=
  Measurable.ite (measurableSet_noReturnBy hn δ r) measurable_const measurable_const

theorem lintegral_notReturnedIndicator {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (r : ℕ)
    (μ : Measure (SampleSpace n)) :
    ∫⁻ ω, notReturnedIndicator hn δ r ω ∂μ = μ (noReturnBy hn δ r) := by
  simpa only [notReturnedIndicator, Set.indicator, one_mul] using
    lintegral_indicator_const (μ := μ) (measurableSet_noReturnBy hn δ r) (1 : ℝ≥0∞)

theorem truncated_checkpoint_step_le {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (r : ℕ)
    (ω : SampleSpace n) :
    (policy n δ).truncatedSamples hn (roundTime n (r + 1) + 1) ω ≤
      (policy n δ).truncatedSamples hn (roundTime n r + 1) ω +
        (roundTime n (r + 1) + 1) * notReturnedIndicator hn δ r ω := by
  by_cases hret : ∃ i, (policy n δ).returnedAt hn (roundTime n r + 1) ω = some i
  · obtain ⟨i, hi⟩ := hret
    have hnret : ω ∉ noReturnBy hn δ r := fun h => h ⟨i, hi⟩
    simp only [notReturnedIndicator, if_neg hnret, mul_zero, add_zero]
    calc
      _ ≤ (policy n δ).sampleCount hn ω := (policy n δ).truncatedSamples_le_sampleCount hn _ ω
      _ = _ := (policy n δ).sampleCount_eq_truncatedSamples_of_returned hn ω _ hi
  · have hnret : ω ∈ noReturnBy hn δ r := hret
    simp only [notReturnedIndicator, if_pos hnret, mul_one]
    exact ((policy n δ).truncatedSamples_le_time hn _ ω).trans (by
      push_cast
      exact le_add_self)

theorem truncated_checkpoint_budget {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (R : ℕ)
    (ω : SampleSpace n) :
    (policy n δ).truncatedSamples hn (roundTime n R + 1) ω ≤
      (n + 1 : ℕ) + ∑ r ∈ Finset.range R,
        (roundTime n (r + 1) + 1) * notReturnedIndicator hn δ r ω := by
  induction R with
  | zero => simpa [roundTime, roundSamples] using (policy n δ).truncatedSamples_le_time hn (n + 1) ω
  | succ R ih =>
      calc
        _ ≤ (policy n δ).truncatedSamples hn (roundTime n R + 1) ω +
            (roundTime n (R + 1) + 1) * notReturnedIndicator hn δ R ω :=
          truncated_checkpoint_step_le hn δ R ω
        _ ≤ ((n + 1 : ℕ) + ∑ r ∈ Finset.range R,
            (roundTime n (r + 1) + 1) * notReturnedIndicator hn δ r ω) +
            (roundTime n (R + 1) + 1) * notReturnedIndicator hn δ R ω := by gcongr
        _ = _ := by rw [Finset.sum_range_succ]; exact add_assoc _ _ _

private theorem nat_le_two_pow (t : ℕ) : t ≤ 2 ^ t := by
  induction t with
  | zero => norm_num
  | succ t ih =>
      have hp : 0 < 2 ^ t := pow_pos (by norm_num) t
      rw [pow_succ]
      omega

theorem sampleCount_le_roundBudget {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (ω : SampleSpace n) :
    (policy n δ).sampleCount hn ω ≤ (n + 1 : ℕ) +
      ∑' r, (roundTime n (r + 1) + 1) * notReturnedIndicator hn δ r ω := by
  rw [Policy.sampleCount_eq_iSup_truncatedSamples]
  apply iSup_le
  intro T
  have hT : T ≤ roundTime n T + 1 := by
    have hp := nat_le_two_pow T
    have hm : 2 ^ T ≤ n * 2 ^ T := Nat.le_mul_of_pos_left _ (by omega)
    exact hp.trans (hm.trans (Nat.le_succ _))
  calc
    _ ≤ (policy n δ).truncatedSamples hn (roundTime n T + 1) ω :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hT) (fun _ _ _ => zero_le)
    _ ≤ (n + 1 : ℕ) + ∑ r ∈ Finset.range T,
        (roundTime n (r + 1) + 1) * notReturnedIndicator hn δ r ω :=
      truncated_checkpoint_budget hn δ T ω
    _ ≤ _ := by gcongr; exact ENNReal.sum_le_tsum (Finset.range T)

theorem expectedSamples_le_roundBudget {n : ℕ} (I : Instance n) (δ : ℝ) :
    (policy n δ).expectedSamples I ≤ (n + 1 : ℕ) +
      ∑' r, (roundTime n (r + 1) + 1) * sampleLaw I (noReturnBy I.two_le δ r) := by
  apply (lintegral_mono (sampleCount_le_roundBudget I.two_le δ)).trans_eq
  rw [lintegral_add_left measurable_const]
  have hm (r : ℕ) : AEMeasurable (fun ω =>
      (roundTime n (r + 1) + 1 : ℝ≥0∞) * notReturnedIndicator I.two_le δ r ω)
      (sampleLaw I) :=
    (measurable_const.mul (measurable_notReturnedIndicator I.two_le δ r)).aemeasurable
  rw [lintegral_tsum hm]
  simp only [lintegral_const, measure_univ, mul_one]
  congr 1
  apply tsum_congr
  intro r
  rw [lintegral_const_mul _ (measurable_notReturnedIndicator I.two_le δ r),
    lintegral_notReturnedIndicator]

theorem checkpoint_cost_le_geometric (n r : ℕ) :
    ((roundTime n (r + 1) + 1 : ℕ) : ℝ) ≤ (2 * (n : ℝ) + 1) * (roundSamples r : ℝ) := by
  have hm : (1 : ℝ) ≤ roundSamples r := by
    exact_mod_cast (pow_pos (by norm_num : (0 : ℕ) < 2) r)
  simp only [roundTime, roundSamples, pow_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, Nat.cast_one] at hm ⊢
  nlinarith

theorem summable_real_round_cost {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    Summable (fun r : ℕ => ((roundTime n (r + 1) + 1 : ℕ) : ℝ) *
      (sampleLaw I).real (noReturnBy I.two_le δ r)) := by
  obtain ⟨g, hg, hgap⟩ := exists_gap_lower_bound I
  have hc : 0 < g ^ 2 / 128 := by positivity
  have hs := (summable_doubling_exp hc).mul_left ((2 * (n : ℝ) + 1) * (2 * (n : ℝ)))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [radius_eventually_le I.two_le hδ hδ1 hg] with r hr
  have ht := not_returned_by_round_probability_le I δ r hg hgap hr
  have he : -((roundSamples r : ℝ) * g ^ 2) / 128 = -(g ^ 2 / 128) * roundSamples r := by ring
  rw [he] at ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg)]
  calc
    _ ≤ ((roundTime n (r + 1) + 1 : ℕ) : ℝ) *
        (2 * (n : ℝ) * Real.exp (-(g ^ 2 / 128) * roundSamples r)) :=
      mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg _)
    _ ≤ ((2 * (n : ℝ) + 1) * (roundSamples r : ℝ)) *
        (2 * (n : ℝ) * Real.exp (-(g ^ 2 / 128) * roundSamples r)) :=
      mul_le_mul_of_nonneg_right (checkpoint_cost_le_geometric n r) (by positivity)
    _ = _ := by ring

/-- Every valid unique-best input has finite unconditional expected sample cost. -/
theorem expectedSamples_ne_top {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (policy n δ).expectedSamples I ≠ ⊤ := by
  have hs := (summable_real_round_cost I hδ hδ1).tsum_ofReal_ne_top
  have he (r : ℕ) : ENNReal.ofReal (((roundTime n (r + 1) + 1 : ℕ) : ℝ) *
      (sampleLaw I).real (noReturnBy I.two_le δ r)) =
      (roundTime n (r + 1) + 1) * sampleLaw I (noReturnBy I.two_le δ r) := by
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top (sampleLaw I) _)]
    push_cast
    rfl
  simp only [he] at hs
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨by simp, hs⟩)
    (expectedSamples_le_roundBudget I δ)

theorem almostSurelyTerminates {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) : (policy n δ).AlmostSurelyTerminates I :=
  (policy n δ).almostSurelyTerminates_of_expectedSamples_ne_top I (expectedSamples_ne_top I hδ hδ1)

end GapEntropy.Fallback
