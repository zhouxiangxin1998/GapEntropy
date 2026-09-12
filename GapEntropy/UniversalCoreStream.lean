import GapEntropy.UniversalCoreRisk
import GapEntropy.UniversalTerminalCollapse
import GapEntropy.UniversalFailureStream
import GapEntropy.DyadicCapRisk

/-! Fixed-core events on the actual global retry sample blocks. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GapEntropy.UniversalPolicy
open UniversalAttempt UniversalErrorBudget
variable {n : ℕ}

def coreFailureAt (I : Instance n) (δ : ℝ) (hδ : ValidConfidence δ)
    (B : Finset (Fin n)) (j : ℕ) : Set (SampleSpace n) :=
  shiftedSample ((FixedCapRetry.schedule (attempts n I.two_le δ)
    (attempt_budget_pos n I.two_le hδ)).start j) ⁻¹'
      UniversalAttempt.CoreFailure (config δ j) I B

def CoreFailure (I : Instance n) (δ : ℝ) (hδ : ValidConfidence δ)
    (B : Finset (Fin n)) : Set (SampleSpace n) := ⋃ j, coreFailureAt I δ hδ B j

def CoreFailures (I : Instance n) (δ : ℝ) (hδ : ValidConfidence δ) : Set (SampleSpace n) :=
  ⋃ B ∈ I.terminalCoreFamily, CoreFailure I δ hδ B

theorem coreFailureAt_measure_le (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (B : Finset (Fin n)) (j : ℕ) :
    sampleLaw I (coreFailureAt I δ hδ B j) ≤
      sampleLawOfMeans I.mean (UniversalAttempt.CoreFailure (config δ j) I B) :=
  measure_shiftedSample_preimage_le I.mean _ _

theorem config_workCap (δ : ℝ) (j : ℕ) :
    ((config δ j).workCap : ℝ) = DyadicCapRisk.cap 1024 j := by
  simp only [config, Config.workCap, DyadicCapRisk.cap, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem config_probability (δ : ℝ) (j : ℕ) :
    UniversalSevereProcess.comparisonProbability (config δ j) = severeProbability (δ / 131072) :=
  comparisonProbability_eq _

theorem coreFailureAt_le_flags (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (B : Finset (Fin n)) (hB : B.Nonempty) (j : ℕ) :
    (sampleLaw I).real (coreFailureAt I δ hδ B j) ≤
      coreRisk (severeProbability (δ / 131072)) (B.card - 1) := by
  have h := (coreFailureAt_measure_le I hδ B j).trans
    (probability_coreFailure_le_flags (config δ j) hδ I B hB)
  rw [config_probability] at h
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (coreRisk_nonneg (severeProbability_nonneg (div_nonneg hδ.1.le (by norm_num))) _)).mp h

theorem coreFailureAt_le_small (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (B : Finset (Fin n)) (hB : B.Nonempty) (j : ℕ)
    (hsmall : 192 * DyadicCapRisk.cap 1024 j ≤ BatchCollapse.outsideHardness I B) :
    (sampleLaw I).real (coreFailureAt I δ hδ B j) ≤
      coreRisk (severeProbability (δ / 131072)) (B.card - 1) *
        Real.exp (-(BatchCollapse.outsideHardness I B / (64 * DyadicCapRisk.cap 1024 j)) *
          Real.log (1 / (2 * severeProbability (δ / 131072))) +
            BatchCollapse.outsideHardness I B / (64 * DyadicCapRisk.cap 1024 j)) := by
  have h := (coreFailureAt_measure_le I hδ B j).trans
    (probability_coreFailure_le_small (config δ j) hδ I B hB (by rwa [config_workCap]))
  rw [config_probability, config_workCap] at h
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (mul_nonneg (coreRisk_nonneg (severeProbability_nonneg (div_nonneg hδ.1.le (by norm_num))) _)
      (Real.exp_nonneg _))).mp h

theorem coreFailureAt_le_batch (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (B : Finset (Fin n)) (hbest : I.best ∈ B)
    (hh : 0 < BatchCollapse.outsideHardness I B) (j : ℕ)
    (hlarge : BatchCollapse.outsideHardness I B ≤ DyadicCapRisk.cap 1024 j) :
    (sampleLaw I).real (coreFailureAt I δ hδ B j) ≤
      3 * (δ / 131072) ^ (4 : ℕ) *
        (BatchCollapse.outsideHardness I B / DyadicCapRisk.cap 1024 j) ^ (3 : ℕ) := by
  have h := (coreFailureAt_measure_le I hδ B j).trans
    (probability_coreFailure_le_batch (config δ j) I hδ B hbest hh (by rwa [config_workCap]))
  rw [config_workCap, eta_eq] at h
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by
    exact mul_nonneg (by positivity) (pow_nonneg (div_nonneg hh.le (by
      unfold DyadicCapRisk.cap; positivity)) _))).mp h

/-- E.18 for actual retry blocks and a fixed deterministic core. Both large-cap
estimates bound the same event; no independence between them is assumed. -/
theorem coreFailure_measure_le (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ)
    (B : Finset (Fin n)) (hbest : I.best ∈ B) :
    sampleLaw I (CoreFailure I δ hδ B) ≤ ENNReal.ofReal
      (10 * coreRisk (severeProbability (δ / 131072)) (B.card - 1) +
        3 * (δ / 131072) ^ 2 * Real.sqrt (coreRisk (severeProbability (δ / 131072)) (B.card - 1))) := by
  have hB : B.Nonempty := ⟨I.best, hbest⟩
  have hh0 : 0 ≤ BatchCollapse.outsideHardness I B :=
    Finset.sum_nonneg (fun i _ => I.weight_nonneg i)
  by_cases hh : BatchCollapse.outsideHardness I B = 0
  · have he : CoreFailure I δ hδ B = ∅ := by
      simp only [CoreFailure, coreFailureAt, coreFailure_empty_of_outsideHardness_zero _ I B hh,
        Set.preimage_empty, Set.iUnion_empty]
    rw [he, measure_empty]
    exact bot_le
  · have hp0 : 0 < severeProbability (δ / 131072) := by
      unfold severeProbability
      exact mul_pos (by norm_num) (pow_pos (div_pos hδ.1 (by norm_num)) _)
    exact DyadicCapRisk.probability_iUnion_le (sampleLaw I) (coreFailureAt I δ hδ B)
      (by norm_num : (0 : ℝ) < 1024) hh0 (coreRisk_nonneg hp0.le _) hp0 (severeProbability_le hδ)
      (coreFailureAt_le_flags I hδ B hB)
      (coreFailureAt_le_small I hδ B hB)
      (coreFailureAt_le_batch I hδ B hbest (lt_of_le_of_ne hh0 (Ne.symm hh)))

/-- E.19 for the true global universal policy. The fixed family accounts for
all positive terminal thresholds, including repeated means and nondyadic gaps. -/
theorem coreFailures_measure_le (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    sampleLaw I (CoreFailures I δ hδ) ≤ ENNReal.ofReal
      (40 * severeProbability (δ / 131072) +
        15 * (δ / 131072) ^ 2 * Real.sqrt (severeProbability (δ / 131072))) := by
  apply I.measure_terminalCoreFamily_union_le (sampleLaw I) (CoreFailure I δ hδ)
    (severeProbability_nonneg (div_nonneg hδ.1.le (by norm_num))) (severeProbability_le hδ)
  intro B hB
  obtain ⟨d, hd, rfl⟩ := (I.mem_terminalCoreFamily B).mp hB
  exact coreFailure_measure_le I hδ _ (I.best_mem_terminalCore hd)

end GapEntropy.UniversalPolicy
