import GapEntropy.UniversalTerminalAccounting
import GapEntropy.UniversalErrorBudget

/-! Actual fixed-core error bounds in the small and unrestricted work-cap regimes. -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GapEntropy.UniversalAttempt
variable {n : ℕ}

theorem comparisonProbability_eq (c : Config) :
    UniversalSevereProcess.comparisonProbability c =
      UniversalErrorBudget.severeProbability (c.confidence / 131072) := by
  unfold UniversalSevereProcess.comparisonProbability UniversalSevereProcess.eta
    UniversalErrorBudget.severeProbability Config.errorBudget
  congr 2
  ring

theorem eta_eq (c : Config) : UniversalSevereProcess.eta c = c.confidence / 131072 := by
  unfold UniversalSevereProcess.eta Config.errorBudget
  ring

theorem coreRisk_eq_card (p : ℝ) (B : Finset (Fin n)) (hB : B.Nonempty) :
    coreRisk p (B.card - 1) = (B.card : ℝ) * p ^ max 1 (B.card - 1) := by
  have hc : B.card - 1 + 1 = B.card := Nat.sub_add_cancel hB.card_pos
  unfold coreRisk
  rw [← Nat.cast_add_one, hc]

theorem probability_coreFailure_le_flags (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (B : Finset (Fin n)) (hB : B.Nonempty) :
    sampleLawOfMeans I.mean (CoreFailure c I B) ≤
      ENNReal.ofReal (coreRisk (UniversalSevereProcess.comparisonProbability c) (B.card - 1)) := by
  rw [coreRisk_eq_card _ B hB]
  exact (measure_mono (coreFailure_subset_flags c I hδ B)).trans
    (UniversalSevereProcess.probability_core_flags_le c hδ I.mean B hB)

theorem coreFailure_small_imp (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (B : Finset (Fin n))
    (hsmall : 192 * (c.workCap : ℝ) ≤ BatchCollapse.outsideHardness I B)
    (ω : SampleSpace n) (hω : ω ∈ CoreFailure c I B) :
    max 1 (B.card - 1) ≤ (B ∩ (UniversalSevereProcess.process c hδ I.mean).everFlags ω).card ∧
    BatchCollapse.outsideHardness I B / 2 ≤
      ∑ i ∈ (Finset.univ \ B) ∩ (UniversalSevereProcess.process c hδ I.mean).everFlags ω, I.weight i ∧
    ∀ i ∈ Finset.univ \ B, I.weight i ≤ 32 * c.workCap := by
  obtain ⟨T, ha, out, hf, hw, hv, _, hB⟩ := hω
  have hh : (terminalTrajectory c ω.2 T ha).outsideHardness I = BatchCollapse.outsideHardness I B := by
    simp only [Elimination.PaddedTrajectory.outsideHardness, Elimination.PaddedTrajectory.outside,
      hB, BatchCollapse.outsideHardness]
  have h := terminal_small_cap_joint_flags c I ω T ha hδ hv hf hw (by rw [hh]; linarith)
  simpa only [hh, Elimination.PaddedTrajectory.outside, hB] using h

/-- E.11 is obtained for the same actual erroneous-output event as E.7. -/
theorem probability_coreFailure_le_small (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (B : Finset (Fin n)) (hB : B.Nonempty)
    (hsmall : 192 * (c.workCap : ℝ) ≤ BatchCollapse.outsideHardness I B) :
    sampleLawOfMeans I.mean (CoreFailure c I B) ≤
      ENNReal.ofReal (coreRisk (UniversalSevereProcess.comparisonProbability c) (B.card - 1) *
        Real.exp (-(BatchCollapse.outsideHardness I B / (64 * c.workCap)) *
          Real.log (1 / (2 * UniversalSevereProcess.comparisonProbability c)) +
            BatchCollapse.outsideHardness I B / (64 * c.workCap))) := by
  by_cases hweights : ∀ i ∈ Finset.univ \ B, I.weight i ≤ 32 * c.workCap
  · rw [coreRisk_eq_card _ B hB]
    apply (measure_mono (fun ω hω => (coreFailure_small_imp c hδ I B hsmall ω hω).imp_right And.left)).trans
    exact UniversalSevereProcess.probability_core_weighted_flags_le c hδ I.mean B (Finset.univ \ B)
      hB (Finset.disjoint_left.mpr (fun _ hi hj => (Finset.mem_sdiff.mp hj).2 hi))
      I.weight (fun i _ => I.weight_nonneg i)
      (c.workCap : ℝ) (by unfold Config.workCap; positivity) hweights
  · have he : CoreFailure c I B = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro ω hω
      exact hweights (coreFailure_small_imp c hδ I B hsmall ω hω).2.2
    rw [he, measure_empty]
    exact bot_le

end GapEntropy.UniversalAttempt
