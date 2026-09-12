import GapEntropy.UniversalCoreStream
import GapEntropy.UniversalSmallFailure

/-! Global error control for the actual observable universal policy. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GapEntropy.UniversalAttempt
variable {n : ℕ}

theorem terminal_smallSevere_imp_failure (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (ω : SampleSpace n) (T : ℕ) (hT : T ≤ c.fuel)
    (ha : ∀ t < T, ∃ a z, stage c ω.2 t = .inr (a, z) ∧ a.Allowed c)
    (hsmall : (terminalTrajectory c ω.2 T ha).SmallSevere I) :
    ω ∈ UniversalSevereProcess.SmallFailure c hδ I.mean := by
  obtain ⟨t, ht, hc, i, hi⟩ := hsmall
  obtain ⟨hia, hif⟩ := (terminal_severeAt_iff c hδ I ω T ha t ht i).mp hi
  have hc' : (UniversalSevereProcess.active c t ω).card ≤ 7 := by
    obtain ⟨a, z, hs, hh⟩ := ha t ht
    rw [severe_active_of_pending c ω t a hh z hs]
    change (metadataOfStage (stage c ω.2 t)).active.card < 8 at hc
    simp only [hs, metadataOfStage] at hc
    omega
  exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr (ht.trans_le hT),
    hc', i, hia, hif⟩⟩

end GapEntropy.UniversalAttempt

namespace GapEntropy.UniversalPolicy
open UniversalAttempt UniversalErrorBudget
variable {n : ℕ}

/-- Every wrong return of the actual stream comes from an actual completed
attempt and belongs to one of the three derived error events. -/
theorem wrongReturn_subset_failures (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    (stream n I.two_le δ hδ).returnedNotEvent I.two_le I.best ⊆
      ReferenceFailure I δ hδ ∪ SmallFailure I δ hδ ∪ CoreFailures I δ hδ := by
  rintro ω ⟨t, out, hwrong, hret⟩
  by_cases href : ω ∈ ReferenceFailure I δ hδ
  · exact Or.inl (Or.inl href)
  by_cases hsmall : ω ∈ SmallFailure I δ hδ
  · exact Or.inl (Or.inr hsmall)
  apply Or.inr
  obtain ⟨j, hans⟩ := FixedCapRetry.returned_imp_answer (attempts n I.two_le δ)
    (attempt_budget_pos n I.two_le hδ) I.two_le ω out ⟨t, hret⟩
  let ωj := shiftedSample ((FixedCapRetry.schedule (attempts n I.two_le δ)
    (attempt_budget_pos n I.two_le hδ)).start j) ω
  have hout : (UniversalAttempt.procedure (config δ j) I.two_le).actualOutput ωj = some out :=
    (FixedCapRetry.actualOutput_shifted_eq_answer (attempts n I.two_le δ)
      (attempt_budget_pos n I.two_le hδ) j ω).trans hans
  rw [actualOutput_eq_execute] at hout
  obtain ⟨T, hT, ha, hf⟩ := exists_terminalTrajectory_of_return (config δ j) ωj.2 out hout
  have hrj : ωj ∉ UniversalAttempt.ReferenceFailure (config δ j) (I.mean I.best) := by
    intro h
    exact href (Set.mem_iUnion.mpr ⟨j, h⟩)
  have hsj : ωj ∉ UniversalSevereProcess.SmallFailure (config δ j) hδ I.mean := by
    intro h
    exact hsmall (Set.mem_iUnion.mpr ⟨j, h⟩)
  have hv := terminal_upperValid_of_not_referenceFailure (config δ j) I ωj T ha hrj
  have hs : ¬(terminalTrajectory (config δ j) ωj.2 T ha).SmallSevere I :=
    fun h => hsj (terminal_smallSevere_imp_failure (config δ j) hδ I ωj T hT ha h)
  let B := (terminalTrajectory (config δ j) ωj.2 T ha).core I
  have hB : B ∈ I.terminalCoreFamily :=
    (terminalTrajectory (config δ j) ωj.2 T ha).core_mem_terminalCoreFamily I
      ((terminalTrajectory (config δ j) ωj.2 T ha).pos_of_terminal_singleton I hf)
  exact Set.mem_iUnion.mpr ⟨B, Set.mem_iUnion.mpr ⟨hB,
    Set.mem_iUnion.mpr ⟨j, T, ha, out, hf, hwrong, hv, hs, rfl⟩⟩⟩

/-- E.20: the actual complete retry policy has wrong-return probability below
the requested confidence, without any assumed execution-probability bound. -/
theorem wrongReturn_probability_lt (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    sampleLaw I ((stream n I.two_le δ hδ).returnedNotEvent I.two_le I.best) < ENNReal.ofReal δ := by
  apply incorrect_event_lt_confidence (sampleLaw I) I hδ
    ((stream n I.two_le δ hδ).returnedNotEvent I.two_le I.best)
    (ReferenceFailure I δ hδ) (SmallFailure I δ hδ) (CoreFailure I δ hδ)
    (wrongReturn_subset_failures I hδ) (referenceFailure_measure_le I hδ) (smallFailure_measure_le I hδ)
  intro B hB
  obtain ⟨d, hd, rfl⟩ := (I.mem_terminalCoreFamily B).mp hB
  exact coreFailure_measure_le I hδ _ (I.best_mem_terminalCore hd)

theorem wrongReturnBound (I : Instance n) {δ : ℝ} (hδ : ValidConfidence δ) :
    WrongReturnBound I δ hδ := (wrongReturn_probability_lt I hδ).le

end GapEntropy.UniversalPolicy
