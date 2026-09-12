import GapEntropy.UniversalTerminalObservations
import GapEntropy.UniversalSevereProcess
import GapEntropy.OutsideAccounting

/-! The terminal trajectory's severe errors are the actual predictable process flags. -/
noncomputable section
open scoped BigOperators Classical
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram UniversalCall
variable {n : ℕ}

theorem severe_choice_of_pending (c : Config) (ω : SampleSpace n) (t : ℕ)
    (a : Metadata n) (ha : a.Allowed c) (z : ℝ)
    (hs : stage c ω.2 t = .inr (a, z)) :
    UniversalSevereProcess.choice c t ω = some ⟨a, ha⟩ := by
  simp only [UniversalSevereProcess.choice, hs, UniversalSevereProcess.choiceFromStage, dif_pos ha]

theorem severe_active_of_pending (c : Config) (ω : SampleSpace n) (t : ℕ)
    (a : Metadata n) (ha : a.Allowed c) (z : ℝ)
    (hs : stage c ω.2 t = .inr (a, z)) :
    UniversalSevereProcess.active c t ω = a.active := by
  rw [UniversalSevereProcess.active, severe_choice_of_pending c ω t a ha z hs]

theorem fresh_eq_observed_severe (c : Config) (hδ : ValidConfidence c.confidence)
    (I : Instance n) (ω : SampleSpace n) (t : ℕ) (a : Metadata n)
    (ha : a.Allowed c) (z : ℝ) (hs : stage c ω.2 t = .inr (a, z))
    (i : Fin n) (hi : i ∈ a.active) :
    UniversalSevereProcess.fresh c hδ I.mean t ω i = true ↔
      callObservedEstimates c ω.2 a ha z i - I.mean i < -5 * a.tolerance / 16 := by
  have hm := (UniversalSevereProcess.gaussianSchedule c hδ).samples_pos ⟨a, ha⟩
  change 0 < EliminationTape.activeSamples a.tolerance (a.alpha c) at hm
  rw [UniversalSevereProcess.fresh, AdaptiveGaussianCalls.Schedule.optionalFlags,
    severe_choice_of_pending c ω t a ha z hs]
  change AdaptiveGaussianCalls.scheduledSevere a.active
    (a.samples + observedActiveOffset c a)
    (EliminationTape.activeSamples a.tolerance (a.alpha c)) I.mean a.tolerance ω i = true ↔ _
  rw [AdaptiveGaussianCalls.scheduledSevere_eq_decide _ _ hm, decide_eq_true_eq,
    ← callObservedEstimates_eq_schedule c ω a ha z i hi]
  simp only [neg_mul, neg_div]

variable (c : Config) (hδ : ValidConfidence c.confidence) (I : Instance n)
  (ω : SampleSpace n) (T : ℕ)
  (haccepted : ∀ t < T, ∃ a z, stage c ω.2 t = .inr (a, z) ∧ a.Allowed c)

theorem terminal_severeAt_iff (t : ℕ) (ht : t < T) (i : Fin n) :
    i ∈ (terminalTrajectory c ω.2 T haccepted).severeAt I t ↔
      i ∈ UniversalSevereProcess.active c t ω ∧
        UniversalSevereProcess.fresh c hδ I.mean t ω i = true := by
  obtain ⟨a, z, hs, ha⟩ := haccepted t ht
  rw [Elimination.PaddedTrajectory.mem_severeAt,
    severe_active_of_pending c ω t a ha z hs]
  change i ∈ (metadataOfStage (stage c ω.2 t)).active ∧
    observedEstimates c ω.2 t i - I.mean i <
      -5 * (metadataOfStage (stage c ω.2 t)).tolerance / 16 ↔ _
  simp only [observedEstimates, hs, metadataOfStage, dif_pos ha]
  exact and_congr_right (fun hi => (fresh_eq_observed_severe c hδ I ω t a ha z hs i hi).symm)

theorem terminal_everSevere_subset :
    (terminalTrajectory c ω.2 T haccepted).everSevere I ⊆
      (UniversalSevereProcess.process c hδ I.mean).everFlags ω := by
  intro i hi
  obtain ⟨t, ht, hit⟩ := (Elimination.PaddedTrajectory.mem_everSevere _ I i).mp hi
  obtain ⟨ha, hf⟩ := (terminal_severeAt_iff c hδ I ω T haccepted t ht i).mp hit
  exact (UniversalSevereProcess.mem_everFlags_iff c hδ I.mean ω i).mpr ⟨t, ha, hf⟩

theorem terminal_wrong_core_flags
    (hv : (terminalTrajectory c ω.2 T haccepted).UpperValid I)
    {out : Fin n} (hfinal : (terminalTrajectory c ω.2 T haccepted).active T = {out})
    (hwrong : out ≠ I.best) :
    I.best ∈ (UniversalSevereProcess.process c hδ I.mean).everFlags ω ∧
      max 1 (((terminalTrajectory c ω.2 T haccepted).core I).card - 1) ≤
        ((terminalTrajectory c ω.2 T haccepted).core I ∩
          (UniversalSevereProcess.process c hδ I.mean).everFlags ω).card := by
  have hf := (terminalTrajectory c ω.2 T haccepted).wrong_singleton_core_flags I hv hfinal hwrong
  have hsub := terminal_everSevere_subset c hδ I ω T haccepted
  exact ⟨hsub hf.1, hf.2.trans (Finset.card_le_card (Finset.inter_subset_inter_left hsub))⟩

end GapEntropy.UniversalAttempt
