import GapEntropy.UniversalTerminalFlags
import GapEntropy.UniversalReferenceFailure
import GapEntropy.UniversalBatchCollapse

/-! Work and fixed-core accounting for actual completed universal attempts. -/
noncomputable section
open scoped BigOperators Classical
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram
variable {n : ℕ} (c : Config) (I : Instance n) (ω : SampleSpace n) (T : ℕ)
  (haccepted : ∀ t < T, ∃ a z, stage c ω.2 t = .inr (a, z) ∧ a.Allowed c)

theorem terminal_active_two (t : ℕ) (ht : t < T) :
    2 ≤ ((terminalTrajectory c ω.2 T haccepted).active t).card := by
  obtain ⟨a, z, hs, ha⟩ := haccepted t ht
  change 2 ≤ (metadataOfStage (stage c ω.2 t)).active.card
  simpa only [hs, metadataOfStage] using ha.1

theorem terminal_callWork_eq (t : ℕ) (ht : t < T) :
    (terminalTrajectory c ω.2 T haccepted).callWork t =
      (workCharge c (stage c ω.2 t) : ℝ) := by
  obtain ⟨a, z, hs, ha⟩ := haccepted t ht
  change (metadataOfStage (stage c ω.2 t)).active.card *
    ((metadataOfStage (stage c ω.2 t)).tolerance ^ 2)⁻¹ = _
  simp only [hs, metadataOfStage, workCharge, if_pos ha]
  exact (UniversalBatchCollapse.call_work_eq c a).symm

theorem terminal_baseWork_le :
    (terminalTrajectory c ω.2 T haccepted).baseWork ≤ (c.workCap : ℝ) := by
  unfold Elimination.PaddedTrajectory.baseWork
  calc
    _ = ∑ t ∈ Finset.range T, (workCharge c (stage c ω.2 t) : ℝ) :=
      Finset.sum_congr rfl (fun t ht => terminal_callWork_eq c ω T haccepted t (Finset.mem_range.mp ht))
    _ = ((∑ t ∈ Finset.range T, workCharge c (stage c ω.2 t) : ℕ) : ℝ) := by simp only [Nat.cast_sum]
    _ ≤ (c.workCap : ℝ) := by exact_mod_cast stage_work_sum_le c ω.2 T

theorem terminal_upperValid_of_not_referenceFailure
    (hno : ω ∉ ReferenceFailure c (I.mean I.best)) :
    (terminalTrajectory c ω.2 T haccepted).UpperValid I := by
  intro t ht
  obtain ⟨a, z, hs, ha⟩ := haccepted t ht
  change observedReference c ω.2 t ≤ I.mean I.best +
    (metadataOfStage (stage c ω.2 t)).tolerance / 16
  simp only [observedReference, hs, dif_pos ha, metadataOfStage]
  exact callReference_le_of_not_referenceFailure c (I.mean I.best) ω hno t a z hs ha

theorem terminal_small_cap_joint_flags (hδ : ValidConfidence c.confidence)
    (hv : (terminalTrajectory c ω.2 T haccepted).UpperValid I)
    {out : Fin n} (hfinal : (terminalTrajectory c ω.2 T haccepted).active T = {out})
    (hwrong : out ≠ I.best)
    (hsmall : (c.workCap : ℝ) ≤
      (terminalTrajectory c ω.2 T haccepted).outsideHardness I / 192) :
    max 1 (((terminalTrajectory c ω.2 T haccepted).core I).card - 1) ≤
      ((terminalTrajectory c ω.2 T haccepted).core I ∩
        (UniversalSevereProcess.process c hδ I.mean).everFlags ω).card ∧
    (terminalTrajectory c ω.2 T haccepted).outsideHardness I / 2 ≤
      ∑ i ∈ (terminalTrajectory c ω.2 T haccepted).outside I ∩
        (UniversalSevereProcess.process c hδ I.mean).everFlags ω, I.weight i ∧
    ∀ i ∈ (terminalTrajectory c ω.2 T haccepted).outside I, I.weight i ≤ 32 * c.workCap := by
  let P := terminalTrajectory c ω.2 T haccepted
  have hT := P.pos_of_terminal_singleton I hfinal
  have hf := P.small_cap_joint_flags I hv hfinal hwrong
    (terminal_active_two c ω T haccepted (T - 1) (by omega))
    (terminal_baseWork_le c ω T haccepted) hsmall
  have hsub := terminal_everSevere_subset c hδ I ω T haccepted
  refine ⟨(terminal_wrong_core_flags c hδ I ω T haccepted hv hfinal hwrong).2, ?_, hf.2.2⟩
  exact hf.2.1.trans (Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.inter_subset_inter_left hsub) (fun i _ _ => I.weight_nonneg i))

/-- A true wrong terminal trajectory with both exceptional events excluded,
restricted to a fixed deterministic instance core. -/
def CoreFailure (c : Config) (I : Instance n) (B : Finset (Fin n)) : Set (SampleSpace n) :=
  {ω | ∃ T, ∃ haccepted : ∀ t < T, ∃ a z, stage c ω.2 t = .inr (a, z) ∧ a.Allowed c,
    ∃ out, (terminalTrajectory c ω.2 T haccepted).active T = {out} ∧ out ≠ I.best ∧
      (terminalTrajectory c ω.2 T haccepted).UpperValid I ∧
      ¬(terminalTrajectory c ω.2 T haccepted).SmallSevere I ∧
      (terminalTrajectory c ω.2 T haccepted).core I = B}

theorem coreFailure_subset_flags (hδ : ValidConfidence c.confidence) (B : Finset (Fin n)) :
    CoreFailure c I B ⊆ {ω | max 1 (B.card - 1) ≤
      (B ∩ (UniversalSevereProcess.process c hδ I.mean).everFlags ω).card} := by
  rintro ω ⟨T, ha, out, hf, hw, hv, _, hB⟩
  simpa only [hB, Set.mem_ofPred_eq] using (terminal_wrong_core_flags c hδ I ω T ha hv hf hw).2

theorem coreFailure_empty_of_outsideHardness_zero (B : Finset (Fin n))
    (hh : BatchCollapse.outsideHardness I B = 0) : CoreFailure c I B = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro ω ⟨T, ha, out, hf, hw, hv, hs, hB⟩
  exact hw ((terminalTrajectory c ω.2 T ha).not_wrong_singleton_of_outsideHardness_zero
    I hv hs hf (by rwa [hB]))

end GapEntropy.UniversalAttempt
