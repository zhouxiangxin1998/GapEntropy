import GapEntropy.ActualAttemptLocal
import GapEntropy.ProgramSimulation

/-!
# C.2 for the actual bounded history-based attempt

The finite script samples consecutive actual Gaussian reward blocks. Its
adaptive-tail estimate is proved from disjoint block independence. The local
block guarantees are actual A.3 theorems. ProgramSimulation identifies this
sequential execution with the padded bounded procedure's history readout.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Classical

namespace GapEntropy.ActualAttempt
open FiniteCallProgram TargetAttempt GaussianBlocks
variable {n : ℕ}

theorem execute_correct_of_good (I J : Instance n) (ε : ℝ) (x : Values n)
    (hg : executionGood (removalGood J) (TargetProgram.program I ε) I.two_le x)
    {a : Fin n} (ha : (execute (TargetProgram.program I ε) I.two_le x).2 = some a) : a = J.best := by
  obtain ⟨f, hf, hgood⟩ := execute_good_oracle (removalGood J) (TargetProgram.program_ordered I ε) I.two_le x hg
  have hrequests := TargetProgram.good_program_requests I ε (removalGood J) f hgood
  have hret : TargetAttempt.result I (TargetProgram.loopOracle f) (f .final) = some a := by
    rw [← TargetProgram.eval_program, hf, ha]
  exact result_correct_of_protection
    (fun k hk r hr S hreq hb => hrequests.1 k hk r hr S hreq hb)
    (fun S hreq hb => hrequests.2 S hreq hb) hret

theorem execute_success_of_good (I J : Instance n) (ε : ℝ) (x : Values n)
    (hg : executionGood (targetGood I J) (TargetProgram.program I ε) I.two_le x) :
    (execute (TargetProgram.program I ε) I.two_le x).2 = some J.best := by
  obtain ⟨f, hf, hgood⟩ := execute_good_oracle (targetGood I J) (TargetProgram.program_ordered I ε) I.two_le x hg
  have hrequests := TargetProgram.good_program_requests I ε (targetGood I J) f hgood
  rw [← hf, TargetProgram.eval_program]
  apply result_success_of_good_calls
  · intro k hk r hr S hreq hb
    obtain ⟨U, _, hU⟩ := TargetAttempt.loopRequest_some hreq
    have hbig := (AttemptScale.request_some_iff.mp hU).2
    have h := hrequests.1 k hk r hr S hreq
    simpa only [targetGood, if_pos (And.intro hb hbig), TargetProgram.loopOracle] using h
  · intro S hreq hb
    have hcard := (TargetAttempt.finalRequest_some hreq).2.2
    have h := hrequests.2 S hreq
    simpa only [targetGood, if_pos (And.intro hb hcard)] using h

theorem execute_incorrect_le (I J : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (sampleLawOfMeans J.mean).real {ω |
      (execute (TargetProgram.program I ε) I.two_le ω.2).2 ≠ none ∧
      (execute (TargetProgram.program I ε) I.two_le ω.2).2 ≠ some J.best} ≤ ε := by
  have hb := executionGood_failure_le J.mean I.two_le (removalGood J) (TargetProgram.program I ε)
    (program_locallyValid I ε J.mean (removalGood J) (removal_localBound I J hε hε10))
  apply (measureReal_mono (μ := sampleLawOfMeans J.mean)
    (s₂ := {ω | ¬ executionGood (removalGood J) (TargetProgram.program I ε) I.two_le ω.2}) ?_).trans
    (hb.trans (TargetProgram.risk_le I hε.le))
  intro ω ⟨hnone, hwrong⟩ hgood
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hnone
  have hbest := execute_correct_of_good I J ε ω.2 hgood ha
  exact hwrong (ha.trans (congrArg some hbest))

theorem execute_target_failure_le (I : Instance n) (π : Equiv.Perm (Fin n))
    {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (sampleLawOfMeans (I.permute π).mean).real {ω |
      (execute (TargetProgram.program I ε) I.two_le ω.2).2 ≠ some (I.permute π).best} ≤ ε := by
  have hb := executionGood_failure_le (I.permute π).mean I.two_le (targetGood I (I.permute π))
    (TargetProgram.program I ε) (program_locallyValid I ε (I.permute π).mean
      (targetGood I (I.permute π)) (target_localBound I π hε hε10))
  apply (measureReal_mono (μ := sampleLawOfMeans (I.permute π).mean)
    (s₂ := {ω | ¬ executionGood (targetGood I (I.permute π)) (TargetProgram.program I ε) I.two_le ω.2}) ?_).trans
    (hb.trans (TargetProgram.risk_le I hε.le))
  intro ω hfail hgood
  exact hfail (execute_success_of_good I (I.permute π) ε ω.2 hgood)

theorem procedure_event_real_eq_execute (I J : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) (Q : Option (Fin n) → Prop) :
    (blockLaw J.mean (AttemptProcedure.procedure I ε).budget).real
      {v | Q ((AttemptProcedure.procedure I ε).evaluate v)} =
    (sampleLawOfMeans J.mean).real {ω | Q ((execute (TargetProgram.program I ε) I.two_le ω.2).2)} := by
  have h := congrArg ENNReal.toReal ((AttemptProcedure.procedure I ε).actualOutput_event J.mean
    {a | Q a} (show MeasurableSet {a | Q a} from trivial))
  simpa only [measureReal_def, Set.preimage, Set.mem_ofPred_eq,
    AttemptProcedure.actualOutput_eq_execute I hε hε10] using h.symm

/-- Actual bounded procedure, universal wrong-return budget; there is no oracle
or conditional-success premise in this theorem. -/
theorem procedure_incorrect_le (I J : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    blockLaw J.mean (AttemptProcedure.procedure I ε).budget
      {v | (AttemptProcedure.procedure I ε).evaluate v ≠ none ∧
        (AttemptProcedure.procedure I ε).evaluate v ≠ some J.best} ≤ ENNReal.ofReal ε := by
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  rw [procedure_event_real_eq_execute I J hε hε10 (fun a => a ≠ none ∧ a ≠ some J.best)]
  exact execute_incorrect_le I J hε hε10

/-- C.2 target guarantee for each labeling, in failure form, for the actual
padded BoundedProcedure simulation under its real finite Gaussian block law. -/
theorem procedure_target_failure_le (I : Instance n) (π : Equiv.Perm (Fin n))
    {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (blockLaw (I.permute π).mean (AttemptProcedure.procedure I ε).budget).real
      {v | (AttemptProcedure.procedure I ε).evaluate v ≠ some (I.permute π).best} ≤ ε := by
  rw [procedure_event_real_eq_execute I (I.permute π) hε hε10 (fun a => a ≠ some (I.permute π).best)]
  exact execute_target_failure_le I π hε hε10

/-- Actual target abort probability, ready for the fixed-cap retry policy. -/
theorem procedure_abort_le (I : Instance n) (π : Equiv.Perm (Fin n))
    {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    blockLaw (I.permute π).mean (AttemptProcedure.procedure I ε).budget
      {v | (AttemptProcedure.procedure I ε).evaluate v = none} ≤ ENNReal.ofReal ε := by
  rw [← ofReal_measureReal]
  apply ENNReal.ofReal_le_ofReal
  apply (measureReal_mono (μ := blockLaw (I.permute π).mean (AttemptProcedure.procedure I ε).budget)
    (s₂ := {v | (AttemptProcedure.procedure I ε).evaluate v ≠ some (I.permute π).best}) ?_).trans
    (procedure_target_failure_le I π hε hε10)
  intro v hv
  change (AttemptProcedure.procedure I ε).evaluate v = none at hv
  simp only [Set.mem_ofPred_eq, hv, ne_eq, reduceCtorEq, not_false_eq_true]

theorem procedure_target_success_ge (I : Instance n) (π : Equiv.Perm (Fin n))
    {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    1 - ε ≤ (blockLaw (I.permute π).mean (AttemptProcedure.procedure I ε).budget).real
      {v | (AttemptProcedure.procedure I ε).evaluate v = some (I.permute π).best} := by
  have hf := procedure_target_failure_le I π hε hε10
  have hmeas : MeasurableSet {v | (AttemptProcedure.procedure I ε).evaluate v = some (I.permute π).best} :=
    (AttemptProcedure.procedure I ε).measurable_evaluate
      (show MeasurableSet {some (I.permute π).best} from trivial)
  have hm := measureReal_add_measureReal_compl
    (μ := blockLaw (I.permute π).mean (AttemptProcedure.procedure I ε).budget) hmeas
  rw [probReal_univ] at hm
  change (blockLaw (I.permute π).mean (AttemptProcedure.procedure I ε).budget).real
      {v | (AttemptProcedure.procedure I ε).evaluate v = some (I.permute π).best} +
    (blockLaw (I.permute π).mean (AttemptProcedure.procedure I ε).budget).real
      {v | (AttemptProcedure.procedure I ε).evaluate v ≠ some (I.permute π).best} = 1 at hm
  linarith

/-- C.2 completed for an actual bounded history-based procedure, including its
full fixed sample budget and all target labelings. The budget includes padding. -/
theorem actual_finite_attempt_C2 (I : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (∀ J : Instance n, blockLaw J.mean (AttemptProcedure.procedure I ε).budget
      {v | (AttemptProcedure.procedure I ε).evaluate v ≠ none ∧
        (AttemptProcedure.procedure I ε).evaluate v ≠ some J.best} ≤ ENNReal.ofReal ε) ∧
    (∀ π : Equiv.Perm (Fin n), 1 - ε ≤
      (blockLaw (I.permute π).mean (AttemptProcedure.procedure I ε).budget).real
        {v | (AttemptProcedure.procedure I ε).evaluate v = some (I.permute π).best}) ∧
    0 < (AttemptProcedure.procedure I ε).budget ∧
    ((AttemptProcedure.procedure I ε).budget : ℝ) ≤
      2000000000000 * I.hardness * (Real.log ε⁻¹ + I.gapEntropy) := by
  refine ⟨fun J => procedure_incorrect_le I J hε hε10,
    fun π => procedure_target_success_ge I π hε hε10,
    AttemptProcedure.cap_pos I ε, ?_⟩
  have h := AttemptProcedure.cap_le_twice_realCap I hε hε10
  change (AttemptProcedure.cap I ε : ℝ) ≤ _
  dsimp only [AttemptProcedure.realCap] at h
  nlinarith

end GapEntropy.ActualAttempt
