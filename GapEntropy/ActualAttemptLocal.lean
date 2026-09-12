import GapEntropy.ProgramProbability
import GapEntropy.TargetProgramGood
import GapEntropy.AttemptLocalBounds

/-!
# Local A.3 bounds for the actual target program

This module instantiates the local validity predicate of `ProgramProbability` for the finite
call script `TargetProgram.program`. Two good-call predicates are defined: `removalGood`, which
only asks that the best arm survive each call, and `targetGood`, which additionally asks for the
C.2 halving and final-singleton guarantees. `LocalBound` states that every fixed A.3 block
experiment violates one of these predicates with probability at most its declared call
confidence.

Both bounds are derived from the fixed-block A.3 failure probabilities of `EliminationPolicy`;
the target bound uses the near-count and final-gap bridge of `TargetNearCount` on every
relabeling `I.permute π`. The remaining theorems propagate a local bound through `step`, `run`,
`finishScale`, `entry`, and `finish` to `LocallyValid` for the whole program.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace GapEntropy.ActualAttempt
open TargetAttempt FiniteCallProgram GaussianBlocks
variable {n : ℕ}

def removalGood (J : Instance n) : Good n := fun _ S R => J.best ∈ S → J.best ∈ R

def targetGood (I J : Instance n) : Good n
  | .loop k _, S, R => if J.best ∈ S ∧ 4 * I.targetCount k < S.card then
      J.best ∈ R ∧ R.card ≤ (S.card + 1) / 2 else True
  | .final, S, R => if J.best ∈ S ∧ S.card ≤ 4 then R = {J.best} else True

def LocalBound (I : Instance n) (ε : ℝ) (mean : Fin n → ℝ) (G : Good n) : Prop :=
  ∀ key, AttemptExperiment.ValidKey I key → ∀ S : Finset (Fin n), ∀ hS : S.Nonempty,
    (blockLaw mean (EliminationPolicy.budget S.card (callTolerance I key) (callConfidence I ε key))).real
      {v | ¬ G key S (EliminationPolicy.rawOutputFromBlock S hS
        (callTolerance I key) (callConfidence I ε key) I.two_le v)} ≤ callConfidence I ε key

theorem removal_localBound (I J : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    LocalBound I ε J.mean (removalGood J) := by
  intro key hkey S hS
  have hα := AttemptExperiment.confidence_pos I hε key
  by_cases hb : J.best ∈ S
  · have h := EliminationPolicy.rawBlock_best_failure S hS I.two_le J.mean hb
      (fun i _ => sub_nonneg.mp (J.gap_nonneg i)) (AttemptExperiment.tolerance_pos I key)
      hα (AttemptExperiment.confidence_le_one I hε hε10 key hkey)
    simpa only [removalGood, hb, true_implies] using h
  · simpa [removalGood, hb] using hα.le

theorem target_localBound (I : Instance n) (π : Equiv.Perm (Fin n)) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) : LocalBound I ε (I.permute π).mean (targetGood I (I.permute π)) := by
  intro key hkey S hS
  let J := I.permute π
  change (blockLaw J.mean _).real {v | ¬ targetGood I J key S
    (EliminationPolicy.rawOutputFromBlock S hS _ _ I.two_le v)} ≤ _
  have hα := AttemptExperiment.confidence_pos I hε key
  cases key with
  | loop k r =>
    by_cases hg : J.best ∈ S ∧ 4 * I.targetCount k < S.card
    · have h := EliminationPolicy.rawBlock_large_failure S hS I.two_le J.mean hg.1
        (fun i _ => sub_nonneg.mp (J.gap_nonneg i)) (AttemptExperiment.tolerance_pos I (.loop k r))
        hα (AttemptExperiment.confidence_le_one I hε hε10 (.loop k r) hkey)
        (I.permuted_near_card_le_targetCount π S k) hg.2
      simpa only [targetGood, if_pos hg, not_and_or, not_le] using h
    · simpa [targetGood, hg] using hα.le
  | final =>
    by_cases hg : J.best ∈ S ∧ S.card ≤ 4
    · have h := EliminationPolicy.rawBlock_small_failure S hS I.two_le J.mean hg.1
        (fun i _ => sub_nonneg.mp (J.gap_nonneg i)) (AttemptExperiment.tolerance_pos I .final)
        hα (AttemptExperiment.confidence_le_one I hε hε10 .final hkey) hg.2
        (fun i _ hi => I.permuted_last_targetTolerance_le_gap π hi)
      simpa only [targetGood, if_pos hg] using h
    · simpa [targetGood, hg] using hα.le

theorem step_locallyValid (I : Instance n) (ε : ℝ) (mean : Fin n → ℝ) (G : Good n)
    (hloc : LocalBound I ε mean G) (k r : ℕ) (hk : k ≤ I.lastBucket) (state : TargetProgram.ArmState n) :
    LocallyValid mean I.two_le G (TargetProgram.step I ε k r state) := by
  cases state with
  | none => trivial
  | some S =>
    by_cases hb : 4 * I.targetCount k < S.card
    · simp only [TargetProgram.step, dif_pos hb, LocallyValid]
      exact ⟨hloc (.loop k r) hk S _, fun _ => trivial⟩
    · simp only [TargetProgram.step, dif_neg hb, LocallyValid]

theorem run_locallyValid (I : Instance n) (ε : ℝ) (mean : Fin n → ℝ) (G : Good n)
    (hloc : LocalBound I ε mean G) (k : ℕ) (hk : k ≤ I.lastBucket) (S : Finset (Fin n)) (R : ℕ) :
    LocallyValid mean I.two_le G (TargetProgram.run I ε k S R) := by
  induction R with
  | zero => trivial
  | succ R ih => exact locallyValid_bind mean I.two_le G _ _ ih (step_locallyValid I ε mean G hloc k R hk)

theorem finishScale_locallyValid (I : Instance n) (ε : ℝ) (mean : Fin n → ℝ) (G : Good n)
    (hloc : LocalBound I ε mean G) (k : ℕ) (hk : k ≤ I.lastBucket) (state : TargetProgram.ArmState n) :
    LocallyValid mean I.two_le G (TargetProgram.finishScale I ε k state) := by
  cases state with
  | none => trivial
  | some S => exact run_locallyValid I ε mean G hloc k hk S n

theorem entry_locallyValid (I : Instance n) (ε : ℝ) (mean : Fin n → ℝ) (G : Good n)
    (hloc : LocalBound I ε mean G) (K : ℕ) (hK : K ≤ I.lastBucket + 1) :
    LocallyValid mean I.two_le G (TargetProgram.entry I ε K) := by
  induction K with
  | zero => trivial
  | succ K ih =>
    exact locallyValid_bind mean I.two_le G _ _ (ih (by omega))
      (finishScale_locallyValid I ε mean G hloc K (by omega))

theorem finish_locallyValid (I : Instance n) (ε : ℝ) (mean : Fin n → ℝ) (G : Good n)
    (hloc : LocalBound I ε mean G) (state : TargetProgram.ArmState n) :
    LocallyValid mean I.two_le G (TargetProgram.finish I ε state) := by
  cases state with
  | none => trivial
  | some S =>
    by_cases hc : S.card = 1
    · simp only [TargetProgram.finish, if_pos hc, LocallyValid]
    · by_cases hS : S.Nonempty
      · simp only [TargetProgram.finish, if_neg hc, dif_pos hS, LocallyValid]
        exact ⟨hloc .final trivial S hS, fun _ => trivial⟩
      · simp only [TargetProgram.finish, if_neg hc, dif_neg hS, LocallyValid]

theorem program_locallyValid (I : Instance n) (ε : ℝ) (mean : Fin n → ℝ) (G : Good n)
    (hloc : LocalBound I ε mean G) : LocallyValid mean I.two_le G (TargetProgram.program I ε) :=
  locallyValid_bind mean I.two_le G _ _ (entry_locallyValid I ε mean G hloc _ le_rfl)
    (finish_locallyValid I ε mean G hloc)

end GapEntropy.ActualAttempt
