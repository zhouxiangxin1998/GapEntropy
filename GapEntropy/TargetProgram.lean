import GapEntropy.FiniteCallProgram
import GapEntropy.AttemptControlFacts

/-!
# The target-profile algorithm as a finite call program

`TargetProgram.program` expresses the C.1 target attempt as a `FiniteCallProgram`. At each scale
`k` and round `r` it calls the A.3 elimination on the current active set with tolerance
`targetTolerance k` and confidence `callConfidence ε k r` while the set exceeds
`4 · targetCount k` arms, and it finishes with a final call at confidence `ε/2` when more than
one arm remains. Evaluating the program on an addressed oracle yields exactly
`TargetAttempt.result`, and its consumed cost equals `TargetAttempt.totalCost`. Consequently
every oracle path obeys the C.2 bound `1000000000000 · hardness · (log(1/ε) + gapEntropy)`.
-/

noncomputable section
open scoped BigOperators Classical

namespace GapEntropy.TargetProgram
open FiniteCallProgram TargetAttempt
variable {n : ℕ}

abbrev ArmState (n : ℕ) := Option (Finset (Fin n))

def loopOracle (f : FiniteCallProgram.Oracle n) : TargetAttempt.Oracle n :=
  fun k r S => f (.loop k r) S

def step (I : Instance n) (ε : ℝ) (k r : ℕ) : ArmState n → Program n (ArmState n)
  | none => .pure none
  | some S =>
      if hbig : 4 * I.targetCount k < S.card then
        .call (.loop k r) S (Finset.card_pos.mp (by omega)) (I.targetTolerance k)
          (I.callConfidence ε k r) (fun R =>
            .pure (if R.Nonempty ∧ R.card ≤ (S.card + 1) / 2 then some R else none))
      else .pure (some S)

def run (I : Instance n) (ε : ℝ) (k : ℕ) (S : Finset (Fin n)) : ℕ → Program n (ArmState n)
  | 0 => .pure (some S)
  | r + 1 => bind (run I ε k S r) (step I ε k r)

def finishScale (I : Instance n) (ε : ℝ) (k : ℕ) : ArmState n → Program n (ArmState n)
  | none => .pure none
  | some S => run I ε k S n

def entry (I : Instance n) (ε : ℝ) : ℕ → Program n (ArmState n)
  | 0 => .pure (some Finset.univ)
  | k + 1 => bind (entry I ε k) (finishScale I ε k)

def finish (I : Instance n) (ε : ℝ) : ArmState n → Program n (Option (Fin n))
  | none => .pure none
  | some S =>
      if S.card = 1 then .pure (singletonReturn S)
      else if hS : S.Nonempty then
        .call .final S hS (I.targetTolerance I.lastBucket) (ε / 2)
          (fun R => .pure (singletonReturn R))
      else .pure none

def program (I : Instance n) (ε : ℝ) : Program n (Option (Fin n)) :=
  bind (entry I ε (I.lastBucket + 1)) (finish I ε)

theorem eval_step (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n)
    (k r : ℕ) (state : ArmState n) :
    eval f (step I ε k r state) =
      AttemptScale.step (I.targetCount k) (loopOracle f k) r state := by
  cases state with
  | none => rfl
  | some S =>
    by_cases hbig : 4 * I.targetCount k < S.card
    · simp only [step, AttemptScale.step, dif_pos hbig, if_pos hbig, eval, loopOracle]
      rfl
    · simp only [step, AttemptScale.step, dif_neg hbig, if_neg hbig, eval]

theorem eval_run (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n)
    (k : ℕ) (S : Finset (Fin n)) (r : ℕ) :
    eval f (run I ε k S r) = AttemptScale.run (I.targetCount k) (loopOracle f k) S r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [run, eval_bind, ih, eval_step]; rfl

theorem eval_finishScale (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n)
    (k : ℕ) (state : ArmState n) :
    eval f (finishScale I ε k state) = TargetAttempt.finishScale I (loopOracle f) k state := by
  cases state with
  | none => rfl
  | some S => exact eval_run I ε f k S n

theorem eval_entry (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n) (k : ℕ) :
    eval f (entry I ε k) = TargetAttempt.entry I (loopOracle f) k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [entry, eval_bind, ih, eval_finishScale]; rfl

/-- The finite call script has exactly the previously verified C.1 control flow. -/
theorem eval_program (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n) :
    eval f (program I ε) = TargetAttempt.result I (loopOracle f) (f .final) := by
  rw [program, eval_bind, eval_entry]
  cases he : TargetAttempt.entry I (loopOracle f) (I.lastBucket + 1) with
  | none => simp only [finish, eval, result, he]
  | some S =>
    have hS := TargetAttempt.entry_nonempty he
    by_cases hc : S.card = 1
    · simp only [finish, result, he, if_pos hc, eval]
    · simp only [finish, result, he, if_neg hc, dif_pos hS, eval]

def charge (I : Instance n) (ε : ℝ) (k : ℕ) (r : ℕ) : ArmState n → ℕ
  | none => 0
  | some S => if 4 * I.targetCount k < S.card then
      EliminationPolicy.budget S.card (I.targetTolerance k) (I.callConfidence ε k r)
    else 0

theorem cost_step (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n)
    (k r : ℕ) (state : ArmState n) : cost f (step I ε k r state) = charge I ε k r state := by
  cases state with
  | none => rfl
  | some S =>
    by_cases hbig : 4 * I.targetCount k < S.card
    · simp only [step, charge, dif_pos hbig, if_pos hbig, cost, Nat.add_zero]
    · simp only [step, charge, dif_neg hbig, if_neg hbig, cost]

theorem cost_run (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n)
    (k : ℕ) (S : Finset (Fin n)) (R : ℕ) :
    cost f (run I ε k S R) = ∑ r ∈ Finset.range R,
      charge I ε k r (AttemptScale.run (I.targetCount k) (loopOracle f k) S r) := by
  induction R with
  | zero => simp [run, cost]
  | succ R ih => rw [run, cost_bind, ih, eval_run, cost_step, Finset.sum_range_succ]

theorem charge_eq_request (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n)
    (k r : ℕ) (S : Finset (Fin n)) :
    charge I ε k r (AttemptScale.run (I.targetCount k) (loopOracle f k) S r) =
      match AttemptScale.request (I.targetCount k) (loopOracle f k) S r with
      | none => 0
      | some T => EliminationPolicy.budget T.card (I.targetTolerance k) (I.callConfidence ε k r) := by
  unfold AttemptScale.request
  cases AttemptScale.run (I.targetCount k) (loopOracle f k) S r with
  | none => rfl
  | some T => by_cases hb : 4 * I.targetCount k < T.card <;> simp [charge, hb]

theorem cost_finishScale_entry (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n) (k : ℕ) :
    cost f (finishScale I ε k (TargetAttempt.entry I (loopOracle f) k)) =
      ∑ r ∈ Finset.range n, TargetAttempt.loopCost I ε (loopOracle f) k r := by
  cases he : TargetAttempt.entry I (loopOracle f) k with
  | none => simp [finishScale, cost, TargetAttempt.loopCost, TargetAttempt.loopRequest, he]
  | some S =>
    rw [finishScale, cost_run]
    apply Finset.sum_congr rfl
    intro r _
    rw [charge_eq_request]
    simp only [TargetAttempt.loopCost, TargetAttempt.loopRequest, he]
    rfl

theorem cost_entry (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n) (K : ℕ) :
    cost f (entry I ε K) = ∑ k ∈ Finset.range K,
      ∑ r ∈ Finset.range n, TargetAttempt.loopCost I ε (loopOracle f) k r := by
  induction K with
  | zero => simp [entry, cost]
  | succ K ih => rw [entry, cost_bind, eval_entry, ih, cost_finishScale_entry, Finset.sum_range_succ]

/-- All consumed call budgets agree exactly with C.2's previous all-path budget. -/
theorem cost_program (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n) :
    cost f (program I ε) = TargetAttempt.totalCost I ε (loopOracle f) := by
  rw [program, cost_bind, cost_entry, eval_entry]
  unfold TargetAttempt.totalCost
  congr 1
  cases he : TargetAttempt.entry I (loopOracle f) (I.lastBucket + 1) with
  | none => simp [finish, cost, TargetAttempt.finalCost, TargetAttempt.finalRequest, he]
  | some S =>
    have hS := TargetAttempt.entry_nonempty he
    by_cases hc : S.card = 1
    · simp [finish, cost, TargetAttempt.finalCost, TargetAttempt.finalRequest, he, hc]
    · simp [finish, cost, TargetAttempt.finalCost, TargetAttempt.finalRequest, he, hc, hS]

theorem cost_program_le (I : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (f : FiniteCallProgram.Oracle n) :
    (cost f (program I ε) : ℝ) ≤
      1000000000000 * I.hardness * (Real.log ε⁻¹ + I.gapEntropy) := by
  rw [cost_program]
  exact TargetAttempt.totalCost_le I hε hε10 _

end GapEntropy.TargetProgram
