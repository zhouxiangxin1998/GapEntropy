import GapEntropy.TargetProgram
import GapEntropy.FiniteCallOrder

/-!
# Call ordering and capacity of the target program

The rank of a loop key `(k, r)` is `k · n + r` and the final key has rank `(lastBucket + 1) · n`.
Every component of `TargetProgram.program` is `Ordered` with respect to this rank, so the whole
program has strictly increasing call keys along every branch. Its finite parser `capacity` is
therefore attained by a consistent addressed oracle and obeys the same C.2 bound
`1000000000000 · hardness · (log(1/ε) + gapEntropy)` as every oracle path.
-/

noncomputable section
open scoped Classical

namespace GapEntropy.TargetProgram
open FiniteCallProgram TargetAttempt
variable {n : ℕ}

def rank (I : Instance n) : CallKey → ℕ
  | .loop k r => k * n + r
  | .final => (I.lastBucket + 1) * n

theorem step_ordered (I : Instance n) (ε : ℝ) (k r : ℕ) (state : ArmState n) :
    Ordered (rank I) (k * n + r) (k * n + r + 1) (step I ε k r state) := by
  cases state with
  | none => trivial
  | some S =>
    by_cases hbig : 4 * I.targetCount k < S.card
    · simp only [step, dif_pos hbig, Ordered, rank]
      exact ⟨le_rfl, Nat.lt_succ_self _, fun _ => trivial⟩
    · simp only [step, dif_neg hbig, Ordered]

theorem run_ordered (I : Instance n) (ε : ℝ) (k : ℕ) (S : Finset (Fin n)) (R : ℕ) :
    Ordered (rank I) (k * n) (k * n + R) (run I ε k S R) := by
  induction R with
  | zero => trivial
  | succ R ih =>
    exact ordered_bind (Nat.le_add_right _ _) (by omega) ih (step_ordered I ε k R)

theorem finishScale_ordered (I : Instance n) (ε : ℝ) (k : ℕ) (state : ArmState n) :
    Ordered (rank I) (k * n) ((k + 1) * n) (finishScale I ε k state) := by
  cases state with
  | none => trivial
  | some S => simpa only [finishScale, Nat.add_mul, one_mul] using run_ordered I ε k S n

theorem entry_ordered (I : Instance n) (ε : ℝ) (K : ℕ) :
    Ordered (rank I) 0 (K * n) (entry I ε K) := by
  induction K with
  | zero => trivial
  | succ K ih =>
    exact ordered_bind (Nat.zero_le _) (Nat.mul_le_mul_right n (Nat.le_succ K)) ih
      (finishScale_ordered I ε K)

theorem finish_ordered (I : Instance n) (ε : ℝ) (state : ArmState n) :
    Ordered (rank I) ((I.lastBucket + 1) * n) ((I.lastBucket + 1) * n + 1) (finish I ε state) := by
  cases state with
  | none => trivial
  | some S =>
    by_cases hc : S.card = 1
    · simp only [finish, if_pos hc, Ordered]
    · by_cases hS : S.Nonempty
      · simp only [finish, if_neg hc, dif_pos hS, Ordered, rank]
        exact ⟨le_rfl, Nat.lt_succ_self _, fun _ => trivial⟩
      · simp only [finish, if_neg hc, dif_neg hS, Ordered]

theorem program_ordered (I : Instance n) (ε : ℝ) :
    Ordered (rank I) 0 ((I.lastBucket + 1) * n + 1) (program I ε) :=
  ordered_bind (Nat.zero_le _) (Nat.le_succ _) (entry_ordered I ε _) (finish_ordered I ε)

/-- The finite parser's maximum cost obeys the same entropy bound as every
oracle path. Its maximum is attained by a consistent addressed oracle. -/
theorem capacity_le (I : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (capacity (program I ε) : ℝ) ≤
      1000000000000 * I.hardness * (Real.log ε⁻¹ + I.gapEntropy) := by
  obtain ⟨f, hf⟩ := capacity_attained (program_ordered I ε)
  rw [← hf]
  exact cost_program_le I hε hε10 f

end GapEntropy.TargetProgram
