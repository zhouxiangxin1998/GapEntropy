import GapEntropy.TargetAttemptCost

/-!
# Addressed finite-attempt calls and C.2 deterministic guarantees

Each possible invocation has a distinct key and an explicit active set, tolerance,
and confidence. This is the control/statistical-oracle interface. No probability
theorem or `Policy` implementation is asserted by this module.
-/

noncomputable section
namespace GapEntropy.TargetAttempt

inductive CallKey where
  | loop (scale ordinal : ℕ)
  | final
  deriving DecidableEq

structure CallInput (n : ℕ) where
  active : Finset (Fin n)
  tolerance : ℝ
  confidence : ℝ

abbrev Primitive (n : ℕ) := CallKey → CallInput n → Finset (Fin n)

def callTolerance {n : ℕ} (I : Instance n) : CallKey → ℝ
  | .loop k _ => I.targetTolerance k
  | .final => I.targetTolerance I.lastBucket

def callConfidence {n : ℕ} (I : Instance n) (ε : ℝ) : CallKey → ℝ
  | .loop k r => I.callConfidence ε k r
  | .final => ε / 2

def callInput {n : ℕ} (I : Instance n) (ε : ℝ) (key : CallKey) (S : Finset (Fin n)) : CallInput n :=
  ⟨S, callTolerance I key, callConfidence I ε key⟩

def addressedOracle {n : ℕ} (I : Instance n) (ε : ℝ) (primitive : Primitive n) : Oracle n :=
  fun k r S => primitive (.loop k r) (callInput I ε (.loop k r) S)

def addressedFinalOracle {n : ℕ} (I : Instance n) (ε : ℝ) (primitive : Primitive n)
    (S : Finset (Fin n)) : Finset (Fin n) := primitive .final (callInput I ε .final S)

/-- The actual finite C.1 control flow, with A.3 parameters supplied in every call. -/
def attempt {n : ℕ} (I : Instance n) (ε : ℝ) (primitive : Primitive n) : Option (Fin n) :=
  result I (addressedOracle I ε primitive) (addressedFinalOracle I ε primitive)

/-- The deterministic portion of C.2, quantified over every possible raw primitive.
It includes the finite call cap, no further while-loop calls beyond the unrolling,
the complete confidence-path bound, and the target's hardness/entropy sample budget. -/
theorem finite_attempt_bounds {n : ℕ} (I : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) (primitive : Primitive n) :
    let oracle := addressedOracle I ε primitive
    callCount I oracle ≤ (I.lastBucket + 1) * n + 1 ∧
    (∀ k r, n ≤ r → loopRequest I oracle k r = none) ∧
    confidenceSpent I ε oracle ≤ ε ∧
    (totalCost I ε oracle : ℝ) ≤
      1000000000000 * I.hardness * (Real.log ε⁻¹ + I.gapEntropy) := by
  exact ⟨callCount_le I _, loopRequest_none_after_n I _, confidenceSpent_le I hε.le _,
    totalCost_le I hε hε10 _⟩

end GapEntropy.TargetAttempt
