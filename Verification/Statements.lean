import GapEntropy.Problem

/-!
# Independently transcribed review statements

This file imports the instance/model/definition foundation, but no main-result
proof module. None of the target propositions below is an alias of the project's
conjecture or main-theorem propositions. Correctness, unconditional cost, the
permutation infimum, and the logarithmic expressions are transcribed explicitly
from the manuscript. `CheckStatements.lean` proves them from the main theorems.

The shared semantic foundation still includes `Instance`, `Policy`, its actual
execution, and `sampleLaw`; those definitions must themselves be reviewed.
This is a statement-checking aid, not a proof of equivalence with an unspecified
larger class of randomized algorithms; see `GapEntropy.PolicyRepresentations` for the policy classes
that have been shown to give the same benchmark.
-/

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section
namespace GapEntropy.StatementChecks

/-- Success means a finite actual return of the best label, on every instance. -/
def ReferenceCorrect (A : (n : ℕ) → Policy n) (δ : ℝ) : Prop :=
  ∀ (n : ℕ) (I : Instance n),
    ENNReal.ofReal (1 - δ) ≤
      sampleLaw I {ω | ∃ t, (A n).returnedAt I.two_le t ω = some I.best}

/-- Full nonnegative integral: no conditioning on success or termination. -/
def ReferenceCost {n : ℕ} (P : Policy n) (I : Instance n) : ℝ≥0∞ :=
  ∫⁻ ω, P.sampleCount I.two_le ω ∂sampleLaw I

/-- The infimum is pointwise, but admissibility is global, at every arm count.
All n! permutations occur, including repetitions of equal mean vectors. -/
def ReferenceBenchmark {n : ℕ} (I : Instance n) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ A : (m : ℕ) → Policy m, ⨅ (_ : ReferenceCorrect A δ),
    (∑ π : Equiv.Perm (Fin n), ReferenceCost (A n) (I.permute π)) /
      (n.factorial : ℝ≥0∞)

/-- Manuscript Theorem 2.1 / source Conjecture 3.5, with explicit constants. -/
def GapEntropyStatement : Prop :=
  ∀ (δ : ℝ), 0 < δ → δ < 1 / 10 → ∀ (n : ℕ) (I : Instance n),
    ENNReal.ofReal (I.hardness * (Real.log δ⁻¹ + I.gapEntropy) / 5) ≤
        ReferenceBenchmark I δ ∧
    ReferenceBenchmark I δ ≤
      ENNReal.ofReal (64000000000000 *
        (I.hardness * (Real.log δ⁻¹ + I.gapEntropy)))

/-- Manuscript Theorem 2.2: one family chosen before the unknown instance.
The witness takes only confidence and arm count, and all paths are charged. -/
def UniversalStatement : Prop :=
  ∃ A : ℝ → (n : ℕ) → Policy n,
    ∀ (δ : ℝ), 0 < δ → δ < 1 / 10 →
      ReferenceCorrect (A δ) δ ∧ ∀ (n : ℕ) (I : Instance n),
        (∀ᵐ ω ∂sampleLaw I, ∃ t i, (A δ n).returnedAt I.two_le t ω = some i) ∧
        ReferenceCost (A δ n) I < ⊤ ∧
        ReferenceCost (A δ n) I ≤ ENNReal.ofReal (12000000000012 *
          (I.hardness * (Real.log δ⁻¹ + I.gapEntropy) +
            I.twoArmHardness * Real.log
              (Real.exp 1 + Real.log (Real.exp 1 + I.twoArmHardness))))

/-- The source almost-optimality conclusion with the manuscript's explicitly
positive smooth logarithm. The universal constant precedes every input. -/
def AlmostOptimalStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ → (n : ℕ) → Policy n,
    ∀ (δ : ℝ), (0 < δ ∧ δ < 1 / 10) →
      ReferenceCorrect (A δ) δ ∧ ∀ (n : ℕ) (I : Instance n),
        ReferenceCost (A δ n) I ≤ ENNReal.ofReal C *
          (ReferenceBenchmark I δ + ENNReal.ofReal
            (I.twoArmHardness * Real.log
              (Real.exp 1 + Real.log (Real.exp 1 + I.twoArmHardness))))

/-- A separate positive max-with-one convention, NOT the literal untruncated
source expression. No main-result proof is imported to state this target. -/
def PositiveAlmostOptimalStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ → (n : ℕ) → Policy n,
    ∀ (δ : ℝ), (0 < δ ∧ δ < 1 / 10) →
      ReferenceCorrect (A δ) δ ∧ ∀ (n : ℕ) (I : Instance n),
        ReferenceCost (A δ n) I ≤ ENNReal.ofReal C *
          (ReferenceBenchmark I δ + ENNReal.ofReal
            (I.twoArmHardness * max 1
              (Real.log (Real.log (Real.sqrt I.twoArmHardness)))))

end GapEntropy.StatementChecks
