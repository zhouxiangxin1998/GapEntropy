import GapEntropy.UniversalProcedure
import GapEntropy.UniversalCallCost
import GapEntropy.FallbackGuarantees

/-!
# The single actual universal policy

The runtime code receives only confidence and arm count. Every attempt executes
D.2's observable controller at the fixed numerical cap constant, and all attempts
are joined by the proved chronological fixed-cap retry policy.

The assembly helpers below explicitly retain two execution-probability
obligations. `UniversalSoundness.lean` and `UniversalFavorableProbability.lean`
prove them for this actual policy; `UniversalTheorem.lean` supplies the
unconditional main endpoints.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal Classical
namespace GapEntropy.UniversalPolicy

open UniversalCapAnalysis

def config (δ : ℝ) (j : ℕ) : UniversalAttempt.Config :=
  ⟨δ, j, UniversalCallCost.sampleCapConstant⟩

def attempts (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (j : ℕ) : BoundedProcedure n (Option (Fin n)) :=
  UniversalAttempt.procedure (config δ j) hn

theorem attempt_budget_eq (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (j : ℕ) :
    (attempts n hn δ j).budget =
      ⌈UniversalCallCost.sampleCapConstant * (2 : ℝ) ^ j * confidenceCost δ⌉₊ := rfl

theorem attempt_budget_pos (n : ℕ) (hn : 2 ≤ n) {δ : ℝ} (hδ : ValidConfidence δ) (j : ℕ) :
    0 < (attempts n hn δ j).budget := by
  rw [attempt_budget_eq]
  apply Nat.one_le_ceil_iff.mpr
  have hL := confidenceCost_pos hδ
  unfold UniversalCallCost.sampleCapConstant
  positivity

def stream (n : ℕ) (hn : 2 ≤ n) (δ : ℝ) (hδ : ValidConfidence δ) : Policy n :=
  FixedCapRetry.policy (attempts n hn δ) (attempt_budget_pos n hn hδ)

/-- Exactly one algorithm family, chosen before any unknown instance is supplied.
The irrelevant invalid-confidence/nontrivial-arm-count branches are totalized. -/
def algorithm (δ : ℝ) : Algorithm := fun n =>
  if hn : 2 ≤ n then
    if hδ : ValidConfidence δ then stream n hn δ hδ else Fallback.policy n δ
  else Fallback.policy n δ

theorem algorithm_eq_stream (n : ℕ) (hn : 2 ≤ n) {δ : ℝ} (hδ : ValidConfidence δ) :
    algorithm δ n = stream n hn δ hδ := by simp only [algorithm, dif_pos hn, dif_pos hδ]

/-- F.2/F.1's remaining statistical execution assertion, stated for the actual
bounded procedure and its true chronological Gaussian block law. -/
def LargeAttemptAbortBound {n : ℕ} (I : Instance n) (δ : ℝ) : Prop :=
  ∀ j, complexityTarget I δ ≤ (2 : ℝ) ^ j * confidenceCost δ →
    GaussianBlocks.blockLaw I.mean (attempts n I.two_le δ j).budget
      {x | (attempts n I.two_le δ j).evaluate x = none} ≤ 1 / 4

/-- E's remaining global soundness assertion is the actual stream return event;
it contains no termination or expected-cost assumption. -/
def WrongReturnBound {n : ℕ} (I : Instance n) (δ : ℝ) (hδ : ValidConfidence δ) : Prop :=
  sampleLaw I ((stream n I.two_le δ hδ).returnedNotEvent I.two_le I.best) ≤ ENNReal.ofReal δ

def finalConstant : ℝ := 12000000000012

theorem expectedSamples_le_of_abort_bound {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) (habort : LargeAttemptAbortBound I δ) :
    (algorithm δ n).expectedSamples I ≤
      ENNReal.ofReal (finalConstant * (entropyCost I δ + twoArmCost I)) := by
  rw [algorithm_eq_stream n I.two_le hδ]
  have h := expectedSamples_le_entropy_of_abort_bound (attempts n I.two_le δ)
    (attempt_budget_pos n I.two_le hδ) I hδ
    (by norm_num [UniversalCallCost.sampleCapConstant])
    (attempt_budget_eq n I.two_le δ) habort
  have hcoef : 12 * (UniversalCallCost.sampleCapConstant + 1) = finalConstant := by
    norm_num [finalConstant, UniversalCallCost.sampleCapConstant]
  rw [hcoef] at h
  exact h

theorem expectedSamples_lt_top_of_abort_bound {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) (habort : LargeAttemptAbortBound I δ) :
    (algorithm δ n).expectedSamples I < ⊤ :=
  (expectedSamples_le_of_abort_bound I hδ habort).trans_lt ENNReal.ofReal_lt_top

theorem almostSurelyTerminates_of_abort_bound {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) (habort : LargeAttemptAbortBound I δ) :
    (algorithm δ n).AlmostSurelyTerminates I :=
  (algorithm δ n).almostSurelyTerminates_of_expectedSamples_ne_top I
    (expectedSamples_lt_top_of_abort_bound I hδ habort).ne

theorem successProb_ge_of_execution_bounds {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) (hbad : WrongReturnBound I δ hδ)
    (habort : LargeAttemptAbortBound I δ) :
    ENNReal.ofReal (1 - δ) ≤ (algorithm δ n).successProb I := by
  apply (algorithm δ n).successProb_ge_of_wrong_return_le_of_almostSurelyTerminates I hδ.1.le
    (almostSurelyTerminates_of_abort_bound I hδ habort)
  simpa only [algorithm_eq_stream n I.two_le hδ, WrongReturnBound] using hbad

/-- Final assembly with its actual-probability obligations still visible.
This theorem does not assert those obligations hold. -/
theorem universalEntropyUpperBound_of_execution_bounds
    (hbad : ∀ δ, ∀ hδ : ValidConfidence δ, ∀ n, ∀ I : Instance n, WrongReturnBound I δ hδ)
    (habort : ∀ δ, ValidConfidence δ → ∀ n, ∀ I : Instance n, LargeAttemptAbortBound I δ) :
    UniversalEntropyUpperBound := by
  refine ⟨finalConstant, by norm_num [finalConstant], algorithm, ?_⟩
  intro δ hδ
  refine ⟨fun n I => successProb_ge_of_execution_bounds I hδ (hbad δ hδ n I) (habort δ hδ n I), ?_⟩
  intro n I
  exact ⟨almostSurelyTerminates_of_abort_bound I hδ (habort δ hδ n I),
    expectedSamples_lt_top_of_abort_bound I hδ (habort δ hδ n I),
    expectedSamples_le_of_abort_bound I hδ (habort δ hδ n I)⟩

end GapEntropy.UniversalPolicy
