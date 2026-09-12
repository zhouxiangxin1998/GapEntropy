import GapEntropy.UniversalTheorem

/-!
# Deterministic representatives of the proved upper-bound witnesses

The `GapEntropy` development allows an arbitrary measurable use of a private Gaussian
tape. Its two constructed upper-bound witnesses happen not to use that tape:
their decisions are functions of the finite observation history alone.

This module proves that fact for the actual decision rules, including all
fallback branches. It then packages them as measurable deterministic history
policies, with exact equality after conversion back to `GapEntropy.Policy`.
These equalities allow a behavioral-kernel interface to use Dirac action laws
for the existing witnesses without representing every randomized tape policy.
-/

open GapEntropy MeasureTheory
open scoped ENNReal

noncomputable section
namespace GapEntropy.PolicyRepresentations

/-- A policy's actual decision is unchanged by changing its private tape,
at every history, including histories of probability zero. -/
def SeedIndependent {n : ℕ} (A : Policy n) : Prop :=
  ∀ (hn : 2 ≤ n) (t : ℕ) (z z' : Seed) (h : History n t),
    A.choose hn t (z, h) = A.choose hn t (z', h)

/-- A measurable history-only policy. As in the `GapEntropy` model, legal executions
have at least two arms and a decision either samples or returns a label. -/
structure DeterministicPolicy (n : ℕ) where
  choose : 2 ≤ n → (t : ℕ) → History n t → Decision n
  measurable_choose : ∀ hn t, Measurable (choose hn t)

namespace DeterministicPolicy

/-- Ignore the supplied private tape and use the observed history. -/
def toPolicy {n : ℕ} (A : DeterministicPolicy n) : Policy n where
  choose hn t p := A.choose hn t p.2
  measurable_choose hn t := (A.measurable_choose hn t).comp measurable_snd

@[simp] theorem toPolicy_choose {n : ℕ} (A : DeterministicPolicy n)
    (hn : 2 ≤ n) (t : ℕ) (z : Seed) (h : History n t) :
    A.toPolicy.choose hn t (z, h) = A.choose hn t h := rfl

theorem seedIndependent_toPolicy {n : ℕ} (A : DeterministicPolicy n) :
    SeedIndependent A.toPolicy := fun _ _ _ _ _ => rfl

/-- Evaluate a seed-independent policy at a fixed zero tape. The conclusion
below proves exact equality to the original policy, rather than assuming any
representation or distributional equality. -/
def ofSeedIndependent {n : ℕ} (A : Policy n) (_hA : SeedIndependent A) :
    DeterministicPolicy n where
  choose hn t h := A.choose hn t ((fun _ => 0), h)
  measurable_choose hn t :=
    (A.measurable_choose hn t).comp (measurable_const.prodMk measurable_id)

theorem toPolicy_ofSeedIndependent {n : ℕ} (A : Policy n) (hA : SeedIndependent A) :
    (ofSeedIndependent A hA).toPolicy = A := by
  cases A with
  | mk choose measurable_choose =>
    unfold ofSeedIndependent toPolicy
    congr 1
    funext hn t p
    exact hA hn t (fun _ => 0) p.1 p.2

end DeterministicPolicy

theorem seedIndependent_iff_exists_deterministic {n : ℕ} (A : Policy n) :
    SeedIndependent A ↔ ∃ D : DeterministicPolicy n, D.toPolicy = A := by
  constructor
  · intro hA
    exact ⟨DeterministicPolicy.ofSeedIndependent A hA,
      DeterministicPolicy.toPolicy_ofSeedIndependent A hA⟩
  · rintro ⟨D, rfl⟩
    exact D.seedIndependent_toPolicy

/-- Every bounded procedure request is history-only by its actual type. -/
theorem seedIndependent_boundedProcedure {n : ℕ} {α : Type*}
    [MeasurableSpace α] (R : BoundedProcedure n α) :
    SeedIndependent R.samplingPolicy := fun _ _ _ _ _ => rfl

/-- The actual retry parser uses the finite history, not the private tape. -/
theorem seedIndependent_fixedCapRetry {n : ℕ}
    (R : ℕ → BoundedProcedure n (Option (Fin n)))
    (hpos : ∀ j, 0 < (R j).budget) :
    SeedIndependent (FixedCapRetry.policy R hpos) := fun _ _ _ _ _ => rfl

/-- The actual fallback decisions use history means and deterministic times. -/
theorem seedIndependent_fallback (n : ℕ) (δ : ℝ) :
    SeedIndependent (Fallback.policy n δ) := fun _ _ _ _ _ => rfl

/-- Splitting a tape in the interleaving wrapper has no effect when both
actual component decisions ignore their tapes. -/
theorem seedIndependent_interleave {n : ℕ} {A B : Policy n}
    (hA : SeedIndependent A) (hB : SeedIndependent B) :
    SeedIndependent (Interleave.policy A B) := by
  intro hn t z z' h
  simp only [Interleave.policy]
  split_ifs
  · exact hA hn _ _ _ _
  · exact hB hn _ _ _ _

theorem seedIndependent_targetStream {n : ℕ} (I : Instance n) (δ : ℝ) :
    SeedIndependent (TargetPolicy.stream I δ) :=
  seedIndependent_fixedCapRetry _ _

theorem seedIndependent_targetLocal {n : ℕ} (I : Instance n) (δ : ℝ) :
    SeedIndependent (TargetPolicy.localPolicy I δ) :=
  seedIndependent_interleave (seedIndependent_targetStream I δ)
    (seedIndependent_fallback n δ)

/-- No confidence or instance hypothesis is needed for the structural fact;
the off-target arm-count branches are also seed independent. -/
theorem seedIndependent_targetAlgorithm {n : ℕ} (I : Instance n) (δ : ℝ) (m : ℕ) :
    SeedIndependent (TargetPolicy.algorithm I δ m) := by
  by_cases hm : m = n
  · subst m
    rw [TargetPolicy.algorithm_at_target]
    exact seedIndependent_targetLocal I δ
  · simpa only [TargetPolicy.algorithm, dif_neg hm] using seedIndependent_fallback m δ

theorem seedIndependent_universalStream (n : ℕ) (hn : 2 ≤ n)
    (δ : ℝ) (hδ : ValidConfidence δ) :
    SeedIndependent (UniversalPolicy.stream n hn δ hδ) :=
  seedIndependent_fixedCapRetry _ _

/-- All branches of the actual universal family are history-only, even for
invalid confidence inputs or excluded arm counts. -/
theorem seedIndependent_universalAlgorithm (δ : ℝ) (n : ℕ) :
    SeedIndependent (UniversalPolicy.algorithm δ n) := by
  unfold UniversalPolicy.algorithm
  split_ifs with hn hδ
  · exact seedIndependent_universalStream n hn δ hδ
  · exact seedIndependent_fallback n δ
  · exact seedIndependent_fallback n δ

/-- The pointwise target-profile witness in the deterministic interface. -/
def targetWitness {n : ℕ} (I : Instance n) (δ : ℝ) (m : ℕ) : DeterministicPolicy m :=
  DeterministicPolicy.ofSeedIndependent (TargetPolicy.algorithm I δ m)
    (seedIndependent_targetAlgorithm I δ m)

@[simp] theorem targetWitness_toPolicy {n : ℕ} (I : Instance n) (δ : ℝ) (m : ℕ) :
    (targetWitness I δ m).toPolicy = TargetPolicy.algorithm I δ m :=
  DeterministicPolicy.toPolicy_ofSeedIndependent _ _

/-- The same universal witness is chosen before any unknown instance. -/
def universalWitness (δ : ℝ) (n : ℕ) : DeterministicPolicy n :=
  DeterministicPolicy.ofSeedIndependent (UniversalPolicy.algorithm δ n)
    (seedIndependent_universalAlgorithm δ n)

@[simp] theorem universalWitness_toPolicy (δ : ℝ) (n : ℕ) :
    (universalWitness δ n).toPolicy = UniversalPolicy.algorithm δ n :=
  DeterministicPolicy.toPolicy_ofSeedIndependent _ _

/-- Full C.1 admissibility and target cost, for the actual deterministic witness.
The target can be fixed in its parameters; correctness still ranges over all
actual input instances and all their arm counts. -/
theorem targetWitness_spec {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) :
    DeltaCorrect (fun m => (targetWitness I δ m).toPolicy) δ ∧
      (∀ (m : ℕ) (J : Instance m), (targetWitness I δ m).toPolicy.AlmostSurelyTerminates J ∧
        (targetWitness I δ m).toPolicy.expectedSamples J < ⊤) ∧
      (∀ π : Equiv.Perm (Fin n),
        (targetWitness I δ n).toPolicy.expectedSamples (I.permute π) ≤
          ENNReal.ofReal (64000000000000 * entropyCost I δ)) := by
  simpa only [targetWitness_toPolicy] using TargetPolicy.proposition_C1 I hδ

/-- Theorem 2.2's full global correctness and unconditional cost hold for a
single deterministic history-policy family. No random-kernel representation
assumption is needed to obtain these explicit upper-bound witnesses. -/
theorem universalWitness_spec {δ : ℝ} (hδ : ValidConfidence δ) :
    DeltaCorrect (fun n => (universalWitness δ n).toPolicy) δ ∧
      ∀ (n : ℕ) (I : Instance n),
        (universalWitness δ n).toPolicy.AlmostSurelyTerminates I ∧
        (universalWitness δ n).toPolicy.expectedSamples I < ⊤ ∧
        (universalWitness δ n).toPolicy.expectedSamples I ≤
          ENNReal.ofReal (12000000000012 * (entropyCost I δ + twoArmCost I)) := by
  simp only [universalWitness_toPolicy]
  exact ⟨UniversalPolicy.deltaCorrect hδ, fun n I =>
    ⟨UniversalPolicy.almostSurelyTerminates I hδ,
      UniversalPolicy.expectedSamples_lt_top I hδ,
      UniversalPolicy.expectedSamples_le I hδ⟩⟩

end GapEntropy.PolicyRepresentations
