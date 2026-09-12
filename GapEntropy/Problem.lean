import GapEntropy.Model
import Mathlib.Data.EReal.Basic

/-!
# The original problem and the manuscript's main claims

The propositions below define the target statements. `GapEntropyTheorem.lean` proves
`GapEntropyConjecture`; `UniversalTheorem.lean` proves the universal algorithm statements. Their
algorithm quantifiers range over `Model.lean`'s actual Gaussian sampling model.
In particular a complexity function is not accepted as a substitute for a policy.

The source's iterated logarithm is normally truncated near gap one. We expose both
the literal real expression (with mathlib's totalized log convention) and the
manuscript's positive truncation rather than silently identifying them.
-/

open scoped ENNReal BigOperators

namespace GapEntropy

/-- One policy for every arm count. Policies see no unknown instance parameters. -/
abbrev Algorithm := (n : ℕ) → Policy n

/-- Manuscript §2.1: the success event includes finite return.
Almost-sure termination is an additional upper-bound conclusion, not an assumption. -/
def DeltaCorrect (A : Algorithm) (δ : ℝ) : Prop :=
  ∀ (n : ℕ) (I : Instance n), ENNReal.ofReal (1 - δ) ≤ (A n).successProb I

def ValidConfidence (δ : ℝ) : Prop := 0 < δ ∧ δ < 1 / 10

/-- Definition 3.1: average over all `n!` label permutations. -/
noncomputable def permutationAverage (A : Algorithm) {n : ℕ} (I : Instance n) : ℝ≥0∞ :=
  (∑ π : Equiv.Perm (Fin n), (A n).expectedSamples (I.permute π)) / (n.factorial : ℝ≥0∞)

/-- Pointwise infimum over algorithms that are correct on *every* instance.
Extended nonnegative reals preserve infinite expected runtimes. -/
noncomputable def benchmark {n : ℕ} (I : Instance n) (δ : ℝ) : ℝ≥0∞ :=
  ⨅ A : Algorithm, ⨅ (_ : DeltaCorrect A δ), permutationAverage A I

noncomputable def confidenceCost (δ : ℝ) : ℝ := Real.log δ⁻¹

noncomputable def entropyCost {n : ℕ} (I : Instance n) (δ : ℝ) : ℝ :=
  I.hardness * (confidenceCost δ + I.gapEntropy)

/-- Manuscript equation (2.3): `log(e + log(e + D))`. -/
noncomputable def iteratedLog (D : ℝ) : ℝ :=
  Real.log (Real.exp 1 + Real.log (Real.exp 1 + D))

noncomputable def twoArmCost {n : ℕ} (I : Instance n) : ℝ :=
  I.twoArmHardness * iteratedLog I.twoArmHardness

/-- Literal source formula, using `sqrt D = 1 / Δ_[2]`.
At the boundary `D=1`, the source logarithm is undefined in ordinary analysis;
Lean's real logarithm is totalized. No equivalence with the truncation is claimed here. -/
noncomputable def sourceTwoArmExpression {n : ℕ} (I : Instance n) : ℝ :=
  I.twoArmHardness * Real.log (Real.log (Real.sqrt I.twoArmHardness))

/-- Chen–Li Conjecture 3.5 and manuscript Theorem 2.1, with explicit uniform constants. -/
def GapEntropyConjecture : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (δ : ℝ), ValidConfidence δ → ∀ (n : ℕ) (I : Instance n),
      ENNReal.ofReal (c * entropyCost I δ) ≤ benchmark I δ ∧
      benchmark I δ ≤ ENNReal.ofReal (C * entropyCost I δ)

/-- Chen–Li Conjecture 3.2 with the manuscript's explicit nonnegative truncation. -/
def AlmostInstanceWiseOptimality : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ → Algorithm,
    ∀ δ : ℝ, ValidConfidence δ → DeltaCorrect (A δ) δ ∧
      ∀ (n : ℕ) (I : Instance n),
        (A δ n).expectedSamples I ≤
          ENNReal.ofReal C * (benchmark I δ + ENNReal.ofReal (twoArmCost I))

/-- A transcription of the untruncated source expression, kept separate because
of its boundary convention. This proposition is also not proved. -/
def SourceConjecture32Literal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ → Algorithm,
    ∀ δ : ℝ, ValidConfidence δ → DeltaCorrect (A δ) δ ∧
      ∀ (n : ℕ) (I : Instance n),
        ((A δ n).expectedSamples I).toEReal ≤ (C : EReal) *
          ((benchmark I δ).toEReal + (sourceTwoArmExpression I : EReal))

/-- Manuscript Theorem 2.2. The family takes only `δ` and arm count; its policies
receive observations and private randomness. All instance quantities occur only
on the right side of the performance statement. -/
def UniversalEntropyUpperBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ A : ℝ → Algorithm,
    ∀ δ : ℝ, ValidConfidence δ → DeltaCorrect (A δ) δ ∧
      ∀ (n : ℕ) (I : Instance n),
        (A δ n).AlmostSurelyTerminates I ∧
        (A δ n).expectedSamples I < ⊤ ∧
        (A δ n).expectedSamples I ≤
          ENNReal.ofReal (C * (entropyCost I δ + twoArmCost I))

theorem benchmark_le_permutationAverage (A : Algorithm) {δ : ℝ}
    (hA : DeltaCorrect A δ) {n : ℕ} (I : Instance n) :
    benchmark I δ ≤ permutationAverage A I := by
  exact iInf_le_of_le A (iInf_le_of_le hA le_rfl)

theorem benchmark_mono_confidence {δ₁ δ₂ : ℝ} (hδ : δ₁ ≤ δ₂)
    {n : ℕ} (I : Instance n) : benchmark I δ₂ ≤ benchmark I δ₁ := by
  apply le_iInf
  intro A
  apply le_iInf
  intro hA
  apply benchmark_le_permutationAverage A
  intro m J
  exact (ENNReal.ofReal_le_ofReal (by linarith)).trans (hA m J)

theorem confidenceCost_pos {δ : ℝ} (hδ : ValidConfidence δ) : 0 < confidenceCost δ := by
  apply Real.log_pos
  exact (one_lt_inv₀ hδ.1).2 (by have := hδ.2; norm_num at this ⊢; linarith)

theorem entropyCost_pos {δ : ℝ} (hδ : ValidConfidence δ) {n : ℕ} (I : Instance n) :
    0 < entropyCost I δ :=
  mul_pos I.hardness_pos (add_pos_of_pos_of_nonneg (confidenceCost_pos hδ) I.gapEntropy_nonneg)

theorem iteratedLog_pos {D : ℝ} (hD : 0 ≤ D) : 0 < iteratedLog D := by
  have he : 1 < Real.exp 1 := by
    have h := Real.exp_lt_exp.mpr (show (0 : ℝ) < 1 by norm_num)
    simpa only [Real.exp_zero] using h
  have hl : 0 < Real.log (Real.exp 1 + D) := Real.log_pos (by linarith)
  exact Real.log_pos (by linarith)

theorem twoArmCost_pos {n : ℕ} (I : Instance n) : 0 < twoArmCost I := by
  have hD : 0 < I.twoArmHardness := lt_of_lt_of_le zero_lt_one I.one_le_twoArmHardness
  exact mul_pos hD (iteratedLog_pos hD.le)

/-- The purely logical final implication in §2.3. The two main manuscript claims
are explicit hypotheses; this lemma does not establish either of them. -/
theorem almostInstanceWiseOptimality_of_main_claims
    (hgap : GapEntropyConjecture) (hupper : UniversalEntropyUpperBound) :
    AlmostInstanceWiseOptimality := by
  obtain ⟨c, C₀, hc, _, hgap⟩ := hgap
  obtain ⟨C, hC, A, hA⟩ := hupper
  let K : ℝ := max c⁻¹ 1
  have hK1 : 1 ≤ K := le_max_right _ _
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hK1
  have hcK : 1 ≤ K * c := by
    calc
      1 = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
      _ ≤ K * c := mul_le_mul_of_nonneg_right (le_max_left _ _) hc.le
  refine ⟨C * K, mul_pos hC hK, A, ?_⟩
  intro δ hδ
  obtain ⟨hcorrect, hruntime⟩ := hA δ hδ
  refine ⟨hcorrect, ?_⟩
  intro n I
  have hX := (entropyCost_pos hδ I).le
  have hY := (twoArmCost_pos I).le
  have hsum : entropyCost I δ + twoArmCost I ≤
      K * (c * entropyCost I δ + twoArmCost I) := by
    have hx := mul_le_mul_of_nonneg_right hcK hX
    have hy := mul_le_mul_of_nonneg_right hK1 hY
    nlinarith
  calc
    (A δ n).expectedSamples I ≤
        ENNReal.ofReal (C * (entropyCost I δ + twoArmCost I)) := (hruntime n I).2.2
    _ ≤ ENNReal.ofReal ((C * K) * (c * entropyCost I δ + twoArmCost I)) := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_left hsum hC.le]
    _ = ENNReal.ofReal (C * K) *
        (ENNReal.ofReal (c * entropyCost I δ) + ENNReal.ofReal (twoArmCost I)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC.le hK.le),
        ENNReal.ofReal_add (mul_nonneg hc.le hX) hY]
    _ ≤ ENNReal.ofReal (C * K) * (benchmark I δ + ENNReal.ofReal (twoArmCost I)) :=
      mul_le_mul' le_rfl (add_le_add (hgap δ hδ n I).1 le_rfl)

end GapEntropy
