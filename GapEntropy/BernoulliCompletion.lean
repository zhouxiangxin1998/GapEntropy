import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Tactic

/-! Finite independent Bernoulli completion, the finite-state foundation for E.1. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace GapEntropy

/-- The union probability for two independent Bernoulli flags. -/
def bernoulliUnionProbability (p q : unitInterval) : unitInterval :=
  ⟨p + q - p * q, by
    constructor
    · nlinarith [p.property.1, p.property.2, q.property.1, q.property.2,
        mul_nonneg p.property.1 (sub_nonneg.mpr q.property.2)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr p.property.2)
        (sub_nonneg.mpr q.property.2)]⟩

@[simp] theorem bernoulliUnionProbability_coe (p q : unitInterval) :
    (bernoulliUnionProbability p q : ℝ) = p + q - p * q := rfl

/-- Independent Bernoulli flags coalesce under Boolean OR with the usual union parameter. -/
theorem bernoulliMeasure_or (p q : unitInterval) :
    ((bernoulliMeasure true false p).prod (bernoulliMeasure true false q)).map
      (fun z : Bool × Bool => z.1 || z.2) =
      bernoulliMeasure true false (bernoulliUnionProbability p q) := by
  apply MeasureTheory.ext_iff_measureReal_singleton.mpr
  intro b
  have hi (μ : Measure Bool) [IsFiniteMeasure μ] :
      μ.real {b} = ∫ x, (if x = b then (1 : ℝ) else 0) ∂μ := by
    simpa [Set.indicator] using
      (integral_indicator_one (μ := μ) (measurableSet_singleton b)).symm
  rw [hi, hi, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable,
    integral_prod _ Integrable.of_finite]
  simp only [integral_bernoulliMeasure, smul_eq_mul, bernoulliUnionProbability_coe]
  cases b <;> norm_num <;> ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Actual law of independent flags, one for each finite label. -/
def bernoulliFlagLaw (p : ι → unitInterval) : Measure (ι → Bool) :=
  Measure.pi fun i => bernoulliMeasure true false (p i)

instance bernoulliFlagLaw_isProbabilityMeasure (p : ι → unitInterval) :
    IsProbabilityMeasure (bernoulliFlagLaw p) := by
  unfold bernoulliFlagLaw
  infer_instance

omit [DecidableEq ι] in
/-- The coordinates in the flag law are jointly independent. -/
theorem bernoulliFlagLaw_indep (p : ι → unitInterval) :
    iIndepFun (fun i (x : ι → Bool) => x i) (bernoulliFlagLaw p) :=
  iIndepFun_pi (fun _ => measurable_id.aemeasurable)

/-- The labels flagged by a Boolean vector. -/
def freshFlagSet (x : ι → Bool) : Finset ι := Finset.univ.filter fun i => x i = true

omit [DecidableEq ι] in
@[simp] theorem mem_freshFlagSet (x : ι → Bool) (i : ι) :
    i ∈ freshFlagSet x ↔ x i = true := by simp [freshFlagSet]

@[simp] theorem freshFlagSet_or (x y : ι → Bool) :
    freshFlagSet (fun i => x i || y i) = freshFlagSet x ∪ freshFlagSet y := by
  ext i
  simp

omit [DecidableEq ι] in
/-- The union of independent product vectors is again a product law. -/
theorem bernoulliFlagLaw_or (p q : ι → unitInterval) :
    ((bernoulliFlagLaw p).prod (bernoulliFlagLaw q)).map
      (fun z : (ι → Bool) × (ι → Bool) => fun i => z.1 i || z.2 i) =
      bernoulliFlagLaw (fun i => bernoulliUnionProbability (p i) (q i)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow Bool Bool ι
  have he := measurePreserving_arrowProdEquivProdArrow Bool Bool ι
    (fun i => bernoulliMeasure true false (p i))
    (fun i => bernoulliMeasure true false (q i))
  change ((Measure.pi fun i => bernoulliMeasure true false (p i)).prod
    (Measure.pi fun i => bernoulliMeasure true false (q i))).map _ = _
  rw [← he.map_eq, Measure.map_map (measurable_of_countable _) e.measurable]
  change (Measure.pi fun i => (bernoulliMeasure true false (p i)).prod
    (bernoulliMeasure true false (q i))).map
      (fun x i => (x i).1 || (x i).2) = _
  rw [Measure.pi_map_pi (f := fun (_ : ι) (z : Bool × Bool) => z.1 || z.2)
    (fun i => (measurable_of_countable _).aemeasurable)]
  simp only [bernoulliMeasure_or, bernoulliFlagLaw]

/-- Expectation after adding independent fresh flags to the flags already present. -/
def completionExpectation (p : ι → unitInterval) (φ : Finset ι → ℝ) (F : Finset ι) : ℝ :=
  ∫ x, φ (F ∪ freshFlagSet x) ∂bernoulliFlagLaw p

/-- Completion can only increase a monotone test function. -/
theorem le_completionExpectation (p : ι → unitInterval) {φ : Finset ι → ℝ}
    (hφ : Monotone φ) (F : Finset ι) : φ F ≤ completionExpectation p φ F := by
  calc
    φ F = ∫ _ : ι → Bool, φ F ∂bernoulliFlagLaw p := by simp
    _ ≤ _ := integral_mono Integrable.of_finite Integrable.of_finite
      (fun x => hφ Finset.subset_union_left)

/-- The completion operator preserves monotonicity in the existing flag set. -/
theorem completionExpectation_monotone (p : ι → unitInterval) {φ : Finset ι → ℝ}
    (hφ : Monotone φ) : Monotone (completionExpectation p φ) := by
  intro F G hFG
  exact integral_mono Integrable.of_finite Integrable.of_finite
    (fun x => hφ (Finset.union_subset_union hFG Finset.Subset.rfl))

/-- Exact semigroup law for independent completion, without any monotonicity premise. -/
theorem completionExpectation_union (p q : ι → unitInterval)
    (φ : Finset ι → ℝ) (F : Finset ι) :
    completionExpectation (fun i => bernoulliUnionProbability (p i) (q i)) φ F =
      completionExpectation p (completionExpectation q φ) F := by
  unfold completionExpectation
  rw [← bernoulliFlagLaw_or, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable,
    integral_prod _ Integrable.of_finite]
  simp only [freshFlagSet_or, Finset.union_assoc]

/-- Completion is monotone in its test function. -/
theorem completionExpectation_mono_test (p : ι → unitInterval)
    {φ ψ : Finset ι → ℝ} (h : ∀ F, φ F ≤ ψ F) (F : Finset ι) :
    completionExpectation p φ F ≤ completionExpectation p ψ F :=
  integral_mono Integrable.of_finite Integrable.of_finite (fun _ => h _)

/-- Independent extra flags that increase a Bernoulli parameter from `p` to `q`. -/
def bernoulliSupplementProbability (p q : unitInterval) (h : p ≤ q) : unitInterval :=
  if hp : p = 1 then 0 else
    ⟨((q : ℝ) - p) / (1 - p), by
      have hp' : (p : ℝ) < 1 := lt_of_le_of_ne p.property.2
        (fun he => hp (Subtype.ext he))
      constructor
      · exact div_nonneg (sub_nonneg.mpr h) (by linarith)
      · apply (div_le_one (by linarith : 0 < 1 - (p : ℝ))).mpr
        linarith [q.property.2]⟩

@[simp] theorem bernoulliUnionProbability_supplement (p q : unitInterval) (h : p ≤ q) :
    bernoulliUnionProbability p (bernoulliSupplementProbability p q h) = q := by
  apply Subtype.ext
  unfold bernoulliSupplementProbability
  split_ifs with hp
  · have hp' : (p : ℝ) = 1 := congrArg Subtype.val hp
    have hreal : (p : ℝ) ≤ q := h
    have hq : (q : ℝ) = 1 := le_antisymm q.property.2 (by simpa [hp'] using hreal)
    simp [bernoulliUnionProbability_coe, hp', hq]
  · have hp' : (p : ℝ) ≠ 1 := fun he => hp (Subtype.ext he)
    change (p : ℝ) + ((q : ℝ) - p) / (1 - p) -
      p * (((q : ℝ) - p) / (1 - p)) = q
    field_simp
    ring

/-- Stochastic monotonicity in all coordinate probabilities, proved by an independent OR coupling. -/
theorem completionExpectation_mono_probability (p q : ι → unitInterval)
    (hpq : ∀ i, p i ≤ q i) {φ : Finset ι → ℝ} (hφ : Monotone φ) (F : Finset ι) :
    completionExpectation p φ F ≤ completionExpectation q φ F := by
  let r i := bernoulliSupplementProbability (p i) (q i) (hpq i)
  calc
    completionExpectation p φ F ≤ completionExpectation p (completionExpectation r φ) F :=
      completionExpectation_mono_test p (le_completionExpectation r hφ) F
    _ = completionExpectation q φ F := by
      rw [← completionExpectation_union]
      simp [r]

/-- Expose only the active labels of a fresh independent vector. -/
def activeCompletionExpectation (p : ι → unitInterval) (active : Finset ι)
    (φ : Finset ι → ℝ) (F : Finset ι) : ℝ :=
  ∫ x, φ (F ∪ (freshFlagSet x ∩ active)) ∂bernoulliFlagLaw p

/-- Omitting inactive labels decreases every monotone test expectation. -/
theorem activeCompletionExpectation_le (p : ι → unitInterval) (active : Finset ι)
    {φ : Finset ι → ℝ} (hφ : Monotone φ) (F : Finset ι) :
    activeCompletionExpectation p active φ F ≤ completionExpectation p φ F :=
  integral_mono Integrable.of_finite Integrable.of_finite
    (fun _ => hφ (Finset.union_subset_union Finset.Subset.rfl Finset.inter_subset_left))

/-- Active-coordinate exposure with smaller probabilities also decreases the expectation. -/
theorem activeCompletionExpectation_le_of_probability_le (p q : ι → unitInterval)
    (hpq : ∀ i, p i ≤ q i) (active : Finset ι)
    {φ : Finset ι → ℝ} (hφ : Monotone φ) (F : Finset ι) :
    activeCompletionExpectation p active φ F ≤ completionExpectation q φ F :=
  (activeCompletionExpectation_le p active hφ F).trans
    (completionExpectation_mono_probability p q hpq hφ F)

/-- An exponential clock of nonnegative hazard `b` fires with probability `1-exp(-b)`. -/
def hazardProbability (b : ℝ≥0) : unitInterval :=
  ⟨1 - Real.exp (-(b : ℝ)), by
    constructor
    · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (neg_nonpos.mpr b.property))
    · linarith [Real.exp_pos (-(b : ℝ))]⟩

@[simp] theorem hazardProbability_coe (b : ℝ≥0) :
    (hazardProbability b : ℝ) = 1 - Real.exp (-(b : ℝ)) := rfl

@[simp] theorem hazardProbability_zero : hazardProbability 0 = 0 := by
  apply Subtype.ext
  simp

/-- Two independent clock increments add their hazards exactly. -/
theorem hazardProbability_add (b c : ℝ≥0) :
    hazardProbability (b + c) =
      bernoulliUnionProbability (hazardProbability b) (hazardProbability c) := by
  apply Subtype.ext
  simp only [hazardProbability_coe, bernoulliUnionProbability_coe, NNReal.coe_add,
    neg_add_rev, Real.exp_add]
  ring

/-- Remaining-budget completion potential for an arbitrary finite-state test function. -/
def hazardCompletion (b : ℝ≥0) (φ : Finset ι → ℝ) (F : Finset ι) : ℝ :=
  completionExpectation (fun _ => hazardProbability b) φ F

/-- Every monotone payoff is bounded above by its remaining-budget completion. -/
theorem le_hazardCompletion (b : ℝ≥0) {φ : Finset ι → ℝ}
    (hφ : Monotone φ) (F : Finset ι) : φ F ≤ hazardCompletion b φ F :=
  le_completionExpectation _ hφ F

/-- Completion under two independent common hazard increments is exact. -/
theorem completionExpectation_add_hazard (b c : ℝ≥0) (φ : Finset ι → ℝ) (F : Finset ι) :
    hazardCompletion (b + c) φ F =
      completionExpectation (fun _ => hazardProbability b) (hazardCompletion c φ) F := by
  simp only [hazardCompletion, hazardProbability_add]
  exact completionExpectation_union _ _ _ _

/-- Split the available hazard into the next increment and the remaining budget. -/
theorem hazardCompletion_split (b step : ℝ≥0) (hstep : step ≤ b)
    (φ : Finset ι → ℝ) (F : Finset ι) :
    hazardCompletion b φ F =
      completionExpectation (fun _ => hazardProbability step)
        (hazardCompletion (b - step) φ) F := by
  rw [← completionExpectation_add_hazard, add_tsub_cancel_of_le hstep]

/-- One finite independent call, with arbitrary active labels and coordinate probabilities below
its allocated hazard, has expected remaining potential at most the current potential. -/
theorem active_hazardCompletion_le (b step : ℝ≥0) (hstep : step ≤ b)
    (p : ι → unitInterval) (hp : ∀ i, p i ≤ hazardProbability step)
    (active : Finset ι) {φ : Finset ι → ℝ} (hφ : Monotone φ) (F : Finset ι) :
    activeCompletionExpectation p active (hazardCompletion (b - step) φ) F ≤
      hazardCompletion b φ F := by
  rw [hazardCompletion_split b step hstep]
  exact activeCompletionExpectation_le_of_probability_le p _ hp active
    (completionExpectation_monotone _ hφ) F

end GapEntropy
