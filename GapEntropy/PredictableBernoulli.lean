import GapEntropy.BernoulliCompletion
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Probability.Process.Filtration
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Finite-horizon joint domination under an actual conditional product law and a predictable
remaining common hazard budget. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace GapEntropy
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Product flag probabilities, as real singleton masses of the actual law. -/
theorem bernoulliFlagLaw_real_singleton (p : ι → unitInterval) (x : ι → Bool) :
    (bernoulliFlagLaw p).real {x} =
      ∏ i, if x i = true then (p i : ℝ) else 1 - p i := by
  rw [measureReal_def, bernoulliFlagLaw, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  change (bernoulliMeasure true false (p i)).real {x i} = _
  cases x i <;> simp

/-- Finite expansion of the completion potential, including its probability law. -/
theorem completionExpectation_eq_sum (p : ι → unitInterval)
    (φ : Finset ι → ℝ) (F : Finset ι) :
    completionExpectation p φ F = ∑ x : ι → Bool,
      (∏ i, if x i = true then (p i : ℝ) else 1 - p i) * φ (F ∪ freshFlagSet x) := by
  rw [completionExpectation, integral_fintype Integrable.of_finite]
  simp only [bernoulliFlagLaw_real_singleton, smul_eq_mul]

/-- A uniform finite bound for all values of a finite-state test function. -/
def finitePayoffBound (φ : Finset ι → ℝ) : ℝ := ∑ F : Finset ι, ‖φ F‖

omit [DecidableEq ι] in
theorem finitePayoffBound_nonneg (φ : Finset ι → ℝ) : 0 ≤ finitePayoffBound φ :=
  Finset.sum_nonneg (fun _ _ => norm_nonneg _)

omit [DecidableEq ι] in
theorem norm_le_finitePayoffBound (φ : Finset ι → ℝ) (F : Finset ι) :
    ‖φ F‖ ≤ finitePayoffBound φ :=
  Finset.single_le_sum (fun G _ => norm_nonneg (φ G)) (Finset.mem_univ F)

/-- Completion has the same uniform bound as its finite-state payoff. -/
theorem norm_completionExpectation_le (p : ι → unitInterval) (φ : Finset ι → ℝ)
    (F : Finset ι) : ‖completionExpectation p φ F‖ ≤ finitePayoffBound φ := by
  simpa [completionExpectation] using
    norm_integral_le_of_norm_le_const (μ := bernoulliFlagLaw p)
      (ae_of_all _ fun x => norm_le_finitePayoffBound φ (F ∪ freshFlagSet x))

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Completion is measurable when both the remaining budget and existing flags are random. -/
theorem measurable_hazardCompletion {b : Ω → ℝ≥0} {F : Ω → Finset ι}
    (hb : Measurable b) (hF : Measurable F) (φ : Finset ι → ℝ) :
    Measurable (fun ω => hazardCompletion (b ω) φ (F ω)) := by
  simp only [hazardCompletion, completionExpectation_eq_sum]
  apply Finset.measurable_sum
  intro x _
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro i _
    cases x i <;> simp only [Bool.false_eq_true, if_false, if_true,
      hazardProbability_coe] <;> fun_prop
  · exact (measurable_of_countable (fun G : Finset ι => φ (G ∪ freshFlagSet x))).comp hF

/-- Conditional law of the entire new flag vector. This is stronger than assumptions about
individual conditional flag probabilities. -/
def HasConditionalBernoulliLaw (μ : Measure Ω) (m : MeasurableSpace Ω)
    (X : Ω → ι → Bool) (p : Ω → ι → unitInterval) : Prop :=
  ∀ x : ι → Bool,
    μ[fun ω => if X ω = x then (1 : ℝ) else 0 | m] =ᵐ[μ]
      fun ω => (bernoulliFlagLaw (p ω)).real {x}

section ConditionalFinite
variable {α : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω}

/-- A full finite conditional law determines conditional expectations even for payoffs whose
coefficients depend measurably on the past. The proof expands every singleton indicator. -/
theorem condExp_finite_random_payoff (hm : m ≤ mΩ) (X : Ω → α) (hX : Measurable[mΩ] X)
    (κ : Ω → Measure α) (g : α → Ω → ℝ)
    (hg : ∀ x, StronglyMeasurable[m] (g x)) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x ω, ‖g x ω‖ ≤ C)
    (hlaw : ∀ x, μ[fun ω => if X ω = x then (1 : ℝ) else 0 | m] =ᵐ[μ]
      fun ω => (κ ω).real {x}) :
    μ[fun ω => g (X ω) ω | m] =ᵐ[μ]
      fun ω => ∑ x, g x ω * (κ ω).real {x} := by
  let ind (x : α) (ω : Ω) : ℝ := if X ω = x then 1 else 0
  have hind_meas (x : α) : Measurable[mΩ] (ind x) := by
    exact measurable_const.ite (hX (measurableSet_singleton x)) measurable_const
  have hind_int (x : α) : Integrable (ind x) μ := by
    apply (integrable_const (1 : ℝ)).mono' (hind_meas x).aestronglyMeasurable
    exact ae_of_all _ fun ω => by simp only [ind]; split_ifs <;> norm_num
  have hprod_int (x : α) : Integrable (g x * ind x) μ := by
    apply (integrable_const C).mono'
      (((hg x).mono hm).mul (hind_meas x).stronglyMeasurable).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      change ‖g x ω * ind x ω‖ ≤ C
      simp only [ind]
      split_ifs <;> simp_all
  have heq : (fun ω => g (X ω) ω) = ∑ x, g x * ind x := by
    funext ω
    simp [ind, Finset.sum_ite_eq', eq_comm]
  rw [heq]
  have hs := condExp_finsetSum (fun x (_ : x ∈ (Finset.univ : Finset α)) => hprod_int x) m
  have hp (x : α) := condExp_mul_of_stronglyMeasurable_left (hg x)
    (hprod_int x) (hind_int x)
  filter_upwards [hs, ae_all_iff.mpr hp, ae_all_iff.mpr hlaw] with ω hsum hmul hprob
  change (μ[∑ x, g x * ind x | m]) ω = _ at hsum ⊢
  rw [hsum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [hmul x]
  change g x ω * (μ[ind x | m]) ω = _
  rw [hprob x]

end ConditionalFinite

/-- A finite-label process with a predictable common hazard budget and an actual conditional
product law for each new vector. No potential inequality is part of this structure. -/
structure PredictableBernoulliProcess (μ : Measure Ω) (ℱ : Filtration ℕ mΩ) where
  flags : ℕ → Ω → Finset ι
  active : ℕ → Ω → Finset ι
  remaining : ℕ → Ω → ℝ≥0
  increment : ℕ → Ω → ℝ≥0
  parameters : ℕ → Ω → ι → unitInterval
  fresh : ℕ → Ω → ι → Bool
  measurable_flags : ∀ t, Measurable[ℱ t] (flags t)
  measurable_active : ∀ t, Measurable[ℱ t] (active t)
  measurable_remaining : ∀ t, Measurable[ℱ t] (remaining t)
  measurable_increment : ∀ t, Measurable[ℱ t] (increment t)
  measurable_parameters : ∀ t i, Measurable[ℱ t] (fun ω => parameters t ω i)
  measurable_fresh : ∀ t, Measurable[ℱ (t + 1)] (fresh t)
  increment_le : ∀ t ω, increment t ω ≤ remaining t ω
  parameters_le : ∀ t ω i, parameters t ω i ≤ hazardProbability (increment t ω)
  remaining_succ : ∀ t ω, remaining (t + 1) ω = remaining t ω - increment t ω
  flags_succ : ∀ t ω, flags (t + 1) ω =
    flags t ω ∪ (freshFlagSet (fresh t ω) ∩ active t ω)
  conditional_law : ∀ t, HasConditionalBernoulliLaw μ (ℱ t) (fresh t) (parameters t)

namespace PredictableBernoulliProcess
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
    (P : PredictableBernoulliProcess (ι := ι) μ ℱ)

/-- The verified remaining-budget potential, evaluated on the actual random state. -/
def potential (φ : Finset ι → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  hazardCompletion (P.remaining t ω) φ (P.flags t ω)

omit [IsProbabilityMeasure μ] in
theorem measurable_potential (φ : Finset ι → ℝ) (t : ℕ) :
    Measurable[ℱ t] (P.potential φ t) :=
  measurable_hazardCompletion (P.measurable_remaining t) (P.measurable_flags t) φ

omit [IsProbabilityMeasure μ] in
theorem norm_potential_le (φ : Finset ι → ℝ) (t : ℕ) (ω : Ω) :
    ‖P.potential φ t ω‖ ≤ finitePayoffBound φ :=
  norm_completionExpectation_le _ _ _

theorem integrable_potential (φ : Finset ι → ℝ) (t : ℕ) :
    Integrable (P.potential φ t) μ := by
  apply (integrable_const (finitePayoffBound φ)).mono'
    ((P.measurable_potential φ t).mono (ℱ.le t) le_rfl).aestronglyMeasurable
  exact ae_of_all _ (P.norm_potential_le φ t)

/-- The conditional expectation of the next potential is its actual finite conditional-law
integral. Random budgets, increments, existing flags, and active sets stay inside this identity. -/
theorem condExp_potential_eq (φ : Finset ι → ℝ) (t : ℕ) :
    μ[P.potential φ (t + 1) | ℱ t] =ᵐ[μ]
      fun ω => activeCompletionExpectation (P.parameters t ω) (P.active t ω)
        (hazardCompletion (P.remaining t ω - P.increment t ω) φ) (P.flags t ω) := by
  let g (x : ι → Bool) (ω : Ω) :=
    hazardCompletion (P.remaining t ω - P.increment t ω) φ
      (P.flags t ω ∪ (freshFlagSet x ∩ P.active t ω))
  have hg (x : ι → Bool) : StronglyMeasurable[ℱ t] (g x) := by
    apply Measurable.stronglyMeasurable
    apply measurable_hazardCompletion
      ((P.measurable_remaining t).sub (P.measurable_increment t))
    exact (measurable_of_countable
      (fun z : Finset ι × Finset ι => z.1 ∪ (freshFlagSet x ∩ z.2))).comp
        ((P.measurable_flags t).prodMk (P.measurable_active t))
  have hgC (x : ι → Bool) (ω : Ω) : ‖g x ω‖ ≤ finitePayoffBound φ :=
    norm_completionExpectation_le _ _ _
  have heq : P.potential φ (t + 1) = (fun ω => g (P.fresh t ω) ω) := by
    funext ω
    simp only [potential, P.remaining_succ, P.flags_succ, g]
  rw [heq]
  have hc := condExp_finite_random_payoff (ℱ.le t) (P.fresh t)
    ((P.measurable_fresh t).mono (ℱ.le _) le_rfl)
    (fun ω => bernoulliFlagLaw (P.parameters t ω)) g hg (finitePayoffBound φ)
    (finitePayoffBound_nonneg φ) hgC (P.conditional_law t)
  filter_upwards [hc] with ω hω
  rw [hω, activeCompletionExpectation, integral_fintype Integrable.of_finite]
  simp only [smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  exact mul_comm _ _

/-- The supermartingale inequality follows from the full conditional law and the hazard budget. -/
theorem condExp_potential_le {φ : Finset ι → ℝ} (hφ : Monotone φ) (t : ℕ) :
    μ[P.potential φ (t + 1) | ℱ t] ≤ᵐ[μ] P.potential φ t := by
  filter_upwards [P.condExp_potential_eq φ t] with ω hω
  rw [hω]
  exact active_hazardCompletion_le _ _ (P.increment_le t ω)
    _ (P.parameters_le t ω) _ hφ _

/-- Expected remaining potential decreases along the actual filtered process. -/
theorem integral_potential_le_initial {φ : Finset ι → ℝ} (hφ : Monotone φ) (T : ℕ) :
    (∫ ω, P.potential φ T ω ∂μ) ≤ ∫ ω, P.potential φ 0 ω ∂μ := by
  induction T with
  | zero => rfl
  | succ T ih =>
    calc
      (∫ ω, P.potential φ (T + 1) ω ∂μ) =
          ∫ ω, μ[P.potential φ (T + 1) | ℱ T] ω ∂μ :=
        (integral_condExp (ℱ.le T)).symm
      _ ≤ ∫ ω, P.potential φ T ω ∂μ :=
        integral_mono_ae integrable_condExp (P.integrable_potential φ T)
          (P.condExp_potential_le hφ T)
      _ ≤ _ := ih

/-- Finite-horizon joint domination for every monotone payoff under a random predictable
common hazard budget. The comparison is with the actual independent Bernoulli completion law. -/
theorem integral_payoff_le_completion (B : ℝ≥0)
    (hflags0 : ∀ ω, P.flags 0 ω = ∅) (hbudget0 : ∀ ω, P.remaining 0 ω = B)
    {φ : Finset ι → ℝ} (hφ : Monotone φ) (T : ℕ) :
    (∫ ω, φ (P.flags T ω) ∂μ) ≤ hazardCompletion B φ ∅ := by
  have hi : Integrable (fun ω => φ (P.flags T ω)) μ := by
    apply (integrable_const (finitePayoffBound φ)).mono'
      (((measurable_of_countable φ).comp (P.measurable_flags T)).mono
        (ℱ.le T) le_rfl).aestronglyMeasurable
    exact ae_of_all _ fun ω => norm_le_finitePayoffBound φ _
  calc
    (∫ ω, φ (P.flags T ω) ∂μ) ≤ ∫ ω, P.potential φ T ω ∂μ :=
      integral_mono hi (P.integrable_potential φ T)
        (fun ω => le_hazardCompletion _ hφ _)
    _ ≤ ∫ ω, P.potential φ 0 ω ∂μ := P.integral_potential_le_initial hφ T
    _ = hazardCompletion B φ ∅ := by simp [potential, hflags0, hbudget0]

omit [IsProbabilityMeasure μ] in
/-- The process keeps every earlier flag. -/
theorem flags_monotone (ω : Ω) : Monotone (fun t => P.flags t ω) := by
  apply monotone_nat_of_le_succ
  intro t
  rw [P.flags_succ]
  exact Finset.subset_union_left

/-- Actual ENNReal probabilities of arbitrary increasing finite-state events are dominated by
the independent Bernoulli flags of total hazard `B`. This is joint stochastic domination. -/
theorem probability_increasing_event_le (B : ℝ≥0)
    (hflags0 : ∀ ω, P.flags 0 ω = ∅) (hbudget0 : ∀ ω, P.remaining 0 ω = B)
    (S : Set (Finset ι))
    (hS : ∀ F G : Finset ι, F ⊆ G → F ∈ S → G ∈ S) (T : ℕ) :
    μ {ω | P.flags T ω ∈ S} ≤
      bernoulliFlagLaw (fun _ : ι => hazardProbability B) {x | freshFlagSet x ∈ S} := by
  classical
  let φ : Finset ι → ℝ := fun F => if F ∈ S then 1 else 0
  have hφ : Monotone φ := by
    intro F G hFG
    by_cases hF : F ∈ S
    · simp [φ, hF, hS F G hFG hF]
    · simp only [φ, hF, if_false]
      split_ifs <;> norm_num
  have hleft : (∫ ω, φ (P.flags T ω) ∂μ) = μ.real {ω | P.flags T ω ∈ S} := by
    have hmeas : MeasurableSet {ω | P.flags T ω ∈ S} :=
      (P.measurable_flags T).mono (ℱ.le T) le_rfl (Set.toFinite S).measurableSet
    simpa [φ, Set.indicator] using integral_indicator_one (μ := μ) hmeas
  have hright : hazardCompletion B φ ∅ =
      (bernoulliFlagLaw (fun _ : ι => hazardProbability B)).real
        {x | freshFlagSet x ∈ S} := by
    simpa [hazardCompletion, completionExpectation, φ, Set.indicator] using
      integral_indicator_one
        (μ := bernoulliFlagLaw (fun _ : ι => hazardProbability B))
        (Set.toFinite {x : ι → Bool | freshFlagSet x ∈ S}).measurableSet
  have h := P.integral_payoff_le_completion B hflags0 hbudget0 hφ T
  rw [hleft, hright] at h
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
    ENNReal.ofReal_le_ofReal h

end PredictableBernoulliProcess
end GapEntropy
