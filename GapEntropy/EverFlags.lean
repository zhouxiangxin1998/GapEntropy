import GapEntropy.PredictableBernoulli
import Mathlib.Order.Filter.Finite

/-! Infinite ever-flags under predictable common hazard budgets. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace GapEntropy

/-- The exact clock firing probability is bounded by its nonnegative hazard budget. -/
theorem hazardProbability_le_budget (B : ℝ≥0) : (hazardProbability B : ℝ) ≤ B := by
  have h := Real.add_one_le_exp (-(B : ℝ))
  simp only [hazardProbability_coe]
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- All labels that occur at any finite time in a flag sequence. -/
def everFlagSet (F : ℕ → Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => ∃ t, i ∈ F t

omit [DecidableEq ι] in
@[simp] theorem mem_everFlagSet (F : ℕ → Finset ι) (i : ι) :
    i ∈ everFlagSet F ↔ ∃ t, i ∈ F t := by
  classical
  simp [everFlagSet]

omit [DecidableEq ι] in
theorem subset_everFlagSet (F : ℕ → Finset ι) (t : ℕ) : F t ⊆ everFlagSet F := by
  intro i hi
  exact (mem_everFlagSet F i).mpr ⟨t, hi⟩

/-- A monotone sequence of subsets of a finite type eventually includes all its ever-members. -/
theorem eventually_eq_everFlagSet (F : ℕ → Finset ι) (hF : Monotone F) :
    ∀ᶠ t in atTop, F t = everFlagSet F := by
  have hi (i : ι) : ∀ᶠ t in atTop, i ∈ F t ↔ i ∈ everFlagSet F := by
    by_cases h : i ∈ everFlagSet F
    · obtain ⟨T, hT⟩ := (mem_everFlagSet F i).mp h
      filter_upwards [eventually_ge_atTop T] with t ht
      exact iff_of_true (hF ht hT) h
    · exact Eventually.of_forall fun t => iff_of_false
        (fun ht => h (subset_everFlagSet F t ht)) h
  filter_upwards [eventually_all.mpr hi] with t ht
  exact Finset.ext ht

/-- Count flags in one fixed block and require nonnegative flagged weight in another block. -/
def jointFlagThreshold (core outside : Finset ι) (r : ℕ) (w : ι → ℝ) (u : ℝ) :
    Set (Finset ι) := {F | r ≤ (core ∩ F).card ∧ u ≤ ∑ i ∈ outside ∩ F, w i}

omit [Fintype ι] in
theorem jointFlagThreshold_increasing (core outside : Finset ι) (r : ℕ)
    (w : ι → ℝ) (hw : ∀ i ∈ outside, 0 ≤ w i) (u : ℝ) :
    ∀ F G : Finset ι, F ⊆ G → F ∈ jointFlagThreshold core outside r w u →
      G ∈ jointFlagThreshold core outside r w u := by
  intro F G hFG hF
  refine ⟨hF.1.trans (Finset.card_le_card
    (Finset.inter_subset_inter Finset.Subset.rfl hFG)), hF.2.trans ?_⟩
  apply Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.inter_subset_inter Finset.Subset.rfl hFG)
  intro i hi _
  exact hw i (Finset.mem_inter.mp hi).1

/-- Reconstructing the fresh flags in a fixed block from that block's coordinate vector. -/
theorem freshFlagSet_subtype_image (S : Finset ι) (x : ι → Bool) :
    (freshFlagSet (fun i : S => x i)).image Subtype.val = S ∩ freshFlagSet x := by
  ext i
  simp only [Finset.mem_image, mem_freshFlagSet, Finset.mem_inter]
  constructor
  · rintro ⟨⟨j, hj⟩, hx, hji⟩
    subst i
    exact ⟨hj, hx⟩
  · rintro ⟨hi, hx⟩
    exact ⟨⟨i, hi⟩, hx, rfl⟩

/-- Under the comparison product law, fresh flag sets on disjoint fixed blocks are independent. -/
theorem bernoulliFlagLaw_indep_blocks (p : ι → unitInterval) (S T : Finset ι)
    (hST : Disjoint S T) :
    IndepFun (fun x => S ∩ freshFlagSet x) (fun x => T ∩ freshFlagSet x)
      (bernoulliFlagLaw p) := by
  have h := (bernoulliFlagLaw_indep p).indepFun_finset S T hST
    (fun i => measurable_pi_apply i)
  have hc := h.comp
    (measurable_of_countable (fun x : S → Bool => (freshFlagSet x).image Subtype.val))
    (measurable_of_countable (fun x : T → Bool => (freshFlagSet x).image Subtype.val))
  simpa only [Function.comp_def, freshFlagSet_subtype_image] using hc

/-- The joint comparison probability factors across disjoint core/outside blocks. -/
theorem bernoulliFlagLaw_joint_threshold_eq_mul (p : ι → unitInterval)
    (core outside : Finset ι) (hdisjoint : Disjoint core outside)
    (r : ℕ) (w : ι → ℝ) (u : ℝ) :
    bernoulliFlagLaw p {x | freshFlagSet x ∈ jointFlagThreshold core outside r w u} =
      bernoulliFlagLaw p {x | r ≤ (core ∩ freshFlagSet x).card} *
      bernoulliFlagLaw p {x | u ≤ ∑ i ∈ outside ∩ freshFlagSet x, w i} := by
  have h := (bernoulliFlagLaw_indep_blocks p core outside hdisjoint).measure_inter_preimage_eq_mul {F : Finset ι | r ≤ F.card}
      {F : Finset ι | u ≤ ∑ i ∈ F, w i}
      (Set.toFinite _).measurableSet (Set.toFinite _).measurableSet
  exact h

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ mΩ}
namespace PredictableBernoulliProcess
variable (P : PredictableBernoulliProcess (ι := ι) μ ℱ)

/-- All flags in the entire actual attempt, allowing countably many executed or padded calls. -/
def everFlags (ω : Ω) : Finset ι := everFlagSet (fun t => P.flags t ω)

@[simp] theorem mem_everFlags (ω : Ω) (i : ι) :
    i ∈ P.everFlags ω ↔ ∃ t, i ∈ P.flags t ω := mem_everFlagSet _ _

theorem flags_subset_everFlags (t : ℕ) (ω : Ω) : P.flags t ω ⊆ P.everFlags ω :=
  subset_everFlagSet (fun t => P.flags t ω) t

theorem eventually_flags_eq_ever (ω : Ω) :
    ∀ᶠ t in atTop, P.flags t ω = P.everFlags ω :=
  eventually_eq_everFlagSet _ (P.flags_monotone ω)

/-- The infinite ever-flag set is a measurable finite-valued random variable. -/
theorem measurable_everFlags : Measurable P.everFlags := by
  apply measurable_finset_iff.mpr
  intro i
  simp only [mem_everFlags]
  apply Measurable.exists
  intro t
  exact (measurable_finset_mem i).comp
    ((P.measurable_flags t).mono (ℱ.le t) le_rfl)

/-- An increasing event of ever-flags occurs at some finite prefix, without any deterministic
bound on the last flag time. -/
theorem everFlags_event_eq_iUnion (S : Set (Finset ι))
    (hS : ∀ F G : Finset ι, F ⊆ G → F ∈ S → G ∈ S) :
    {ω | P.everFlags ω ∈ S} = ⋃ T, {ω | P.flags T ω ∈ S} := by
  ext ω
  constructor
  · intro hω
    obtain ⟨T, hT⟩ := (P.eventually_flags_eq_ever ω).exists
    apply Set.mem_iUnion.mpr
    refine ⟨T, ?_⟩
    change P.flags T ω ∈ S
    rwa [hT]
  · intro hω
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hω
    exact hS _ _ (P.flags_subset_everFlags T ω) hT

/-- The actual probability of an increasing ever-flag event is the supremum of its finite
prefix probabilities. -/
theorem probability_everFlags_eq_iSup (S : Set (Finset ι))
    (hS : ∀ F G : Finset ι, F ⊆ G → F ∈ S → G ∈ S) :
    μ {ω | P.everFlags ω ∈ S} = ⨆ T, μ {ω | P.flags T ω ∈ S} := by
  rw [P.everFlags_event_eq_iUnion S hS]
  apply Monotone.measure_iUnion
  intro t u htu ω hω
  exact hS _ _ (P.flags_monotone ω htu) hω

variable [IsProbabilityMeasure μ]

/-- Infinite-horizon joint stochastic domination of all ever-flags by the actual independent
Bernoulli product law at the total predictable hazard budget. -/
theorem probability_everFlags_increasing_event_le (B : ℝ≥0)
    (hflags0 : ∀ ω, P.flags 0 ω = ∅) (hbudget0 : ∀ ω, P.remaining 0 ω = B)
    (S : Set (Finset ι))
    (hS : ∀ F G : Finset ι, F ⊆ G → F ∈ S → G ∈ S) :
    μ {ω | P.everFlags ω ∈ S} ≤
      bernoulliFlagLaw (fun _ : ι => hazardProbability B) {x | freshFlagSet x ∈ S} := by
  rw [P.probability_everFlags_eq_iSup S hS]
  exact iSup_le fun T => P.probability_increasing_event_le B hflags0 hbudget0 S hS T

/-- Joint core-count and outside-weight domination for the entire actual attempt. Both
requirements are transferred together to the independent comparison law. -/
theorem probability_everFlags_joint_threshold_le (B : ℝ≥0)
    (hflags0 : ∀ ω, P.flags 0 ω = ∅) (hbudget0 : ∀ ω, P.remaining 0 ω = B)
    (core outside : Finset ι) (r : ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ outside, 0 ≤ w i) (u : ℝ) :
    μ {ω | r ≤ (core ∩ P.everFlags ω).card ∧
      u ≤ ∑ i ∈ outside ∩ P.everFlags ω, w i} ≤
      bernoulliFlagLaw (fun _ : ι => hazardProbability B)
        {x | r ≤ (core ∩ freshFlagSet x).card ∧
          u ≤ ∑ i ∈ outside ∩ freshFlagSet x, w i} :=
  P.probability_everFlags_increasing_event_le B hflags0 hbudget0
    (jointFlagThreshold core outside r w u)
    (jointFlagThreshold_increasing core outside r w hw u)

/-- Core and outside requirements factor only in the independent comparison law. No
independence is assumed or concluded for the actual adaptive flags. -/
theorem probability_everFlags_joint_threshold_le_product (B : ℝ≥0)
    (hflags0 : ∀ ω, P.flags 0 ω = ∅) (hbudget0 : ∀ ω, P.remaining 0 ω = B)
    (core outside : Finset ι) (hdisjoint : Disjoint core outside) (r : ℕ) (w : ι → ℝ)
    (hw : ∀ i ∈ outside, 0 ≤ w i) (u : ℝ) :
    μ {ω | r ≤ (core ∩ P.everFlags ω).card ∧
      u ≤ ∑ i ∈ outside ∩ P.everFlags ω, w i} ≤
      bernoulliFlagLaw (fun _ : ι => hazardProbability B)
        {x | r ≤ (core ∩ freshFlagSet x).card} *
      bernoulliFlagLaw (fun _ : ι => hazardProbability B)
        {x | u ≤ ∑ i ∈ outside ∩ freshFlagSet x, w i} := by
  rw [← bernoulliFlagLaw_joint_threshold_eq_mul _ core outside hdisjoint r w u]
  exact P.probability_everFlags_joint_threshold_le B hflags0 hbudget0
    core outside r w hw u

end PredictableBernoulliProcess
end GapEntropy
