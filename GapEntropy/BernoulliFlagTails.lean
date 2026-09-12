import GapEntropy.EverFlags
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Probability.Moments.Basic

/-! Actual product Bernoulli probabilities used in the terminal-core bounds. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace GapEntropy
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact probability that every label in a fixed block is flagged. -/
theorem bernoulliFlagLaw_subset_real (p : ι → unitInterval) (S : Finset ι) :
    (bernoulliFlagLaw p).real {x | S ⊆ freshFlagSet x} = ∏ i ∈ S, (p i : ℝ) := by
  have heq : {x : ι → Bool | S ⊆ freshFlagSet x} =
      Set.univ.pi (fun i => if i ∈ S then ({true} : Set Bool) else Set.univ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.subset_iff, mem_freshFlagSet,
      Set.mem_pi, Set.mem_univ, forall_const]
    constructor
    · intro h i
      split_ifs with hi
      · exact h hi
      · trivial
    · intro h i hi
      simpa [hi] using h i
  rw [measureReal_def, bernoulliFlagLaw, heq, Measure.pi_pi, ENNReal.toReal_prod]
  have hterm (i : ι) :
      ((bernoulliMeasure true false (p i))
        (if i ∈ S then {true} else Set.univ)).toReal =
      if i ∈ S then (p i : ℝ) else 1 := by
    split_ifs <;> simp
  simp_rw [hterm]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

omit [Fintype ι] in
/-- If all but at most one core arm are flagged, erasing one core label leaves only flags. -/
theorem exists_erase_subset_of_card_inter (core F : Finset ι) (hcore : core.Nonempty)
    (hcount : core.card - 1 ≤ (core ∩ F).card) :
    ∃ i ∈ core, core.erase i ⊆ F := by
  by_cases hsub : core ⊆ F
  · obtain ⟨i, hi⟩ := hcore
    exact ⟨i, hi, (Finset.erase_subset _ _).trans hsub⟩
  · obtain ⟨i, hi, hiF⟩ := Finset.not_subset.mp hsub
    have hsmall : (core \ F).card ≤ 1 := by
      have hpart := Finset.card_inter_add_card_sdiff core F
      omega
    refine ⟨i, hi, ?_⟩
    intro j hj
    by_contra hjF
    have heq := Finset.card_le_one.mp hsmall i (Finset.mem_sdiff.mpr ⟨hi, hiF⟩)
      j (Finset.mem_sdiff.mpr ⟨(Finset.mem_erase.mp hj).2, hjF⟩)
    exact (Finset.mem_erase.mp hj).1 heq.symm

/-- The actual core-event probability, including the singleton-core case. -/
theorem bernoulliFlagLaw_core_real_le (q : unitInterval) (core : Finset ι)
    (hcore : core.Nonempty) :
    (bernoulliFlagLaw (fun _ : ι => q)).real
      {x | max 1 (core.card - 1) ≤ (core ∩ freshFlagSet x).card} ≤
      (core.card : ℝ) * (q : ℝ) ^ max 1 (core.card - 1) := by
  by_cases hc : core.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    have hevent : {x : ι → Bool | max 1 (({i} : Finset ι).card - 1) ≤
        ({i} ∩ freshFlagSet x).card} = {x | ({i} : Finset ι) ⊆ freshFlagSet x} := by
      ext x
      by_cases hx : x i = true <;> simp [Finset.singleton_inter, hx]
    rw [hevent, bernoulliFlagLaw_subset_real]
    simp
  · have hc2 : 2 ≤ core.card := by have := hcore.card_pos; omega
    have hm : max 1 (core.card - 1) = core.card - 1 := max_eq_right (by omega)
    rw [hm]
    calc
      (bernoulliFlagLaw (fun _ : ι => q)).real
          {x | core.card - 1 ≤ (core ∩ freshFlagSet x).card} ≤
          (bernoulliFlagLaw (fun _ : ι => q)).real
            (⋃ i ∈ core, {x | core.erase i ⊆ freshFlagSet x}) := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro x hx
        obtain ⟨i, hi, hsub⟩ := exists_erase_subset_of_card_inter core _ hcore hx
        exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hsub⟩⟩
      _ ≤ ∑ i ∈ core, (bernoulliFlagLaw (fun _ : ι => q)).real
          {x | core.erase i ⊆ freshFlagSet x} := measureReal_biUnion_finset_le _ _
      _ = (core.card : ℝ) * (q : ℝ) ^ (core.card - 1) := by
        simp_rw [bernoulliFlagLaw_subset_real, Finset.prod_const]
        have heq : (∑ i ∈ core, (q : ℝ) ^ (core.erase i).card) =
            ∑ _i ∈ core, (q : ℝ) ^ (core.card - 1) :=
          Finset.sum_congr rfl (fun i hi => by rw [Finset.card_erase_of_mem hi])
        rw [heq]
        simp

/-- Core-event bound in the actual ENNReal measure. -/
theorem bernoulliFlagLaw_core_le (q : unitInterval) (core : Finset ι)
    (hcore : core.Nonempty) :
    bernoulliFlagLaw (fun _ : ι => q)
      {x | max 1 (core.card - 1) ≤ (core ∩ freshFlagSet x).card} ≤
      ENNReal.ofReal ((core.card : ℝ) * (q : ℝ) ^ max 1 (core.card - 1)) := by
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
    ENNReal.ofReal_le_ofReal (bernoulliFlagLaw_core_real_le q core hcore)

/-- The sum of flagged weights in a fixed block as a sum of coordinate functions. -/
theorem sum_inter_freshFlagSet (S : Finset ι) (a : ι → ℝ) (x : ι → Bool) :
    (∑ i ∈ S ∩ freshFlagSet x, a i) = ∑ i ∈ S, if x i = true then a i else 0 := by
  have heq : S ∩ freshFlagSet x = S.filter (fun i => x i = true) := by ext i; simp
  rw [heq, Finset.sum_filter]

/-- Exact weighted MGF of the actual independent product flag law. -/
theorem integral_exp_flag_weights (p : ι → unitInterval) (S : Finset ι)
    (a : ι → ℝ) (θ : ℝ) :
    (∫ x, Real.exp (θ * ∑ i ∈ S ∩ freshFlagSet x, a i) ∂bernoulliFlagLaw p) =
      ∏ i ∈ S, (1 + (p i : ℝ) * (Real.exp (θ * a i) - 1)) := by
  simp_rw [sum_inter_freshFlagSet, Finset.mul_sum]
  have heq (x : ι → Bool) : (∑ i ∈ S, θ * (if x i = true then a i else 0)) =
      ∑ i, if i ∈ S then θ * (if x i = true then a i else 0) else 0 := by simp
  simp_rw [heq, Real.exp_sum]
  rw [bernoulliFlagLaw, integral_fintype_prod_eq_prod
    (fun i (x : Bool) => Real.exp (if i ∈ S then θ * (if x = true then a i else 0) else 0))]
  have hterm (i : ι) :
      (∫ x : Bool, Real.exp (if i ∈ S then θ * (if x = true then a i else 0) else 0)
        ∂bernoulliMeasure true false (p i)) =
      if i ∈ S then 1 + (p i : ℝ) * (Real.exp (θ * a i) - 1) else 1 := by
    rw [integral_bernoulliMeasure]
    by_cases hi : i ∈ S
    · simp [hi]
      ring
    · simp [hi]
  simp_rw [hterm]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- The exponential chord inequality on a unit weight, from convexity. -/
theorem exp_mul_unit_sub_one_le (θ v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Real.exp (θ * v) - 1 ≤ v * (Real.exp θ - 1) := by
  have h := convexOn_exp.2 (show (0 : ℝ) ∈ Set.univ from trivial)
    (show θ ∈ Set.univ from trivial) (show 0 ≤ 1 - v by linarith) hv0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [mul_comm v θ] at h
  linarith

/-- Actual weighted Bernoulli MGF bound with a possibly larger comparison parameter `p`. -/
theorem integral_exp_unit_flag_weights_le (q : unitInterval) (S : Finset ι)
    (v : ι → ℝ) (hv0 : ∀ i ∈ S, 0 ≤ v i) (hv1 : ∀ i ∈ S, v i ≤ 1)
    (p : ℝ) (hqp : (q : ℝ) ≤ p) (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ x, Real.exp (θ * ∑ i ∈ S ∩ freshFlagSet x, v i)
      ∂bernoulliFlagLaw (fun _ : ι => q)) ≤
      Real.exp (p * (∑ i ∈ S, v i) * (Real.exp θ - 1)) := by
  rw [integral_exp_flag_weights]
  have hsum : p * (∑ i ∈ S, v i) * (Real.exp θ - 1) =
      ∑ i ∈ S, p * v i * (Real.exp θ - 1) := by
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hsum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    have he : 1 ≤ Real.exp (θ * v i) := Real.one_le_exp_iff.mpr (mul_nonneg hθ (hv0 i hi))
    nlinarith [mul_nonneg q.property.1 (sub_nonneg.mpr he)]
  · intro i hi
    have hc := exp_mul_unit_sub_one_le θ (v i) (hv0 i hi) (hv1 i hi)
    have hterm : (q : ℝ) * (Real.exp (θ * v i) - 1) ≤ p * v i * (Real.exp θ - 1) := by
      calc
        (q : ℝ) * (Real.exp (θ * v i) - 1) ≤
            q * (v i * (Real.exp θ - 1)) := mul_le_mul_of_nonneg_left hc q.property.1
        _ ≤ p * (v i * (Real.exp θ - 1)) :=
          mul_le_mul_of_nonneg_right hqp (mul_nonneg (hv0 i hi)
            (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hθ)))
        _ = _ := by ring
    exact (add_le_add_right hterm 1).trans (by
      simpa only [add_comm] using Real.add_one_le_exp (p * v i * (Real.exp θ - 1)))

/-- Exponential Markov at half the total unit weight, with the exact E.10 exponent. -/
theorem bernoulliFlagLaw_unit_weight_tail_real (q : unitInterval) (S : Finset ι)
    (v : ι → ℝ) (hv0 : ∀ i ∈ S, 0 ≤ v i) (hv1 : ∀ i ∈ S, v i ≤ 1)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) (hqp : (q : ℝ) ≤ p) :
    (bernoulliFlagLaw (fun _ : ι => q)).real
      {x | (∑ i ∈ S, v i) / 2 ≤ ∑ i ∈ S ∩ freshFlagSet x, v i} ≤
      Real.exp (-((∑ i ∈ S, v i) / 2) * Real.log (1 / (2 * p)) +
        (∑ i ∈ S, v i) / 2) := by
  let V := ∑ i ∈ S, v i
  let θ := Real.log (1 / (2 * p))
  have hV : 0 ≤ V := Finset.sum_nonneg hv0
  have hθ : 0 ≤ θ := Real.log_nonneg
    ((le_div_iff₀ (by positivity : 0 < 2 * p)).mpr (by linarith))
  have h_exp : Real.exp θ = 1 / (2 * p) := Real.exp_log (by positivity)
  have hcancel : p * (1 / (2 * p) - 1) = 1 / 2 - p := by field_simp
  have htail := measure_ge_le_exp_mul_mgf (μ := bernoulliFlagLaw (fun _ : ι => q))
    (X := fun x => ∑ i ∈ S ∩ freshFlagSet x, v i) (V / 2) hθ Integrable.of_finite
  calc
    _ ≤ Real.exp (-θ * (V / 2)) *
        Real.exp (p * V * (Real.exp θ - 1)) := by
      apply htail.trans
      exact mul_le_mul_of_nonneg_left
        (integral_exp_unit_flag_weights_le q S v hv0 hv1 p hqp θ hθ) (Real.exp_pos _).le
    _ = Real.exp (-θ * (V / 2) + p * V * (Real.exp θ - 1)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [h_exp]
      have heq : p * V * (1 / (2 * p) - 1) = (1 / 2 - p) * V := by
        rw [mul_right_comm, hcancel]
      rw [heq]
      change -θ * (V / 2) + (1 / 2 - p) * V ≤ -(V / 2) * θ + V / 2
      nlinarith

/-- The actual weighted outside tail in E.10, for weights at most `32 M`. -/
theorem bernoulliFlagLaw_weighted_tail_real (q : unitInterval) (outside : Finset ι)
    (a : ι → ℝ) (ha0 : ∀ i ∈ outside, 0 ≤ a i) (M : ℝ) (hM : 0 < M)
    (haM : ∀ i ∈ outside, a i ≤ 32 * M)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) (hqp : (q : ℝ) ≤ p) :
    (bernoulliFlagLaw (fun _ : ι => q)).real
      {x | (∑ i ∈ outside, a i) / 2 ≤ ∑ i ∈ outside ∩ freshFlagSet x, a i} ≤
      Real.exp (-((∑ i ∈ outside, a i) / (64 * M)) * Real.log (1 / (2 * p)) +
        (∑ i ∈ outside, a i) / (64 * M)) := by
  let v i := a i / (32 * M)
  have hv0 (i : ι) (hi : i ∈ outside) : 0 ≤ v i := div_nonneg (ha0 i hi) (by positivity)
  have hv1 (i : ι) (hi : i ∈ outside) : v i ≤ 1 :=
    (div_le_one (by positivity : 0 < 32 * M)).mpr (haM i hi)
  have h := bernoulliFlagLaw_unit_weight_tail_real q outside v hv0 hv1 p hp0 hp1 hqp
  have hevent : {x : ι → Bool | (∑ i ∈ outside, v i) / 2 ≤
      ∑ i ∈ outside ∩ freshFlagSet x, v i} =
      {x | (∑ i ∈ outside, a i) / 2 ≤ ∑ i ∈ outside ∩ freshFlagSet x, a i} := by
    ext x
    simp only [v, ← Finset.sum_div, Set.mem_ofPred_eq]
    rw [div_right_comm]
    exact div_le_div_iff_of_pos_right (by positivity : 0 < 32 * M)
  rw [hevent] at h
  convert h using 1
  congr 1
  simp only [v, ← Finset.sum_div]
  field_simp
  ring

/-- ENNReal form of the weighted outside tail, including an empty outside block. -/
theorem bernoulliFlagLaw_weighted_tail_le (q : unitInterval) (outside : Finset ι)
    (a : ι → ℝ) (ha0 : ∀ i ∈ outside, 0 ≤ a i) (M : ℝ) (hM : 0 < M)
    (haM : ∀ i ∈ outside, a i ≤ 32 * M)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) (hqp : (q : ℝ) ≤ p) :
    bernoulliFlagLaw (fun _ : ι => q)
      {x | (∑ i ∈ outside, a i) / 2 ≤ ∑ i ∈ outside ∩ freshFlagSet x, a i} ≤
      ENNReal.ofReal (Real.exp (-((∑ i ∈ outside, a i) / (64 * M)) *
        Real.log (1 / (2 * p)) + (∑ i ∈ outside, a i) / (64 * M))) := by
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using
    ENNReal.ofReal_le_ofReal
      (bernoulliFlagLaw_weighted_tail_real q outside a ha0 M hM haM p hp0 hp1 hqp)

/-- The core probability can be bounded using any upper bound on the actual flag parameter. -/
theorem bernoulliFlagLaw_core_le_of_parameter_le (q : unitInterval) (p : ℝ)
    (hqp : (q : ℝ) ≤ p) (core : Finset ι) (hcore : core.Nonempty) :
    bernoulliFlagLaw (fun _ : ι => q)
      {x | max 1 (core.card - 1) ≤ (core ∩ freshFlagSet x).card} ≤
      ENNReal.ofReal ((core.card : ℝ) * p ^ max 1 (core.card - 1)) := by
  apply (bernoulliFlagLaw_core_le q core hcore).trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ q.property.1 hqp _)
    (Nat.cast_nonneg _)

namespace PredictableBernoulliProcess
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ mΩ} (P : PredictableBernoulliProcess (ι := ι) μ ℱ)
    [IsProbabilityMeasure μ]

/-- The E.11 probabilistic bridge on the actual adaptive sample space: fixed core and outside
requirements have probability at most the core factor times the E.10 exponential tail. The only
independence used is the already proved independence in the common-clock comparison law. -/
theorem probability_everFlags_core_weighted_le (B : ℝ≥0)
    (hflags0 : ∀ ω, P.flags 0 ω = ∅) (hbudget0 : ∀ ω, P.remaining 0 ω = B)
    (core outside : Finset ι) (hcore : core.Nonempty) (hdisjoint : Disjoint core outside)
    (a : ι → ℝ) (ha0 : ∀ i ∈ outside, 0 ≤ a i) (M : ℝ) (hM : 0 < M)
    (haM : ∀ i ∈ outside, a i ≤ 32 * M)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1 / 2) (hBp : (B : ℝ) ≤ p) :
    μ {ω | max 1 (core.card - 1) ≤ (core ∩ P.everFlags ω).card ∧
      (∑ i ∈ outside, a i) / 2 ≤ ∑ i ∈ outside ∩ P.everFlags ω, a i} ≤
      ENNReal.ofReal ((core.card : ℝ) * p ^ max 1 (core.card - 1) *
        Real.exp (-((∑ i ∈ outside, a i) / (64 * M)) * Real.log (1 / (2 * p)) +
          (∑ i ∈ outside, a i) / (64 * M))) := by
  have hqp : (hazardProbability B : ℝ) ≤ p := (hazardProbability_le_budget B).trans hBp
  have h := P.probability_everFlags_joint_threshold_le_product B hflags0 hbudget0
    core outside hdisjoint (max 1 (core.card - 1)) a ha0 ((∑ i ∈ outside, a i) / 2)
  apply h.trans
  rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0.le _))]
  exact mul_le_mul'
    (bernoulliFlagLaw_core_le_of_parameter_le (hazardProbability B) p hqp core hcore)
    (bernoulliFlagLaw_weighted_tail_le (hazardProbability B) outside a ha0 M hM haM
      p hp0 hp1 hqp)

/-- The core-only consequence E.7, including singleton cores, for all ever-flags. -/
theorem probability_everFlags_core_le (B : ℝ≥0)
    (hflags0 : ∀ ω, P.flags 0 ω = ∅) (hbudget0 : ∀ ω, P.remaining 0 ω = B)
    (core : Finset ι) (hcore : core.Nonempty) (p : ℝ) (hBp : (B : ℝ) ≤ p) :
    μ {ω | max 1 (core.card - 1) ≤ (core ∩ P.everFlags ω).card} ≤
      ENNReal.ofReal ((core.card : ℝ) * p ^ max 1 (core.card - 1)) := by
  have h := P.probability_everFlags_increasing_event_le B hflags0 hbudget0
    {F | max 1 (core.card - 1) ≤ (core ∩ F).card}
    (fun F G hFG hF => hF.trans (Finset.card_le_card
      (Finset.inter_subset_inter Finset.Subset.rfl hFG)))
  exact h.trans (bernoulliFlagLaw_core_le_of_parameter_le (hazardProbability B) p
    ((hazardProbability_le_budget B).trans hBp) core hcore)

end PredictableBernoulliProcess
end GapEntropy
