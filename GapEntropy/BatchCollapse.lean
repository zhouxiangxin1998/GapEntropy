import GapEntropy.BernoulliFlagTails
import GapEntropy.Instance
import GapEntropy.Elimination
import GapEntropy.GaussianNoise

/-! Single-call batch-collapse bounds for actual independent Gaussian sample blocks. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators
namespace GapEntropy

namespace ProductFlagEvents
variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace β]
    (μ : ι → Measure β) [∀ i, IsProbabilityMeasure (μ i)]

/-- Flags on an actual product sample, with possibly different coordinate events. -/
def flags (E : ι → Set β) (x : ι → β) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => x i ∈ E i

omit [DecidableEq ι] [MeasurableSpace β] in
@[simp] theorem mem_flags (E : ι → Set β) (x : ι → β) (i : ι) :
    i ∈ flags E x ↔ x i ∈ E i := by
  classical
  simp [flags]

/-- Exact probability of all designated independent coordinate events. -/
theorem subset_real (E : ι → Set β) (S : Finset ι) :
    (Measure.pi μ).real {x | S ⊆ flags E x} = ∏ i ∈ S, (μ i).real (E i) := by
  classical
  have heq : {x : ι → β | S ⊆ flags E x} =
      Set.univ.pi (fun i => if i ∈ S then E i else Set.univ) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.subset_iff, mem_flags, Set.mem_pi,
      Set.mem_univ, forall_const]
    constructor
    · intro h i
      split_ifs with hi
      · exact h hi
      · trivial
    · intro h i hi
      simpa [hi] using h i
  rw [measureReal_def, heq, Measure.pi_pi, ENNReal.toReal_prod]
  have ht (i : ι) : ((μ i) (if i ∈ S then E i else Set.univ)).toReal =
      if i ∈ S then (μ i).real (E i) else 1 := by split_ifs <;> simp [measureReal_def]
  simp_rw [ht]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem subset_real_le (E : ι → Set β) (S : Finset ι) (a : ℝ)
    (hE : ∀ i ∈ S, (μ i).real (E i) ≤ a) :
    (Measure.pi μ).real {x | S ⊆ flags E x} ≤ a ^ S.card := by
  rw [subset_real, ← Finset.prod_const]
  exact Finset.prod_le_prod (fun i _ => measureReal_nonneg) hE

/-- Independent coordinate events with probability at most a give the exact core union bound. -/
theorem core_real_le (E : ι → Set β) (S : Finset ι) (hS : S.Nonempty) (a : ℝ)
    (hE : ∀ i ∈ S, (μ i).real (E i) ≤ a) :
    (Measure.pi μ).real {x | max 1 (S.card - 1) ≤ (S ∩ flags E x).card} ≤
      (S.card : ℝ) * a ^ max 1 (S.card - 1) := by
  classical
  by_cases hs1 : S.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs1
    have hevent : {x : ι → β | max 1 (({i} : Finset ι).card - 1) ≤
        ({i} ∩ flags E x).card} = {x | ({i} : Finset ι) ⊆ flags E x} := by
      ext x
      by_cases hi : x i ∈ E i <;> simp [Finset.singleton_inter, hi]
    rw [hevent]
    simpa using subset_real_le μ E {i} a hE
  · have hs2 : 2 ≤ S.card := by have := hS.card_pos; omega
    have hm : max 1 (S.card - 1) = S.card - 1 := max_eq_right (by omega)
    rw [hm]
    calc
      _ ≤ (Measure.pi μ).real (⋃ i ∈ S, {x | S.erase i ⊆ flags E x}) := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro x hx
        obtain ⟨i, hi, hsub⟩ := exists_erase_subset_of_card_inter S _ hS hx
        exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hsub⟩⟩
      _ ≤ ∑ i ∈ S, (Measure.pi μ).real {x | S.erase i ⊆ flags E x} :=
        measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ S, a ^ (S.card - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        simpa [Finset.card_erase_of_mem hi] using
          subset_real_le μ E (S.erase i) a (fun j hj => hE j (Finset.mem_erase.mp hj).2)
      _ = _ := by simp

omit [DecidableEq ι] in
theorem measurable_flags (E : ι → Set β) (hE : ∀ i, MeasurableSet (E i)) :
    Measurable (flags E) := by
  apply measurable_finset_iff.mpr
  intro i
  simp only [mem_flags]
  exact ((hE i).preimage (measurable_pi_apply i)).mem

omit [MeasurableSpace β] in
/-- The real-valued flag count is a sum of coordinate indicators. -/
theorem card_inter_flags_real (E : ι → Set β) (S : Finset ι) (x : ι → β) :
    ((S ∩ flags E x).card : ℝ) = ∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) (x i) := by
  classical
  have heq : S ∩ flags E x = S.filter (fun i => x i ∈ E i) := by ext i; simp
  rw [heq, Finset.card_filter]
  simp [Set.indicator]

/-- Exact count MGF on the actual product space, with coordinate-dependent events. -/
theorem integral_exp_count (E : ι → Set β) (hE : ∀ i, MeasurableSet (E i))
    (S : Finset ι) (θ : ℝ) :
    (∫ x, Real.exp (θ * ((S ∩ flags E x).card : ℝ)) ∂Measure.pi μ) =
      ∏ i ∈ S, (1 + (μ i).real (E i) * (Real.exp θ - 1)) := by
  classical
  simp_rw [card_inter_flags_real, Set.indicator, Finset.mul_sum]
  have hs (x : ι → β) : (∑ i ∈ S, θ * (if x i ∈ E i then (1 : ℝ) else 0)) =
      ∑ i, if i ∈ S then θ * (if x i ∈ E i then (1 : ℝ) else 0) else 0 := by simp
  simp_rw [hs, Real.exp_sum]
  rw [integral_fintype_prod_eq_prod
    (fun i y => Real.exp (if i ∈ S then θ * (if y ∈ E i then (1 : ℝ) else 0) else 0))]
  have ht (i : ι) :
      (∫ y, Real.exp (if i ∈ S then θ * (if y ∈ E i then (1 : ℝ) else 0) else 0) ∂μ i) =
      if i ∈ S then 1 + (μ i).real (E i) * (Real.exp θ - 1) else 1 := by
    by_cases hi : i ∈ S
    · simp only [hi, if_true]
      have hf : (fun y : β => Real.exp (θ * (if y ∈ E i then (1 : ℝ) else 0))) =
          fun y => (Real.exp θ - 1) * (E i).indicator (fun _ => (1 : ℝ)) y + 1 := by
        funext y
        by_cases hy : y ∈ E i <;> simp [hy]
      rw [hf, integral_add (((integrable_const (1 : ℝ)).indicator (hE i)).const_mul _)
        (integrable_const 1), integral_const_mul, integral_indicator_const (μ := μ i) (1 : ℝ) (hE i)]
      simp
      ring
    · simp [hi]
  simp_rw [ht]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- Exponential count MGF bound derived from independent coordinate events. -/
theorem integral_exp_count_le (E : ι → Set β) (hE : ∀ i, MeasurableSet (E i))
    (S : Finset ι) (a : ℝ) (ha : ∀ i ∈ S, (μ i).real (E i) ≤ a)
    (θ : ℝ) (hθ : 0 ≤ θ) :
    (∫ x, Real.exp (θ * ((S ∩ flags E x).card : ℝ)) ∂Measure.pi μ) ≤
      Real.exp (a * S.card * (Real.exp θ - 1)) := by
  rw [integral_exp_count μ E hE]
  have he : 0 ≤ Real.exp θ - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hθ)
  calc
    _ ≤ ∏ _i ∈ S, Real.exp (a * (Real.exp θ - 1)) := by
      apply Finset.prod_le_prod
      · intro i _
        nlinarith [mul_nonneg (measureReal_nonneg (μ := μ i) (s := E i)) he]
      · intro i hi
        apply (add_le_add_right (mul_le_mul_of_nonneg_right (ha i hi) he) 1).trans
        simpa only [add_comm] using Real.add_one_le_exp (a * (Real.exp θ - 1))
    _ = Real.exp (a * S.card * (Real.exp θ - 1)) := by
      rw [Finset.prod_const, ← Real.exp_nat_mul]
      congr 1
      ring

/-- A true exponential-Markov bound on the count of independent coordinate events. -/
theorem count_tail_real_le (E : ι → Set β) (hE : ∀ i, MeasurableSet (E i))
    (S : Finset ι) (a : ℝ) (ha : ∀ i ∈ S, (μ i).real (E i) ≤ a)
    (θ : ℝ) (hθ : 0 ≤ θ) (u : ℝ) :
    (Measure.pi μ).real {x | u ≤ ((S ∩ flags E x).card : ℝ)} ≤
      Real.exp (-θ * u + a * S.card * (Real.exp θ - 1)) := by
  let φ (F : Finset ι) := Real.exp (θ * ((S ∩ F).card : ℝ))
  have hint : Integrable (fun x => Real.exp (θ * ((S ∩ flags E x).card : ℝ))) (Measure.pi μ) := by
    apply (integrable_const (finitePayoffBound φ)).mono'
      (((measurable_of_countable φ).comp (measurable_flags E hE)).aestronglyMeasurable)
    exact ae_of_all _ fun x => norm_le_finitePayoffBound φ _
  have h := measure_ge_le_exp_mul_mgf u hθ hint
  rw [Real.exp_add]
  exact h.trans (mul_le_mul_of_nonneg_left
    (integral_exp_count_le μ E hE S a ha θ hθ) (Real.exp_pos _).le)

end ProductFlagEvents

namespace BatchCollapse
variable {n : ℕ}

/-- A collapse reduces two or more active core arms to at most one, or removes the sole core arm. -/
def collapse (S B : Finset (Fin n)) (x : Fin n → ℝ) (z d : ℝ) : Prop :=
  ((S ∩ B).card = 1 ∧ (Elimination.padded S x z d ∩ B).card = 0) ∨
    (2 ≤ (S ∩ B).card ∧ (Elimination.padded S x z d ∩ B).card ≤ 1)

/-- The core severe flags of this actual call. -/
def severeCore (S B : Finset (Fin n)) (x μ : Fin n → ℝ) (d : ℝ) : Finset (Fin n) :=
  (S ∩ B).filter fun i => x i - μ i < -5 * d / 16

/-- Actual padded collapse on an upper-valid reference requires the core severe-flag count. -/
theorem collapse_severe_count (S B : Finset (Fin n)) (x μ : Fin n → ℝ) (z d μstar : ℝ)
    (hz : z ≤ μstar + d / 16) (hgap : ∀ i ∈ S ∩ B, μstar - μ i ≤ d / 8)
    (hcollapse : collapse S B x z d) :
    max 1 ((S ∩ B).card - 1) ≤ (severeCore S B x μ d).card := by
  have hcover : S ∩ B ⊆ severeCore S B x μ d ∪ (Elimination.padded S x z d ∩ B) := by
    intro i hi
    by_cases hret : i ∈ Elimination.padded S x z d
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hret, (Finset.mem_inter.mp hi).2⟩)
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨hi, Elimination.padded_removed_near_severe
        (Finset.mem_inter.mp hi).1 hz (hgap i hi) hret⟩
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rcases hcollapse with ⟨hq, hr⟩ | ⟨hq, hr⟩ <;> omega

/-- Actual independent blocks of `m` standard Gaussian observations, one block per original arm. -/
def callLaw (n m : ℕ) : Measure (Fin n → Fin m → ℝ) :=
  Measure.pi fun _ : Fin n => GaussianNoise.law m

instance callLaw_isProbabilityMeasure (n m : ℕ) : IsProbabilityMeasure (callLaw n m) := by
  unfold callLaw
  infer_instance

/-- The observed empirical means, shifted by the original arm means. -/
def empirical (μ : Fin n → ℝ) {m : ℕ} (ω : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  μ i + GaussianNoise.mean (ω i)

/-- One-sided Gaussian bound for the actual centered observation block. -/
theorem noise_lower_tail {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) :
    (GaussianNoise.law m).real {x | GaussianNoise.mean x < -t} ≤
      Real.exp (-((m : ℝ) * t ^ 2) / 2) := by
  have hlaw (j : Fin m) : HasLaw (fun x : Fin m → ℝ => x j) (gaussianReal 0 1)
      (GaussianNoise.law m) := by
    have h := measurePreserving_eval_infinitePi (fun _ : Fin m => gaussianReal 0 1) j
    exact ⟨h.measurable.aemeasurable, h.map_eq⟩
  have hind : iIndepFun (fun j (x : Fin m → ℝ) => x j) (GaussianNoise.law m) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have h := Gaussian.sampleMean_lower_tail hm hind hlaw ht
  apply (measureReal_mono (h₂ := measure_ne_top _ _) (show
    {x : Fin m → ℝ | GaussianNoise.mean x < -t} ⊆
      {x | GaussianNoise.mean x ≤ -t} from by
        intro x hx
        exact (show GaussianNoise.mean x < -t from hx).le)).trans
  simpa [Gaussian.sampleMean, GaussianNoise.mean] using h

/-- The exact severe-tail arithmetic in D.13, retaining the exponent 25. -/
theorem severe_tail_of_budget {m : ℕ} {d ρ : ℝ} (hd : 0 < d) (hρ : 0 < ρ)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ)) :
    Real.exp (-((m : ℝ) * (5 * d / 16) ^ 2) / 2) ≤ ρ ^ 25 := by
  have hmul := mul_le_mul_of_nonneg_right hbudget (sq_nonneg d)
  have hid : (512 * (d ^ 2)⁻¹ * Real.log (1 / ρ)) * d ^ 2 =
      512 * Real.log (1 / ρ) := by field_simp [hd.ne']
  rw [hid] at hmul
  have he : -((m : ℝ) * (5 * d / 16) ^ 2) / 2 ≤ -25 * Real.log (1 / ρ) := by nlinarith
  apply (Real.exp_le_exp.mpr he).trans_eq
  rw [show -25 * Real.log (1 / ρ) = (25 : ℕ) * (-Real.log (1 / ρ)) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by positivity)]
  simp

/-- The source's q*a^(q-1)≤2a bound for q≥2, proved by induction. -/
theorem card_mul_pow_pred_le_two (q : ℕ) (hq : 2 ≤ q) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) : (q : ℝ) * a ^ (q - 1) ≤ 2 * a := by
  induction q, hq using Nat.le_induction with
  | base => norm_num
  | succ q hq ih =>
    have hcoeff : ((q : ℝ) + 1) * a ≤ q := by
      have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
      nlinarith
    have hp : a ^ q = a ^ (q - 1) * a := by
      rw [← pow_succ]
      congr 1
      omega
    calc
      ((q + 1 : ℕ) : ℝ) * a ^ (q + 1 - 1) =
          (((q : ℝ) + 1) * a) * a ^ (q - 1) := by
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, hp]
        ring
      _ ≤ (q : ℝ) * a ^ (q - 1) := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg ha0 _)
      _ ≤ _ := ih

/-- A nonempty core's union bound is uniformly at most twice its marginal flag bound. -/
theorem card_mul_pow_max_le_two (q : ℕ) (hq : 1 ≤ q) {a : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1 / 2) :
    (q : ℝ) * a ^ max 1 (q - 1) ≤ 2 * a := by
  by_cases hq1 : q = 1
  · subst q
    simp only [Nat.sub_self, max_eq_left (by omega : 0 ≤ 1), pow_one, Nat.cast_one, one_mul]
    linarith
  · have hq2 : 2 ≤ q := by omega
    rw [max_eq_right (by omega : 1 ≤ q - 1)]
    exact card_mul_pow_pred_le_two q hq2 ha0 ha1

/-- E.13 for the actual independent Gaussian blocks, with the exact core union factor. -/
theorem collapse_probability_le_core_factor (μ : Fin n → ℝ) (S B : Finset (Fin n))
    (hcore : (S ∩ B).Nonempty) {m : ℕ} (hm : 0 < m) {z d μstar ρ : ℝ}
    (hd : 0 < d) (hρ : 0 < ρ) (hz : z ≤ μstar + d / 16)
    (hgap : ∀ i ∈ S ∩ B, μstar - μ i ≤ d / 8)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ)) :
    (callLaw n m).real {ω | collapse S B (empirical μ ω) z d} ≤
      ((S ∩ B).card : ℝ) * (ρ ^ 25) ^ max 1 ((S ∩ B).card - 1) := by
  let E (_ : Fin n) : Set (Fin m → ℝ) := {x | GaussianNoise.mean x < -(5 * d / 16)}
  have hE (i : Fin n) (_ : i ∈ S ∩ B) : (GaussianNoise.law m).real (E i) ≤ ρ ^ 25 :=
    (noise_lower_tail hm (by positivity)).trans (severe_tail_of_budget hd hρ hbudget)
  have htail := ProductFlagEvents.core_real_le (fun _ : Fin n => GaussianNoise.law m)
    E (S ∩ B) hcore (ρ ^ 25) hE
  apply (measureReal_mono (h₂ := measure_ne_top _ _) ?_).trans htail
  intro ω hω
  have hcount := collapse_severe_count S B (empirical μ ω) μ z d μstar hz hgap hω
  have heq : severeCore S B (empirical μ ω) μ d =
      (S ∩ B) ∩ ProductFlagEvents.flags E ω := by
    ext i
    simp [severeCore, ProductFlagEvents.flags, E, empirical, neg_div, and_assoc]
  rwa [heq] at hcount

/-- The final uniform severe-collapse estimate in E.13. -/
theorem collapse_probability_le_two_severe (μ : Fin n → ℝ) (S B : Finset (Fin n))
    (hcore : (S ∩ B).Nonempty) {m : ℕ} (hm : 0 < m) {z d μstar ρ : ℝ}
    (hd : 0 < d) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) (hz : z ≤ μstar + d / 16)
    (hgap : ∀ i ∈ S ∩ B, μstar - μ i ≤ d / 8)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ)) :
    (callLaw n m).real {ω | collapse S B (empirical μ ω) z d} ≤ 2 * ρ ^ 25 := by
  apply (collapse_probability_le_core_factor μ S B hcore hm hd hρ hz hgap hbudget).trans
  apply card_mul_pow_max_le_two _ hcore.card_pos (pow_nonneg hρ.le _)
  have hpow : ρ ^ 25 ≤ ρ := by
    simpa using pow_le_pow_of_le_one hρ.le (show ρ ≤ 1 by linarith) (show 1 ≤ 25 by omega)
  exact hpow.trans hρhalf

/-- Core estimates below the fixed empirical-rank comparison threshold. -/
def lowCore (S B : Finset (Fin n)) (x : Fin n → ℝ) (cut : ℝ) : Finset (Fin n) :=
  (S ∩ B).filter fun i => x i < cut

/-- Active outside arms whose true gaps are less than the rank separation. -/
def nearOutside (S B : Finset (Fin n)) (μ : Fin n → ℝ) (μstar g : ℝ) : Finset (Fin n) :=
  (S \ B).filter fun i => μstar - μ i < g

/-- Far outside arms that exceed the empirical-rank comparison threshold. -/
def farHigh (S B : Finset (Fin n)) (x μ : Fin n → ℝ) (μstar g cut : ℝ) : Finset (Fin n) :=
  (S \ B).filter fun i => g ≤ μstar - μ i ∧ cut ≤ x i

/-- The deterministic rank alternative behind E.14–E.16. An actual padded collapse either has
many low core estimates, or at least a quarter of the active size consists of high far estimates. -/
theorem collapse_rank_alternative (S B : Finset (Fin n)) (x μ : Fin n → ℝ)
    (z d μstar g cut : ℝ) (hs : 8 ≤ S.card)
    (hnear : 8 * (nearOutside S B μ μstar g).card ≤ S.card)
    (hcollapse : collapse S B x z d) :
    max 1 ((S ∩ B).card - 1) ≤ (lowCore S B x cut).card ∨
      S.card ≤ 4 * (farHigh S B x μ μstar g cut).card := by
  classical
  by_cases hex : ∃ j ∈ S ∩ B, cut ≤ x j ∧ j ∉ Elimination.padded S x z d
  · right
    obtain ⟨j, hj, hjhigh, hjnot⟩ := hex
    have hjupper : j ∉ Elimination.upperHalf S x :=
      fun h => hjnot (Elimination.upperHalf_subset_padded S x z d h)
    have hcover : Elimination.upperHalf S x ⊆
        (Elimination.padded S x z d ∩ B) ∪ nearOutside S B μ μstar g ∪
          farHigh S B x μ μstar g cut := by
      intro i hi
      have hiS := Elimination.upperHalf_subset S x hi
      by_cases hiB : i ∈ B
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_inter.mpr ⟨Elimination.upperHalf_subset_padded S x z d hi, hiB⟩))
      · by_cases hgap : μstar - μ i < g
        · exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hiS, hiB⟩, hgap⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨hiS, hiB⟩, le_of_not_gt hgap,
              hjhigh.trans (Elimination.upperHalf_rank hi (Finset.mem_inter.mp hj).1 hjupper)⟩)
    have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    have hc' := Finset.card_union_le (Elimination.padded S x z d ∩ B)
      (nearOutside S B μ μstar g)
    rw [Elimination.upperHalf_card] at hc
    rcases hcollapse with ⟨hq, hr⟩ | ⟨hq, hr⟩ <;> omega
  · left
    have hcover : S ∩ B ⊆ lowCore S B x cut ∪ (Elimination.padded S x z d ∩ B) := by
      intro i hi
      by_cases hlow : x i < cut
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hi, hlow⟩)
      · have hret : i ∈ Elimination.padded S x z d := by
          by_contra hnot
          exact hex ⟨i, hi, le_of_not_gt hlow, hnot⟩
        exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hret, (Finset.mem_inter.mp hi).2⟩)
    have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
    rcases hcollapse with ⟨hq, hr⟩ | ⟨hq, hr⟩ <;> omega

/-- The fixed original outside hardness used in the rank argument. -/
def outsideHardness (I : Instance n) (B : Finset (Fin n)) : ℝ :=
  ∑ i ∈ Finset.univ \ B, I.weight i

/-- There are few outside arms with gap below `g`, because each contributes inverse-square
weight to the fixed original outside hardness. -/
theorem nearOutside_card_bound (I : Instance n) (S B : Finset (Fin n))
    (hbest : I.best ∈ B) {g : ℝ} (hg : 0 < g)
    (hscale : g ^ 2 * outsideHardness I B = (S.card : ℝ) / 8) :
    8 * (nearOutside S B I.mean (I.mean I.best) g).card ≤ S.card := by
  let N := nearOutside S B I.mean (I.mean I.best) g
  have hsub : N ⊆ Finset.univ \ B := by
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp
      (Finset.mem_filter.mp hi).1).2⟩
  have hterm (i : Fin n) (hi : i ∈ N) : 1 ≤ g ^ 2 * I.weight i := by
    have hnot : i ∉ B := (Finset.mem_sdiff.mp (hsub hi)).2
    have hiBest : i ≠ I.best := fun h => hnot (h ▸ hbest)
    have hgap0 := I.gap_pos hiBest
    have hgapg : I.gap i < g := (Finset.mem_filter.mp hi).2
    have hinv : I.gap i ^ 2 * I.weight i = 1 := by
      unfold Instance.weight
      exact mul_inv_cancel₀ (sq_pos_of_pos hgap0).ne'
    have hsq : I.gap i ^ 2 ≤ g ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right hsq (I.weight_nonneg i)
    rwa [hinv] at h
  have hcard : (N.card : ℝ) ≤ g ^ 2 * outsideHardness I B := by
    calc
      (N.card : ℝ) = ∑ _i ∈ N, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ N, g ^ 2 * I.weight i := Finset.sum_le_sum hterm
      _ = g ^ 2 * ∑ i ∈ N, I.weight i := (Finset.mul_sum _ _ _).symm
      _ ≤ g ^ 2 * outsideHardness I B := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => I.weight_nonneg i)) (sq_nonneg g)
  rw [hscale] at hcard
  have hreal : (8 : ℝ) * N.card ≤ S.card := by linarith
  exact_mod_cast hreal

/-- Upper one-sided Gaussian bound for the actual centered observation block. -/
theorem noise_upper_tail {m : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 ≤ t) :
    (GaussianNoise.law m).real {x | t ≤ GaussianNoise.mean x} ≤
      Real.exp (-((m : ℝ) * t ^ 2) / 2) := by
  have hlaw (j : Fin m) : HasLaw (fun x : Fin m → ℝ => x j) (gaussianReal 0 1)
      (GaussianNoise.law m) := by
    have h := measurePreserving_eval_infinitePi (fun _ : Fin m => gaussianReal 0 1) j
    exact ⟨h.measurable.aemeasurable, h.map_eq⟩
  have hind : iIndepFun (fun j (x : Fin m → ℝ) => x j) (GaussianNoise.law m) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  simpa [Gaussian.sampleMean, GaussianNoise.mean] using
    Gaussian.sampleMean_upper_tail hm hind hlaw ht

/-- The sampling budget gives the common rank exponent before either one-sided tail is applied. -/
theorem rank_exponent_of_budget {m : ℕ} {d g x ρ : ℝ}
    (hd : 0 < d) (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ))
    (hgd : g ^ 2 = x * d ^ 2 / 8) :
    64 * x * Real.log (1 / ρ) ≤ (m : ℝ) * g ^ 2 := by
  have h := mul_le_mul_of_nonneg_right hbudget (sq_nonneg g)
  have heq : (512 * (d ^ 2)⁻¹ * Real.log (1 / ρ)) * g ^ 2 =
      64 * x * Real.log (1 / ρ) := by
    rw [hgd]
    field_simp [hd.ne']
    ring
  rwa [heq] at h

/-- Exact E.14 exponent in exponential form. -/
theorem rank_core_tail_exponent {m : ℕ} {d g x ρ : ℝ} (hd : 0 < d) (hρ : 0 < ρ)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ))
    (hgd : g ^ 2 = x * d ^ 2 / 8) :
    Real.exp (-((m : ℝ) * (g / 4) ^ 2) / 2) ≤ Real.exp (2 * x * Real.log ρ) := by
  have h := rank_exponent_of_budget hd hbudget hgd
  rw [Real.log_div (by norm_num) hρ.ne', Real.log_one, zero_sub] at h
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Exact E.15 exponent in exponential form. -/
theorem rank_far_tail_exponent {m : ℕ} {d g x ρ : ℝ} (hd : 0 < d) (hρ : 0 < ρ)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ))
    (hgd : g ^ 2 = x * d ^ 2 / 8) :
    Real.exp (-((m : ℝ) * (g / 2) ^ 2) / 2) ≤ Real.exp (8 * x * Real.log ρ) := by
  have h := rank_exponent_of_budget hd hbudget hgd
  rw [Real.log_div (by norm_num) hρ.ne', Real.log_one, zero_sub] at h
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A convenient negative-log bound used only in the rank tail arithmetic. -/
theorem log_le_neg_half {ρ : ℝ} (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) :
    Real.log ρ ≤ -1 / 2 := by
  have h := Real.log_le_sub_one_of_pos hρ
  linarith

theorem rank_core_probability_le_half {x ρ : ℝ} (hx : 2 ≤ x)
    (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) : Real.exp (2 * x * Real.log ρ) ≤ 1 / 2 := by
  have hlog := log_le_neg_half hρ hρhalf
  have he : 2 * x * Real.log ρ ≤ Real.log ρ := by nlinarith
  calc
    _ ≤ Real.exp (Real.log ρ) := Real.exp_le_exp.mpr he
    _ = ρ := Real.exp_log hρ
    _ ≤ _ := hρhalf

/-- The far-event count Chernoff exponent is at most the source's `2x log ρ`. -/
theorem rank_far_markov_arithmetic {s k x ρ : ℝ} (hs : 8 ≤ s) (hk0 : 0 ≤ k) (hk : k ≤ s)
    (hx : 2 ≤ x) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) :
    0 ≤ -Real.log 4 - 8 * x * Real.log ρ ∧
    -(-Real.log 4 - 8 * x * Real.log ρ) * (s / 4) +
      Real.exp (8 * x * Real.log ρ) * k *
        (Real.exp (-Real.log 4 - 8 * x * Real.log ρ) - 1) ≤ 2 * x * Real.log ρ := by
  have hlog := log_le_neg_half hρ hρhalf
  have hlog4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
    linarith
  have hθ : 0 ≤ -Real.log 4 - 8 * x * Real.log ρ := by nlinarith
  refine ⟨hθ, ?_⟩
  have hcancel : Real.exp (8 * x * Real.log ρ) *
      Real.exp (-Real.log 4 - 8 * x * Real.log ρ) = 1 / 4 := by
    rw [← Real.exp_add, show 8 * x * Real.log ρ + (-Real.log 4 - 8 * x * Real.log ρ) =
      -Real.log 4 by ring, Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have ha : 0 ≤ Real.exp (8 * x * Real.log ρ) := (Real.exp_pos _).le
  have hmgf : Real.exp (8 * x * Real.log ρ) * k *
      (Real.exp (-Real.log 4 - 8 * x * Real.log ρ) - 1) ≤ s / 4 := by
    have heq : Real.exp (8 * x * Real.log ρ) * k *
        (Real.exp (-Real.log 4 - 8 * x * Real.log ρ) - 1) =
        (1 / 4 - Real.exp (8 * x * Real.log ρ)) * k := by
      calc
        _ = (Real.exp (8 * x * Real.log ρ) *
          Real.exp (-Real.log 4 - 8 * x * Real.log ρ) - Real.exp (8 * x * Real.log ρ)) * k := by ring
        _ = _ := by rw [hcancel]
    rw [heq]
    nlinarith
  have hbase : Real.log 4 + 1 + 8 * x * Real.log ρ ≤ 4 * x * Real.log ρ := by nlinarith
  have hscale := mul_le_mul_of_nonneg_left hbase (show 0 ≤ s / 4 by linarith)
  have hxlog : x * Real.log ρ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have hlast := mul_le_mul_of_nonpos_right (show 2 ≤ s by linarith) hxlog
  nlinarith

/-- The low-core branch of the empirical-rank calculation, from actual Gaussian observations. -/
theorem lowCore_probability_le (μ : Fin n → ℝ) (S B : Finset (Fin n))
    (hcore : (S ∩ B).Nonempty) {m : ℕ} (hm : 0 < m) {d g x μstar ρ : ℝ}
    (hd : 0 < d) (hg : 0 < g) (hx : 2 ≤ x) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (hgap : ∀ i ∈ S ∩ B, μstar - μ i ≤ g / 4)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ))
    (hgd : g ^ 2 = x * d ^ 2 / 8) :
    (callLaw n m).real {ω | max 1 ((S ∩ B).card - 1) ≤
      (lowCore S B (empirical μ ω) (μstar - g / 2)).card} ≤
      2 * Real.exp (2 * x * Real.log ρ) := by
  let E (i : Fin n) : Set (Fin m → ℝ) := {v | μ i + GaussianNoise.mean v < μstar - g / 2}
  have hE (i : Fin n) (hi : i ∈ S ∩ B) :
      (GaussianNoise.law m).real (E i) ≤ Real.exp (2 * x * Real.log ρ) := by
    have hsub : E i ⊆ {v | GaussianNoise.mean v < -(g / 4)} := by
      intro v hv
      have hgi := hgap i hi
      change μ i + GaussianNoise.mean v < μstar - g / 2 at hv
      change GaussianNoise.mean v < -(g / 4)
      linarith
    exact (measureReal_mono hsub).trans ((noise_lower_tail hm (by positivity)).trans
      (rank_core_tail_exponent hd hρ hbudget hgd))
  have htail := ProductFlagEvents.core_real_le (fun _ : Fin n => GaussianNoise.law m)
    E (S ∩ B) hcore (Real.exp (2 * x * Real.log ρ)) hE
  have heq (ω : Fin n → Fin m → ℝ) : lowCore S B (empirical μ ω) (μstar - g / 2) =
      (S ∩ B) ∩ ProductFlagEvents.flags E ω := by
    ext i
    constructor
    · intro hi
      obtain ⟨hiSB, hlo⟩ := Finset.mem_filter.mp hi
      exact Finset.mem_inter.mpr ⟨hiSB, (ProductFlagEvents.mem_flags E ω i).mpr hlo⟩
    · intro hi
      obtain ⟨hiSB, hlo⟩ := Finset.mem_inter.mp hi
      exact Finset.mem_filter.mpr ⟨hiSB, (ProductFlagEvents.mem_flags E ω i).mp hlo⟩
  simp_rw [heq]
  exact htail.trans (card_mul_pow_max_le_two _ hcore.card_pos (Real.exp_pos _).le
    (rank_core_probability_le_half hx hρ hρhalf))

/-- The far-high branch of the rank bound, using a true independent-event count MGF. -/
theorem farHigh_probability_le (μ : Fin n → ℝ) (S B : Finset (Fin n))
    (hs : 8 ≤ S.card) {m : ℕ} (hm : 0 < m) {d g x μstar ρ : ℝ}
    (hd : 0 < d) (hg : 0 < g) (hx : 2 ≤ x) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ))
    (hgd : g ^ 2 = x * d ^ 2 / 8) :
    (callLaw n m).real {ω | S.card ≤ 4 *
      (farHigh S B (empirical μ ω) μ μstar g (μstar - g / 2)).card} ≤
      Real.exp (2 * x * Real.log ρ) := by
  let F := (S \ B).filter fun i => g ≤ μstar - μ i
  let E (i : Fin n) : Set (Fin m → ℝ) := {v | μstar - g / 2 ≤ μ i + GaussianNoise.mean v}
  have hEm (i : Fin n) : MeasurableSet (E i) :=
    measurableSet_le measurable_const ((GaussianNoise.mean_measurable m).const_add (μ i))
  have hE (i : Fin n) (hi : i ∈ F) :
      (GaussianNoise.law m).real (E i) ≤ Real.exp (8 * x * Real.log ρ) := by
    have hsub : E i ⊆ {v | g / 2 ≤ GaussianNoise.mean v} := by
      intro v hv
      have hgi := (Finset.mem_filter.mp hi).2
      change μstar - g / 2 ≤ μ i + GaussianNoise.mean v at hv
      change g / 2 ≤ GaussianNoise.mean v
      linarith
    exact (measureReal_mono hsub).trans ((noise_upper_tail hm (by positivity)).trans
      (rank_far_tail_exponent hd hρ hbudget hgd))
  have hFsub : F ⊆ S := (Finset.filter_subset _ _).trans Finset.sdiff_subset
  have hFc : (F.card : ℝ) ≤ S.card := by exact_mod_cast Finset.card_le_card hFsub
  have hsr : (8 : ℝ) ≤ S.card := by exact_mod_cast hs
  have harith := rank_far_markov_arithmetic hsr (Nat.cast_nonneg F.card) hFc hx hρ hρhalf
  have htail := ProductFlagEvents.count_tail_real_le (fun _ : Fin n => GaussianNoise.law m)
    E hEm F (Real.exp (8 * x * Real.log ρ)) hE
    (-Real.log 4 - 8 * x * Real.log ρ) harith.1 ((S.card : ℝ) / 4)
  have heq (ω : Fin n → Fin m → ℝ) :
      farHigh S B (empirical μ ω) μ μstar g (μstar - g / 2) =
      F ∩ ProductFlagEvents.flags E ω := by
    ext i
    simp [farHigh, empirical, ProductFlagEvents.flags, E, F, and_assoc]
  have hevent : {ω : Fin n → Fin m → ℝ | S.card ≤ 4 *
      (farHigh S B (empirical μ ω) μ μstar g (μstar - g / 2)).card} =
      {ω | (S.card : ℝ) / 4 ≤ ((F ∩ ProductFlagEvents.flags E ω).card : ℝ)} := by
    ext ω
    simp only [heq, Set.mem_ofPred_eq, div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    rw [mul_comm]
    exact_mod_cast Iff.rfl
  rw [hevent]
  exact htail.trans (Real.exp_le_exp.mpr harith.2)

/-- The rank bound in E.16 before combining it with severe flags. It holds for every fixed
reference value, since the empirical upper half is always retained. -/
theorem collapse_probability_rank_le (μ : Fin n → ℝ) (S B : Finset (Fin n))
    (hcore : (S ∩ B).Nonempty) (hs : 8 ≤ S.card) {m : ℕ} (hm : 0 < m)
    {z d g x μstar ρ : ℝ} (hd : 0 < d) (hg : 0 < g) (hx : 2 ≤ x)
    (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (hgap : ∀ i ∈ S ∩ B, μstar - μ i ≤ d / 8)
    (hnear : 8 * (nearOutside S B μ μstar g).card ≤ S.card)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ))
    (hgd : g ^ 2 = x * d ^ 2 / 8) :
    (callLaw n m).real {ω | collapse S B (empirical μ ω) z d} ≤
      3 * Real.exp (2 * x * Real.log ρ) := by
  have hgd_le : d / 2 ≤ g := by nlinarith [sq_nonneg d]
  have hgapg (i : Fin n) (hi : i ∈ S ∩ B) : μstar - μ i ≤ g / 4 := by
    have h := hgap i hi
    linarith
  let C : Set (Fin n → Fin m → ℝ) := {ω | max 1 ((S ∩ B).card - 1) ≤
    (lowCore S B (empirical μ ω) (μstar - g / 2)).card}
  let F : Set (Fin n → Fin m → ℝ) := {ω | S.card ≤ 4 *
    (farHigh S B (empirical μ ω) μ μstar g (μstar - g / 2)).card}
  have hsub : {ω | collapse S B (empirical μ ω) z d} ⊆ C ∪ F := by
    intro ω hω
    exact collapse_rank_alternative S B (empirical μ ω) μ z d μstar g (μstar - g / 2)
      hs hnear hω
  calc
    _ ≤ (callLaw n m).real (C ∪ F) := measureReal_mono hsub
    _ ≤ (callLaw n m).real C + (callLaw n m).real F := measureReal_union_le _ _
    _ ≤ 2 * Real.exp (2 * x * Real.log ρ) + Real.exp (2 * x * Real.log ρ) :=
      add_le_add (lowCore_probability_le μ S B hcore hm hd hg hx hρ hρhalf hgapg hbudget hgd)
        (farHigh_probability_le μ S B hs hm hd hg hx hρ hρhalf hbudget hgd)
    _ = _ := by ring

/-- Exact E.16 in exponential notation: combine severe errors and actual empirical ranks.
The reference is fixed and upper-valid; no future validity event is conditioned upon. -/
theorem collapse_probability_le_max_exponent (μ : Fin n → ℝ) (S B : Finset (Fin n))
    (hcore : (S ∩ B).Nonempty) (hs : 8 ≤ S.card) {m : ℕ} (hm : 0 < m)
    {z d g x μstar ρ : ℝ} (hd : 0 < d) (hg : 0 < g)
    (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2) (hz : z ≤ μstar + d / 16)
    (hgap : ∀ i ∈ S ∩ B, μstar - μ i ≤ d / 8)
    (hnear : 8 * (nearOutside S B μ μstar g).card ≤ S.card)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ))
    (hgd : g ^ 2 = x * d ^ 2 / 8) :
    (callLaw n m).real {ω | collapse S B (empirical μ ω) z d} ≤
      3 * Real.exp (max 25 (2 * x) * Real.log ρ) := by
  by_cases hx : 2 * x ≤ 25
  · rw [max_eq_left hx]
    have h := collapse_probability_le_two_severe μ S B hcore hm hd hρ hρhalf hz hgap hbudget
    have heq : Real.exp (25 * Real.log ρ) = ρ ^ 25 := by
      exact (Real.exp_nat_mul (Real.log ρ) 25).trans (by rw [Real.exp_log hρ])
    rw [heq]
    exact h.trans (by nlinarith [pow_nonneg hρ.le 25])
  · rw [max_eq_right (le_of_not_ge hx)]
    exact collapse_probability_rank_le μ S B hcore hs hm hd hg (by linarith)
      hρ hρhalf hgap hnear hbudget hgd

/-- The fixed rank separation chosen in the source, from active size and original outside hardness. -/
def rankSeparation (S : Finset (Fin n)) (h : ℝ) : ℝ := Real.sqrt ((S.card : ℝ) / (8 * h))

/-- The normalized work of the current call. -/
def workRatio (S : Finset (Fin n)) (d h : ℝ) : ℝ := (S.card : ℝ) * (d ^ 2)⁻¹ / h

/-- E.16 for the manuscript's actual outside hardness and rank separation, with no assumed
near-arm count or rank-tail bound. The only probability space is independent Gaussian samples. -/
theorem collapse_probability_le_source_exponent (I : Instance n) (S B : Finset (Fin n))
    (hbest : I.best ∈ B) (hcore : (S ∩ B).Nonempty) (hs : 8 ≤ S.card)
    (hh : 0 < outsideHardness I B) {m : ℕ} (hm : 0 < m) {z d ρ : ℝ}
    (hd : 0 < d) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (hz : z ≤ I.mean I.best + d / 16) (hgap : ∀ i ∈ B, I.gap i ≤ d / 8)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ)) :
    (callLaw n m).real {ω | collapse S B (empirical I.mean ω) z d} ≤
      3 * Real.exp (max 25 (2 * workRatio S d (outsideHardness I B)) * Real.log ρ) := by
  let h := outsideHardness I B
  let g := rankSeparation S h
  have hspos : (0 : ℝ) < S.card := by exact_mod_cast (show 0 < S.card by omega)
  have hg : 0 < g := Real.sqrt_pos.mpr (div_pos hspos (by positivity))
  have hg2 : g ^ 2 = (S.card : ℝ) / (8 * h) := Real.sq_sqrt (by positivity)
  have hscale : g ^ 2 * outsideHardness I B = (S.card : ℝ) / 8 := by
    rw [hg2]
    dsimp [h]
    field_simp
  have hgd : g ^ 2 = workRatio S d (outsideHardness I B) * d ^ 2 / 8 := by
    rw [hg2, workRatio]
    dsimp [h]
    field_simp [hd.ne']
  exact collapse_probability_le_max_exponent I.mean S B hcore hs hm hd hg hρ hρhalf hz
    (fun i hi => hgap i (Finset.mem_inter.mp hi).2)
    (nearOutside_card_bound I S B hbest hg hscale) hbudget hgd

/-- Zero outside hardness, with the original best in the core, means there are no outside arms. -/
theorem core_eq_univ_of_outsideHardness_zero (I : Instance n) (B : Finset (Fin n))
    (hbest : I.best ∈ B) (hh : outsideHardness I B = 0) : B = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  by_contra hi
  have hiBest : i ≠ I.best := fun heq => hi (heq ▸ hbest)
  have hpos := I.weight_pos ((I.mem_suboptimal i).mpr hiBest)
  have hle : I.weight i ≤ outsideHardness I B :=
    Finset.single_le_sum (fun j _ => I.weight_nonneg j)
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩)
  rw [hh] at hle
  linarith

/-- The h=0 clause of E.2 is an actual impossibility from empirical upper-half padding. -/
theorem collapse_impossible_of_outsideHardness_zero (I : Instance n)
    (S B : Finset (Fin n)) (hbest : I.best ∈ B) (hs : 8 ≤ S.card)
    (hh : outsideHardness I B = 0) (x : Fin n → ℝ) (z d : ℝ) :
    ¬collapse S B x z d := by
  have hB := core_eq_univ_of_outsideHardness_zero I B hbest hh
  have hhalf := Elimination.padded_card_ge_half S x z d
  simp only [hB, collapse, Finset.inter_univ]
  omega

/-- The usual real-power notation for the fully derived single-call E.16 bound. -/
theorem collapse_probability_le_source_power (I : Instance n) (S B : Finset (Fin n))
    (hbest : I.best ∈ B) (hcore : (S ∩ B).Nonempty) (hs : 8 ≤ S.card)
    (hh : 0 < outsideHardness I B) {m : ℕ} (hm : 0 < m) {z d ρ : ℝ}
    (hd : 0 < d) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1 / 2)
    (hz : z ≤ I.mean I.best + d / 16) (hgap : ∀ i ∈ B, I.gap i ≤ d / 8)
    (hbudget : 512 * (d ^ 2)⁻¹ * Real.log (1 / ρ) ≤ (m : ℝ)) :
    (callLaw n m).real {ω | collapse S B (empirical I.mean ω) z d} ≤
      3 * ρ ^ max 25 (2 * workRatio S d (outsideHardness I B)) := by
  simpa only [Real.rpow_def_of_pos hρ, mul_comm] using
    collapse_probability_le_source_exponent I S B hbest hcore hs hh hm hd hρ hρhalf hz hgap hbudget

end BatchCollapse
end GapEntropy
