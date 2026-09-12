import GapEntropy.Elimination
import GapEntropy.Gaussian
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# One median-elimination round

This module proves the deterministic upper-half selection argument and a
stochastic one-round failure bound from marginal Gaussian sample-mean tails.
It is a building block for the full multi-round PAC procedure in Lemma A.2.

Sorting measurability is not assumed or proved here: the bad-event bounds are
valid outer-measure bounds obtained from containment in measurable events.
The measurable implementation of the complete recursive algorithm remains separate.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace GapEntropy.PACRound

variable {ι : Type*} [DecidableEq ι]

def upwardErrors (S : Finset ι) (μ x : ι → ℝ) (ε : ℝ) : Finset ι :=
  S.filter fun i => μ i + ε < x i

/-- If the reference is not underestimated and fewer than half of all arms
overestimate, the actual empirical upper half contains an arm within `2ε` of it. -/
theorem upperHalf_retains_approx {S : Finset ι} {μ x : ι → ℝ} {a : ι} {ε : ℝ}
    (ha : a ∈ S) (hε : 0 ≤ ε) (hxa : μ a - ε ≤ x a)
    (hcount : 2 * (upwardErrors S μ x ε).card < S.card) :
    ∃ b ∈ GapEntropy.Elimination.upperHalf S x, μ a - 2 * ε ≤ μ b := by
  by_cases hau : a ∈ GapEntropy.Elimination.upperHalf S x
  · exact ⟨a, hau, by linarith⟩
  have hcard : (upwardErrors S μ x ε).card < (GapEntropy.Elimination.upperHalf S x).card := by
    rw [GapEntropy.Elimination.upperHalf_card]
    omega
  obtain ⟨b, hbu, hbe⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hbs := GapEntropy.Elimination.upperHalf_subset S x hbu
  have hxb : x b ≤ μ b + ε := by
    by_contra! h
    exact hbe (Finset.mem_filter.mpr ⟨hbs, h⟩)
  have hrank := GapEntropy.Elimination.upperHalf_rank hbu ha hau
  exact ⟨b, hbu, by linarith⟩

/-- Specializing the reference to a true maximum controls the loss of the retained maximum. -/
theorem upperHalf_retains_pac {S : Finset ι} {μ x : ι → ℝ} {a : ι} {ε : ℝ}
    (ha : a ∈ S) (hmax : ∀ i ∈ S, μ i ≤ μ a) (hε : 0 ≤ ε)
    (hxa : μ a - ε ≤ x a) (hcount : 2 * (upwardErrors S μ x ε).card < S.card) :
    ∃ b ∈ GapEntropy.Elimination.upperHalf S x, ∀ i ∈ S, μ i - 2 * ε ≤ μ b := by
  obtain ⟨b, hb, happrox⟩ := upperHalf_retains_approx ha hε hxa hcount
  refine ⟨b, hb, fun i hi => ?_⟩
  linarith [hmax i hi]

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

def occurringEvents (S : Finset ι) (E : ι → Set Ω) (ω : Ω) : Finset ι := by
  classical
  exact S.filter fun i => ω ∈ E i

/-- A finite count of events, represented as a sum of real indicators. -/
def eventCount (S : Finset ι) (E : ι → Set Ω) (ω : Ω) : ℝ :=
  ∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω

omit [DecidableEq ι] [MeasurableSpace Ω] in
theorem eventCount_eq_card (S : Finset ι) (E : ι → Set Ω) (ω : Ω) :
    eventCount S E ω = ((occurringEvents S E ω).card : ℝ) := by
  classical
  simp [eventCount, occurringEvents, Set.indicator]

omit [DecidableEq ι] in
/-- Finite-count Markov: if each marginal event has probability at most `η`,
then the probability that at least half occur is at most `2η`.
No independence among the events is required. -/
theorem measure_many_events_le {S : Finset ι} (hS : S.Nonempty) {E : ι → Set Ω}
    (hE : ∀ i ∈ S, MeasurableSet (E i)) {η : ℝ}
    (hprob : ∀ i ∈ S, P.real (E i) ≤ η) :
    P.real {ω | S.card ≤ 2 * (occurringEvents S E ω).card} ≤ 2 * η := by
  classical
  have hint_i (i : ι) (hi : i ∈ S) :
      Integrable ((E i).indicator (fun _ : Ω => (1 : ℝ))) P :=
    (integrable_const 1).indicator (hE i hi)
  have hint : Integrable (eventCount S E) P := integrable_finsetSum S hint_i
  have hnonneg : 0 ≤ᵐ[P] eventCount S E := ae_of_all P fun ω => by
    rw [eventCount_eq_card]
    positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hint ((S.card : ℝ) / 2)
  have hintegral : ∫ ω, eventCount S E ω ∂P = ∑ i ∈ S, P.real (E i) := by
    change (∫ ω, ∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω ∂P) = _
    rw [integral_finsetSum S hint_i]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [smul_eq_mul, mul_one] using
      integral_indicator_const (μ := P) (1 : ℝ) (hE i hi)
  rw [hintegral] at hmarkov
  have hbound : ∑ i ∈ S, P.real (E i) ≤ (S.card : ℝ) * η := by
    have h := Finset.sum_le_sum hprob
    simpa using h
  have hevent : {ω | (S.card : ℝ) / 2 ≤ eventCount S E ω} =
      {ω | S.card ≤ 2 * (occurringEvents S E ω).card} := by
    ext ω
    change ((S.card : ℝ) / 2 ≤ eventCount S E ω) ↔ S.card ≤ 2 * (occurringEvents S E ω).card
    rw [eventCount_eq_card]
    constructor
    · intro h
      have hr : (S.card : ℝ) ≤ 2 * ((occurringEvents S E ω).card : ℝ) := by linarith
      exact_mod_cast hr
    · intro h
      have hr : (S.card : ℝ) ≤ 2 * ((occurringEvents S E ω).card : ℝ) := by exact_mod_cast h
      linarith
  rw [hevent] at hmarkov
  have hcard : 0 < (S.card : ℝ) := by exact_mod_cast hS.card_pos
  nlinarith

/-- Failure to keep any arm within `2ε` of reference arm `a`. -/
def failureEvent (S : Finset ι) (μ : ι → ℝ) (X : ι → Ω → ℝ) (a : ι) (ε : ℝ) : Set Ω :=
  {ω | ¬ ∃ b ∈ GapEntropy.Elimination.upperHalf S (fun i => X i ω), μ a - 2 * ε ≤ μ b}

/-- The stochastic core of A.2: one lower-tail event plus a finite-count Markov event. -/
theorem failure_le_three_eta {S : Finset ι} {μ : ι → ℝ} {X : ι → Ω → ℝ} {a : ι}
    {ε η : ℝ} (ha : a ∈ S) (hε : 0 ≤ ε) (hX : ∀ i ∈ S, Measurable (X i))
    (hlower : P.real {ω | X a ω < μ a - ε} ≤ η)
    (hupper : ∀ i ∈ S, P.real {ω | μ i + ε < X i ω} ≤ η) :
    P.real (failureEvent S μ X a ε) ≤ 3 * η := by
  classical
  let E : ι → Set Ω := fun i => {ω | μ i + ε < X i ω}
  have hmany := measure_many_events_le (P := P) ⟨a, ha⟩
    (E := E) (fun i hi => measurableSet_lt measurable_const (hX i hi)) hupper
  have hsubset : failureEvent S μ X a ε ⊆
      {ω | X a ω < μ a - ε} ∪ {ω | S.card ≤ 2 * (occurringEvents S E ω).card} := by
    intro ω hfail
    by_cases hlow : X a ω < μ a - ε
    · exact Or.inl hlow
    · right
      by_contra hnot
      have hcount : 2 * (upwardErrors S μ (fun i => X i ω) ε).card < S.card :=
        lt_of_not_ge hnot
      exact hfail (upperHalf_retains_approx ha hε (le_of_not_gt hlow) hcount)
  calc
    _ ≤ P.real ({ω | X a ω < μ a - ε} ∪
        {ω | S.card ≤ 2 * (occurringEvents S E ω).card}) := measureReal_mono hsubset
    _ ≤ P.real {ω | X a ω < μ a - ε} +
        P.real {ω | S.card ≤ 2 * (occurringEvents S E ω).card} := measureReal_union_le _ _
    _ ≤ 3 * η := by linarith

/-- Gaussian specialization of the one-round bound for actual independent blocks.
Only within-arm independence is needed by this bound; cross-arm independence is unnecessary. -/
theorem gaussian_failure_le {S : Finset ι} {μ : ι → ℝ} {a : ι} {m : ℕ} (hm : 0 < m)
    {X : ι → Fin m → Ω → ℝ} {ε : ℝ} (ha : a ∈ S) (hε : 0 ≤ ε)
    (hX : ∀ i ∈ S, ∀ j, Measurable (X i j))
    (hind : ∀ i ∈ S, iIndepFun (X i) P)
    (hlaw : ∀ i ∈ S, ∀ j, HasLaw (X i j) (gaussianReal (μ i) 1) P) :
    P.real (failureEvent S μ (fun i => GapEntropy.Gaussian.sampleMean (X i)) a ε) ≤
      3 * Real.exp (-((m : ℝ) * ε ^ 2) / 2) := by
  apply failure_le_three_eta ha hε
  · intro i hi
    have hmi := hX i hi
    unfold GapEntropy.Gaussian.sampleMean
    fun_prop
  · calc
      _ ≤ P.real {ω | GapEntropy.Gaussian.sampleMean (X a) ω - μ a ≤ -ε} := by
        refine measureReal_mono ?_ (measure_ne_top P _)
        intro ω hω
        dsimp at hω ⊢
        linarith
      _ ≤ _ := GapEntropy.Gaussian.sampleMean_lower_tail hm (hind a ha) (hlaw a ha) hε
  · intro i hi
    calc
      _ ≤ P.real {ω | ε ≤ GapEntropy.Gaussian.sampleMean (X i) ω - μ i} := by
        refine measureReal_mono ?_ (measure_ne_top P _)
        intro ω hω
        dsimp at hω ⊢
        linarith
      _ ≤ _ := GapEntropy.Gaussian.sampleMean_upper_tail hm (hind i hi) (hlaw i hi) hε

/-- The explicit sample budget in A.2 makes each Gaussian one-sided tail at most `(β/8)^4`. -/
theorem gaussian_tail_of_round_budget {m : ℕ} {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β)
    (hbudget : 8 * (ε ^ 2)⁻¹ * Real.log (8 / β) ≤ (m : ℝ)) :
    Real.exp (-((m : ℝ) * ε ^ 2) / 2) ≤ (β / 8) ^ 4 := by
  have hmul := mul_le_mul_of_nonneg_right hbudget (sq_nonneg ε)
  have hcancel : (8 * (ε ^ 2)⁻¹ * Real.log (8 / β)) * ε ^ 2 =
      8 * Real.log (8 / β) := by field_simp [hε.ne']
  rw [hcancel] at hmul
  have hlog : -(4 * Real.log (8 / β)) = Real.log ((β / 8) ^ 4) := by
    rw [Real.log_pow, Real.log_div (by norm_num) hβ.ne',
      Real.log_div hβ.ne' (by norm_num)]
    norm_num
    ring
  calc
    _ ≤ Real.exp (-(4 * Real.log (8 / β))) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = (β / 8) ^ 4 := by rw [hlog, Real.exp_log (by positivity)]

theorem three_tail_power_le {β : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) :
    3 * (β / 8) ^ 4 ≤ β := by
  have hsq : β ^ 2 ≤ β := by nlinarith
  have hsq1 : β ^ 2 ≤ 1 := by nlinarith
  have hfour : β ^ 4 ≤ β ^ 2 := by nlinarith [sq_nonneg β]
  norm_num [div_pow]
  nlinarith

/-- With the manuscript's declared sample budget, the one-round failure bound is exactly
`3η`, where `η=(β/8)^4`. -/
theorem gaussian_failure_le_three_tail_power {S : Finset ι} {μ : ι → ℝ} {a : ι} {m : ℕ}
    (hm : 0 < m) {X : ι → Fin m → Ω → ℝ} {ε β : ℝ} (ha : a ∈ S)
    (hε : 0 < ε) (hβ : 0 < β)
    (hbudget : 8 * (ε ^ 2)⁻¹ * Real.log (8 / β) ≤ (m : ℝ))
    (hX : ∀ i ∈ S, ∀ j, Measurable (X i j))
    (hind : ∀ i ∈ S, iIndepFun (X i) P)
    (hlaw : ∀ i ∈ S, ∀ j, HasLaw (X i j) (gaussianReal (μ i) 1) P) :
    P.real (failureEvent S μ (fun i => GapEntropy.Gaussian.sampleMean (X i)) a ε) ≤
      3 * (β / 8) ^ 4 :=
  (gaussian_failure_le hm ha hε.le hX hind hlaw).trans
    (mul_le_mul_of_nonneg_left (gaussian_tail_of_round_budget hε hβ hbudget) (by norm_num))

/-- The per-round error budget used when composing median-elimination rounds. -/
theorem gaussian_failure_le_beta {S : Finset ι} {μ : ι → ℝ} {a : ι} {m : ℕ}
    (hm : 0 < m) {X : ι → Fin m → Ω → ℝ} {ε β : ℝ} (ha : a ∈ S)
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hbudget : 8 * (ε ^ 2)⁻¹ * Real.log (8 / β) ≤ (m : ℝ))
    (hX : ∀ i ∈ S, ∀ j, Measurable (X i j))
    (hind : ∀ i ∈ S, iIndepFun (X i) P)
    (hlaw : ∀ i ∈ S, ∀ j, HasLaw (X i j) (gaussianReal (μ i) 1) P) :
    P.real (failureEvent S μ (fun i => GapEntropy.Gaussian.sampleMean (X i)) a ε) ≤ β :=
  (gaussian_failure_le_three_tail_power hm ha hε hβ hbudget hX hind hlaw).trans
    (three_tail_power_le hβ.le hβ1)

end Probability
end GapEntropy.PACRound
