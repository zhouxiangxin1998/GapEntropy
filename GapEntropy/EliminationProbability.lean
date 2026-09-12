import GapEntropy.FiniteEventCount
import GapEntropy.SortingMeasurability

/-!
# Probability bounds for one threshold elimination step

This module derives the three A.3 probability claims for the deterministic raw and padded
elimination of `Elimination` from two kinds of events: the reference estimate leaving the window
`[μ* - 3d/16, μ* + d/16]`, and an arm's estimate deviating from its mean by at least `d/16`. The
events are abstract; only their probabilities are assumed, at most `α/8` for the reference and
at most `α/64` for each deviation.

A.3(1) bounds the probability that the best arm is dropped. A.3(2) bounds the probability that a
large set fails to halve while keeping the best, via the Markov count of `FiniteEventCount`
applied to far errors; padding preserves this guarantee and has exactly the rounded-half size.
A.3(3) shows that on at most four well-separated arms the raw output is exactly the best arm.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GapEntropy.EliminationProbability
open GapEntropy.Elimination GapEntropy.PACRound

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ}

def referenceBad (μstar d : ℝ) (Z : Ω → ℝ) : Set Ω :=
  {ω | ¬ (μstar - 3 * d / 16 ≤ Z ω ∧ Z ω ≤ μstar + d / 16)}

def deviation (μ : Fin n → ℝ) (d : ℝ) (X : Fin n → Ω → ℝ) (i : Fin n) : Set Ω :=
  {ω | d / 16 ≤ |X i ω - μ i|}

theorem deviation_measurable (μ : Fin n → ℝ) (d : ℝ) {X : Fin n → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (i : Fin n) : MeasurableSet (deviation μ d X i) :=
  measurableSet_le measurable_const (((hX i).sub_const (μ i)).abs)

omit [MeasurableSpace Ω] in
theorem accurate_best_lower {μ : Fin n → ℝ} {d : ℝ} {X : Fin n → Ω → ℝ}
    {best : Fin n} {ω : Ω} (h : ω ∉ deviation μ d X best) :
    μ best - d / 16 ≤ X best ω := by
  have ha : |X best ω - μ best| < d / 16 := lt_of_not_ge h
  have hl := (abs_lt.mp ha).1
  linarith

omit [MeasurableSpace Ω] in
theorem farErrors_subset_deviations {S : Finset (Fin n)} {μ : Fin n → ℝ}
    {d μstar : ℝ} (hd : 0 ≤ d) (X : Fin n → Ω → ℝ) (ω : Ω) :
    farErrors S (fun i => X i ω) μ μstar d ⊆ occurringEvents S (deviation μ d X) ω := by
  classical
  intro i hi
  rcases Finset.mem_filter.mp hi with ⟨his, _, herr⟩
  apply Finset.mem_filter.mpr
  refine ⟨his, ?_⟩
  change d / 16 ≤ |X i ω - μ i|
  have ha := le_abs_self (X i ω - μ i)
  linarith

/-- A.3(1), for the actual raw set, from the separately established reference and
Gaussian deviation probabilities. -/
theorem raw_best_failure_le {S : Finset (Fin n)} {μ : Fin n → ℝ} {best : Fin n}
    (hbest : best ∈ S) {d α : ℝ} (hd : 0 ≤ d) (hα : 0 ≤ α)
    {X : Fin n → Ω → ℝ} {Z : Ω → ℝ}
    (href : P.real (referenceBad (μ best) d Z) ≤ α / 8)
    (hdev : P.real (deviation μ d X best) ≤ α / 64) :
    P.real {ω | best ∉ raw S (fun i => X i ω) (Z ω) d} ≤ α := by
  have hsub : {ω | best ∉ raw S (fun i => X i ω) (Z ω) d} ⊆
      referenceBad (μ best) d Z ∪ deviation μ d X best := by
    intro ω hω
    by_contra! h
    simp only [Set.mem_union, not_or] at h
    have hr : μ best - 3 * d / 16 ≤ Z ω ∧ Z ω ≤ μ best + d / 16 := not_not.mp h.1
    exact hω (best_mem_raw hbest hd hr.2 (accurate_best_lower h.2))
  have hu := (measureReal_mono hsub (measure_ne_top P _)).trans (measureReal_union_le _ _)
  linarith

/-- A.3(2) for the raw procedure: best retention and at most the rounded half. -/
theorem raw_large_failure_le {S : Finset (Fin n)} {μ : Fin n → ℝ} {best : Fin n}
    (hbest : best ∈ S) {d α : ℝ} (hd : 0 ≤ d) (hα : 0 ≤ α)
    {X : Fin n → Ω → ℝ} {Z : Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (href : P.real (referenceBad (μ best) d Z) ≤ α / 8)
    (hdev : ∀ i ∈ S, P.real (deviation μ d X i) ≤ α / 64)
    {N : ℕ} (hnear : (near S μ (μ best) d).card ≤ N) (hs : 4 * N < S.card) :
    P.real {ω | best ∉ raw S (fun i => X i ω) (Z ω) d ∨
      (S.card + 1) / 2 < (raw S (fun i => X i ω) (Z ω) d).card} ≤ α := by
  let E := deviation μ d X
  let many : Set Ω := {ω | S.card ≤ 4 * (occurringEvents S E ω).card}
  have hm : P.real many ≤ 4 * (α / 64) :=
    measure_fraction_events_le ⟨best, hbest⟩ (fun i _ => deviation_measurable μ d hX i)
      hdev (by norm_num : 0 < (4 : ℕ))
  have hsub : {ω | best ∉ raw S (fun i => X i ω) (Z ω) d ∨
      (S.card + 1) / 2 < (raw S (fun i => X i ω) (Z ω) d).card} ⊆
      referenceBad (μ best) d Z ∪ (E best ∪ many) := by
    intro ω hω
    by_contra! h
    simp only [Set.mem_union, not_or] at h
    have hr : μ best - 3 * d / 16 ≤ Z ω ∧ Z ω ≤ μ best + d / 16 := not_not.mp h.1
    rcases hω with hb | hc
    · exact hb (best_mem_raw hbest hd hr.2 (accurate_best_lower h.2.1))
    · have hfar := large_raw_many_far_errors hr.1 hnear hs hc
      have hcard := Finset.card_le_card (farErrors_subset_deviations (S := S) (μ := μ) (μstar := μ best) hd X ω)
      apply h.2.2
      change S.card ≤ 4 * (occurringEvents S (deviation μ d X) ω).card
      omega
  have hu := (measureReal_mono hsub (measure_ne_top P _)).trans (measureReal_union_le _ _)
  have hu2 := measureReal_union_le (μ := P) (E best) many
  have hb := hdev best hbest
  linarith

/-- Padding preserves the large-set guarantee and has exactly the rounded-half size. -/
theorem padded_large_failure_le {S : Finset (Fin n)} {μ : Fin n → ℝ} {best : Fin n}
    (hbest : best ∈ S) {d α : ℝ} (hd : 0 ≤ d) (hα : 0 ≤ α)
    {X : Fin n → Ω → ℝ} {Z : Ω → ℝ} (hX : ∀ i, Measurable (X i))
    (href : P.real (referenceBad (μ best) d Z) ≤ α / 8)
    (hdev : ∀ i ∈ S, P.real (deviation μ d X i) ≤ α / 64)
    {N : ℕ} (hnear : (near S μ (μ best) d).card ≤ N) (hs : 4 * N < S.card) :
    P.real {ω | best ∉ padded S (fun i => X i ω) (Z ω) d ∨
      (padded S (fun i => X i ω) (Z ω) d).card ≠ (S.card + 1) / 2} ≤ α := by
  apply le_trans (measureReal_mono (μ := P) (s₂ := {ω | best ∉ raw S (fun i => X i ω) (Z ω) d ∨
      (S.card + 1) / 2 < (raw S (fun i => X i ω) (Z ω) d).card}) ?_ (measure_ne_top P _))
    (raw_large_failure_le hbest hd hα hX href hdev hnear hs)
  intro ω hω
  by_contra! h
  simp only [Set.mem_ofPred_eq, not_or, not_not, not_lt] at h
  rcases hω with hb | hc
  · exact hb (raw_subset_padded _ _ _ _ h.1)
  · exact hc (padded_halves_of_raw_small h.2)

/-- A.3(3): on a set of size at most four, the raw output is exactly the best. -/
theorem raw_small_failure_le {S : Finset (Fin n)} {μ : Fin n → ℝ} {best : Fin n}
    (hbest : best ∈ S) {d α : ℝ} (hd : 0 ≤ d) (hα : 0 ≤ α)
    {X : Fin n → Ω → ℝ} {Z : Ω → ℝ}
    (href : P.real (referenceBad (μ best) d Z) ≤ α / 8)
    (hdev : ∀ i ∈ S, P.real (deviation μ d X i) ≤ α / 64)
    (hs : S.card ≤ 4) (hgaps : ∀ i ∈ S, i ≠ best → d ≤ μ best - μ i) :
    P.real {ω | raw S (fun i => X i ω) (Z ω) d ≠ {best}} ≤ α := by
  have hsub : {ω | raw S (fun i => X i ω) (Z ω) d ≠ {best}} ⊆
      referenceBad (μ best) d Z ∪ ⋃ i ∈ S, deviation μ d X i := by
    intro ω hω
    by_contra! h
    simp only [Set.mem_union, not_or] at h
    have hr : μ best - 3 * d / 16 ≤ Z ω ∧ Z ω ≤ μ best + d / 16 := not_not.mp h.1
    have hn (i : Fin n) (hi : i ∈ S) : ω ∉ deviation μ d X i := by
      intro hbad
      exact h.2 (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hbad⟩⟩)
    apply hω
    apply raw_eq_best_singleton hbest hd hr.1 hr.2 (accurate_best_lower (hn best hbest)) hgaps
    intro i hi _
    have ha : |X i ω - μ i| < d / 16 := lt_of_not_ge (hn i hi)
    have hu := (abs_lt.mp ha).2
    linarith
  have hu := (measureReal_mono hsub (measure_ne_top P _)).trans (measureReal_union_le _ _)
  have hsum := measureReal_biUnion_finset_le (μ := P) S (deviation μ d X)
  have hb : ∑ i ∈ S, P.real (deviation μ d X i) ≤ (S.card : ℝ) * (α / 64) := by
    simpa using Finset.sum_le_sum hdev
  have hsR : (S.card : ℝ) ≤ 4 := by exact_mod_cast hs
  have hprod := mul_le_mul_of_nonneg_right hsR (by positivity : 0 ≤ α / 64)
  linarith

end GapEntropy.EliminationProbability
