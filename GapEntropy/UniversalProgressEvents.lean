import GapEntropy.UniversalCallGuarantees

/-! # Deterministic progress implications and their event-count bounds -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GapEntropy.UniversalCall
open Elimination EliminationProbability PACRound

/-- The reference interval used for local progress, as in A.4/F.1. -/
def Suitable (μstar d z : ℝ) : Prop := μstar - 3 * d / 16 ≤ z ∧ z ≤ μstar + d / 16

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ} {S : Finset (Fin n)} {mean : Fin n → ℝ} {best : Fin n}
  {d α p : ℝ} {X : Fin n → Ω → ℝ} {Z : Ω → ℝ} {R : Set Ω}

/-- On any past restriction, best protection can fail only through its own
fresh estimate. The later concrete theorems supply the Gaussian bound. -/
theorem protected_failure_of_deviation (hbest : best ∈ S) (hd : 0 ≤ d)
    (hdev : P.real (R ∩ deviation mean d X best) ≤ p * (α / 64)) :
    P.real {ω | ω ∈ R ∧ Suitable (mean best) d (Z ω) ∧
      best ∉ padded S (fun i => X i ω) (Z ω) d} ≤ p * (α / 64) := by
  apply (measureReal_mono (μ := P) (h₂ := measure_ne_top _ _) ?_).trans hdev
  rintro ω ⟨hR, hz, hb⟩
  refine ⟨hR, ?_⟩
  by_contra h
  exact hb (best_mem_padded hbest hd hz.2 (accurate_best_lower h))

/-- A large raw set requires at least a quarter of the active estimates to be
bad. The same event prevents a padded set from having exactly the rounded half. -/
theorem halving_failure_of_deviations (hS : S.Nonempty) (hd : 0 ≤ d)
    (hR : MeasurableSet R) (hX : ∀ i, Measurable (X i))
    (hdev : ∀ i ∈ S, P.real (R ∩ deviation mean d X i) ≤ p * (α / 64))
    {N : ℕ} (hnear : (near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    P.real {ω | ω ∈ R ∧ Suitable (mean best) d (Z ω) ∧
      (padded S (fun i => X i ω) (Z ω) d).card ≠ (S.card + 1) / 2} ≤ p * (α / 16) := by
  let E : Fin n → Set Ω := fun i => R ∩ deviation mean d X i
  have hm : P.real {ω | S.card ≤ 4 * (occurringEvents S E ω).card} ≤ 4 * (p * (α / 64)) :=
    measure_fraction_events_le hS (fun i _ => hR.inter (deviation_measurable mean d hX i))
      hdev (by norm_num : 0 < (4 : ℕ))
  have hsub : {ω | ω ∈ R ∧ Suitable (mean best) d (Z ω) ∧
      (padded S (fun i => X i ω) (Z ω) d).card ≠ (S.card + 1) / 2} ⊆
      {ω | S.card ≤ 4 * (occurringEvents S E ω).card} := by
    rintro ω ⟨hω, hz, hp⟩
    have hr : (S.card + 1) / 2 < (raw S (fun i => X i ω) (Z ω) d).card := by
      by_contra! h
      exact hp (padded_halves_of_raw_small h)
    have hf := large_raw_many_far_errors hz.1 hnear hs hr
    have hc := Finset.card_le_card
      (farErrors_subset_deviations (S := S) (μ := mean) (μstar := mean best) hd X ω)
    have he : occurringEvents S E ω = occurringEvents S (deviation mean d X) ω := by
      ext i
      simp only [occurringEvents, Finset.mem_filter, Set.mem_inter_iff, E, hω, true_and]
    change S.card ≤ 4 * (occurringEvents S E ω).card
    rw [he]
    omega
  have hh := (measureReal_mono hsub (measure_ne_top P _)).trans hm
  nlinarith

/-- With at most four separated active arms, any failure of exact raw isolation
requires at least one inaccurate active estimate. Padding may retain more arms. -/
theorem isolation_failure_of_deviations (hbest : best ∈ S) (hd : 0 ≤ d)
    (hpα : 0 ≤ p * (α / 64))
    (hdev : ∀ i ∈ S, P.real (R ∩ deviation mean d X i) ≤ p * (α / 64))
    (hs : S.card ≤ 4) (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    P.real {ω | ω ∈ R ∧ Suitable (mean best) d (Z ω) ∧
      raw S (fun i => X i ω) (Z ω) d ≠ {best}} ≤ p * (α / 16) := by
  have hsub : {ω | ω ∈ R ∧ Suitable (mean best) d (Z ω) ∧
      raw S (fun i => X i ω) (Z ω) d ≠ {best}} ⊆ ⋃ i ∈ S, R ∩ deviation mean d X i := by
    rintro ω ⟨hR, hz, hb⟩
    by_contra h
    have hn (i : Fin n) (hi : i ∈ S) : ω ∉ deviation mean d X i := by
      intro hdv
      exact h (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hR, hdv⟩⟩)
    apply hb
    apply raw_eq_best_singleton hbest hd hz.1 hz.2 (accurate_best_lower (hn best hbest)) hgaps
    intro i hi _
    have ha : |X i ω - mean i| < d / 16 := lt_of_not_ge (hn i hi)
    have hh := (abs_lt.mp ha).2
    linarith
  have hu := (measureReal_mono hsub (measure_ne_top P _)).trans
    (measureReal_biUnion_finset_le (μ := P) S (fun i => R ∩ deviation mean d X i))
  have hsum : ∑ i ∈ S, P.real (R ∩ deviation mean d X i) ≤ (S.card : ℝ) * (p * (α / 64)) := by
    simpa using Finset.sum_le_sum hdev
  have hsR : (S.card : ℝ) ≤ 4 := by exact_mod_cast hs
  have hmul := mul_le_mul_of_nonneg_right hsR hpα
  nlinarith

end GapEntropy.UniversalCall
