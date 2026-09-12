import GapEntropy.Fallback

/-!
# Gaussian laws for the actual fallback's potential schedule

All samples below are coordinates of `Model.sampleLawOfMeans`. Independence
comes from its infinite product, and the operational connection is the active
history identity proved in `Fallback.lean`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.Fallback

def observation {n : ℕ} (r : ℕ) (i : Fin n) (k : Fin (roundSamples r))
    (ω : SampleSpace n) : ℝ := ω.2 (n * k + i) i

theorem measurable_observation {n : ℕ} (r : ℕ) (i : Fin n) (k : Fin (roundSamples r)) :
    Measurable (observation r i k) := by
  unfold observation
  fun_prop

theorem observation_hasLaw {n : ℕ} (mean : Fin n → ℝ) (r : ℕ) (i : Fin n)
    (k : Fin (roundSamples r)) :
    HasLaw (observation r i k) (gaussianReal (mean i) 1) (sampleLawOfMeans mean) :=
  ⟨(measurable_observation r i k).aemeasurable, sampleLawOfMeans_map_reward mean _ _⟩

theorem sample_rows_independent {n : ℕ} (mean : Fin n → ℝ) :
    iIndepFun (fun t (ω : SampleSpace n) => ω.2 t) (sampleLawOfMeans mean) := by
  have hlaw (t : ℕ) : HasLaw (fun ω : SampleSpace n => ω.2 t)
      (Measure.pi (fun i => gaussianReal (mean i) 1)) (sampleLawOfMeans mean) := by
    have hp := (measurePreserving_eval_infinitePi
      (fun _ : ℕ => Measure.pi (fun i => gaussianReal (mean i) 1)) t).comp
        (measurePreserving_snd (μ := seedLaw) (ν := rewardLaw mean))
    exact ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  apply (iIndepFun_iff_hasLaw_Pi_infinitePi hlaw (by fun_prop)).mpr
  exact ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩

theorem observations_independent {n : ℕ} (hn : 2 ≤ n) (mean : Fin n → ℝ)
    (r : ℕ) (i : Fin n) : iIndepFun (observation r i) (sampleLawOfMeans mean) := by
  have hinj : Function.Injective (fun k : Fin (roundSamples r) => n * (k : ℕ) + i) := by
    intro k l h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_right_cancel h)
  have hrows := (sample_rows_independent mean).precomp hinj
  exact hrows.comp (fun _ row => row i) (fun _ => measurable_pi_apply i)

theorem empiricalMean_two_sided {n : ℕ} (hn : 2 ≤ n) (mean : Fin n → ℝ)
    (r : ℕ) (i : Fin n) {ε : ℝ} (hε : 0 ≤ ε) :
    (sampleLawOfMeans mean).real {ω | ε ≤ |empiricalMean r i ω - mean i|} ≤
      2 * Real.exp (-((roundSamples r : ℝ) * ε ^ 2) / 2) := by
  exact Gaussian.sampleMean_two_sided (pow_pos (by norm_num) r)
    (observations_independent hn mean r i) (observation_hasLaw mean r i) hε

theorem confidence_ratio_ge_one {n : ℕ} (hn : 2 ≤ n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (r : ℕ) :
    1 ≤ 8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ := by
  apply (le_div_iff₀ hδ).mpr
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hs : (1 : ℝ) ≤ ((r : ℝ) + 1)^2 := by nlinarith
  nlinarith [mul_nonneg (show 0 ≤ 8 * (n : ℝ) by positivity) (sub_nonneg.mpr hs)]

theorem radius_sq {n : ℕ} (hn : 2 ≤ n) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (r : ℕ) :
    radius n δ r ^ 2 = (2 / (roundSamples r : ℝ)) *
      Real.log (8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ) := by
  apply Real.sq_sqrt
  apply mul_nonneg (by positivity)
  exact Real.log_nonneg (confidence_ratio_ge_one hn hδ hδ1 r)

/-- C.6's exact Gaussian confidence allocation on the genuine potential samples. -/
theorem empiricalMean_confidence_tail {n : ℕ} (hn : 2 ≤ n) (mean : Fin n → ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (r : ℕ) (i : Fin n) :
    (sampleLawOfMeans mean).real {ω | radius n δ r < |empiricalMean r i ω - mean i|} ≤
      δ / (4 * (n : ℝ) * ((r : ℝ) + 1)^2) := by
  have hs : {ω | radius n δ r < |empiricalMean r i ω - mean i|} ⊆
      {ω | radius n δ r ≤ |empiricalMean r i ω - mean i|} := by
    intro ω hω
    change radius n δ r < |empiricalMean r i ω - mean i| at hω
    exact hω.le
  have h := (measureReal_mono hs).trans
    (empiricalMean_two_sided hn mean r i (Real.sqrt_nonneg _))
  have hm : (roundSamples r : ℝ) ≠ 0 := by
    exact_mod_cast (pow_ne_zero r (by norm_num : (2 : ℕ) ≠ 0))
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hr0 : (r : ℝ) + 1 ≠ 0 := by positivity
  have hq : 0 < 8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ :=
    lt_of_lt_of_le (by norm_num) (confidence_ratio_ge_one hn hδ hδ1 r)
  rw [radius_sq hn hδ hδ1 r] at h
  have he : -((roundSamples r : ℝ) * ((2 / (roundSamples r : ℝ)) *
      Real.log (8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ))) / 2 =
      -Real.log (8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ) := by field_simp
  rw [he, Real.exp_neg, Real.exp_log hq] at h
  have hc : 2 * (8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ)⁻¹ =
      δ / (4 * (n : ℝ) * ((r : ℝ) + 1)^2) := by field_simp; norm_num
  rwa [hc] at h

/-- The exact round-tail form in C.2, once the deterministic radius is small. -/
theorem not_returned_by_round_probability_le {n : ℕ} (I : Instance n) (δ : ℝ)
    (r : ℕ) {g : ℝ} (hg : 0 < g) (hgap : ∀ j, j ≠ I.best → g ≤ I.gap j)
    (hρ : radius n δ r ≤ g / 8) :
    (sampleLaw I).real {ω | ¬ ∃ i,
      (policy n δ).returnedAt I.two_le (roundTime n r + 1) ω = some i} ≤
      2 * (n : ℝ) * Real.exp (-((roundSamples r : ℝ) * g ^ 2) / 128) := by
  have hs : {ω | ¬ ∃ i, (policy n δ).returnedAt I.two_le (roundTime n r + 1) ω = some i} ⊆
      ⋃ i : Fin n, {ω | g / 8 ≤ |empiricalMean r i ω - I.mean i|} := by
    intro ω hω
    obtain ⟨i, hi⟩ := not_returned_by_round_imp_error I δ ω r hg hgap hρ hω
    exact Set.mem_iUnion.mpr ⟨i, hi.le⟩
  calc
    _ ≤ (sampleLaw I).real (⋃ i : Fin n, {ω | g / 8 ≤ |empiricalMean r i ω - I.mean i|}) :=
      measureReal_mono hs
    _ ≤ ∑ i : Fin n, (sampleLaw I).real {ω | g / 8 ≤ |empiricalMean r i ω - I.mean i|} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _i : Fin n, 2 * Real.exp (-((roundSamples r : ℝ) * (g / 8)^2) / 2) :=
      Finset.sum_le_sum (fun i _ => empiricalMean_two_sided I.two_le I.mean r i (by positivity))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have he : -((roundSamples r : ℝ) * (g / 8)^2) / 2 =
          -((roundSamples r : ℝ) * g ^ 2) / 128 := by ring
      rw [he]
      ring

end GapEntropy.Fallback
