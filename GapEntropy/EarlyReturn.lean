import GapEntropy.Censor
import GapEntropy.TiedNull

/-!
# The lower end of the designated-arm stopping window

The capped policy is used only as a comparison device. It is not assumed to be
correct: its wrong-return event is contained in the original policy's event.
All KL costs come from its actual bounded designated-arm count.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GapEntropy.Policy

variable {n : ℕ} (A : Policy n)

theorem censor_returnedNotEvent_subset (hn : 2 ≤ n) (d : Fin n) (B : ℕ) :
    (A.censor d B).returnedNotEvent hn d ⊆ A.returnedNotEvent hn d := by
  rintro ω ⟨T, i, hi, hret⟩
  exact ⟨T, i, hi, A.censor_return_ne_tag_imp_original hn d i B T ω hi hret⟩

theorem returnedNotEvent_cap_subset_censor (hn : 2 ≤ n) (d : Fin n) (B : ℕ) :
    A.returnedNotEvent hn d ∩ {ω | A.armSamples hn d ω ≤ B} ⊆
      (A.censor d B).returnedNotEvent hn d := by
  rintro ω ⟨⟨T, i, hi, hret⟩, hcount⟩
  obtain ⟨s, hs⟩ := A.censor_preserves_returns_of_count_le hn d i B ω hcount ⟨T, hret⟩
  exact ⟨s, i, hi, hs⟩

theorem censor_klDiv_transcript_raised_le (I : Instance n) (d : Fin n) (B T : ℕ) :
    InformationTheory.klDiv ((A.censor d B).transcriptLaw I.two_le I.mean T)
      ((A.censor d B).transcriptLaw I.two_le (Coupling.raisedMean I.mean I.best d) T) ≤
      ENNReal.ofReal (I.gap d ^ 2 * (B : ℝ) / 2) := by
  have hc (j : Fin n) :
      ENNReal.ofReal ((I.mean j - Coupling.raisedMean I.mean I.best d j)^2 / 2) =
        if j = d then ENNReal.ofReal (I.gap d ^ 2 / 2) else 0 := by
    by_cases hj : j = d
    · subst j
      simp only [Coupling.raisedMean, Function.update_self, if_true, Instance.gap]
      congr 1
      ring
    · simp [Coupling.raisedMean, hj]
  rw [klDiv_transcriptLaw_eq_source_counts]
  simp_rw [hc]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hcount : ∫⁻ ω, (A.censor d B).truncatedArmSamples I.two_le T d ω
      ∂sampleLawOfMeans I.mean ≤ B := by
    calc
      _ ≤ ∫⁻ _ω, (B : ℝ≥0∞) ∂sampleLawOfMeans I.mean :=
        lintegral_mono (A.censor_truncatedArmSamples_le I.two_le d B T)
      _ = B := by simp
  calc
    _ ≤ ENNReal.ofReal (I.gap d ^ 2 / 2) * B := mul_le_mul_right hcount _
    _ = ENNReal.ofReal (I.gap d ^ 2 * (B : ℝ) / 2) := by
      rw [show (B : ℝ≥0∞) = ENNReal.ofReal (B : ℝ) by simp,
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ I.gap d ^ 2 / 2)]
      congr 1
      ring

theorem censor_klDiv_run_raised_le (I : Instance n) (d : Fin n) (B T : ℕ) :
    InformationTheory.klDiv
      ((sampleLawOfMeans I.mean).map (fun ω => (A.censor d B).run I.two_le ω T))
      ((sampleLawOfMeans (Coupling.raisedMean I.mean I.best d)).map
        (fun ω => (A.censor d B).run I.two_le ω T)) ≤
      ENNReal.ofReal (I.gap d ^ 2 * (B : ℝ) / 2) :=
  ((A.censor d B).klDiv_run_le_transcript I.two_le I.mean _ T).trans
    (A.censor_klDiv_transcript_raised_le I d B T)

theorem censor_returnedNotAt_real_le (I : Instance n) (d : Fin n) (hd : d ≠ I.best)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hcorrect : ∀ J : Instance n, ENNReal.ofReal (1 - δ) ≤ A.successProb J) (B T : ℕ) :
    (sampleLaw I).real ((A.censor d B).returnedNotAt I.two_le d T) ≤
      δ + Real.sqrt (I.gap d ^ 2 * (B : ℝ) / 4) := by
  let C := A.censor d B
  let μ := (sampleLawOfMeans I.mean).map (fun ω => C.run I.two_le ω T)
  let ν := (sampleLawOfMeans (Coupling.raisedMean I.mean I.best d)).map
    (fun ω => C.run I.two_le ω T)
  have : IsProbabilityMeasure μ := Measure.isProbabilityMeasure_map (C.measurable_run I.two_le T).aemeasurable
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (C.measurable_run I.two_le T).aemeasurable
  have hv := measure_event_abs_sub_le_sqrt μ ν (measurableSet_returnedNotState d T)
    (I.gap d ^ 2 * (B : ℝ) / 2) (by positivity) (A.censor_klDiv_run_raised_le I d B T)
  change |((sampleLawOfMeans I.mean).map (fun ω => C.run I.two_le ω T)).real _ -
      ((sampleLawOfMeans (Coupling.raisedMean I.mean I.best d)).map
        (fun ω => C.run I.two_le ω T)).real _| ≤ _ at hv
  rw [C.map_run_returnedNotState_real, C.map_run_returnedNotState_real] at hv
  have hs : C.returnedNotAt I.two_le d T ⊆ A.returnedNotEvent I.two_le d :=
    fun _ h => A.censor_returnedNotEvent_subset I.two_le d B ⟨T, h⟩
  have hq : (sampleLawOfMeans (Coupling.raisedMean I.mean I.best d)).real
      (C.returnedNotAt I.two_le d T) ≤ δ :=
    (measureReal_mono hs).trans (A.tied_returnedNotEvent_real_le I d hd hδ hcorrect)
  have he : (I.gap d ^ 2 * (B : ℝ) / 2) / 2 = I.gap d ^ 2 * (B : ℝ) / 4 := by ring
  rw [he] at hv
  change (sampleLawOfMeans I.mean).real (C.returnedNotAt I.two_le d T) ≤ _
  linarith [le_abs_self ((sampleLawOfMeans I.mean).real (C.returnedNotAt I.two_le d T) -
    (sampleLawOfMeans (Coupling.raisedMean I.mean I.best d)).real (C.returnedNotAt I.two_le d T))]

theorem censor_returnedNotEvent_measure_le (I : Instance n) (d : Fin n) (hd : d ≠ I.best)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hcorrect : ∀ J : Instance n, ENNReal.ofReal (1 - δ) ≤ A.successProb J) (B : ℕ) :
    sampleLaw I ((A.censor d B).returnedNotEvent I.two_le d) ≤
      ENNReal.ofReal (δ + Real.sqrt (I.gap d ^ 2 * (B : ℝ) / 4)) := by
  apply (A.censor d B).measure_returnedNotEvent_le_of_finite
  intro T
  rw [← ENNReal.ofReal_toReal (measure_ne_top (sampleLaw I) _)]
  exact ENNReal.ofReal_le_ofReal (A.censor_returnedNotAt_real_le I d hd hδ hcorrect B T)

/-- Generic cap version of the early-return comparison. -/
theorem returnedNotEvent_cap_measure_le (I : Instance n) (d : Fin n) (hd : d ≠ I.best)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hcorrect : ∀ J : Instance n, ENNReal.ofReal (1 - δ) ≤ A.successProb J) (B : ℕ) :
    sampleLaw I (A.returnedNotEvent I.two_le d ∩ {ω | A.armSamples I.two_le d ω ≤ B}) ≤
      ENNReal.ofReal (δ + Real.sqrt (I.gap d ^ 2 * (B : ℝ) / 4)) :=
  (measure_mono (A.returnedNotEvent_cap_subset_censor I.two_le d B)).trans
    (A.censor_returnedNotEvent_measure_le I d hd hδ hcorrect B)

/-- A strict real count threshold becomes the exact integer cap `ceil x - 1`,
also for infinite paths, by bounding every finite integer count. -/
theorem armSamples_le_ceil_sub_one_of_lt (hn : 2 ≤ n) (d : Fin n) (ω : SampleSpace n)
    {x : ℝ} (hx : 0 < x) (hcount : A.armSamples hn d ω < ENNReal.ofReal x) :
    A.armSamples hn d ω ≤ (Nat.ceil x - 1 : ℕ) := by
  rw [A.armSamples_eq_iSup_truncatedArmSamples]
  apply iSup_le
  intro T
  rw [← A.cast_requestCountNat]
  have ht := (A.truncatedArmSamples_le_armSamples hn T d ω).trans_lt hcount
  rw [← A.cast_requestCountNat] at ht
  have ht' : (A.requestCountNat hn T d ω : ℝ) < x := by
    apply (ENNReal.ofReal_lt_ofReal_iff hx).mp
    simpa using ht
  have hceil : A.requestCountNat hn T d ω < Nat.ceil x := Nat.lt_ceil.mpr ht'
  exact_mod_cast (show A.requestCountNat hn T d ω ≤ Nat.ceil x - 1 by omega)

private theorem ceil_sub_one_lt {x : ℝ} (hx : 0 < x) :
    ((Nat.ceil x - 1 : ℕ) : ℝ) < x := by
  have hpos : 0 < Nat.ceil x := Nat.ceil_pos.mpr hx
  rw [Nat.cast_sub (by omega : 1 ≤ Nat.ceil x), Nat.cast_one]
  linarith [Nat.ceil_lt_add_one hx.le]

/-- The manuscript's lower stopping-window endpoint with `c₀ = 1/100`.
The event requires a finite return different from the designated arm. -/
theorem early_return_measure_le (I : Instance n) (d : Fin n) (hd : d ≠ I.best)
    {δ : ℝ} (hδ : δ ≤ 1)
    (hcorrect : ∀ J : Instance n, ENNReal.ofReal (1 - δ) ≤ A.successProb J) :
    sampleLaw I (A.returnedNotEvent I.two_le d ∩
      {ω | A.armSamples I.two_le d ω < ENNReal.ofReal ((1 / 100 : ℝ) * (I.gap d ^ 2)⁻¹)}) ≤
      ENNReal.ofReal (δ + 1 / 20) := by
  let x : ℝ := (1 / 100 : ℝ) * (I.gap d ^ 2)⁻¹
  let B : ℕ := Nat.ceil x - 1
  have hgap := I.gap_pos hd
  have hx : 0 < x := mul_pos (by norm_num) (inv_pos.mpr (sq_pos_of_pos hgap))
  have hs : A.returnedNotEvent I.two_le d ∩ {ω | A.armSamples I.two_le d ω < ENNReal.ofReal x} ⊆
      A.returnedNotEvent I.two_le d ∩ {ω | A.armSamples I.two_le d ω ≤ B} := by
    rintro ω ⟨hret, hc⟩
    exact ⟨hret, A.armSamples_le_ceil_sub_one_of_lt I.two_le d ω hx hc⟩
  have hb : (B : ℝ) < x := ceil_sub_one_lt hx
  have hcost : I.gap d ^ 2 * (B : ℝ) ≤ 1 / 100 := by
    have hm := mul_le_mul_of_nonneg_left hb.le (sq_nonneg (I.gap d))
    have he : I.gap d ^ 2 * x = 1 / 100 := by
      dsimp [x]
      field_simp [hgap.ne']
    simpa only [he] using hm
  have hroot : Real.sqrt (I.gap d ^ 2 * (B : ℝ) / 4) ≤ 1 / 20 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · norm_num
    · nlinarith
  exact ((measure_mono hs).trans (A.returnedNotEvent_cap_measure_le I d hd hδ hcorrect B)).trans
    (ENNReal.ofReal_le_ofReal (by linarith))

end GapEntropy.Policy
