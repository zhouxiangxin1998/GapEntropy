import GapEntropy.BinaryTesting

/-!
# Passing finite-horizon statistical tests to the return event

Only finite transcript KL bounds are used. The source event probabilities have
the stated supremum; the target may never terminate. Right continuity in the
confidence level recovers the exact `log(1/δ)` constant without assuming that a
finite horizon already captures all successful returns.
-/

open MeasureTheory
open scoped ENNReal

namespace GapEntropy

theorem log_inv_le_of_right_neighborhood {δ K : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1 / 10)
    (h : ∀ η : ℝ, δ < η → η < 1 / 10 → Real.log η⁻¹ ≤ K) :
    Real.log δ⁻¹ ≤ K := by
  have hx : δ ∈ closure (Set.Ioo δ (1 / 10 : ℝ)) := by
    rw [closure_Ioo hδ1.ne]
    exact ⟨le_rfl, hδ1.le⟩
  have hf : ContinuousWithinAt (fun x : ℝ => Real.log x⁻¹)
      (Set.Ioo δ (1 / 10 : ℝ)) δ := by
    simp_rw [Real.log_inv]
    exact (Real.continuousAt_log hδ0.ne').neg.continuousWithinAt
  exact ContinuousWithinAt.closure_le hx hf continuousWithinAt_const
    (fun η hη => h η hη.1 hη.2)

section Families

variable {Ω : ℕ → Type*} [∀ T, MeasurableSpace (Ω T)]
  (P Q : ∀ T, Measure (Ω T))
  [∀ T, IsProbabilityMeasure (P T)] [∀ T, IsProbabilityMeasure (Q T)]
  (E : ∀ T, Set (Ω T)) (hE : ∀ T, MeasurableSet (E T))

include hE

/-- Exact confidence cost from bounded finite-horizon information and a source
return probability at least `1-δ`. -/
theorem confidence_lower_bound_of_finite_horizons {δ K : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1 / 10) (hK : 0 ≤ K)
    (hp : ENNReal.ofReal (1 - δ) ≤ ⨆ T, P T (E T))
    (hq : ∀ T, Q T (E T) ≤ ENNReal.ofReal δ)
    (hKL : ∀ T, InformationTheory.klDiv (P T) (Q T) ≤ ENNReal.ofReal (K / 2)) :
    Real.log δ⁻¹ ≤ K := by
  apply log_inv_le_of_right_neighborhood hδ0 hδ1
  intro η hδη hη
  have hη0 : 0 < η := hδ0.trans hδη
  have hη1 : η < 1 := by linarith
  have hstrict : ENNReal.ofReal (1 - η) < ⨆ T, P T (E T) := by
    apply lt_of_lt_of_le _ hp
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : 0 < 1 - δ)).2 (by linarith)
  obtain ⟨T, hT⟩ := lt_iSup_iff.mp hstrict
  have hpT : 1 - η ≤ (P T).real (E T) := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) hT.le
    simpa only [ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - η), measureReal_def] using hh
  have hqT : (Q T).real (E T) ≤ η := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((hq T).trans (ENNReal.ofReal_le_ofReal hδη.le))
    simpa only [ENNReal.toReal_ofReal hη0.le, measureReal_def] using hh
  have htest := (measure_event_confidence_lower_bound (P T) (Q T) (hE T) η hη0 hη hpT hqT).trans
    (hKL T)
  have hh := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ K / 2)).1 htest
  linarith

/-- A strict source probability above one half is already witnessed at some
finite horizon. Thus the full target event inherits the exponential transfer
bound from finite transcript KL, even if the target policy does not terminate. -/
theorem event_transfer_of_finite_horizons {a b : ℝ} {q : ℝ≥0∞}
    (hab : 0 ≤ a + b)
    (hp : ENNReal.ofReal (1 / 2 : ℝ) < ⨆ T, P T (E T))
    (hq : ∀ T, Q T (E T) ≤ q)
    (hKL : ∀ T, InformationTheory.klDiv (P T) (Q T) ≤ ENNReal.ofReal ((a + b) / 2)) :
    ENNReal.ofReal (Real.exp (-(a + b)) / 4) ≤ q := by
  obtain ⟨T, hT⟩ := lt_iSup_iff.mp hp
  have hpT : 1 / 2 ≤ (P T).real (E T) := by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) hT.le
    simpa only [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (1 / 2 : ℝ)), measureReal_def] using hh
  have ht := measure_event_transfer (P T) (Q T) (hE T) a b hpT hab (hKL T)
  have hh := ENNReal.ofReal_le_ofReal ht
  rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hh
  exact hh.trans (hq T)

end Families

end GapEntropy
