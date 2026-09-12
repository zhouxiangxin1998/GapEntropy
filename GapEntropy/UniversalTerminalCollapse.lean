import GapEntropy.UniversalTerminalAccounting

/-! Actual wrong terminal core events imply the fixed Gaussian batch comparisons. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators
namespace GapEntropy
namespace Elimination
variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
/-- The actual stable sorting rule depends only on estimates of active arms, including ties. -/
theorem ranking_congr_on (S : Finset ι) {x y : ι → ℝ}
    (hxy : ∀ i ∈ S, x i = y i) : ranking S x = ranking S y := by
  have h := List.map_mergeSort (f := id) (l := S.toList)
    (r := fun i j => decide (x j ≤ x i)) (s := fun i j => decide (y j ≤ y i))
    (fun i hi j hj => by
      simp only [id_eq, hxy i (Finset.mem_toList.mp hi), hxy j (Finset.mem_toList.mp hj)])
  simpa only [List.map_id_fun, id_eq, ranking] using h

theorem upperHalf_congr_on (S : Finset ι) {x y : ι → ℝ}
    (hxy : ∀ i ∈ S, x i = y i) : upperHalf S x = upperHalf S y := by
  unfold upperHalf
  rw [ranking_congr_on S hxy]

theorem padded_congr_on (S : Finset ι) {x y : ι → ℝ} (z d : ℝ)
    (hxy : ∀ i ∈ S, x i = y i) : padded S x z d = padded S y z d := by
  have hr : raw S x z d = raw S y z d := by
    apply Finset.filter_congr
    intro i hi
    rw [hxy i hi]
  rw [padded, padded, hr, upperHalf_congr_on S hxy]

end Elimination
namespace BatchCollapse
variable {n : ℕ}

theorem collapse_congr_on (S B : Finset (Fin n)) {x y : Fin n → ℝ} (z d : ℝ)
    (hxy : ∀ i ∈ S, x i = y i) : collapse S B x z d ↔ collapse S B y z d := by
  unfold collapse
  rw [Elimination.padded_congr_on S z d hxy]

end BatchCollapse
namespace UniversalAttempt
open UniversalSevereProcess UniversalBatchCollapse UniversalCall
variable {n : ℕ} (c : Config) (I : Instance n) (ω : SampleSpace n) (T : ℕ)
  (haccepted : ∀ t < T, ∃ a z, stage c ω.2 t = .inr (a, z) ∧ a.Allowed c)

/-- Eligible collapse in the actual extracted trajectory triggers the actual selected-block
comparison. Estimate equality is required and proved only on the active set. -/
theorem terminal_eligibleCollapse_implies_selectedComparison (B : Finset (Fin n))
    (hv : (terminalTrajectory c ω.2 T haccepted).UpperValid I) (t : ℕ)
    (he : (terminalTrajectory c ω.2 T haccepted).EligibleCollapse I B t) :
    selectedComparison c I B t ω = true := by
  obtain ⟨ht, hs8, hnonempty, hgap, hcollapse⟩ := he
  obtain ⟨a, z, hs, ha⟩ := haccepted t ht
  have hv' := hv t ht
  change observedReference c ω.2 t ≤ I.mean I.best +
    (metadataOfStage (stage c ω.2 t)).tolerance / 16 at hv'
  change 8 ≤ (metadataOfStage (stage c ω.2 t)).active.card at hs8
  change ((metadataOfStage (stage c ω.2 t)).active ∩ B).Nonempty at hnonempty
  change ∀ i ∈ B, I.gap i ≤ (metadataOfStage (stage c ω.2 t)).tolerance / 8 at hgap
  change BatchCollapse.collapse (metadataOfStage (stage c ω.2 t)).active B
    (observedEstimates c ω.2 t) (observedReference c ω.2 t)
    (metadataOfStage (stage c ω.2 t)).tolerance at hcollapse
  simp only [hs, metadataOfStage, observedEstimates, observedReference, dif_pos ha]
    at hs8 hnonempty hgap hcollapse hv'
  apply selectedComparison_true_of_collapse c I B t ω ⟨a, ha⟩
    (severe_choice_of_pending c ω t a ha z hs) ⟨hs8, hnonempty, hgap⟩ hv'
  apply (BatchCollapse.collapse_congr_on a.active B _ _ ?_).mp hcollapse
  intro i hi
  exact callObservedEstimates_eq_schedule c ω a ha z i hi

/-- Every true wrong terminal core trajectory outside the two exceptional events has an
actual eligible Gaussian comparison on its chronological call path. -/
theorem coreFailure_subset_comparisons (B : Finset (Fin n)) :
    CoreFailure c I B ⊆ ⋃ r, {ω | selectedComparison c I B r ω = true} := by
  rintro ω ⟨T, ha, out, hf, hw, hv, hsmall, hB⟩
  obtain ⟨t, ht⟩ := (terminalTrajectory c ω.2 T ha).wrong_singleton_fixed_core_exists_eligible_collapse
    I hv hsmall B hB hf hw
  exact Set.mem_iUnion.mpr ⟨t, terminal_eligibleCollapse_implies_selectedComparison c I ω T ha B hv t ht⟩

/-- Actual terminal-event E.12: no padded-update, Gaussian-law, or collapse-probability premise. -/
theorem probability_coreFailure_le_batch (hδ : ValidConfidence c.confidence)
    (B : Finset (Fin n)) (hbest : I.best ∈ B)
    (hh : 0 < BatchCollapse.outsideHardness I B)
    (hhM : BatchCollapse.outsideHardness I B ≤ c.workCap) :
    sampleLawOfMeans I.mean (CoreFailure c I B) ≤
      ENNReal.ofReal (3 * eta c ^ (4 : ℕ) *
        (BatchCollapse.outsideHardness I B / c.workCap) ^ (3 : ℕ)) :=
  (measure_mono (coreFailure_subset_comparisons c I B)).trans
    (probability_any_comparison_le c hδ I B hbest hh hhM)

end UniversalAttempt
end GapEntropy
