import GapEntropy.UniversalCallFreshness

/-! # Exact set readouts and their parameter measurability -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical
namespace GapEntropy.UniversalCall
open EliminationTape GaussianBlocks
variable {n : ℕ}

theorem padded_congr_on (S : Finset (Fin n)) {x y : Fin n → ℝ} (z d : ℝ)
    (hxy : ∀ i ∈ S, x i = y i) : Elimination.padded S x z d = Elimination.padded S y z d := by
  have hr : Elimination.raw S x z d = Elimination.raw S y z d := by
    apply Finset.filter_congr
    intro i hi
    rw [hxy i hi]
  simp only [Elimination.padded, hr, SortingCongruence.upperHalf_congr_on S hxy]

theorem entry_actualOutput_eq (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (ω : SampleSpace n) :
    (entryProcedure S hS d α β).actualOutput ω =
      (referenceEstimate S hS d α β ω, Elimination.padded S
        (scheduleEstimate S (activeStart S.card d α β) (activeSamples d α) ω)
        (referenceEstimate S hS d α β ω) d) := by
  apply Prod.ext
  · rfl
  · exact padded_congr_on S _ d (entryEstimate_eq_schedule S hS d α β ω)

theorem later_actualOutput_eq (S : Finset (Fin n)) (hS : S.Nonempty) (d α z : ℝ)
    (ω : SampleSpace n) :
    (laterProcedure S hS d α z).actualOutput ω =
      Elimination.padded S (scheduleEstimate S 0 (activeSamples d α) ω) z d :=
  padded_congr_on S z d (laterEstimate_eq_schedule S hS d α z ω)

theorem later_evaluate_eq (S : Finset (Fin n)) (hS : S.Nonempty) (d α z : ℝ)
    (v : (laterProcedure S hS d α z).Tape) :
    (laterProcedure S hS d α z).evaluate v =
      Elimination.padded S (blockEstimates S hS (activeSamples d α) v) z d := by
  let ω := EliminationPolicy.sampleFromBlock (laterBudget S.card d α) v
  have hb : rewardBlock 0 (laterBudget S.card d α) ω = v :=
    EliminationPolicy.rewardBlock_sampleFromBlock _ v
  have he := later_actualOutput_eq S hS d α z ω
  change (laterProcedure S hS d α z).evaluate
    (rewardBlock 0 (laterBudget S.card d α) ω) = _ at he
  rw [hb] at he
  have hm := blockEstimates_rewardBlock S hS 0 (activeSamples d α) ω
  change blockEstimates S hS (activeSamples d α)
    (rewardBlock 0 (laterBudget S.card d α) ω) = _ at hm
  rw [hb] at hm
  exact he.trans (congrArg (fun x => Elimination.padded S x z d) hm.symm)

/-- The entire later-call finite-tape evaluator is jointly measurable in z and
the fresh tape, even though z ranges over an uncountable space. -/
theorem measurable_later_evaluate (S : Finset (Fin n)) (hS : S.Nonempty) (d α : ℝ) :
    Measurable (fun p : ℝ × (Fin (laterBudget S.card d α) → Fin n → ℝ) =>
      (laterProcedure S hS d α p.1).evaluate p.2) := by
  have he : (fun p : ℝ × (Fin (laterBudget S.card d α) → Fin n → ℝ) =>
      (laterProcedure S hS d α p.1).evaluate p.2) =
      (fun p => Elimination.padded S (blockEstimates S hS (activeSamples d α) p.2) p.1 d) :=
    funext (fun p => later_evaluate_eq S hS d α p.1 p.2)
  rw [he]
  exact SortingMeasurability.padded_measurable measurable_const
    (fun i => (measurable_pi_apply i).comp
      ((measurable_blockEstimates S hS (activeSamples d α)).comp measurable_snd))
    measurable_fst measurable_const

theorem entry_evaluate_subset (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (v : (entryProcedure S hS d α β).Tape) : ((entryProcedure S hS d α β).evaluate v).2 ⊆ S :=
  Elimination.padded_subset _ _ _ _

theorem later_evaluate_subset (S : Finset (Fin n)) (hS : S.Nonempty) (d α z : ℝ)
    (v : (laterProcedure S hS d α z).Tape) : (laterProcedure S hS d α z).evaluate v ⊆ S :=
  Elimination.padded_subset _ _ _ _

theorem entry_evaluate_nonempty (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (v : (entryProcedure S hS d α β).Tape) : ((entryProcedure S hS d α β).evaluate v).2.Nonempty := by
  apply Finset.card_pos.mp
  have hh : (S.card + 1) / 2 ≤ ((entryProcedure S hS d α β).evaluate v).2.card :=
    Elimination.padded_card_ge_half S _ _ _
  have hp := hS.card_pos
  omega

theorem later_evaluate_nonempty (S : Finset (Fin n)) (hS : S.Nonempty) (d α z : ℝ)
    (v : (laterProcedure S hS d α z).Tape) : ((laterProcedure S hS d α z).evaluate v).Nonempty := by
  apply Finset.card_pos.mp
  have hh : (S.card + 1) / 2 ≤ ((laterProcedure S hS d α z).evaluate v).card :=
    Elimination.padded_card_ge_half S _ _ _
  have hp := hS.card_pos
  omega

end GapEntropy.UniversalCall
