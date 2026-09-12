import GapEntropy.UniversalCallProgress

/-! # Actual entry-call progress, including its one-time reference failures -/
noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical
namespace GapEntropy.UniversalCall
open EliminationTape GaussianBlocks Elimination
variable {n : ℕ}

theorem entry_best_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (mean : Fin n → ℝ) {best : Fin n} (hbest : best ∈ S) {d α β : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1)
    (E : Set (SeedPrefix n (activeStart S.card d α β))) (hE : MeasurableSet E) :
    (sampleLawOfMeans mean).real {ω | seedPrefix (activeStart S.card d α β) ω ∈ E ∧
      Suitable (mean best) d (referenceEstimate S hS d α β ω) ∧
      best ∉ ((entryProcedure S hS d α β).actualOutput ω).2} ≤
      (sampleLawOfMeans mean).real ((seedPrefix (activeStart S.card d α β)) ⁻¹' E) * (α / 64) := by
  simp_rw [entry_actualOutput_eq]
  exact progress_best_on_past_le S hS _ mean hbest hd hα hα1 (referenceEstimate S hS d α β) E hE

theorem entry_halving_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (mean : Fin n → ℝ) {best : Fin n} {d α β : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1)
    (E : Set (SeedPrefix n (activeStart S.card d α β))) (hE : MeasurableSet E)
    {N : ℕ} (hnear : (near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (sampleLawOfMeans mean).real {ω | seedPrefix (activeStart S.card d α β) ω ∈ E ∧
      Suitable (mean best) d (referenceEstimate S hS d α β ω) ∧
      ((entryProcedure S hS d α β).actualOutput ω).2.card ≠ (S.card + 1) / 2} ≤
      (sampleLawOfMeans mean).real ((seedPrefix (activeStart S.card d α β)) ⁻¹' E) * (α / 16) := by
  simp_rw [entry_actualOutput_eq]
  exact progress_halving_on_past_le S hS _ mean hd hα hα1 (referenceEstimate S hS d α β) E hE hnear hs

/-- The raw set formed from the same actual entry estimates, before padding. -/
def entryRawOutput (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ) (ω : SampleSpace n) :
    Finset (Fin n) := raw S (entryEstimate S hS d α β ω) (referenceEstimate S hS d α β ω) d

theorem entryRawOutput_eq_schedule (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (ω : SampleSpace n) :
    entryRawOutput S hS d α β ω = raw S
      (scheduleEstimate S (activeStart S.card d α β) (activeSamples d α) ω)
      (referenceEstimate S hS d α β ω) d := by
  apply Finset.filter_congr
  intro i hi
  rw [entryEstimate_eq_schedule S hS d α β ω i hi]

theorem entry_isolation_on_past_le (S : Finset (Fin n)) (hS : S.Nonempty)
    (mean : Fin n → ℝ) {best : Fin n} (hbest : best ∈ S) {d α β : ℝ}
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1)
    (E : Set (SeedPrefix n (activeStart S.card d α β))) (hE : MeasurableSet E)
    (hs : S.card ≤ 4) (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    (sampleLawOfMeans mean).real {ω | seedPrefix (activeStart S.card d α β) ω ∈ E ∧
      Suitable (mean best) d (referenceEstimate S hS d α β ω) ∧
      entryRawOutput S hS d α β ω ≠ {best}} ≤
      (sampleLawOfMeans mean).real ((seedPrefix (activeStart S.card d α β)) ⁻¹' E) * (α / 16) := by
  simp_rw [entryRawOutput_eq_schedule]
  exact progress_isolation_on_past_le S hS _ mean hbest hd hα hα1
    (referenceEstimate S hS d α β) E hE hs hgaps

private theorem failure_le_bad_reference_add {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (G F : Set Ω) {a b : ℝ}
    (hbad : P.real Gᶜ ≤ a) (hfail : P.real (G ∩ F) ≤ b) : P.real F ≤ a + b := by
  have hs : F ⊆ Gᶜ ∪ (G ∩ F) := by
    intro ω hω
    by_cases hg : ω ∈ G
    · exact Or.inr ⟨hg, hω⟩
    · exact Or.inl hg
  exact ((measureReal_mono hs (measure_ne_top P _)).trans (measureReal_union_le _ _)).trans
    (add_le_add hbad hfail)

variable (S : Finset (Fin n)) (hS : S.Nonempty) (hn : 2 ≤ n) (mean : Fin n → ℝ)
  {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, mean i ≤ mean best)
  {d α β : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
include hn hbest hmax hd hα hα1 hβ hβ1

theorem entry_best_failure_le :
    (sampleLawOfMeans mean).real {ω | best ∉ ((entryProcedure S hS d α β).actualOutput ω).2} ≤
      5 * α / 64 + β := by
  have hg := entry_best_on_past_le (β := β) S hS mean hbest hd hα hα1 Set.univ MeasurableSet.univ
  simp only [Set.mem_univ, true_and, Set.preimage_univ, probReal_univ, one_mul] at hg
  have hh := failure_le_bad_reference_add
    {ω | Suitable (mean best) d (referenceEstimate S hS d α β ω)}
    {ω | best ∉ ((entryProcedure S hS d α β).actualOutput ω).2}
    (reference_unsuitable_le S hS hn mean hbest hmax hd hα hα1 hβ hβ1) hg
  linarith

theorem entry_halving_failure_le {N : ℕ}
    (hnear : (near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (sampleLawOfMeans mean).real
      {ω | ((entryProcedure S hS d α β).actualOutput ω).2.card ≠ (S.card + 1) / 2} ≤ α / 8 + β := by
  have hg := entry_halving_on_past_le (β := β) S hS mean hd hα hα1 Set.univ MeasurableSet.univ hnear hs
  simp only [Set.mem_univ, true_and, Set.preimage_univ, probReal_univ, one_mul] at hg
  have hh := failure_le_bad_reference_add
    {ω | Suitable (mean best) d (referenceEstimate S hS d α β ω)}
    {ω | ((entryProcedure S hS d α β).actualOutput ω).2.card ≠ (S.card + 1) / 2}
    (reference_unsuitable_le S hS hn mean hbest hmax hd hα hα1 hβ hβ1) hg
  linarith

theorem entry_raw_isolation_failure_le (hs : S.card ≤ 4)
    (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    (sampleLawOfMeans mean).real {ω | entryRawOutput S hS d α β ω ≠ {best}} ≤ α / 8 + β := by
  have hg := entry_isolation_on_past_le (β := β) S hS mean hbest hd hα hα1 Set.univ MeasurableSet.univ hs hgaps
  simp only [Set.mem_univ, true_and, Set.preimage_univ, probReal_univ, one_mul] at hg
  have hh := failure_le_bad_reference_add
    {ω | Suitable (mean best) d (referenceEstimate S hS d α β ω)}
    {ω | entryRawOutput S hS d α β ω ≠ {best}}
    (reference_unsuitable_le S hS hn mean hbest hmax hd hα hα1 hβ hβ1) hg
  linarith

theorem entry_best_block_failure_le :
    (blockLaw mean (entryBudget S.card d α β)).real
      {v | best ∉ ((entryProcedure S hS d α β).evaluate v).2} ≤ 5 * α / 64 + β := by
  have he := (entryProcedure S hS d α β).actualOutput_event mean
    {p : ℝ × Finset (Fin n) | best ∉ p.2}
    ((MeasurableSet.of_discrete : MeasurableSet {U : Finset (Fin n) | best ∉ U}).preimage measurable_snd)
  exact (congrArg ENNReal.toReal he).symm.trans_le
    (entry_best_failure_le S hS hn mean hbest hmax hd hα hα1 hβ hβ1)

theorem entry_halving_block_failure_le {N : ℕ}
    (hnear : (near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (blockLaw mean (entryBudget S.card d α β)).real
      {v | ((entryProcedure S hS d α β).evaluate v).2.card ≠ (S.card + 1) / 2} ≤ α / 8 + β := by
  have he := (entryProcedure S hS d α β).actualOutput_event mean
    {p : ℝ × Finset (Fin n) | p.2.card ≠ (S.card + 1) / 2}
    ((MeasurableSet.of_discrete : MeasurableSet
      {U : Finset (Fin n) | U.card ≠ (S.card + 1) / 2}).preimage measurable_snd)
  exact (congrArg ENNReal.toReal he).symm.trans_le
    (entry_halving_failure_le S hS hn mean hbest hmax hd hα hα1 hβ hβ1 hnear hs)

end GapEntropy.UniversalCall
