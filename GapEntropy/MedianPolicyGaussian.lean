import GapEntropy.MedianPolicyFreshness
import GapEntropy.SortingCongruence

/-!
# A.2 for the actual interactive median policy

Conditioning on the finite-valued current active set is implemented by a finite
partition. The new block is independent of that set by the actual prefix theorem;
each fixed-set block interpretation satisfies the Gaussian round bound. Summing
the true round failure events gives the PAC guarantee for the actual returned arm.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.MedianPolicy
open MedianElimination GaussianBlocks

def actualEstimates {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (ε β : ℝ)
    (hn : 2 ≤ n) (ω : SampleSpace n) : ℕ → Fin n → ℝ :=
  estimates S ε β (historyValues (completedHistory S hS ε β hn ω))

def output {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (ε β : ℝ)
    (hn : 2 ≤ n) (ω : SampleSpace n) : Fin n :=
  outputFromHistory S hS ε β (completedHistory S hS ε β hn ω)

theorem measurable_output {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (ε β : ℝ)
    (hn : 2 ≤ n) : Measurable (output S hS ε β hn) :=
  (measurable_outputFromHistory S hS ε β).comp (measurable_historyAt S hS ε β hn _)

theorem output_eq_medianEliminate {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    output S hS ε β hn ω = medianEliminate S hS (actualEstimates S hS ε β hn ω) :=
  outputFromHistory_eq_medianEliminate S hS ε β _

theorem actualEstimates_eq_rawMean_on_active {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (r : ℕ) (hrs : r < S.card)
    (hr : 2 ≤ cardinalSchedule S.card r) (i : Fin n)
    (hi : i ∈ activeAt S hS ε β hn r ω) :
    actualEstimates S hS ε β hn ω r i = rawMean hn (activeAt S hS ε β hn r ω)
      (rewardBlock (start S.card ε β r) (n * roundSamples ε β r) ω) i := by
  rw [activeAt_eq_completed S hS ε β hn r hrs.le ω] at hi ⊢
  unfold actualEstimates estimates blockMean rawMean
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  have h := round_observation_eq_reward S hS ε β hn ω r hrs hr i hi j
  simpa only [rewardBlock, rawIndex, Nat.add_assoc] using h

theorem goodRound_iff_raw_block {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (mean : Fin n → ℝ) (ω : SampleSpace n)
    (r : ℕ) (hrs : r < S.card) (hr : 2 ≤ cardinalSchedule S.card r) :
    GoodRound S mean (actualEstimates S hS ε β hn ω) ε r ↔
      rawMean hn (activeAt S hS ε β hn r ω)
        (rewardBlock (start S.card ε β r) (n * roundSamples ε β r) ω) ∉
          badNext mean (roundEpsilon ε r) (activeAt S hS ε β hn r ω) := by
  have hset : activeSets S (actualEstimates S hS ε β hn ω) r = activeAt S hS ε β hn r ω := by
    rw [activeAt_eq_completed S hS ε β hn r hrs.le ω]
    exact (reconstruct_eq_activeSets S ε β _ r).symm
  have hnext := SortingCongruence.nextActive_congr_on (activeAt S hS ε β hn r ω)
    (actualEstimates_eq_rawMean_on_active S hS ε β hn ω r hrs hr)
  simp only [GoodRound, activeSets, hset, hnext, badNext, Set.mem_ofPred_eq, not_not]

/-- Gaussian round failure bound for the actual sampled active set. No round
success or independence premise is assumed about this policy. -/
theorem actual_goodRound_failure_le {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (r : ℕ) (hrs : r < S.card) :
    (sampleLawOfMeans mean).real
      {ω | ¬ GoodRound S mean (actualEstimates S hS ε β hn ω) ε r} ≤ roundBeta β r := by
  by_cases hr : 2 ≤ cardinalSchedule S.card r
  · let bad : Finset (Fin n) → Set (Fin (n * roundSamples ε β r) → Fin n → ℝ) :=
      fun U => rawMean hn U ⁻¹' badNext mean (roundEpsilon ε r) U
    have hb := FiniteAdaptivity.measure_adaptive_event_le
      (measurable_activeAt S hS ε β hn r)
      (indepFun_activeAt_rewardBlock S hS ε β hn mean r (n * roundSamples ε β r))
      (bad := bad)
      (fun U => (measurable_rawMean hn U) (measurableSet_badNext mean (roundEpsilon ε r) U))
      (fun U => rawMean_badNext_le hn S U mean hε hβ hβ1 r)
    have he : {ω | ¬ GoodRound S mean (actualEstimates S hS ε β hn ω) ε r} =
        {ω | rewardBlock (start S.card ε β r) (n * roundSamples ε β r) ω ∈
          bad (activeAt S hS ε β hn r ω)} := by
      ext ω
      simp only [Set.mem_ofPred_eq, goodRound_iff_raw_block S hS ε β hn mean ω r hrs hr,
        not_not, bad, Set.mem_preimage]
    rwa [he]
  · have hgood (ω : SampleSpace n) : GoodRound S mean (actualEstimates S hS ε β hn ω) ε r := by
      intro i hi
      refine ⟨i, ?_, ?_⟩
      · simpa only [activeSets, nextActive, activeSets_card, if_neg hr] using hi
      · have he := roundEpsilon_pos hε r
        linarith
    have he : {ω | ¬ GoodRound S mean (actualEstimates S hS ε β hn ω) ε r} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_not.mpr (hgood ω)
    rw [he, measureReal_empty]
    exact (roundBeta_pos hβ r).le

theorem output_failure_le {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (sampleLawOfMeans mean).real
      {ω | ¬ ∀ i ∈ S, mean i - ε ≤ mean (output S hS ε β hn ω)} ≤ β := by
  let E : ℕ → Set (SampleSpace n) := fun r =>
    {ω | ¬ GoodRound S mean (actualEstimates S hS ε β hn ω) ε r}
  have hsubset : {ω | ¬ ∀ i ∈ S, mean i - ε ≤ mean (output S hS ε β hn ω)} ⊆
      ⋃ r ∈ Finset.range S.card, E r := by
    intro ω hbad
    by_contra hnot
    apply hbad
    rw [output_eq_medianEliminate]
    apply medianEliminate_pac_of_goodRounds hS hε.le
    intro r hr
    by_contra hfail
    exact hnot (Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr hr, hfail⟩⟩)
  calc
    _ ≤ (sampleLawOfMeans mean).real (⋃ r ∈ Finset.range S.card, E r) :=
      measureReal_mono hsubset (measure_ne_top _ _)
    _ ≤ ∑ r ∈ Finset.range S.card, (sampleLawOfMeans mean).real (E r) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ Finset.range S.card, roundBeta β r :=
      Finset.sum_le_sum (fun r hr => actual_goodRound_failure_le S hS hn mean hε hβ hβ1 r
        (Finset.mem_range.mp hr))
    _ ≤ β := cumulative_confidence hβ.le S.card

theorem output_success_ge {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    1 - β ≤ (sampleLawOfMeans mean).real
      {ω | ∀ i ∈ S, mean i - ε ≤ mean (output S hS ε β hn ω)} := by
  have hgood : MeasurableSet {ω | ∀ i ∈ S, mean i - ε ≤ mean (output S hS ε β hn ω)} :=
    (measurable_output S hS ε β hn) (Set.toFinite {a | ∀ i ∈ S, mean i - ε ≤ mean a}).measurableSet
  have hf := output_failure_le S hS hn mean hε hβ hβ1
  have hc := measureReal_compl (μ := sampleLawOfMeans mean) hgood
  rw [probReal_univ] at hc
  change (sampleLawOfMeans mean).real
    {ω | ¬ ∀ i ∈ S, mean i - ε ≤ mean (output S hS ε β hn ω)} = _ at hc
  linarith

/-- Full A.2 guarantee for the concrete interactive policy under the actual
reward-table law, including the operational return and pathwise charged count. -/
theorem medianElimination_A2 {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) {ε β : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    Measurable (output S hS ε β hn) ∧
    (∀ ω, output S hS ε β hn ω ∈ S) ∧
    (∀ ω, (policy S hS ε β).returnedAt hn (declaredCost S.card ε β + 1) ω =
      some (output S hS ε β hn ω)) ∧
    (1 - β ≤ (sampleLawOfMeans mean).real
      {ω | ∀ i ∈ S, mean i - ε ≤ mean (output S hS ε β hn ω)}) ∧
    (∀ ω, (policy S hS ε β).sampleCount hn ω = declaredCost S.card ε β) ∧
    (declaredCost S.card ε β : ℝ) ≤
      100000 * (S.card : ℝ) * (ε ^ 2)⁻¹ * Real.log (8 / β) := by
  exact ⟨measurable_output S hS ε β hn,
    fun ω => outputFromHistory_mem S hS ε β _,
    run_return_at_budget S hS ε β hn,
    output_success_ge S hS hn mean hε hβ hβ1,
    sampleCount_eq_declaredCost S hS ε β hn,
    declaredCost_le hS.card_pos hε hε1 hβ hβ1⟩

end GapEntropy.MedianPolicy
