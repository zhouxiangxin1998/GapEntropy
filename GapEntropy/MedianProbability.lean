import GapEntropy.MedianFreshness
import GapEntropy.FiniteAdaptivity

/-!
# Failure probability of median elimination from independent rounds

`badNext` is the fixed-set event that the next active set loses more than `2ε` relative to the
best mean of the current set; it is measurable and is contained in the one-round failure event
of `PACRound`. Because the active set is independent of the current round vector, a uniform
fixed-set bound transfers to the actually selected set through
`FiniteAdaptivity.measure_adaptive_event_le`. Summing the per-round confidences `roundBeta` over
at most `|S|` rounds bounds the failure probability of `medianEliminate` by `β`. The fixed-set
premises are discharged separately from the actual Gaussian sample laws and declared sample
counts.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GapEntropy.MedianElimination

def badNext {n : ℕ} (μ : Fin n → ℝ) (ε : ℝ) (S : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {x | ¬ ∀ i ∈ S, ∃ b ∈ nextActive S x, μ i - 2 * ε ≤ μ b}

theorem measurableSet_badNext {n : ℕ} (μ : Fin n → ℝ) (ε : ℝ) (S : Finset (Fin n)) :
    MeasurableSet (badNext μ ε S) := by
  have h := nextActive_measurable (S := fun _ : Fin n → ℝ => S)
    measurable_const (fun i => measurable_pi_apply i)
  exact h (Set.toFinite
    {T : Finset (Fin n) | ¬ ∀ i ∈ S, ∃ b ∈ T, μ i - 2 * ε ≤ μ b}).measurableSet

theorem badNext_subset_failure {n : ℕ} {S : Finset (Fin n)} {μ : Fin n → ℝ}
    {ε : ℝ} (hε : 0 ≤ ε) {a : Fin n} (_ha : a ∈ S)
    (hmax : ∀ i ∈ S, μ i ≤ μ a) :
    badNext μ ε S ⊆ GapEntropy.PACRound.failureEvent S μ (fun i x => x i) a ε := by
  intro x hbad hgood
  apply hbad
  intro i hi
  by_cases hs : 2 ≤ S.card
  · obtain ⟨b, hb, hba⟩ := hgood
    refine ⟨b, ?_, ?_⟩
    · simpa only [nextActive, if_pos hs] using hb
    · linarith [hmax i hi]
  · refine ⟨i, ?_, ?_⟩
    · simpa only [nextActive, if_neg hs] using hi
    · linarith

theorem badNext_empty {n : ℕ} (μ : Fin n → ℝ) (ε : ℝ) :
    badNext μ ε ∅ = ∅ := by
  ext x
  simp [badNext]

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n : ℕ}

/-- Uniform fixed-set errors remain valid for the actual set selected by earlier rounds. -/
theorem random_round_failure_le (S : Finset (Fin n)) {μ : Fin n → ℝ} {ε δ : ℝ}
    {X : ℕ → Ω → (Fin n → ℝ)} (hX : ∀ r, Measurable (X r))
    (hind : iIndepFun X P) (r : ℕ)
    (hbound : ∀ T, P.real (X r ⁻¹' badNext μ (roundEpsilon ε r) T) ≤ δ) :
    P.real {ω | ¬ GoodRound S μ (fun k => X k ω) ε r} ≤ δ := by
  exact GapEntropy.FiniteAdaptivity.measure_adaptive_event_le
    (activeSets_measurable S (fun r i => (measurable_pi_apply i).comp (hX r)) r)
    (activeSets_indep_current hX hind S r)
    (measurableSet_badNext μ (roundEpsilon ε r)) hbound

/-- Finite independent-round composition. The Gaussian theorem below establishes all
fixed-set error premises from the actual sample laws and declared sample counts. -/
theorem medianEliminate_failure_le_of_independent_rounds
    {S : Finset (Fin n)} (hS : S.Nonempty) {μ : Fin n → ℝ} {ε β : ℝ}
    (hε : 0 ≤ ε) (hβ : 0 ≤ β) {X : ℕ → Ω → (Fin n → ℝ)}
    (hX : ∀ r, Measurable (X r)) (hind : iIndepFun X P)
    (hbound : ∀ r < S.card, ∀ T,
      P.real (X r ⁻¹' badNext μ (roundEpsilon ε r) T) ≤ roundBeta β r) :
    P.real {ω | ¬ ∀ i ∈ S, μ i - ε ≤ μ (medianEliminate S hS (fun k => X k ω))} ≤ β := by
  classical
  let E : ℕ → Set Ω := fun r => {ω | ¬ GoodRound S μ (fun k => X k ω) ε r}
  have hsubset : {ω | ¬ ∀ i ∈ S,
      μ i - ε ≤ μ (medianEliminate S hS (fun k => X k ω))} ⊆
      ⋃ r ∈ Finset.range S.card, E r := by
    intro ω hfail
    by_contra hnot
    apply hfail
    apply medianEliminate_pac_of_goodRounds hS hε
    intro r hr
    by_contra hbad
    exact hnot (Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr hr, hbad⟩⟩)
  calc
    _ ≤ P.real (⋃ r ∈ Finset.range S.card, E r) := measureReal_mono hsubset (measure_ne_top P _)
    _ ≤ ∑ r ∈ Finset.range S.card, P.real (E r) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ r ∈ Finset.range S.card, roundBeta β r := by
      apply Finset.sum_le_sum
      intro r hr
      exact random_round_failure_le S hX hind r (hbound r (Finset.mem_range.mp hr))
    _ ≤ β := cumulative_confidence hβ S.card

end Probability
end GapEntropy.MedianElimination
