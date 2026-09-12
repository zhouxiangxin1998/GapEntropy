import GapEntropy.AttemptLocalBounds

/-!
# Adaptive bad events of the actual finite attempt

An adaptive event evaluates a per-request bad set of the current call tape at the request
actually made by the earlier calls. Because the request is independent of its own canonical
tape, the uniform A.3 bound for fixed requests lifts to the adaptive event without any
conditional success assumption; the proof goes through
`FiniteAdaptivity.measure_adaptive_event_le`.

`allBad` collects the bad events of every loop key and of the final key. Its probability under
the attempt law is at most `ε`, because the call confidences sum to at most `ε`. The final
theorems give this bound for the best-removal events under any instance and for the full C.2
target events under every relabeling of the target instance.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GapEntropy.AttemptExperiment
open GapEntropy.TargetAttempt
variable {n : ℕ}

def adaptiveEvent (I J : Instance n) (ε : ℝ) (key : CallKey)
    (B : Option (Finset (Fin n)) → Set (CallTape I ε key)) : Set (Space I ε) :=
  {ω | ω key ∈ B (request I J ε key ω)}

theorem adaptiveEvent_measurable (I J : Instance n) (ε : ℝ) (key : CallKey)
    (B : Option (Finset (Fin n)) → Set (CallTape I ε key)) (hB : ∀ S, MeasurableSet (B S)) :
    MeasurableSet (adaptiveEvent I J ε key B) := by
  have he : Measurable (fun ω : Space I ε => ω key) := measurable_pi_apply _
  have hrep : adaptiveEvent I J ε key B =
      ⋃ S : Option (Finset (Fin n)), (request I J ε key ⁻¹' {S}) ∩
        (fun ω : Space I ε => ω key) ⁻¹' B S := by
    ext ω
    simp only [adaptiveEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => ⟨request I J ε key ω, rfl, h⟩, fun ⟨_, h, hB⟩ => h ▸ hB⟩
  rw [hrep]
  exact MeasurableSet.iUnion (fun S =>
    ((request_measurable I J ε key) (measurableSet_singleton S)).inter (he (hB S)))

/-- The request is independent of its current canonical tape, so the uniform A.3
bound lifts to the actual adaptive call without a conditional-success assumption. -/
theorem adaptiveEvent_le (I J : Instance n) (ε : ℝ) (key : CallKey)
    (B : Option (Finset (Fin n)) → Set (CallTape I ε key)) (hB : ∀ S, MeasurableSet (B S))
    {δ : ℝ} (hbound : ∀ S, (localLaw I J ε key).real (B S) ≤ δ) :
    (law I J ε).real (adaptiveEvent I J ε key B) ≤ δ := by
  apply GapEntropy.FiniteAdaptivity.measure_adaptive_event_le
    (request_measurable I J ε key) (request_independent_current I J ε key) hB
  intro S
  rw [(call_preserving I J ε key).measureReal_preimage (hB S).nullMeasurableSet]
  exact hbound S

def allBad (I : Instance n) {Ω : Type*} (E : CallKey → Set Ω) : Set Ω :=
  (⋃ k ∈ Finset.range (I.lastBucket + 1), ⋃ r ∈ Finset.range n, E (.loop k r)) ∪ E .final

theorem loop_subset_allBad (I : Instance n) {Ω : Type*} (E : CallKey → Set Ω)
    {k r : ℕ} (hk : k < I.lastBucket + 1) (hr : r < n) : E (.loop k r) ⊆ allBad I E := by
  intro ω hω
  exact Or.inl (Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hk,
    Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hr, hω⟩⟩⟩⟩)

theorem final_subset_allBad (I : Instance n) {Ω : Type*} (E : CallKey → Set Ω) :
    E .final ⊆ allBad I E := Set.subset_union_right

theorem allBad_measurable (I : Instance n) {Ω : Type*} [MeasurableSpace Ω]
    (E : CallKey → Set Ω) (hE : ∀ key, MeasurableSet (E key)) : MeasurableSet (allBad I E) :=
  (MeasurableSet.iUnion (fun _ => MeasurableSet.iUnion (fun _ =>
    MeasurableSet.iUnion (fun _ => MeasurableSet.iUnion (fun _ => hE _))))).union (hE .final)

theorem allBad_le (I : Instance n) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {ε : ℝ} (hε : 0 ≤ ε)
    (E : CallKey → Set Ω)
    (hE : ∀ key, ValidKey I key → P.real (E key) ≤ callConfidence I ε key) :
    P.real (allBad I E) ≤ ε := by
  calc
    _ ≤ P.real (⋃ k ∈ Finset.range (I.lastBucket + 1),
        ⋃ r ∈ Finset.range n, E (.loop k r)) + P.real (E .final) := measureReal_union_le _ _
    _ ≤ (∑ k ∈ Finset.range (I.lastBucket + 1),
        ∑ r ∈ Finset.range n, P.real (E (.loop k r))) + P.real (E .final) := by
      apply add_le_add _ le_rfl
      exact (measureReal_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum (fun k _ => measureReal_biUnion_finset_le _ _))
    _ ≤ (∑ k ∈ Finset.range (I.lastBucket + 1),
        ∑ r ∈ Finset.range n, I.callConfidence ε k r) + ε / 2 := by
      apply add_le_add _ (hE .final trivial)
      exact Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun r _ =>
        hE (.loop k r) (Nat.le_of_lt_succ (Finset.mem_range.mp hk))))
    _ ≤ ε := I.all_callConfidence_le hε n

def removalEvent (I J : Instance n) (ε : ℝ) (key : CallKey) : Set (Space I ε) :=
  adaptiveEvent I J ε key (removalBad I J ε key)

def targetEvent (I J : Instance n) (ε : ℝ) (key : CallKey) : Set (Space I ε) :=
  adaptiveEvent I J ε key (targetBad I J ε key)

theorem removalEvent_measurable (I J : Instance n) (ε : ℝ) (key : CallKey) :
    MeasurableSet (removalEvent I J ε key) :=
  adaptiveEvent_measurable I J ε key _ (removalBad_measurable I J ε key)

theorem targetEvent_measurable (I J : Instance n) (ε : ℝ) (key : CallKey) :
    MeasurableSet (targetEvent I J ε key) :=
  adaptiveEvent_measurable I J ε key _ (targetBad_measurable I J ε key)

theorem all_removalEvent_le (I J : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (law I J ε).real (allBad I (removalEvent I J ε)) ≤ ε :=
  allBad_le I hε.le _ (fun key hkey => adaptiveEvent_le I J ε key _
    (removalBad_measurable I J ε key) (removalBad_le I J hε hε10 key hkey))

theorem all_targetEvent_le (I : Instance n) (π : Equiv.Perm (Fin n)) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (law I (I.permute π) ε).real (allBad I (targetEvent I (I.permute π) ε)) ≤ ε :=
  allBad_le I hε.le _ (fun key hkey => adaptiveEvent_le I (I.permute π) ε key _
    (targetBad_measurable I (I.permute π) ε key) (targetBad_le I π hε hε10 key hkey))

end GapEntropy.AttemptExperiment
