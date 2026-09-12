import GapEntropy.UniversalSevereProcess
import GapEntropy.UniversalPathIndices
import GapEntropy.UniversalCallEquivalence
import GapEntropy.UniversalCallGuarantees
import GapEntropy.UniversalTerminalObservations
import GapEntropy.UniversalErrorBudget

/-! Actual scale-entry reference failures and inheritance of the stored numerical reference. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram UniversalCall GaussianBlocks UniversalSevereProcess
variable {n : ℕ}

abbrev EntryAt (c : Config) (n k : ℕ) :=
  {a : Accepted c n // a.val.entry = true ∧ a.val.scale = k}

def entryReference (c : Config) (a : Accepted c n) (ω : SampleSpace n) : ℝ :=
  ((entryProcedure a.val.active
    (Finset.card_pos.mp (by have := a.property.1; omega)) a.val.tolerance (a.val.alpha c) (a.val.beta c)).evaluate
      (rewardBlock a.val.samples (entryBudget a.val.active.card a.val.tolerance (a.val.alpha c) (a.val.beta c)) ω)).1

theorem measurable_entryReference (c : Config) (a : Accepted c n) : Measurable (entryReference c a) :=
  ((entryProcedure a.val.active _ _ _ _).measurable_evaluate.comp (measurable_rewardBlock _ _)).fst

def entryCell (c : Config) (k : ℕ) (q : ℕ × EntryAt c n k) : Set (SampleSpace n) :=
  {ω | choice c q.1 ω = some q.2.val}

def entryBadCell (c : Config) (μstar : ℝ) (k : ℕ) (q : ℕ × EntryAt c n k) : Set (SampleSpace n) :=
  entryCell c k q ∩ {ω | μstar + q.2.val.val.tolerance / 16 < entryReference c q.2.val ω}

def referenceFailureAtScale (c : Config) (μstar : ℝ) (k : ℕ) : Set (SampleSpace n) :=
  ⋃ q : ℕ × EntryAt c n k, entryBadCell c μstar k q

def ReferenceFailure (c : Config) (μstar : ℝ) : Set (SampleSpace n) :=
  ⋃ k, referenceFailureAtScale c μstar k

theorem measurableSet_entryCell (c : Config) (k : ℕ) (q : ℕ × EntryAt c n k) :
    MeasurableSet (entryCell c k q) :=
  (((choice_adapted c q.1).mono ((callFiltration c).le q.1) le_rfl).eq_const _).setOf

theorem measurableSet_entryBadCell (c : Config) (μstar : ℝ) (k : ℕ) (q : ℕ × EntryAt c n k) :
    MeasurableSet (entryBadCell c μstar k q) :=
  (measurableSet_entryCell c k q).inter (measurableSet_lt measurable_const (measurable_entryReference c q.2.val))

theorem measurableSet_referenceFailureAtScale (c : Config) (μstar : ℝ) (k : ℕ) :
    MeasurableSet (referenceFailureAtScale (n := n) c μstar k) :=
  MeasurableSet.iUnion (measurableSet_entryBadCell c μstar k)

theorem measurableSet_referenceFailure (c : Config) (μstar : ℝ) :
    MeasurableSet (ReferenceFailure (n := n) c μstar) :=
  MeasurableSet.iUnion (measurableSet_referenceFailureAtScale c μstar)

theorem choice_some_state (c : Config) (r : ℕ) (ω : SampleSpace n) (a : Accepted c n)
    (ha : choice c r ω = some a) : ∃ z, stage c ω.2 r = .inr (a.val, z) := by
  unfold choice choiceFromStage at ha
  cases hs : stage c ω.2 r with
  | inl result => simp only [hs] at ha; contradiction
  | inr st =>
      obtain ⟨b, z⟩ := st
      rw [hs] at ha
      dsimp only at ha
      split_ifs at ha with hb
      have he : b = a.val := congrArg Subtype.val (Option.some.inj ha)
      exact ⟨z, by simp only [he]⟩

theorem choice_of_pending (c : Config) (r : ℕ) (ω : SampleSpace n) (a : Metadata n) (z : ℝ)
    (hs : stage c ω.2 r = .inr (a, z)) (ha : a.Allowed c) :
    choice c r ω = some (⟨a, ha⟩ : Accepted c n) := by
  simp only [choice, choiceFromStage, hs, dif_pos ha]

/-- Distinct entry cells at the same scale are disjoint on every actual tape. -/
theorem entryCell_disjoint (c : Config) (k : ℕ) :
    Pairwise (Function.onFun Disjoint (entryCell (n := n) c k)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro ω hp hq
  obtain ⟨z, hz⟩ := choice_some_state c p.1 ω p.2.val hp
  obtain ⟨w, hw⟩ := choice_some_state c q.1 ω q.2.val hq
  have ht := pending_entry_scale_injective c ω.2 p.1 q.1 p.2.val.val q.2.val.val z w hz hw
    p.2.property.1 q.2.property.1 (p.2.property.2.trans q.2.property.2.symm)
  apply hpq
  apply Prod.ext ht
  apply Subtype.ext
  apply Option.some.inj
  change choice c p.1 ω = some p.2.val at hp
  change choice c q.1 ω = some q.2.val at hq
  rw [ht] at hp
  exact hp.symm.trans hq

/-- Entry reference upper validity needs only a global upper bound on means;
the true best need not remain active, and PAC success is not assumed. -/
theorem entryBadCell_measure_le (c : Config) (hδ : ValidConfidence c.confidence)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) (μstar : ℝ) (hmax : ∀ i, mean i ≤ μstar)
    (k : ℕ) (q : ℕ × EntryAt c n k) :
    sampleLawOfMeans mean (entryBadCell c μstar k q) ≤
      sampleLawOfMeans mean (entryCell c k q) * ENNReal.ofReal (referenceError c.confidence c.attempt k) := by
  let a := q.2.val
  let R := entryProcedure a.val.active (Finset.card_pos.mp (by have := a.property.1; omega))
    a.val.tolerance (a.val.alpha c) (a.val.beta c)
  let B : Set (Fin R.budget → Fin n → ℝ) := {v | μstar + a.val.tolerance / 16 < (R.evaluate v).1}
  have hB : MeasurableSet B := measurableSet_lt measurable_const R.measurable_evaluate.fst
  obtain ⟨E, hE, he⟩ := past_event_choice_prefix c q.1 (choice c q.1) (choice_adapted c q.1)
    (some a) a.val.samples a.val.samples le_rfl
    (fun ω h => boundary_of_choice_some c q.1 a ω h) Set.univ MeasurableSet.univ
  have he' : entryCell c k q = (seedPrefix a.val.samples) ⁻¹' E := by
    simpa only [Set.mem_univ, true_and, entryCell, a] using he
  have hf := measure_prefix_event_block mean a.val.samples R.budget E hE B hB
  have hfactor : sampleLawOfMeans mean (entryBadCell c μstar k q) =
      sampleLawOfMeans mean (entryCell c k q) * blockLaw mean R.budget B := by
    change sampleLawOfMeans mean {ω | ω ∈ entryCell c k q ∧ rewardBlock a.val.samples R.budget ω ∈ B} = _
    rw [he']
    exact hf
  have hb := entry_reference_upper_block_le a.val.active
    (Finset.card_pos.mp (by have := a.property.1; omega)) hn mean (α := a.val.alpha c)
    (fun i _ => hmax i) (tolerance_pos a.val)
    (referenceError_pos hδ.1 c.attempt a.val.scale)
    (referenceError_le_one hδ.1.le (hδ.2.le.trans (by norm_num)) c.attempt a.val.scale)
  have hb' : blockLaw mean R.budget B ≤ ENNReal.ofReal (a.val.beta c) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (blockLaw mean R.budget) B)]
    exact ENNReal.ofReal_le_ofReal hb
  rw [hfactor]
  apply mul_le_mul' le_rfl
  simpa only [Metadata.beta, a, q.2.property.2] using hb'

/-- The same scale is entered at most once, so random entry times do not
multiply beta by the fuel or by the number of possible active sets. -/
theorem referenceFailureAtScale_measure_le (c : Config) (hδ : ValidConfidence c.confidence)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) (μstar : ℝ) (hmax : ∀ i, mean i ≤ μstar) (k : ℕ) :
    sampleLawOfMeans mean (referenceFailureAtScale c μstar k) ≤
      ENNReal.ofReal (referenceError c.confidence c.attempt k) := by
  apply (measure_iUnion_le _).trans
  apply (ENNReal.tsum_le_tsum (fun q => entryBadCell_measure_le c hδ hn mean μstar hmax k q)).trans
  rw [ENNReal.tsum_mul_right, ← measure_iUnion (entryCell_disjoint c k) (measurableSet_entryCell c k)]
  exact mul_le_of_le_one_left' (prob_le_one)

theorem referenceFailure_measure_le (c : Config) (hδ : ValidConfidence c.confidence)
    (hn : 2 ≤ n) (mean : Fin n → ℝ) (μstar : ℝ) (hmax : ∀ i, mean i ≤ μstar) :
    sampleLawOfMeans mean (ReferenceFailure c μstar) ≤
      ∑' k, ENNReal.ofReal (referenceError c.confidence c.attempt k) := by
  exact (measure_iUnion_le _).trans
    (ENNReal.tsum_le_tsum (referenceFailureAtScale_measure_le c hδ hn mean μstar hmax))


theorem callResult_reference_entry (c : Config) (ω : SampleSpace n) (a : Metadata n)
    (ha : a.Allowed c) (z : ℝ) (he : a.entry = true) :
    (callResult c ω.2 a ha z).1 = entryReference c ⟨a, ha⟩ ω := by
  rcases a with ⟨S, k, entry, w, q⟩
  change entry = true at he
  subst entry
  rfl

theorem callResult_reference_later (c : Config) (x : Values n) (a : Metadata n)
    (ha : a.Allowed c) (z : ℝ) (he : a.entry = false) :
    (callResult c x a ha z).1 = z := by
  rcases a with ⟨S, k, entry, w, q⟩
  change entry = false at he
  subst entry
  rfl

theorem mem_referenceFailure_of_entry (c : Config) (μstar : ℝ) (ω : SampleSpace n)
    (r : ℕ) (a : Metadata n) (z : ℝ) (hs : stage c ω.2 r = .inr (a, z))
    (ha : a.Allowed c) (he : a.entry = true)
    (hbad : μstar + a.tolerance / 16 < (callResult c ω.2 a ha z).1) :
    ω ∈ ReferenceFailure c μstar := by
  apply Set.mem_iUnion.mpr
  refine ⟨a.scale, Set.mem_iUnion.mpr ?_⟩
  refine ⟨(r, ⟨⟨a, ha⟩, he, rfl⟩), ?_, ?_⟩
  · exact choice_of_pending c r ω a z hs ha
  · rwa [callResult_reference_entry c ω a ha z he] at hbad

/-- A retained real reference keeps the entry call's upper validity even when
its former reference arm has been deleted. No best-in-active-set premise is used. -/
theorem callReference_le_of_not_referenceFailure (c : Config) (μstar : ℝ) (ω : SampleSpace n)
    (hno : ω ∉ ReferenceFailure c μstar) (r : ℕ) (a : Metadata n) (z : ℝ)
    (hs : stage c ω.2 r = .inr (a, z)) (ha : a.Allowed c) :
    (callResult c ω.2 a ha z).1 ≤ μstar + a.tolerance / 16 := by
  induction r generalizing a z with
  | zero =>
      have heq : a = initial n := (congrArg Prod.fst (Sum.inr.inj hs)).symm
      have he : a.entry = true := by rw [heq]; rfl
      by_contra! hb
      exact hno (mem_referenceFailure_of_entry c μstar ω 0 a z hs ha he hb)
  | succ r ih =>
      by_cases he : a.entry = true
      · by_contra! hb
        exact hno (mem_referenceFailure_of_entry c μstar ω (r + 1) a z hs ha he hb)
      · have hef : a.entry = false := Bool.eq_false_iff.mpr he
        rw [callResult_reference_later c ω.2 a ha z hef]
        obtain ⟨b, w, hp, hstep⟩ := stage_pending_previous c ω.2 r a z hs
        obtain ⟨hb, _, hadv, hz⟩ := stageStep_pending_result c ω.2 b a w z hstep
        have hh : (callResult c ω.2 b hb w).2.card ≤ (b.active.card + 1) / 2 := by
          rw [hadv] at hef
          change (!(decide ((callResult c ω.2 b hb w).2.card ≤ (b.active.card + 1) / 2))) = false at hef
          simpa using hef
        have htol : a.tolerance = b.tolerance := by
          rw [hadv]
          simp only [Metadata.tolerance, Metadata.advance, Metadata.scale, if_pos hh]
        rw [hz, retainedReference, if_pos hh, htol]
        exact ih b w hp hb

end GapEntropy.UniversalAttempt
