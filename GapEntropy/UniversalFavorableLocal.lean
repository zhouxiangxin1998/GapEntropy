import GapEntropy.UniversalFavorableEvents
import GapEntropy.UniversalSevereProcess

/-! Actual Gaussian local bounds for simultaneous reference suitability and
all favorable-path progress conditions. The entry reference is charged once. -/
noncomputable section
open MeasureTheory
open scoped Classical ENNReal
namespace GapEntropy.UniversalAttempt
open UniversalCall Elimination EliminationTape GaussianBlocks
variable {n : ℕ}

theorem measurableSet_favorableResult (I : Instance n) (a : Metadata n) :
    MeasurableSet {out : ℝ × Finset (Fin n) | FavorableResult I a out} :=
  ((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_fst measurable_const)).inter
    ((MeasurableSet.of_discrete : MeasurableSet {R : Finset (Fin n) | CallFavorable I a R}).preimage
      measurable_snd)

theorem favorable_of_isolation (I : Instance n) (a : Metadata n) (X : Fin n → ℝ) (z : ℝ)
    (hS : a.active.Nonempty) (hb : I.best ∈ padded a.active X z a.tolerance)
    (hl : 4 * I.targetCount a.scale < a.active.card →
      (padded a.active X z a.tolerance).card = (a.active.card + 1) / 2)
    (hs : a.active.card ≤ 4 →
      (∀ i ∈ a.active, i ≠ I.best → a.tolerance ≤ I.mean I.best - I.mean i) →
      raw a.active X z a.tolerance = {I.best}) :
    CallFavorable I a (padded a.active X z a.tolerance) := by
  apply callFavorable_of_progress I a _ hb (fun h => (hl h).le)
  intro hsmall hgaps
  have hraw := hs hsmall hgaps
  apply (padded_halves_of_raw_small ?_).le
  rw [hraw, Finset.card_singleton]
  have hpos := hS.card_pos
  omega

/-- Simultaneous best protection, large-set progress, and separated small-set
isolation consume only 9α/64 on the suitable-reference event. -/
theorem favorable_on_past_le (I : Instance n) (a : Metadata n) (hbest : I.best ∈ a.active)
    (start : ℕ) (α : ℝ) (hd : 0 < a.tolerance) (hα : 0 < α) (hα1 : α ≤ 1)
    (Z : SampleSpace n → ℝ) (E : Set (SeedPrefix n start)) (hE : MeasurableSet E) :
    (sampleLawOfMeans I.mean).real {ω | seedPrefix start ω ∈ E ∧
      Suitable (I.mean I.best) a.tolerance (Z ω) ∧
      ¬ CallFavorable I a (padded a.active (scheduleEstimate a.active start
        (activeSamples a.tolerance α) ω) (Z ω) a.tolerance)} ≤
      (sampleLawOfMeans I.mean).real ((seedPrefix start) ⁻¹' E) * (9 * α / 64) := by
  let hS : a.active.Nonempty := ⟨I.best, hbest⟩
  let X := scheduleEstimate a.active start (activeSamples a.tolerance α)
  let P := sampleLawOfMeans I.mean
  let mass := P.real ((seedPrefix start) ⁻¹' E)
  let B : Set (SampleSpace n) := {ω | seedPrefix start ω ∈ E ∧
    Suitable (I.mean I.best) a.tolerance (Z ω) ∧ I.best ∉ padded a.active (X ω) (Z ω) a.tolerance}
  let L : Set (SampleSpace n) := {ω | seedPrefix start ω ∈ E ∧
    Suitable (I.mean I.best) a.tolerance (Z ω) ∧ 4 * I.targetCount a.scale < a.active.card ∧
    (padded a.active (X ω) (Z ω) a.tolerance).card ≠ (a.active.card + 1) / 2}
  let S : Set (SampleSpace n) := {ω | seedPrefix start ω ∈ E ∧
    Suitable (I.mean I.best) a.tolerance (Z ω) ∧ a.active.card ≤ 4 ∧
    (∀ i ∈ a.active, i ≠ I.best → a.tolerance ≤ I.mean I.best - I.mean i) ∧
    raw a.active (X ω) (Z ω) a.tolerance ≠ {I.best}}
  have hB : P.real B ≤ mass * (α / 64) :=
    progress_best_on_past_le a.active hS start I.mean hbest hd hα hα1 Z E hE
  have hL : P.real L ≤ mass * (α / 16) := by
    by_cases hl : 4 * I.targetCount a.scale < a.active.card
    · have hnear : (Elimination.near a.active I.mean (I.mean I.best) a.tolerance).card ≤
          I.targetCount a.scale := by
        rw [tolerance_eq_target I a]
        exact I.near_card_le_targetCount a.active a.scale
      simpa only [L, hl, true_and, X, mass, P] using
        progress_halving_on_past_le a.active hS start I.mean hd hα hα1 Z E hE hnear hl
    · have he : L = ∅ := by ext ω; simp [L, hl]
      rw [he, measureReal_empty]
      exact mul_nonneg measureReal_nonneg (by positivity)
  have hSbad : P.real S ≤ mass * (α / 16) := by
    by_cases hs : a.active.card ≤ 4 ∧
        (∀ i ∈ a.active, i ≠ I.best → a.tolerance ≤ I.mean I.best - I.mean i)
    · apply (measureReal_mono (μ := P) (h₂ := measure_ne_top _ _) ?_).trans
        (progress_isolation_on_past_le a.active hS start I.mean hbest hd hα hα1 Z E hE hs.1 hs.2)
      rintro ω ⟨hEω, hz, _, _, hraw⟩
      exact ⟨hEω, hz, hraw⟩
    · have he : S = ∅ := by ext ω; simp only [S, Set.mem_ofPred_eq, Set.mem_empty_iff_false]; tauto
      rw [he, measureReal_empty]
      exact mul_nonneg measureReal_nonneg (by positivity)
  have hcover : {ω | seedPrefix start ω ∈ E ∧ Suitable (I.mean I.best) a.tolerance (Z ω) ∧
      ¬ CallFavorable I a (padded a.active (X ω) (Z ω) a.tolerance)} ⊆ B ∪ (L ∪ S) := by
    rintro ω ⟨hEω, hz, hfail⟩
    by_contra h
    have hb : I.best ∈ padded a.active (X ω) (Z ω) a.tolerance := by
      by_contra hb
      exact h (Or.inl ⟨hEω, hz, hb⟩)
    apply hfail
    apply favorable_of_isolation I a (X ω) (Z ω) hS hb
    · intro hl
      by_contra hh
      exact h (Or.inr (Or.inl ⟨hEω, hz, hl, hh⟩))
    · intro hs hg
      by_contra hh
      exact h (Or.inr (Or.inr ⟨hEω, hz, hs, hg, hh⟩))
  have hu := ((measureReal_mono (μ := P) hcover (measure_ne_top P _)).trans
    (measureReal_union_le B (L ∪ S))).trans
      (add_le_add_right (measureReal_union_le (μ := P) L S) (P.real B))
  change _ ≤ mass * (9 * α / 64)
  nlinarith

/-- Entry reference failure and all active-estimate failures are combined once.
The bound is for the actual finite Gaussian block evaluator. -/
theorem entry_favorable_block_failure_le (I : Instance n) (a : Metadata n) (hS : a.active.Nonempty)
    (hbest : I.best ∈ a.active) (α β : ℝ) (hd : 0 < a.tolerance)
    (hα : 0 < α) (hα1 : α ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    (blockLaw I.mean (entryBudget a.active.card a.tolerance α β)).real
      {v | ¬ FavorableResult I a ((entryProcedure a.active hS a.tolerance α β).evaluate v)} ≤
      α / 4 + β := by
  let R := entryProcedure a.active hS a.tolerance α β
  have hmax : ∀ i ∈ a.active, I.mean i ≤ I.mean I.best := by
    intro i _
    exact sub_nonneg.mp (I.gap_nonneg i)
  let Z := referenceEstimate a.active hS a.tolerance α β
  have href := reference_unsuitable_le a.active hS I.two_le I.mean hbest hmax hd hα hα1 hβ hβ1
  have hprog := favorable_on_past_le I a hbest (activeStart a.active.card a.tolerance α β)
    α hd hα hα1 Z Set.univ MeasurableSet.univ
  simp only [Set.mem_univ, true_and, Set.preimage_univ, probReal_univ, one_mul] at hprog
  have hc : {ω | ¬ FavorableResult I a (R.actualOutput ω)} ⊆
      {ω | ¬ Suitable (I.mean I.best) a.tolerance (Z ω)} ∪
      {ω | Suitable (I.mean I.best) a.tolerance (Z ω) ∧
        ¬ CallFavorable I a (padded a.active (scheduleEstimate a.active
          (activeStart a.active.card a.tolerance α β) (activeSamples a.tolerance α) ω)
          (Z ω) a.tolerance)} := by
    intro ω hω
    change ¬ (Suitable _ _ _ ∧ CallFavorable _ _ _) at hω
    dsimp only [R] at hω
    rw [entry_actualOutput_eq] at hω
    by_cases hz : Suitable (I.mean I.best) a.tolerance (Z ω)
    · exact Or.inr ⟨hz, fun hf => hω ⟨hz, hf⟩⟩
    · exact Or.inl hz
  have hh := ((measureReal_mono (μ := sampleLawOfMeans I.mean) hc (measure_ne_top _ _)).trans
    (measureReal_union_le _ _)).trans (add_le_add href hprog)
  have hactual : (sampleLawOfMeans I.mean).real {ω | ¬ FavorableResult I a (R.actualOutput ω)} ≤ α / 4 + β := by
    nlinarith
  have htransfer := R.actualOutput_event I.mean {out | ¬ FavorableResult I a out}
    (measurableSet_favorableResult I a).compl
  exact (congrArg ENNReal.toReal htransfer).symm.trans_le hactual

theorem later_favorable_block_failure_le (I : Instance n) (a : Metadata n) (hS : a.active.Nonempty)
    (hbest : I.best ∈ a.active) (α z : ℝ) (hd : 0 < a.tolerance)
    (hα : 0 < α) (hα1 : α ≤ 1) (hz : Suitable (I.mean I.best) a.tolerance z) :
    (blockLaw I.mean (laterBudget a.active.card a.tolerance α)).real
      {v | ¬ FavorableResult I a (z, (laterProcedure a.active hS a.tolerance α z).evaluate v)} ≤
      α / 4 := by
  let R := laterProcedure a.active hS a.tolerance α z
  have hprog := favorable_on_past_le I a hbest 0 α hd hα hα1 (fun _ => z) Set.univ MeasurableSet.univ
  simp only [Set.mem_univ, true_and, hz, Set.preimage_univ, probReal_univ, one_mul] at hprog
  have hactual : (sampleLawOfMeans I.mean).real {ω | ¬ CallFavorable I a (R.actualOutput ω)} ≤ α / 4 := by
    dsimp only [R]
    simp_rw [later_actualOutput_eq]
    nlinarith
  have htransfer := R.actualOutput_event I.mean {out | ¬ CallFavorable I a out} MeasurableSet.of_discrete
  have hh := (congrArg ENNReal.toReal htransfer).symm.trans_le hactual
  change (blockLaw I.mean (laterBudget a.active.card a.tolerance α)).real
    {v | ¬ CallFavorable I a (R.evaluate v)} ≤ α / 4 at hh
  simpa only [FavorableResult, hz, true_and] using hh

theorem beta_bounds (c : Config) (hδ : ValidConfidence c.confidence) (a : Metadata n) :
    0 < a.beta c ∧ a.beta c ≤ 1 := by
  exact ⟨referenceError_pos hδ.1 _ _,
    referenceError_le_one hδ.1.le (by linarith [hδ.2]) _ _⟩

/-- The exact uniform sampler interface used by the real controller, including
an uncountable stored z. Entry β is present exactly in the entry branch. -/
theorem call_favorable_block_failure_le (I : Instance n) (c : Config)
    (hδ : ValidConfidence c.confidence) (a : UniversalSevereProcess.Accepted c n) (z : ℝ)
    (hbest : I.best ∈ a.val.active)
    (hz : a.val.entry = false → Suitable (I.mean I.best) a.val.tolerance z) :
    (blockLaw I.mean (callProcedure c a.val a.property.1 z).budget).real
      {v | ¬ FavorableResult I a.val ((callProcedure c a.val a.property.1 z).evaluate v)} ≤
      a.val.alpha c / 4 + (if a.val.entry then a.val.beta c else 0) := by
  have hd := UniversalSevereProcess.tolerance_pos a.val
  have hα := UniversalSevereProcess.alpha_pos c hδ.1 a
  have hα1 : a.val.alpha c ≤ 1 :=
    (UniversalSevereProcess.alpha_le_errorBudget c hδ.1.le a).trans (by
      unfold Config.errorBudget; linarith [hδ.2])
  let hS : a.val.active.Nonempty := Finset.card_pos.mp (by have := a.property.1; omega)
  cases he : a.val.entry with
  | true =>
    rw [callProcedure_eq_entry c a.val a.property.1 z he]
    change (blockLaw I.mean (entryBudget a.val.active.card a.val.tolerance (a.val.alpha c) (a.val.beta c))).real
      {v | ¬ FavorableResult I a.val ((entryProcedure a.val.active hS a.val.tolerance
        (a.val.alpha c) (a.val.beta c)).evaluate v)} ≤ a.val.alpha c / 4 + a.val.beta c
    exact entry_favorable_block_failure_le I a.val hS hbest
      (a.val.alpha c) (a.val.beta c) hd hα hα1 (beta_bounds c hδ a.val).1 (beta_bounds c hδ a.val).2
  | false =>
    rw [callProcedure_eq_later c a.val a.property.1 z he]
    simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    let R := laterProcedure a.val.active hS a.val.tolerance (a.val.alpha c) z
    change (blockLaw I.mean R.budget).real
      {v | ¬ FavorableResult I a.val ((carryReference R z).evaluate v)} ≤ a.val.alpha c / 4
    simp_rw [carryReference_evaluate R z]
    exact later_favorable_block_failure_le I a.val hS hbest (a.val.alpha c) z hd hα hα1 (hz he)

end GapEntropy.UniversalAttempt
