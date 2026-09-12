import GapEntropy.UniversalFavorableLocal
import GapEntropy.FreshKernelBound

/-! Measurable actual favorable-failure cells, with an unchanged real reference
coordinate and the actual accepted-metadata choice. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GapEntropy.UniversalAttempt
open UniversalCall UniversalSevereProcess FiniteCallProgram GaussianBlocks
variable {n : ℕ}

def storedReference : Stage n → ℝ
  | .inl ((_, z), _) => z
  | .inr (_, z) => z

theorem measurable_storedReference : Measurable (storedReference (n := n)) :=
  (measurable_snd.comp measurable_fst).sumElim measurable_snd

def referenceAt (c : Config) (r : ℕ) (ω : SampleSpace n) : ℝ := storedReference (stage c ω.2 r)

theorem measurable_referenceAt (c : Config) (r : ℕ) : Measurable (referenceAt c (n := n) r) :=
  measurable_storedReference.comp ((measurable_stage c r).comp measurable_snd)

theorem measurable_storedGood_decide (I : Instance n) :
    Measurable (fun st : Stage n => decide (StoredGood I st)) := by
  apply measurable_fun_sum
  · have he : ((fun st : Stage n => decide (StoredGood I st)) ∘ Sum.inl) =
        (fun _ : State n × Option (Fin n) => true) := by
      funext st
      exact decide_eq_true (show StoredGood I (Sum.inl st) from True.intro)
    rw [he]
    exact measurable_const
  · apply measurable_from_prod_countable_right
    intro a
    by_cases hb : I.best ∈ a.active
    · by_cases he : a.entry = false
      · have hm : Measurable (fun z : ℝ => decide (Suitable (I.mean I.best) a.tolerance z)) := by
          apply measurable_to_bool
          convert (measurableSet_Icc : MeasurableSet (Set.Icc (I.mean I.best - 3 * a.tolerance / 16)
            (I.mean I.best + a.tolerance / 16))) using 1
          ext z
          simp [Suitable]
        simpa [StoredGood, hb, he] using hm
      · simp [StoredGood, hb, he]
    · simp [StoredGood, hb]

theorem measurableSet_storedGood (I : Instance n) : MeasurableSet {st : Stage n | StoredGood I st} := by
  simpa only [Set.preimage, Set.mem_singleton_iff, decide_eq_true_eq] using
    (measurable_storedGood_decide I) (measurableSet_singleton true)

theorem storedGood_adapted (I : Instance n) (c : Config) (r : ℕ) :
    MeasurableSet[callPast c r] {ω : SampleSpace n | StoredGood I (stage c ω.2 r)} :=
  (stage_adapted c r) (measurableSet_storedGood I)

theorem stage_eq_of_choice_some (c : Config) (r : ℕ) (a : Accepted c n)
    (ω : SampleSpace n) (ha : choice c r ω = some a) :
    stage c ω.2 r = .inr (a.val, referenceAt c r ω) := by
  unfold choice choiceFromStage at ha
  cases hs : stage c ω.2 r with
  | inl result => simp only [hs] at ha; contradiction
  | inr st =>
    rcases st with ⟨b, z⟩
    rw [hs] at ha
    dsimp only at ha
    split_ifs at ha with hb
    have he : b = a.val := congrArg Subtype.val (Option.some.inj ha)
    simp only [referenceAt, hs, storedReference, he]

def badCell (I : Instance n) (c : Config) (r : ℕ) (a : Accepted c n) : Set (SampleSpace n) :=
  {ω | choice c r ω = some a ∧ StoredGood I (stage c ω.2 r) ∧
    ¬ FavorableResult I a.val ((callProcedure c a.val a.property.1 (referenceAt c r ω)).evaluate
      (rewardBlock a.val.samples (a.val.call c).samples ω))}

theorem measurableSet_badCell (I : Instance n) (c : Config) (r : ℕ) (a : Accepted c n) :
    MeasurableSet (badCell I c r a) := by
  have hchoice : Measurable (choice c (n := n) r) :=
    (choice_adapted c r).mono ((callFiltration c).le r) le_rfl
  have hout := (measurable_call_evaluate c a.val a.property.1).comp
    ((measurable_referenceAt c r).prodMk (measurable_rewardBlock a.val.samples (a.val.call c).samples))
  exact (hchoice (measurableSet_singleton (some a))).inter
    (((callFiltration c).le r _ (storedGood_adapted I c r)).inter
      (hout (measurableSet_favorableResult I a.val).compl))

theorem badAt_eq_union (I : Instance n) (c : Config) (r : ℕ) :
    {ω : SampleSpace n | BadAt I c r ω} = ⋃ a : Accepted c n, badCell I c r a := by
  ext ω
  constructor
  · rintro ⟨hgood, hbad⟩
    cases hs : stage c ω.2 r with
    | inl result => simp only [hs, StepFavorable, not_true_eq_false] at hbad
    | inr st =>
      rcases st with ⟨a, z⟩
      rw [hs] at hbad
      obtain ⟨ha, hfail⟩ := not_forall.mp hbad
      refine Set.mem_iUnion.mpr ⟨⟨a, ha⟩, ?_⟩
      refine ⟨by simp only [choice, hs, choiceFromStage, dif_pos ha], hgood, ?_⟩
      have hreference : referenceAt c r ω = z := by
        unfold referenceAt; rw [hs]; rfl
      rw [hreference]
      exact hfail
  · intro hω
    obtain ⟨a, ha, hg, hf⟩ := Set.mem_iUnion.mp hω
    refine ⟨hg, ?_⟩
    rw [stage_eq_of_choice_some c r a ω ha]
    intro h
    apply hf
    exact h a.property

theorem measurableSet_badAt (I : Instance n) (c : Config) (r : ℕ) :
    MeasurableSet {ω : SampleSpace n | BadAt I c r ω} := by
  rw [badAt_eq_union]
  exact MeasurableSet.iUnion (fun a => measurableSet_badCell I c r a)

def retainedCall (c : Config) (r : ℕ) (a : Accepted c n) (ω : SampleSpace n) : Finset (Fin n) :=
  ((callProcedure c a.val a.property.1 (referenceAt c r ω)).evaluate
    (rewardBlock a.val.samples (a.val.call c).samples ω)).2

set_option maxHeartbeats 800000 in
theorem measurable_retainedCall (c : Config) (r : ℕ) (a : Accepted c n) :
    Measurable (retainedCall c r a) := by
  unfold retainedCall
  exact ((measurable_call_evaluate c a.val a.property.1).comp
    ((measurable_referenceAt c r).prodMk (measurable_rewardBlock a.val.samples (a.val.call c).samples))).snd

set_option maxHeartbeats 800000 in
theorem favorableThrough_iff_choices (I : Instance n) (c : Config) (T : ℕ) (ω : SampleSpace n) :
    FavorableThrough I c ω.2 T ↔ ∀ r < T, ∀ a : Accepted c n,
      choice c r ω = some a → CallFavorable I a.val (retainedCall c r a ω) := by
  constructor
  · intro h r hr a ha
    exact h r hr a.val (referenceAt c r ω) (stage_eq_of_choice_some c r a ω ha) a.property
  · intro h r hr a z hs ha
    have hc : choice c r ω = some (⟨a, ha⟩ : Accepted c n) := by
      simp only [choice, hs, choiceFromStage, dif_pos ha]
    have hh := h r hr ⟨a, ha⟩ hc
    have hz : referenceAt c r ω = z := by unfold referenceAt; rw [hs]; rfl
    unfold retainedCall at hh
    rw [hz] at hh
    exact hh

theorem measurableSet_favorableThrough (I : Instance n) (c : Config) (T : ℕ) :
    MeasurableSet {ω : SampleSpace n | FavorableThrough I c ω.2 T} := by
  simp_rw [favorableThrough_iff_choices]
  simp only [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro r
  apply MeasurableSet.iInter
  intro hr
  apply MeasurableSet.iInter
  intro a
  have hc : Measurable (choice c (n := n) r) :=
    (choice_adapted c r).mono ((callFiltration c).le r) le_rfl
  have hout := (measurable_retainedCall c r a)
    (MeasurableSet.of_discrete : MeasurableSet {R : Finset (Fin n) | CallFavorable I a.val R})
  convert ((hc (measurableSet_singleton (some a))).compl.union hout) using 1
  ext ω
  simp [imp_iff_not_or]

end GapEntropy.UniversalAttempt
