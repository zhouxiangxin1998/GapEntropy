import GapEntropy.UniversalFavorableMeasurability

/-! Actual past-cell favorable bounds from the full Gaussian reward-block law.
The reused numerical reference remains an ordinary measurable real parameter. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical ENNReal
namespace GapEntropy.UniversalAttempt
open UniversalCall UniversalSevereProcess FiniteCallProgram GaussianBlocks
variable {n : ℕ}

def callRisk (c : Config) (a : Accepted c n) : ℝ :=
  a.val.alpha c / 4 + (if a.val.entry then a.val.beta c else 0)

theorem callRisk_nonneg (c : Config) (hδ : ValidConfidence c.confidence) (a : Accepted c n) :
    0 ≤ callRisk c a := by
  have hα := (alpha_pos c hδ.1 a).le
  have hβ := (beta_bounds c hδ a.val).1.le
  unfold callRisk
  split_ifs <;> positivity

def referenceFromPrefix (c : Config) (r t : ℕ) (p : SeedPrefix n t) : ℝ :=
  storedReference (prefixStage c r t p.2)

theorem measurable_referenceFromPrefix (c : Config) (r t : ℕ) :
    Measurable (referenceFromPrefix c (n := n) r t) :=
  measurable_storedReference.comp ((measurable_prefixStage c r t).comp measurable_snd)

theorem referenceFromPrefix_eq (c : Config) (r t : ℕ) (ω : SampleSpace n)
    (ht : boundary (stage c ω.2 r) = t) :
    referenceFromPrefix c r t (seedPrefix t ω) = referenceAt c r ω := by
  have hh := (prefixStage_exact_event c r t ω.2 {stage c ω.2 r}).mp ⟨ht, rfl⟩
  exact congrArg storedReference hh.2

theorem seedPrefix_extendPrefix (t : ℕ) (p : SeedPrefix n t) :
    seedPrefix t (extendPrefix t p) = p := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [seedPrefix, extendPrefix, dif_pos i.isLt]

/-- The conditional favorable failure on a selected actual call is bounded by
its own α/4 plus its once-only entry β. This is derived from genuine independent
reward blocks and holds for continuously distributed past references. -/
theorem badCell_le (I : Instance n) (c : Config) (hδ : ValidConfidence c.confidence)
    (r : ℕ) (a : Accepted c n) :
    sampleLawOfMeans I.mean (badCell I c r a) ≤
      sampleLawOfMeans I.mean {ω | choice c r ω = some a} * ENNReal.ofReal (callRisk c a) := by
  let t := a.val.samples
  let m := (a.val.call c).samples
  obtain ⟨E, hE, he⟩ := past_event_choice_prefix c r (choice c r) (choice_adapted c r)
    (some a) t t le_rfl (fun ω h => boundary_of_choice_some c r a ω h)
    {ω | StoredGood I (stage c ω.2 r)} (storedGood_adapted I c r)
  change {ω | StoredGood I (stage c ω.2 r) ∧ choice c r ω = some a} = (seedPrefix t) ⁻¹' E at he
  let B : Set (SeedPrefix n t × (Fin m → Fin n → ℝ)) := {p |
    ¬ FavorableResult I a.val ((callProcedure c a.val a.property.1
      (referenceFromPrefix c r t p.1)).evaluate p.2)}
  have hB : MeasurableSet B :=
    ((measurable_call_evaluate c a.val a.property.1).comp
      (((measurable_referenceFromPrefix c r t).comp measurable_fst).prodMk measurable_snd))
      (measurableSet_favorableResult I a.val).compl
  have hfiber (u : SeedPrefix n t) (hu : u ∈ E) :
      blockLaw I.mean m {v | (u, v) ∈ B} ≤ ENNReal.ofReal (callRisk c a) := by
    let ω := extendPrefix t u
    have hω : StoredGood I (stage c ω.2 r) ∧ choice c r ω = some a := by
      change ω ∈ {ω | StoredGood I (stage c ω.2 r) ∧ choice c r ω = some a}
      rw [he]
      simpa only [ω, Set.mem_preimage, seedPrefix_extendPrefix] using hu
    have hs := stage_eq_of_choice_some c r a ω hω.2
    have hstored := hω.1
    rw [hs] at hstored
    have hz : referenceFromPrefix c r t u = referenceAt c r ω := by
      have hh := referenceFromPrefix_eq c r t ω (boundary_of_choice_some c r a ω hω.2)
      simpa only [ω, seedPrefix_extendPrefix] using hh
    have hl := call_favorable_block_failure_le I c hδ a (referenceFromPrefix c r t u)
      hstored.1 (by rw [hz]; exact hstored.2)
    have hh := ENNReal.ofReal_le_ofReal hl
    rw [Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at hh
    exact hh
  have hkernel := independent_kernel_event_le (sampleLawOfMeans I.mean) (blockLaw I.mean m)
    (seedPrefix t) (rewardBlock t m) (measurable_prefix t) (measurable_rewardBlock t m)
    (indepFun_seedPrefix_rewardBlock I.mean t m)
    ⟨(measurable_rewardBlock t m).aemeasurable, (measurePreserving_rewardBlock I.mean t m).map_eq⟩
    E hE B hB (ENNReal.ofReal (callRisk c a)) hfiber
  have hcell : badCell I c r a =
      {ω | seedPrefix t ω ∈ E ∧ (seedPrefix t ω, rewardBlock t m ω) ∈ B} := by
    ext ω
    constructor
    · rintro ⟨hc, hg, hf⟩
      refine ⟨?_, ?_⟩
      · change ω ∈ (seedPrefix t) ⁻¹' E
        rw [← he]
        exact ⟨hg, hc⟩
      · change ¬ FavorableResult I a.val _
        rw [referenceFromPrefix_eq c r t ω (boundary_of_choice_some c r a ω hc)]
        exact hf
    · rintro ⟨hEω, hf⟩
      have hpart : StoredGood I (stage c ω.2 r) ∧ choice c r ω = some a := by
        change ω ∈ {ω | StoredGood I (stage c ω.2 r) ∧ choice c r ω = some a}
        rw [he]
        exact hEω
      refine ⟨hpart.2, hpart.1, ?_⟩
      change ¬ FavorableResult I a.val _ at hf
      rw [referenceFromPrefix_eq c r t ω (boundary_of_choice_some c r a ω hpart.2)] at hf
      exact hf
  rw [hcell]
  apply hkernel.trans
  apply mul_le_mul' ?_ le_rfl
  apply measure_mono
  rw [← he]
  exact fun _ h => h.2

end GapEntropy.UniversalAttempt
