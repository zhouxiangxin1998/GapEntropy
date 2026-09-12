import GapEntropy.UniversalCallEquivalence

/-!
# Actual universal call boundaries are prefix stopping times

Two reward tables agreeing before t have the same call-indexed state whenever
that state's consumed sample count is at most t, and agree on whether this
condition holds. This gives measurable prefix representations at the exact
random boundary, with no adaptive-freshness assumption.
-/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram
variable {n : ℕ}

/-- Samples consumed before the next call, also defined on terminal states. -/
def boundary : Stage n → ℕ
  | .inl ((a, _), _) => a.samples
  | .inr (a, _) => a.samples

def nextBoundary (c : Config) : Stage n → ℕ
  | .inl ((a, _), _) => a.samples
  | .inr (a, _) => if a.Allowed c then a.samples + (a.call c).samples else a.samples

theorem measurable_boundary : Measurable (boundary (n := n)) := by
  apply measurable_fun_sum
  · exact measurable_fst.fst.snd.snd.snd.snd
  · exact measurable_fst.snd.snd.snd.snd

theorem boundary_stageStep (c : Config) (x : Values n) (st : Stage n) :
    boundary (stageStep c x st) = nextBoundary c st := by
  cases st with
  | inl result => rcases result with ⟨⟨a, z⟩, ans⟩; rfl
  | inr state =>
    rcases state with ⟨a, z⟩
    simp only [stageStep, nextBoundary]
    split_ifs <;> rfl

theorem boundary_le_nextBoundary (c : Config) (st : Stage n) :
    boundary st ≤ nextBoundary c st := by
  cases st with
  | inl result => rcases result with ⟨⟨a, z⟩, ans⟩; exact le_rfl
  | inr state =>
    rcases state with ⟨a, z⟩
    simp only [boundary, nextBoundary]
    split_ifs <;> omega

theorem stageStep_congr_prefix (c : Config) (x y : Values n) (st : Stage n) (t : ℕ)
    (hxy : ∀ s < t, x s = y s) (ht : nextBoundary c st ≤ t) :
    stageStep c x st = stageStep c y st := by
  cases st with
  | inl result => rfl
  | inr state =>
    rcases state with ⟨a, z⟩
    by_cases ha : a.Allowed c
    · have hend : a.samples + (a.call c).samples ≤ t := by
        simpa only [nextBoundary, if_pos ha] using ht
      have hb : firstBlock (a.call c).samples (shiftValues a.samples x) =
          firstBlock (a.call c).samples (shiftValues a.samples y) := by
        funext i
        exact hxy (a.samples + i) (by have := i.isLt; omega)
      simp only [stageStep, dif_pos ha, hb]
    · simp only [stageStep, dif_neg ha]

/-- Both the boundedness event and the bounded state itself depend only on the
reward rows strictly before the candidate boundary t. -/
theorem stage_prefix_local (c : Config) (r t : ℕ) (x y : Values n)
    (hxy : ∀ s < t, x s = y s) :
    (boundary (stage c x r) ≤ t ↔ boundary (stage c y r) ≤ t) ∧
    (boundary (stage c x r) ≤ t → stage c x r = stage c y r) := by
  induction r with
  | zero => exact ⟨Iff.rfl, fun _ => rfl⟩
  | succ r ih =>
    by_cases hx : boundary (stage c x r) ≤ t
    · have he := ih.2 hx
      have hb : boundary (stage c x (r + 1)) = boundary (stage c y (r + 1)) := by
        simp only [stage, boundary_stageStep, he]
      refine ⟨by rw [hb], fun ht => ?_⟩
      change stageStep c x (stage c x r) = stageStep c y (stage c y r)
      rw [← he]
      exact stageStep_congr_prefix c x y _ t hxy (by simpa only [stage, boundary_stageStep] using ht)
    · have hy : ¬ boundary (stage c y r) ≤ t := fun hy => hx (ih.1.mpr hy)
      have hx' : ¬ boundary (stage c x (r + 1)) ≤ t := by
        intro h
        apply hx
        exact (boundary_le_nextBoundary c _).trans (by simpa only [stage, boundary_stageStep] using h)
      have hy' : ¬ boundary (stage c y (r + 1)) ≤ t := by
        intro h
        apply hy
        exact (boundary_le_nextBoundary c _).trans (by simpa only [stage, boundary_stageStep] using h)
      exact ⟨iff_of_false hx' hy', fun h => (hx' h).elim⟩

/-- Run the same controller on the given finite prefix, filling future rows
with zero. The next theorem says zero filling cannot change a boundary-t event. -/
def prefixStage (c : Config) (r t : ℕ) (v : Fin t → Fin n → ℝ) : Stage n :=
  stage c (extendBlock t v) r

theorem measurable_prefixStage (c : Config) (r t : ℕ) :
    Measurable (prefixStage c (n := n) r t) :=
  (measurable_stage c r).comp (extendBlock_measurable t)

theorem prefixStage_exact_event (c : Config) (r t : ℕ) (x : Values n) (B : Set (Stage n)) :
    (boundary (stage c x r) = t ∧ stage c x r ∈ B) ↔
    (boundary (prefixStage c r t (firstBlock t x)) = t ∧
      prefixStage c r t (firstBlock t x) ∈ B) := by
  have hxy : ∀ s < t, x s = extendBlock t (firstBlock t x) s := by
    intro s hs
    simp only [extendBlock, dif_pos hs, firstBlock]
  have hh := stage_prefix_local c r t x (extendBlock t (firstBlock t x)) hxy
  constructor
  · rintro ⟨hb, hB⟩
    have he := hh.2 hb.le
    exact ⟨by simpa only [prefixStage, ← he] using hb, by simpa only [prefixStage, ← he] using hB⟩
  · rintro ⟨hb, hB⟩
    have he := hh.2 (hh.1.mpr hb.le)
    exact ⟨by simpa only [prefixStage, ← he] using hb, by simpa only [prefixStage, ← he] using hB⟩

/-- Exact prefix representation for every measurable event of the actual
call-indexed state at its random sample boundary. -/
theorem stage_event_prefix (c : Config) (r t : ℕ) (B : Set (Stage n)) (hB : MeasurableSet B) :
    ∃ E : Set (SeedPrefix n t), MeasurableSet E ∧
      {ω : SampleSpace n | boundary (stage c ω.2 r) = t ∧ stage c ω.2 r ∈ B} =
        (seedPrefix t) ⁻¹' E := by
  let E : Set (SeedPrefix n t) := {p | boundary (prefixStage c r t p.2) = t ∧
    prefixStage c r t p.2 ∈ B}
  refine ⟨E, ?_, ?_⟩
  · exact (((measurable_boundary.comp (measurable_prefixStage c r t)).comp measurable_snd)
      (measurableSet_singleton t)).inter (((measurable_prefixStage c r t).comp measurable_snd) hB)
  · ext ω
    exact prefixStage_exact_event c r t ω.2 B

/-- In particular each actual call-indexed sample boundary is a stopping time
for the seed and full-row prefix filtration used by `StoppedBlocks`. -/
theorem boundary_prefix (c : Config) (r t : ℕ) :
    ∃ E : Set (SeedPrefix n t), MeasurableSet E ∧
      {ω : SampleSpace n | boundary (stage c ω.2 r) = t} = (seedPrefix t) ⁻¹' E := by
  simpa only [Set.mem_univ, and_true] using stage_event_prefix c r t Set.univ MeasurableSet.univ

theorem measurable_stage_boundary (c : Config) (r : ℕ) :
    Measurable (fun ω : SampleSpace n => boundary (stage c ω.2 r)) :=
  measurable_boundary.comp ((measurable_stage c r).comp measurable_snd)

end GapEntropy.UniversalAttempt
