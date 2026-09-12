import GapEntropy.UniversalStageBudget
import GapEntropy.UniversalFavorablePath
import GapEntropy.UniversalEntryProgress

/-! First-failure events for actual universal calls. Their deterministic
propagation preserves the best and the numerical reference at a reused scale. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram UniversalCall
variable {n : ℕ}

/-- The completed call's reference is suitable and its padded set makes all
runtime progress required by the actual favorable-path envelope. -/
def FavorableResult (I : Instance n) (a : Metadata n) (out : ℝ × Finset (Fin n)) : Prop :=
  Suitable (I.mean I.best) a.tolerance out.1 ∧ CallFavorable I a out.2

/-- Only a later call needs a suitable stored numerical reference. A new scale
will independently select and estimate its reference before eliminating. -/
def StoredGood (I : Instance n) : Stage n → Prop
  | .inl _ => True
  | .inr (a, z) => I.best ∈ a.active ∧ (a.entry = false → Suitable (I.mean I.best) a.tolerance z)

def StepFavorable (I : Instance n) (c : Config) (x : Values n) : Stage n → Prop
  | .inl _ => True
  | .inr (a, z) => ∀ ha : a.Allowed c, FavorableResult I a (callResult c x a ha z)

def BadAt (I : Instance n) (c : Config) (r : ℕ) (ω : SampleSpace n) : Prop :=
  StoredGood I (stage c ω.2 r) ∧ ¬ StepFavorable I c ω.2 (stage c ω.2 r)

theorem storedGood_initial (I : Instance n) : StoredGood I (.inr (initial n, 0)) := by
  refine ⟨Finset.mem_univ _, ?_⟩
  intro he
  cases he

theorem favorable_preserves_storedGood (I : Instance n) (c : Config) (x : Values n) (st : Stage n)
    (hf : StepFavorable I c x st) : StoredGood I (stageStep c x st) := by
  cases st with
  | inl result => trivial
  | inr state =>
    rcases state with ⟨a, z⟩
    by_cases ha : a.Allowed c
    · have hcall := hf ha
      change Suitable (I.mean I.best) a.tolerance (callResult c x a ha z).1 ∧
        CallFavorable I a (callResult c x a ha z).2 at hcall
      rw [stageStep, dif_pos ha]
      change StoredGood I (if (callResult c x a ha z).2.card = 1 then
        .inl ((a.advance c (callResult c x a ha z).2, (callResult c x a ha z).1),
          singletonAnswer (callResult c x a ha z).2)
        else .inr (a.advance c (callResult c x a ha z).2,
          retainedReference a (callResult c x a ha z).1 (callResult c x a ha z).2))
      by_cases hs : (callResult c x a ha z).2.card = 1
      · simp only [if_pos hs, StoredGood]
      · rw [if_neg hs]
        refine ⟨hcall.2.1, ?_⟩
        intro he
        have hh : (callResult c x a ha z).2.card ≤ (a.active.card + 1) / 2 := by
          change Bool.not (decide ((callResult c x a ha z).2.card ≤ (a.active.card + 1) / 2)) = false at he
          simpa using he
        have hscale := (advance_reuses_reference c a (callResult c x a ha z).1
          (callResult c x a ha z).2 hh).1
        simpa only [Metadata.tolerance, hscale, retainedReference, if_pos hh] using hcall.1
    · simp only [stageStep, dif_neg ha, StoredGood]

theorem storedGood_of_no_bad (I : Instance n) (c : Config) (ω : SampleSpace n) (r : ℕ)
    (hbad : ∀ t < r, ¬ BadAt I c t ω) : StoredGood I (stage c ω.2 r) := by
  induction r with
  | zero => exact storedGood_initial I
  | succ r ih =>
    have hp := ih (fun t ht => hbad t (by omega))
    have hstep : StepFavorable I c ω.2 (stage c ω.2 r) := by
      by_contra h
      exact hbad r (by omega) ⟨hp, h⟩
    exact favorable_preserves_storedGood I c ω.2 _ hstep

/-- Any failure of the deterministic favorable-path property is covered by a
first call failure with a valid incoming state. No distribution is assumed. -/
theorem unfavorable_subset_bad_union (I : Instance n) (c : Config) (T : ℕ) :
    {ω : SampleSpace n | ¬ FavorableThrough I c ω.2 T} ⊆
      ⋃ r ∈ Finset.range T, {ω | BadAt I c r ω} := by
  intro ω hω
  by_contra h
  have hn (r : ℕ) (hr : r < T) : ¬ BadAt I c r ω := by
    intro hb
    exact h (Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hr, hb⟩⟩)
  apply hω
  intro r hr a z hs ha
  have hgood := storedGood_of_no_bad I c ω r (fun t ht => hn t (by omega))
  have hstep : StepFavorable I c ω.2 (stage c ω.2 r) := by
    by_contra hb
    exact hn r hr ⟨hgood, hb⟩
  rw [hs] at hstep
  exact (hstep ha).2

end GapEntropy.UniversalAttempt
