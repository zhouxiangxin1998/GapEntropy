import GapEntropy.Interleave

/-!
# Return semantics of the actual alternating policy

Every combined output is an output of one component on its private tape.
Termination of either component forces combined termination. These are pathwise
statements about the original Policy.run, rather than a separate abstract process.
-/

open MeasureTheory
open scoped ENNReal

namespace GapEntropy.Interleave

variable {n : ℕ} (A B : Policy n)

theorem run_return_imp_component (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) (i : Fin n)
    (hret : (policy A B).run hn ω t = Sum.inl i) :
    (∃ s, A.run hn (samplePart 0 ω) s = Sum.inl i) ∨
      ∃ s, B.run hn (samplePart 1 ω) s = Sum.inl i := by
  induction t with
  | zero => simp [Policy.run] at hret
  | succ t ih =>
      cases hr : (policy A B).run hn ω t with
      | inl j =>
          have hji : j = i := by simpa [Policy.run_succ, Policy.step, hr] using hret
          subst j
          exact ih hr
      | inr h =>
          obtain ⟨hA, hB⟩ := active_component_runs A B hn ω t h hr
          rw [Policy.run_succ, Policy.step, hr] at hret
          simp only [Sum.elim_inr] at hret
          by_cases ht : t % 2 = 0
          · cases hc : A.choose hn ((t + 1) / 2) (seedPart 0 ω.1, evenHistory h) with
            | inl j => simp [policy, ht, hc] at hret
            | inr j =>
                have hji : j = i := by
                  simpa [policy, ht, hc] using hret
                subst j
                refine Or.inl ⟨(t + 1) / 2 + 1, ?_⟩
                rw [Policy.run_succ, Policy.step, hA]
                change (A.choose hn ((t + 1) / 2)
                  (seedPart 0 ω.1, evenHistory h)).elim _ _ = _
                rw [hc]
                rfl
          · cases hc : B.choose hn (t / 2) (seedPart 1 ω.1, oddHistory h) with
            | inl j => simp [policy, ht, hc] at hret
            | inr j =>
                have hji : j = i := by
                  simpa [policy, ht, hc] using hret
                subst j
                refine Or.inr ⟨t / 2 + 1, ?_⟩
                rw [Policy.run_succ, Policy.step, hB]
                change (B.choose hn (t / 2)
                  (seedPart 1 ω.1, oddHistory h)).elim _ _ = _
                rw [hc]
                rfl

theorem returned_imp_component (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) (i : Fin n)
    (hret : (policy A B).returnedAt hn t ω = some i) :
    (∃ s, A.returnedAt hn s (samplePart 0 ω) = some i) ∨
      ∃ s, B.returnedAt hn s (samplePart 1 ω) = some i := by
  simpa only [Policy.returnedAt_eq_some_iff] using
    run_return_imp_component A B hn ω t i ((policy A B).returnedAt_eq_some_iff hn t ω i |>.1 hret)

theorem returnedNotEvent_subset_components (hn : 2 ≤ n) (tag : Fin n) :
    (policy A B).returnedNotEvent hn tag ⊆
      (samplePart 0 ⁻¹' A.returnedNotEvent hn tag) ∪
        (samplePart 1 ⁻¹' B.returnedNotEvent hn tag) := by
  rintro ω ⟨t, i, hi, hret⟩
  rcases returned_imp_component A B hn ω t i hret with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact Or.inl ⟨s, i, hi, hs⟩
  · exact Or.inr ⟨s, i, hi, hs⟩

theorem returnedNotEvent_measure_le (I : Instance n) {a b : ℝ≥0∞}
    (hA : sampleLaw I (A.returnedNotEvent I.two_le I.best) ≤ a)
    (hB : sampleLaw I (B.returnedNotEvent I.two_le I.best) ≤ b) :
    sampleLaw I ((policy A B).returnedNotEvent I.two_le I.best) ≤ a + b := by
  calc
    _ ≤ sampleLaw I ((samplePart 0 ⁻¹' A.returnedNotEvent I.two_le I.best) ∪
        (samplePart 1 ⁻¹' B.returnedNotEvent I.two_le I.best)) :=
      measure_mono (returnedNotEvent_subset_components A B I.two_le I.best)
    _ ≤ sampleLaw I (samplePart 0 ⁻¹' A.returnedNotEvent I.two_le I.best) +
        sampleLaw I (samplePart 1 ⁻¹' B.returnedNotEvent I.two_le I.best) := measure_union_le _ _
    _ = sampleLaw I (A.returnedNotEvent I.two_le I.best) +
        sampleLaw I (B.returnedNotEvent I.two_le I.best) := by
      unfold sampleLaw
      rw [(measurePreserving_samplePart I.mean 0).measure_preimage
          (A.measurableSet_returnedNotEvent I.two_le I.best).nullMeasurableSet,
        (measurePreserving_samplePart I.mean 1).measure_preimage
          (B.measurableSet_returnedNotEvent I.two_le I.best).nullMeasurableSet]
    _ ≤ a + b := add_le_add hA hB

/-- At twice a component's return horizon, the combined run cannot still be
active: that would imply that the already-returned component is active there. -/
theorem terminates_of_component_returns (hn : 2 ≤ n) (ω : SampleSpace n)
    (h : (∃ s i, A.returnedAt hn s (samplePart 0 ω) = some i) ∨
      ∃ s i, B.returnedAt hn s (samplePart 1 ω) = some i) :
    ∃ T i, (policy A B).returnedAt hn T ω = some i := by
  rcases h with ⟨s, i, hi⟩ | ⟨s, i, hi⟩
  · cases hr : (policy A B).run hn ω (2 * s) with
    | inl j => exact ⟨2 * s, j, by simp [Policy.returnedAt, hr]⟩
    | inr hist =>
        have ha := (active_component_runs A B hn ω (2 * s) hist hr).1
        have hs : (2 * s + 1) / 2 = s := by omega
        have hnone : A.returnedAt hn ((2 * s + 1) / 2) (samplePart 0 ω) = none := by
          simp [Policy.returnedAt, ha]
        rw [hs, hi] at hnone
        cases hnone
  · cases hr : (policy A B).run hn ω (2 * s) with
    | inl j => exact ⟨2 * s, j, by simp [Policy.returnedAt, hr]⟩
    | inr hist =>
        have hb := (active_component_runs A B hn ω (2 * s) hist hr).2
        have hs : (2 * s) / 2 = s := by omega
        have hnone : B.returnedAt hn ((2 * s) / 2) (samplePart 1 ω) = none := by
          simp [Policy.returnedAt, hb]
        rw [hs, hi] at hnone
        cases hnone

end GapEntropy.Interleave
