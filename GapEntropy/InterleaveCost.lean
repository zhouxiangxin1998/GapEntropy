import GapEntropy.InterleaveProperties
import GapEntropy.ActiveCounts

/-! The pathwise and unconditional factor-two cost bounds in Appendix C.3. -/

open MeasureTheory
open scoped ENNReal

namespace GapEntropy.Interleave

variable {n : ℕ} (A B : Policy n)

theorem sampleCount_le_left (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy A B).sampleCount hn ω ≤ 2 * A.sampleCount hn (samplePart 0 ω) + 1 := by
  by_cases htop : A.sampleCount hn (samplePart 0 ω) = ⊤
  · simp [htop]
  obtain ⟨s, i, hi⟩ := A.returns_of_sampleCount_ne_top hn (samplePart 0 ω) htop
  obtain ⟨T, j, hj⟩ := terminates_of_component_returns A B hn ω (Or.inl ⟨s, i, hi⟩)
  obtain ⟨t, h, hr, hret⟩ := (policy A B).exists_active_return_transition hn ω T j
    (((policy A B).returnedAt_eq_some_iff hn T ω j).1 hj)
  rw [(policy A B).sampleCount_eq_time_of_return_transition hn ω t h hr j hret]
  have hA := (active_component_runs A B hn ω t h hr).1
  have hcount := A.time_le_sampleCount_of_active hn (samplePart 0 ω) _ _ hA
  calc
    (t : ℝ≥0∞) ≤ 2 * (((t + 1) / 2 : ℕ) : ℝ≥0∞) + 1 := by
      exact_mod_cast (show t ≤ 2 * ((t + 1) / 2) + 1 by omega)
    _ ≤ 2 * A.sampleCount hn (samplePart 0 ω) + 1 :=
      add_le_add (mul_le_mul' le_rfl hcount) le_rfl

theorem sampleCount_le_right (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy A B).sampleCount hn ω ≤ 2 * B.sampleCount hn (samplePart 1 ω) + 1 := by
  by_cases htop : B.sampleCount hn (samplePart 1 ω) = ⊤
  · simp [htop]
  obtain ⟨s, i, hi⟩ := B.returns_of_sampleCount_ne_top hn (samplePart 1 ω) htop
  obtain ⟨T, j, hj⟩ := terminates_of_component_returns A B hn ω (Or.inr ⟨s, i, hi⟩)
  obtain ⟨t, h, hr, hret⟩ := (policy A B).exists_active_return_transition hn ω T j
    (((policy A B).returnedAt_eq_some_iff hn T ω j).1 hj)
  rw [(policy A B).sampleCount_eq_time_of_return_transition hn ω t h hr j hret]
  have hB := (active_component_runs A B hn ω t h hr).2
  have hcount := B.time_le_sampleCount_of_active hn (samplePart 1 ω) _ _ hB
  calc
    (t : ℝ≥0∞) ≤ 2 * ((t / 2 : ℕ) : ℝ≥0∞) + 1 := by
      exact_mod_cast (show t ≤ 2 * (t / 2) + 1 by omega)
    _ ≤ 2 * B.sampleCount hn (samplePart 1 ω) + 1 :=
      add_le_add (mul_le_mul' le_rfl hcount) le_rfl

private theorem lintegral_twice_count_add_one (I : Instance n) (e : Fin 2) (C : Policy n) :
    (∫⁻ ω, 2 * C.sampleCount I.two_le (samplePart e ω) + 1 ∂sampleLaw I) =
      2 * C.expectedSamples I + 1 := by
  have hm : Measurable (fun ω => C.sampleCount I.two_le (samplePart e ω)) :=
    (C.measurable_sampleCount I.two_le).comp (measurable_samplePart e)
  have hm' : Measurable (fun ω => 2 * C.sampleCount I.two_le (samplePart e ω)) :=
    measurable_const.mul hm
  rw [lintegral_add_left hm',
    lintegral_const_mul _ hm, lintegral_const]
  unfold sampleLaw
  rw [(measurePreserving_samplePart I.mean e).lintegral_comp (C.measurable_sampleCount I.two_le)]
  simp [Policy.expectedSamples, sampleLaw]

/-- The expected cost is bounded by either component's unconditional expected
cost, without needing independence between the two return events. -/
theorem expectedSamples_le_left (I : Instance n) :
    (policy A B).expectedSamples I ≤ 2 * A.expectedSamples I + 1 := by
  apply (lintegral_mono (sampleCount_le_left A B I.two_le)).trans_eq
  exact lintegral_twice_count_add_one I 0 A

theorem expectedSamples_le_right (I : Instance n) :
    (policy A B).expectedSamples I ≤ 2 * B.expectedSamples I + 1 := by
  apply (lintegral_mono (sampleCount_le_right A B I.two_le)).trans_eq
  exact lintegral_twice_count_add_one I 1 B

theorem expectedSamples_ne_top_of_right (I : Instance n) (hB : B.expectedSamples I ≠ ⊤) :
    (policy A B).expectedSamples I ≠ ⊤ :=
  ne_top_of_le_ne_top (by finiteness) (expectedSamples_le_right A B I)

end GapEntropy.Interleave
