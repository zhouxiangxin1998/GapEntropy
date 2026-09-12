import GapEntropy.ModelProperties

/-!
# Full per-arm sampling counts

Unconditional total runtime equals the sum of the unconditional per-arm counts.
All identities are in extended nonnegative reals; finite expectations are proved
before any real-valued conversion. These are the counts charged in Appendix B.
-/

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.Policy

variable {n : ℕ} (A : Policy n)

noncomputable def armSamples (hn : 2 ≤ n) (i : Fin n) (ω : SampleSpace n) : ℝ≥0∞ :=
  ∑' t, if A.requestedArm hn t ω = some i then 1 else 0

theorem measurable_armSamples (hn : 2 ≤ n) (i : Fin n) : Measurable (A.armSamples hn i) := by
  apply Measurable.tsum
  intro t
  exact Measurable.ite ((A.measurable_requestedArm hn t).eq_const (some i)).setOf
    measurable_const measurable_const

theorem sum_armSamples (hn : 2 ≤ n) (ω : SampleSpace n) :
    ∑ i : Fin n, A.armSamples hn i ω = A.sampleCount hn ω := by
  unfold armSamples sampleCount
  calc
    (∑ i : Fin n, ∑' t, if A.requestedArm hn t ω = some i then (1 : ℝ≥0∞) else 0) =
        ∑' i : Fin n, ∑' t, if A.requestedArm hn t ω = some i then (1 : ℝ≥0∞) else 0 :=
      (tsum_fintype _).symm
    _ = ∑' t, ∑' i : Fin n, if A.requestedArm hn t ω = some i then (1 : ℝ≥0∞) else 0 :=
      ENNReal.tsum_comm
    _ = ∑' t, A.sampleIndicator hn t ω := by
      apply tsum_congr
      intro t
      rw [tsum_fintype]
      exact (A.sampleIndicator_eq_sum_arms hn t ω).symm

theorem armSamples_le_sampleCount (hn : 2 ≤ n) (i : Fin n) (ω : SampleSpace n) :
    A.armSamples hn i ω ≤ A.sampleCount hn ω := by
  rw [← A.sum_armSamples]
  exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin n => A.armSamples hn j ω)
    (fun _ _ => zero_le) (Finset.mem_univ i)

theorem truncatedArmSamples_le_armSamples (hn : 2 ≤ n) (T : ℕ) (i : Fin n)
    (ω : SampleSpace n) : A.truncatedArmSamples hn T i ω ≤ A.armSamples hn i ω :=
  ENNReal.sum_le_tsum (Finset.range T)

noncomputable def expectedArmSamples (I : Instance n) (i : Fin n) : ℝ≥0∞ :=
  ∫⁻ ω, A.armSamples I.two_le i ω ∂sampleLaw I

theorem sum_expectedArmSamples (I : Instance n) :
    ∑ i : Fin n, A.expectedArmSamples I i = A.expectedSamples I := by
  unfold expectedArmSamples expectedSamples
  rw [← lintegral_finsetSum _ (fun i _ => A.measurable_armSamples I.two_le i)]
  congr 1
  funext ω
  exact A.sum_armSamples I.two_le ω

theorem expectedArmSamples_le_expectedSamples (I : Instance n) (i : Fin n) :
    A.expectedArmSamples I i ≤ A.expectedSamples I :=
  lintegral_mono (A.armSamples_le_sampleCount I.two_le i)

theorem expectedArmSamples_ne_top (I : Instance n) (h : A.expectedSamples I ≠ ⊤) (i : Fin n) :
    A.expectedArmSamples I i ≠ ⊤ :=
  ne_top_of_le_ne_top h (A.expectedArmSamples_le_expectedSamples I i)

theorem sum_toReal_expectedArmSamples (I : Instance n) (h : A.expectedSamples I ≠ ⊤) :
    ∑ i : Fin n, (A.expectedArmSamples I i).toReal = (A.expectedSamples I).toReal := by
  rw [← ENNReal.toReal_sum (fun i _ => A.expectedArmSamples_ne_top I h i),
    A.sum_expectedArmSamples]

end GapEntropy.Policy
