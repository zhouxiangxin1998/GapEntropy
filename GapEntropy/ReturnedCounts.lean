import GapEntropy.ReturnedEvents
import GapEntropy.SamplingCounts

/-!
# Counts freeze after returning

A returned state is absorbing, so every future sampling indicator vanishes.
Consequently the full per-arm count is already visible at any return horizon.
-/

open MeasureTheory
open scoped ENNReal

namespace GapEntropy.Policy

variable {n : ℕ} (A : Policy n)

theorem requestedArm_eq_none_of_returned (hn : 2 ≤ n) (ω : SampleSpace n)
    {T s : ℕ} (hs : T ≤ s) {i : Fin n} (hret : A.returnedAt hn T ω = some i) :
    A.requestedArm hn s ω = none := by
  have hr := (A.returnedAt_eq_some_iff hn s ω i).mp (A.returnedAt_persists hn hs ω i hret)
  simp [requestedArm, hr]

theorem armSamples_eq_truncatedArmSamples_of_returned (hn : 2 ≤ n) (ω : SampleSpace n)
    (T : ℕ) {i : Fin n} (hret : A.returnedAt hn T ω = some i) (j : Fin n) :
    A.armSamples hn j ω = A.truncatedArmSamples hn T j ω := by
  unfold armSamples truncatedArmSamples
  apply tsum_eq_sum
  intro s hs
  have hTs : T ≤ s := by simpa only [Finset.mem_range, not_lt] using hs
  simp [A.requestedArm_eq_none_of_returned hn ω hTs hret]

theorem sampleCount_eq_truncatedSamples_of_returned (hn : 2 ≤ n) (ω : SampleSpace n)
    (T : ℕ) {i : Fin n} (hret : A.returnedAt hn T ω = some i) :
    A.sampleCount hn ω = A.truncatedSamples hn T ω := by
  rw [← A.sum_armSamples, ← A.sum_truncatedArmSamples]
  apply Finset.sum_congr rfl
  intro j _
  exact A.armSamples_eq_truncatedArmSamples_of_returned hn ω T hret j

end GapEntropy.Policy
