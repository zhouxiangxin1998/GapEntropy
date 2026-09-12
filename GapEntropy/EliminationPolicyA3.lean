import GapEntropy.EliminationPolicyGaussian

/-! # The complete A.3 guarantees for the actual elimination sampler -/

noncomputable section
open MeasureTheory
open scoped ENNReal Classical

namespace GapEntropy.EliminationPolicy
open EliminationProbability

variable {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (hn : 2 ≤ n) (mean : Fin n → ℝ)
  {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, mean i ≤ mean best)
  {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1)

include hbest hmax hd hα hα1

theorem raw_best_failure :
    (sampleLawOfMeans mean).real {ω | best ∉ rawOutput S hS d α hn ω} ≤ α :=
  raw_best_failure_le hbest hd.le hα.le (reference_bad_le S hS hn mean hbest hmax hd hα hα1)
    (active_deviation_le S hS hn mean hd hα hα1 best hbest)

theorem padded_best_failure :
    (sampleLawOfMeans mean).real {ω | best ∉ paddedOutput S hS d α hn ω} ≤ α := by
  apply le_trans (measureReal_mono (μ := sampleLawOfMeans mean)
    (s₂ := {ω | best ∉ rawOutput S hS d α hn ω}) ?_ (measure_ne_top _ _))
    (raw_best_failure S hS hn mean hbest hmax hd hα hα1)
  intro ω hω hb
  exact hω (Elimination.raw_subset_padded _ _ _ _ hb)

theorem raw_large_failure {N : ℕ}
    (hnear : (Elimination.near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (sampleLawOfMeans mean).real {ω | best ∉ rawOutput S hS d α hn ω ∨
      (S.card + 1) / 2 < (rawOutput S hS d α hn ω).card} ≤ α :=
  raw_large_failure_le hbest hd.le hα.le (measurable_activeEstimate S hS d α hn)
    (reference_bad_le S hS hn mean hbest hmax hd hα hα1)
    (active_deviation_le S hS hn mean hd hα hα1) hnear hs

theorem padded_large_failure {N : ℕ}
    (hnear : (Elimination.near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (sampleLawOfMeans mean).real {ω | best ∉ paddedOutput S hS d α hn ω ∨
      (paddedOutput S hS d α hn ω).card ≠ (S.card + 1) / 2} ≤ α :=
  padded_large_failure_le hbest hd.le hα.le (measurable_activeEstimate S hS d α hn)
    (reference_bad_le S hS hn mean hbest hmax hd hα hα1)
    (active_deviation_le S hS hn mean hd hα hα1) hnear hs

theorem raw_small_failure (hs : S.card ≤ 4)
    (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    (sampleLawOfMeans mean).real {ω | rawOutput S hS d α hn ω ≠ {best}} ≤ α :=
  raw_small_failure_le hbest hd.le hα.le (reference_bad_le S hS hn mean hbest hmax hd hα hα1)
    (active_deviation_le S hS hn mean hd hα hα1) hs hgaps

theorem padded_small_failure (hs : S.card ≤ 4)
    (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    (sampleLawOfMeans mean).real {ω | best ∉ paddedOutput S hS d α hn ω ∨
      (paddedOutput S hS d α hn ω).card ≠ (S.card + 1) / 2} ≤ α := by
  apply le_trans (measureReal_mono (μ := sampleLawOfMeans mean)
    (s₂ := {ω | rawOutput S hS d α hn ω ≠ {best}}) ?_ (measure_ne_top _ _))
    (raw_small_failure S hS hn mean hbest hmax hd hα hα1 hs hgaps)
  intro ω hω heq
  have hb : best ∈ rawOutput S hS d α hn ω := by simp [heq]
  have hc : (rawOutput S hS d α hn ω).card = 1 := by simp [heq]
  rcases hω with hnot | hsize
  · exact hnot (Elimination.raw_subset_padded _ _ _ _ hb)
  · apply hsize
    apply Elimination.padded_halves_of_raw_small
    change (rawOutput S hS d α hn ω).card ≤ (S.card + 1) / 2
    have hp := hS.card_pos
    omega

/-- All A.3 statistical claims and the charged sample budget concern the same
concrete sampler and its completed-history set readouts. The terminal arm marker
is not interpreted as a best-arm answer. -/
theorem elimination_A3 (hd1 : d ≤ 1) :
    Measurable (rawOutput S hS d α hn) ∧
    Measurable (paddedOutput S hS d α hn) ∧
    (∀ ω, (policy S hS d α).sampleCount hn ω = budget S.card d α) ∧
    (budget S.card d α : ℝ) ≤ 6500000 * (S.card : ℝ) * (d ^ 2)⁻¹ * Real.log (128 / α) ∧
    ((sampleLawOfMeans mean).real {ω | best ∉ rawOutput S hS d α hn ω} ≤ α) ∧
    ((sampleLawOfMeans mean).real {ω | best ∉ paddedOutput S hS d α hn ω} ≤ α) ∧
    (∀ N, (Elimination.near S mean (mean best) d).card ≤ N → 4 * N < S.card →
      (sampleLawOfMeans mean).real {ω | best ∉ rawOutput S hS d α hn ω ∨
        (S.card + 1) / 2 < (rawOutput S hS d α hn ω).card} ≤ α ∧
      (sampleLawOfMeans mean).real {ω | best ∉ paddedOutput S hS d α hn ω ∨
        (paddedOutput S hS d α hn ω).card ≠ (S.card + 1) / 2} ≤ α) ∧
    (S.card ≤ 4 → (∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) →
      (sampleLawOfMeans mean).real {ω | rawOutput S hS d α hn ω ≠ {best}} ≤ α ∧
      (sampleLawOfMeans mean).real {ω | best ∉ paddedOutput S hS d α hn ω ∨
        (paddedOutput S hS d α hn ω).card ≠ (S.card + 1) / 2} ≤ α) := by
  exact ⟨measurable_rawOutput S hS d α hn, measurable_paddedOutput S hS d α hn,
    sampleCount_eq_budget S hS d α hn,
    EliminationTape.declaredCost_le hS.card_pos hd hd1 hα hα1,
    raw_best_failure S hS hn mean hbest hmax hd hα hα1,
    padded_best_failure S hS hn mean hbest hmax hd hα hα1,
    fun _ hnear hs => ⟨raw_large_failure S hS hn mean hbest hmax hd hα hα1 hnear hs,
      padded_large_failure S hS hn mean hbest hmax hd hα hα1 hnear hs⟩,
    fun hs hgaps => ⟨raw_small_failure S hS hn mean hbest hmax hd hα hα1 hs hgaps,
      padded_small_failure S hS hn mean hbest hmax hd hα hα1 hs hgaps⟩⟩

end GapEntropy.EliminationPolicy
