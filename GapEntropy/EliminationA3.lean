import GapEntropy.EliminationCost
import GapEntropy.EliminationObservations

/-!
# Lemma A.3 for the actual Gaussian product-tape procedure

The theorem `elimination_A3` collects the Lemma A.3 guarantees for the raw and padded
elimination outputs of `EliminationTape`. Both outputs are measurable, every trajectory consumes
exactly the declared cost, the declared cost is at most `6500000 · |S| · d⁻² · log(128/α)`, and
each output drops the best arm with probability at most `α`. When at most `N` arms are near and
`4N < |S|`, the raw output keeps the best arm and has at most the rounded half of the input, and
the padded output keeps the best arm and has exactly that size, each failing with probability
at most `α`. When `|S| ≤ 4` and every other arm has gap at least `d`, the raw output is exactly
the best arm with probability at least `1 - α`. The theorem concerns the statistical procedure;
its interactive `Policy` embedding is not asserted here.
-/

noncomputable section
open MeasureTheory

namespace GapEntropy.EliminationTape

/-- Lemma A.3 for the actual Gaussian product-tape procedure. The three probability
claims use no unproved concentration or PAC hypotheses. This theorem concerns the
statistical procedure; its interactive `Policy` embedding is not asserted here. -/
theorem elimination_A3 {n : ℕ} (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    {d α : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, μ i ≤ μ best) :
    Measurable (rawOutput (d := d) (α := α) μ S hS) ∧
    Measurable (paddedOutput (d := d) (α := α) μ S hS) ∧
    (∀ ω : Tape n d α, trajectoryCost S ω = declaredCost S.card d α) ∧
    (declaredCost S.card d α : ℝ) ≤
      6500000 * (S.card : ℝ) * (d ^ 2)⁻¹ * Real.log (128 / α) ∧
    ((law μ d α).real {ω | best ∉ rawOutput μ S hS ω} ≤ α) ∧
    ((law μ d α).real {ω | best ∉ paddedOutput μ S hS ω} ≤ α) ∧
    (∀ N, (GapEntropy.Elimination.near S μ (μ best) d).card ≤ N → 4 * N < S.card →
      (law μ d α).real {ω | best ∉ rawOutput μ S hS ω ∨
        (S.card + 1) / 2 < (rawOutput μ S hS ω).card} ≤ α ∧
      (law μ d α).real {ω | best ∉ paddedOutput μ S hS ω ∨
        (paddedOutput μ S hS ω).card ≠ (S.card + 1) / 2} ≤ α) ∧
    (S.card ≤ 4 → (∀ i ∈ S, i ≠ best → d ≤ μ best - μ i) →
      (law μ d α).real {ω | rawOutput μ S hS ω ≠ {best}} ≤ α ∧
      (law μ d α).real {ω | best ∉ paddedOutput μ S hS ω ∨
        (paddedOutput μ S hS ω).card ≠ (S.card + 1) / 2} ≤ α) := by
  refine ⟨rawOutput_measurable μ S hS, paddedOutput_measurable μ S hS,
    trajectoryCost_eq_declaredCost S, declaredCost_le hS.card_pos hd hd1 hα hα1,
    raw_best_failure μ S hS hbest hmax hd hd1 hα hα1,
    padded_best_failure μ S hS hbest hmax hd hd1 hα hα1, ?_, ?_⟩
  · intro N hnear hs
    exact ⟨raw_large_failure μ S hS hbest hmax hd hd1 hα hα1 hnear hs,
      padded_large_failure μ S hS hbest hmax hd hd1 hα hα1 hnear hs⟩
  · intro hs hgaps
    exact ⟨raw_small_failure μ S hS hbest hmax hd hd1 hα hα1 hs hgaps,
      padded_small_failure μ S hS hbest hmax hd hd1 hα hα1 hs hgaps⟩

end GapEntropy.EliminationTape
