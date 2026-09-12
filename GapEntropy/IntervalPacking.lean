import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-!
# Bounded overlap of stopping windows

Manuscript (B.13) uses greedy selection of disjoint windows. The equivalent
bounded-overlap proof below counts, at each sample coordinate, at most `ℓ + 2`
windows. Integrating that pointwise count yields the same packing inequality.
This does not assume disjointness or independence of the events.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace GapEntropy

noncomputable section

attribute [local instance] Classical.propDecidable

def coveringWindows (s : Finset ℕ) (start : ℕ → ℝ) (ℓ x : ℝ) : Finset ℕ :=
  s.filter fun k => start k ≤ x ∧ x ≤ start k + ℓ

/-- At most `ℓ + 2` starts in distinct cells `(k-1,k]` can cover one point
with closed windows of common length `ℓ`. -/
theorem coveringWindows_card_le (s : Finset ℕ) (start : ℕ → ℝ) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) (hcell : ∀ k ∈ s, (k : ℝ) - 1 < start k ∧ start k ≤ k) (x : ℝ) :
    ((coveringWindows s start ℓ x).card : ℝ) ≤ ℓ + 2 := by
  classical
  let t := coveringWindows s start ℓ x
  by_cases ht : t.Nonempty
  · let a := t.min' ht
    let b := t.max' ht
    have ha : a ∈ t := t.min'_mem ht
    have hb : b ∈ t := t.max'_mem ht
    have hab : a ≤ b := t.min'_le_max' ht
    have hsub : t ⊆ Finset.Icc a b := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨t.min'_le k hk, t.le_max' k hk⟩
    have hc : t.card ≤ b + 1 - a := by
      simpa only [Nat.card_Icc] using Finset.card_le_card hsub
    have hc' : t.card + a ≤ b + 1 := by omega
    have hcR : (t.card : ℝ) + a ≤ b + 1 := by exact_mod_cast hc'
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hca := hcell a ha'.1
    have hcb := hcell b hb'.1
    change (t.card : ℝ) ≤ _
    linarith [ha'.2.2, hb'.2.1]
  · have he : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    change (t.card : ℝ) ≤ _
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

/-- Integral counting: if each outcome lies in at most `c` events and all events
are contained in `F`, their measures sum to at most `c * μ F`. -/
theorem sum_measures_le_of_overlap {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ℕ) (E : ℕ → Set Ω) (F : Set Ω) {c : ℝ}
    (hE : ∀ k ∈ s, MeasurableSet (E k)) (hF : MeasurableSet F)
    (hsub : ∀ k ∈ s, E k ⊆ F)
    (hcount : ∀ ω, ((s.filter fun k => ω ∈ E k).card : ℝ) ≤ c) :
    ∑ k ∈ s, μ (E k) ≤ ENNReal.ofReal c * μ F := by
  classical
  have hpoint (ω : Ω) :
      (∑ k ∈ s, (E k).indicator (fun _ => (1 : ℝ≥0∞)) ω) ≤
        ENNReal.ofReal c * F.indicator (fun _ => (1 : ℝ≥0∞)) ω := by
    by_cases hω : ω ∈ F
    · rw [Set.indicator_of_mem hω, mul_one]
      have heq : (∑ k ∈ s, (E k).indicator (fun _ => (1 : ℝ≥0∞)) ω) =
          ((s.filter fun k => ω ∈ E k).card : ℝ≥0∞) := by
        simp only [Set.indicator_apply, ← Finset.sum_filter, Finset.sum_const,
          nsmul_eq_mul, mul_one]
      rw [heq]
      exact_mod_cast ENNReal.ofReal_le_ofReal (hcount ω)
    · rw [Set.indicator_of_notMem hω, mul_zero]
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro k hk
      exact Set.indicator_of_notMem (fun h => hω (hsub k hk h)) _
  calc
    ∑ k ∈ s, μ (E k) =
        ∫⁻ ω, ∑ k ∈ s, (E k).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ := by
      rw [lintegral_finsetSum _ (fun k hk => measurable_const.indicator (hE k hk))]
      apply Finset.sum_congr rfl
      intro k hk
      exact (lintegral_indicator_one (hE k hk)).symm
    _ ≤ ∫⁻ ω, ENNReal.ofReal c * F.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂μ :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal c * μ F := by
      rw [lintegral_const_mul _ (measurable_const.indicator hF)]
      exact congrArg (ENNReal.ofReal c * ·) (lintegral_indicator_one hF)

/-- The common-null packing inequality underlying (B.13). Different window events
may be dependent; they are all measured under the same law `μ`. -/
theorem stopping_window_packing {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ℕ) (E : ℕ → Set Ω) (F : Set Ω)
    (start : ℕ → ℝ) (coordinate : Ω → ℝ) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hcell : ∀ k ∈ s, (k : ℝ) - 1 < start k ∧ start k ≤ k)
    (hE : ∀ k ∈ s, MeasurableSet (E k)) (hF : MeasurableSet F)
    (hsub : ∀ k ∈ s, E k ⊆ F)
    (hwindow : ∀ k ∈ s, ∀ ω ∈ E k,
      start k ≤ coordinate ω ∧ coordinate ω ≤ start k + ℓ) :
    ∑ k ∈ s, μ (E k) ≤ ENNReal.ofReal (ℓ + 2) * μ F := by
  classical
  apply sum_measures_le_of_overlap μ s E F hE hF hsub
  intro ω
  have hs : (s.filter fun k => ω ∈ E k) ⊆ coveringWindows s start ℓ (coordinate ω) := by
    intro k hk
    obtain ⟨hks, hkE⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨hks, hwindow k hks ω hkE⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hs)).trans
    (coveringWindows_card_le s start hℓ hcell (coordinate ω))

/-- Quantitative counting form: a common lower probability `q` for every window
and a common-null output budget `δ` force `|s| * q ≤ (ℓ+2) * δ`. -/
theorem stopping_window_card_mul_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Finset ℕ) (E : ℕ → Set Ω) (F : Set Ω)
    (start : ℕ → ℝ) (coordinate : Ω → ℝ) {ℓ q δ : ℝ}
    (hℓ : 0 ≤ ℓ) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (hcell : ∀ k ∈ s, (k : ℝ) - 1 < start k ∧ start k ≤ k)
    (hE : ∀ k ∈ s, MeasurableSet (E k)) (hF : MeasurableSet F)
    (hsub : ∀ k ∈ s, E k ⊆ F)
    (hwindow : ∀ k ∈ s, ∀ ω ∈ E k,
      start k ≤ coordinate ω ∧ coordinate ω ≤ start k + ℓ)
    (hlower : ∀ k ∈ s, ENNReal.ofReal q ≤ μ (E k))
    (hbudget : μ F ≤ ENNReal.ofReal δ) :
    (s.card : ℝ) * q ≤ (ℓ + 2) * δ := by
  have hc : 0 ≤ ℓ + 2 := by linarith
  have h : (s.card : ℝ≥0∞) * ENNReal.ofReal q ≤
      ENNReal.ofReal (ℓ + 2) * ENNReal.ofReal δ := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal q = ∑ _k ∈ s, ENNReal.ofReal q := by
        simp [nsmul_eq_mul]
      _ ≤ ∑ k ∈ s, μ (E k) := Finset.sum_le_sum hlower
      _ ≤ ENNReal.ofReal (ℓ + 2) * μ F :=
        stopping_window_packing μ s E F start coordinate hℓ hcell hE hF hsub hwindow
      _ ≤ ENNReal.ofReal (ℓ + 2) * ENNReal.ofReal δ := mul_le_mul' le_rfl hbudget
  have ht := ENNReal.toReal_mono (by finiteness) h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal hq, ENNReal.toReal_ofReal hc, ENNReal.toReal_ofReal hδ] using ht

end
end GapEntropy
