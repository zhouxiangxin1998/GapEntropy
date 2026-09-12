import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-!
# From counts of cheap scales to a Kraft bound

This is the deterministic counting-to-Kraft step of Appendix B. Instead of
Tonelli and the numerical improper integral in (B.14), we group `α` into unit
intervals. The already available confidence bound gives `α ≥ log 10 > 2`.
The resulting bound is `Σ exp(-4α) ≤ (79/9) δ < 10δ`, sufficient for exactly
the same (B.15) conclusion and the manuscript's final constant `1/5`.

No statistical claim is made without its scale-counting hypothesis.
-/

open scoped BigOperators
open scoped Classical

namespace GapEntropy

theorem exp_neg_two_le_seventh : Real.exp (-2) ≤ (1 / 7 : ℝ) := by
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8 / 3) he 2
  have hid : Real.exp (2 : ℝ) = Real.exp 1 ^ 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    ring
  have h7 : 7 ≤ Real.exp 2 := by rw [hid]; norm_num at hs; linarith
  rw [Real.exp_neg, one_div]
  exact (inv_le_inv₀ (Real.exp_pos 2) (by norm_num : (0 : ℝ) < 7)).2 h7

theorem log_ten_gt_two : (2 : ℝ) < Real.log 10 := by
  apply (Real.lt_log_iff_exp_lt (by norm_num)).2
  have he : Real.exp 1 < 3 := Real.exp_one_lt_three
  have hp := Real.exp_pos 1
  rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  nlinarith

theorem log_window_le_linear {x : ℝ} (hx : 1 ≤ x) :
    Real.log (1600 * x) / Real.log 4 + 2 ≤ 10 + x := by
  have hx0 : 0 < x := by linarith
  have h4 : 1 ≤ Real.log 4 := by
    apply (Real.le_log_iff_exp_le (by norm_num)).2
    linarith [Real.exp_one_lt_three]
  have he : (8 / 3 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 8 / 3) he 8
  have h1600 : Real.log 1600 ≤ 8 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).2
    have hid : Real.exp (8 : ℝ) = Real.exp 1 ^ 8 := by
      simpa only [Nat.cast_ofNat, mul_one] using (Real.exp_nat_mul (1 : ℝ) 8)
    rw [hid]
    norm_num at hp
    linarith
  have hlog := Real.log_le_sub_one_of_pos hx0
  rw [Real.log_mul (by norm_num) hx0.ne']
  have hnonneg : 0 ≤ Real.log 1600 + Real.log x :=
    add_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg hx)
  have hdiv : (Real.log 1600 + Real.log x) / Real.log 4 ≤
      Real.log 1600 + Real.log x := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log 4)).2
    nlinarith
  linarith

private theorem geometric_polynomial_sum (M : ℕ) :
    (∑ r ∈ Finset.range M, (13 + (r : ℝ)) * (1 / 7 : ℝ) ^ r) =
      553 / 36 - (553 / 36 + 7 / 6 * M) * (1 / 7 : ℝ) ^ M := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    push_cast
    ring

theorem geometric_polynomial_sum_le (M : ℕ) :
    (∑ r ∈ Finset.range M, (13 + (r : ℝ)) * (1 / 7 : ℝ) ^ r) ≤ 553 / 36 := by
  rw [geometric_polynomial_sum]
  have h : 0 ≤ (553 / 36 + 7 / 6 * (M : ℝ)) * (1 / 7 : ℝ) ^ M := by positivity
  linarith

private theorem floor_bin_bounds {a : ℝ} (ha : 2 ≤ a) :
    ((⌊a⌋₊ - 2 : ℕ) : ℝ) + 2 ≤ a ∧ a < ((⌊a⌋₊ - 2 : ℕ) : ℝ) + 3 := by
  have hf : 2 ≤ ⌊a⌋₊ := Nat.le_floor ha
  have hsum : ((⌊a⌋₊ - 2 : ℕ) : ℝ) + 2 = (⌊a⌋₊ : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hf
  have hlo := Nat.floor_le (by linarith : 0 ≤ a)
  have hhi := Nat.lt_floor_add_one a
  constructor <;> linarith

/-- A finite, explicit substitute for the integral estimate in (B.14). -/
theorem kraft_sum_le_of_linear_count {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (ha : ∀ i ∈ s, 2 ≤ a i)
    (hcount : ∀ x : ℝ, 2 ≤ x →
      ((s.filter fun i => a i ≤ x).card : ℝ) ≤ 4 * δ * (10 + x) * Real.exp (2 * x)) :
    (∑ i ∈ s, Real.exp (-(4 * a i))) ≤ (79 / 9) * δ := by
  classical
  let b : ι → ℕ := fun i => ⌊a i⌋₊ - 2
  let M := s.sup b + 1
  have hb : ∀ i ∈ s, b i ∈ Finset.range M := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup hi))
  have hbin (r : ℕ) :
      (∑ i ∈ s with b i = r, Real.exp (-(4 * a i))) ≤
        (4 * δ / 7) * ((13 + (r : ℝ)) * (1 / 7 : ℝ) ^ r) := by
    have hbds (i : ι) (hi : i ∈ s.filter fun j => b j = r) :
        (r : ℝ) + 2 ≤ a i ∧ a i < (r : ℝ) + 3 := by
      obtain ⟨his, hir⟩ := Finset.mem_filter.mp hi
      simpa only [show ⌊a i⌋₊ - 2 = r from hir] using floor_bin_bounds (ha i his)
    have hs : (s.filter fun i => b i = r) ⊆ s.filter (fun i => a i ≤ (r : ℝ) + 3) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1, (hbds i hi).2.le⟩
    have hc : ((s.filter fun i => b i = r).card : ℝ) ≤
        4 * δ * (13 + (r : ℝ)) * Real.exp (2 * ((r : ℝ) + 3)) := by
      have h := (Nat.cast_le.mpr (Finset.card_le_card hs)).trans
        (hcount ((r : ℝ) + 3) (by have := Nat.cast_nonneg (α := ℝ) r; linarith))
      simpa only [show (10 : ℝ) + ((r : ℝ) + 3) = 13 + r by ring] using h
    have hexp : Real.exp (-2 * ((r : ℝ) + 1)) ≤ (1 / 7 : ℝ) ^ (r + 1) := by
      have hid : Real.exp (-2 * ((r : ℝ) + 1)) = Real.exp (-2) ^ (r + 1) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [hid]
      exact pow_le_pow_left₀ (Real.exp_nonneg _) exp_neg_two_le_seventh _
    calc
      (∑ i ∈ s with b i = r, Real.exp (-(4 * a i))) ≤
          ∑ _i ∈ s with b _i = r, Real.exp (-4 * ((r : ℝ) + 2)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Real.exp_le_exp.mpr (by nlinarith [(hbds i hi).1])
      _ = ((s.filter fun i => b i = r).card : ℝ) * Real.exp (-4 * ((r : ℝ) + 2)) := by
        simp [nsmul_eq_mul]
      _ ≤ (4 * δ * (13 + (r : ℝ)) * Real.exp (2 * ((r : ℝ) + 3))) *
          Real.exp (-4 * ((r : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
      _ = (4 * δ * (13 + (r : ℝ))) * Real.exp (-2 * ((r : ℝ) + 1)) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ (4 * δ * (13 + (r : ℝ))) * (1 / 7 : ℝ) ^ (r + 1) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = _ := by rw [pow_succ]; ring
  calc
    (∑ i ∈ s, Real.exp (-(4 * a i))) =
        ∑ r ∈ Finset.range M, ∑ i ∈ s with b i = r, Real.exp (-(4 * a i)) :=
      (Finset.sum_fiberwise_of_maps_to hb _).symm
    _ ≤ ∑ r ∈ Finset.range M, (4 * δ / 7) * ((13 + (r : ℝ)) * (1 / 7 : ℝ) ^ r) :=
      Finset.sum_le_sum (fun r _ => hbin r)
    _ = (4 * δ / 7) * ∑ r ∈ Finset.range M, (13 + (r : ℝ)) * (1 / 7 : ℝ) ^ r :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (4 * δ / 7) * (553 / 36) :=
      mul_le_mul_of_nonneg_left (geometric_polynomial_sum_le M) (by positivity)
    _ = (79 / 9) * δ := by ring

/-- The Kraft inequality needed by (B.15), assuming the actual scale count (B.13). -/
theorem kraft_sum_lt_one_of_scale_count {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 10)
    (ha : ∀ i ∈ s, Real.log δ⁻¹ ≤ a i)
    (hcount : ∀ x : ℝ, 1 ≤ x → ((s.filter fun i => a i ≤ x).card : ℝ) ≤
      4 * δ * (Real.log (1600 * x) / Real.log 4 + 2) * Real.exp (2 * x)) :
    (∑ i ∈ s, Real.exp (-(4 * a i))) < 1 := by
  have hlog : 2 ≤ Real.log δ⁻¹ := by
    have hinv : (10 : ℝ) ≤ δ⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hδ0).2
      linarith
    exact log_ten_gt_two.le.trans (Real.log_le_log (by norm_num) hinv)
  have hbound := kraft_sum_le_of_linear_count s a hδ0.le
    (fun i hi => hlog.trans (ha i hi)) (fun x hx =>
      (hcount x (by linarith)).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (log_window_le_linear (by linarith)) (by positivity))
          (Real.exp_nonneg _)))
  linarith

end GapEntropy
