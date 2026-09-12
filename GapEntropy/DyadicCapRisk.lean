import GapEntropy.CoreRiskSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Real

/-! The three dyadic work-cap ranges in E.4/E.6, for the actual caps `M0 * 2^j`. -/
noncomputable section
open scoped BigOperators
open MeasureTheory
namespace GapEntropy.DyadicCapRisk

def cap (M0 : ℝ) (j : ℕ) : ℝ := M0 * 2 ^ j

theorem cap_pos {M0 : ℝ} (hM0 : 0 < M0) (j : ℕ) : 0 < cap M0 j := by
  unfold cap
  positivity

theorem cap_add (M0 : ℝ) (j k : ℕ) : cap M0 (j + k) = cap M0 j * 2 ^ k := by
  simp [cap, pow_add, mul_assoc]

theorem cap_sub {j k : ℕ} (hjk : j ≤ k) (M0 : ℝ) :
    cap M0 k = cap M0 j * 2 ^ (k - j) := by
  simpa only [Nat.add_sub_of_le hjk] using cap_add M0 j (k - j)

theorem succ_le_two_pow (k : ℕ) : (k + 1 : ℝ) ≤ 2 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- An injective subset of a geometric series has no greater total mass. -/
theorem sum_geometric_reindex_le (F : Finset ℕ) (f : ℕ → ℕ)
    (hf : Set.InjOn f (F : Set ℕ)) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (∑ j ∈ F, q ^ f j) ≤ 1 / (1 - q) := by
  have hs := hasSum_geometric_of_norm_lt_one (show ‖q‖ < 1 by
    rw [Real.norm_eq_abs, abs_of_nonneg hq0]; exact hq1)
  rw [← Finset.sum_image hf]
  exact (hs.summable.sum_le_tsum (F.image f) (fun i _ => pow_nonneg hq0 i)).trans_eq
    (by simpa only [one_div] using hs.tsum_eq)

/-- The elementary logarithmic margin needed by the small-cap tail holds for p≤1/16. -/
theorem logarithmic_margin {p : ℝ} (hp : 0 < p) (hp16 : p ≤ 1 / 16) :
    1 / 3 ≤ Real.log (1 / (2 * p)) - 1 := by
  have h8 : (8 : ℝ) ≤ 1 / (2 * p) := (le_div_iff₀ (by positivity)).mpr (by linarith)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 8) h8
  have htwo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have heq : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 3
    norm_num at h
    exact h
  rw [heq] at hlog
  norm_num at htwo
  linarith

/-- Small-cap exponential tail factors sum to at most one, including a truncated or empty range. -/
theorem sum_small_factors_le {M0 h L : ℝ} (hM0 : 0 < M0) (hL : 1 / 3 ≤ L)
    (F : Finset ℕ) (hsmall : ∀ j ∈ F, 192 * cap M0 j ≤ h) :
    (∑ j ∈ F, Real.exp (-(h / (64 * cap M0 j)) * L)) ≤ 1 := by
  classical
  by_cases hF : F.Nonempty
  · let J := F.max' hF
    have hJ : J ∈ F := Finset.max'_mem _ _
    have hle (j : ℕ) (hj : j ∈ F) : j ≤ J := Finset.le_max' _ _ hj
    have hinj : Set.InjOn (fun j => J - j) (F : Set ℕ) := by
      intro i hi j hj heq
      have := hle i hi
      have := hle j hj
      dsimp at heq
      omega
    have he : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
      rw [Real.exp_neg]
      have hexp := Real.add_one_le_exp (1 : ℝ)
      rw [← one_div]
      exact (div_le_iff₀ (Real.exp_pos 1)).mpr (by linarith)
    calc
      (∑ j ∈ F, Real.exp (-(h / (64 * cap M0 j)) * L)) ≤
          ∑ j ∈ F, (1 / 2 : ℝ) ^ (J - j + 1) := by
        apply Finset.sum_le_sum
        intro j hj
        have hc := cap_pos hM0 j
        have hratio : 3 * 2 ^ (J - j) ≤ h / (64 * cap M0 j) := by
          apply (le_div_iff₀ (by positivity)).mpr
          have h := hsmall J hJ
          rw [cap_sub (hle j hj) M0] at h
          nlinarith
        have hk := succ_le_two_pow (J - j)
        have hx : -(h / (64 * cap M0 j)) * L ≤ -((J - j + 1 : ℕ) : ℝ) := by
          have hratio0 : 0 ≤ h / (64 * cap M0 j) :=
            (by positivity : (0 : ℝ) ≤ 3 * 2 ^ (J - j)).trans hratio
          have hprod := mul_le_mul_of_nonneg_left hL hratio0
          push_cast
          nlinarith
        calc
          Real.exp (-(h / (64 * cap M0 j)) * L) ≤
              Real.exp (-((J - j + 1 : ℕ) : ℝ)) := Real.exp_le_exp.mpr hx
          _ = Real.exp (-1) ^ (J - j + 1) := by
            rw [← Real.exp_nat_mul]
            congr 1
            ring
          _ ≤ (1 / 2 : ℝ) ^ (J - j + 1) := pow_le_pow_left₀ (Real.exp_nonneg _) he _
      _ = (1 / 2 : ℝ) * ∑ j ∈ F, (1 / 2 : ℝ) ^ (J - j) := by
        simp only [pow_succ']
        rw [Finset.mul_sum]
      _ ≤ 1 := by
        have hg := sum_geometric_reindex_le F (fun j => J - j) hinj
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
        norm_num at hg
        linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    simp

/-- At most nine intermediate caps; the proof in fact gives eight. -/
theorem intermediate_card_le {M0 h : ℝ} (hM0 : 0 < M0) (F : Finset ℕ)
    (hlower : ∀ j ∈ F, h < 192 * cap M0 j) (hupper : ∀ j ∈ F, cap M0 j < h) :
    F.card ≤ 9 := by
  classical
  by_cases hF : F.Nonempty
  · let J := F.min' hF
    have hJ : J ∈ F := Finset.min'_mem _ _
    have hle (j : ℕ) (hj : j ∈ F) : J ≤ j := Finset.min'_le _ _ hj
    have hsub : F ⊆ Finset.Icc J (J + 7) := by
      intro j hj
      refine Finset.mem_Icc.mpr ⟨hle j hj, ?_⟩
      by_contra hh
      have hd : 8 ≤ j - J := by omega
      have hp : (256 : ℝ) ≤ 2 ^ (j - J) := by
        calc
          (256 : ℝ) = 2 ^ (8 : ℕ) := by norm_num
          _ ≤ 2 ^ (j - J) := pow_le_pow_right₀ (by norm_num) hd
      have hc := cap_pos hM0 J
      have hjh := hupper j hj
      rw [cap_sub (hle j hj) M0] at hjh
      have hm := mul_le_mul_of_nonneg_left hp hc.le
      have hh := hlower J hJ
      nlinarith
    have hc := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at hc
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hF]

/-- Geometric square-root interpolation in the large-cap range. This uses both bounds on
the same event and does not assert independence of the core and collapse events. -/
theorem sum_large_risks_le {M0 h A η : ℝ} (hM0 : 0 < M0) (hh : 0 ≤ h) (hA : 0 ≤ A)
    (F : Finset ℕ) (hlarge : ∀ j ∈ F, h ≤ cap M0 j) (e : ℕ → ℝ)
    (he0 : ∀ j ∈ F, 0 ≤ e j) (heA : ∀ j ∈ F, e j ≤ A)
    (hebatch : ∀ j ∈ F, e j ≤ 3 * η ^ (4 : ℕ) * (h / cap M0 j) ^ (3 : ℕ)) :
    (∑ j ∈ F, e j) ≤ 3 * η ^ 2 * Real.sqrt A := by
  classical
  by_cases hF : F.Nonempty
  · let J := F.min' hF
    have hJ : J ∈ F := Finset.min'_mem _ _
    have hle (j : ℕ) (hj : j ∈ F) : J ≤ j := Finset.min'_le _ _ hj
    have hinj : Set.InjOn (fun j => j - J) (F : Set ℕ) := by
      intro i hi j hj heq
      have := hle i hi
      have := hle j hj
      dsimp at heq
      omega
    have hpoint (j : ℕ) (hj : j ∈ F) :
        e j ≤ (7 / 4 : ℝ) * η ^ 2 * Real.sqrt A * (3 / 8 : ℝ) ^ (j - J) := by
      have hc := cap_pos hM0 j
      have hratio0 : 0 ≤ h / cap M0 j := div_nonneg hh hc.le
      have hratio : h / cap M0 j ≤ (1 / 2 : ℝ) ^ (j - J) := by
        apply (div_le_iff₀ hc).mpr
        calc
          h ≤ cap M0 J := hlarge J hJ
          _ = (1 / 2 : ℝ) ^ (j - J) * cap M0 j := by
            rw [cap_sub (hle j hj) M0, one_div_pow]
            field_simp
      have hpow : (h / cap M0 j) ^ (3 : ℕ) ≤ ((3 / 8 : ℝ) ^ (j - J)) ^ 2 := by
        calc
          (h / cap M0 j) ^ (3 : ℕ) ≤ ((1 / 2 : ℝ) ^ (j - J)) ^ 3 :=
            pow_le_pow_left₀ hratio0 hratio 3
          _ = (1 / 8 : ℝ) ^ (j - J) := by
            rw [← pow_mul, Nat.mul_comm (j - J) 3, pow_mul]
            norm_num
          _ ≤ (9 / 64 : ℝ) ^ (j - J) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
          _ = ((3 / 8 : ℝ) ^ (j - J)) ^ 2 := by
            rw [← pow_mul, Nat.mul_comm (j - J) 2, pow_mul]
            norm_num
      have hsq : (e j) ^ 2 ≤ A * (3 * η ^ (4 : ℕ) * (h / cap M0 j) ^ (3 : ℕ)) := by
        simpa only [pow_two] using mul_le_mul (heA j hj) (hebatch j hj) (he0 j hj) hA
      have hprod := mul_le_mul_of_nonneg_left hpow (show 0 ≤ A * (3 * η ^ (4 : ℕ)) by positivity)
      have hsq' : (e j) ^ 2 ≤
          ((7 / 4 : ℝ) * η ^ 2 * Real.sqrt A * (3 / 8 : ℝ) ^ (j - J)) ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hA]
        have hn : 0 ≤ A * η ^ (4 : ℕ) * ((3 / 8 : ℝ) ^ (j - J)) ^ 2 := by positivity
        nlinarith
      have htarget : 0 ≤ (7 / 4 : ℝ) * η ^ 2 * Real.sqrt A * (3 / 8 : ℝ) ^ (j - J) := by
        positivity
      nlinarith
    calc
      (∑ j ∈ F, e j) ≤ ∑ j ∈ F,
          (7 / 4 : ℝ) * η ^ 2 * Real.sqrt A * (3 / 8 : ℝ) ^ (j - J) :=
        Finset.sum_le_sum hpoint
      _ = ((7 / 4 : ℝ) * η ^ 2 * Real.sqrt A) * ∑ j ∈ F, (3 / 8 : ℝ) ^ (j - J) := by
        rw [Finset.mul_sum]
      _ ≤ 3 * η ^ 2 * Real.sqrt A := by
        have hg := sum_geometric_reindex_le F (fun j => j - J) hinj
          (by norm_num : (0 : ℝ) ≤ 3 / 8) (by norm_num : (3 / 8 : ℝ) < 1)
        have hm := mul_le_mul_of_nonneg_left hg
          (show 0 ≤ (7 / 4 : ℝ) * η ^ 2 * Real.sqrt A by positivity)
        norm_num at hm
        nlinarith [sq_nonneg η, Real.sqrt_nonneg A,
          mul_nonneg (sq_nonneg η) (Real.sqrt_nonneg A)]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hF]
    simp only [Finset.sum_empty]
    positivity

/-- All three cap ranges, including empty ranges and endpoints below the initial cap. -/
theorem sum_three_ranges_le {M0 h A η L : ℝ}
    (hM0 : 0 < M0) (hh : 0 ≤ h) (hA : 0 ≤ A) (hL : 1 / 3 ≤ L)
    (F : Finset ℕ) (e : ℕ → ℝ) (he0 : ∀ j ∈ F, 0 ≤ e j) (heA : ∀ j ∈ F, e j ≤ A)
    (hesmall : ∀ j ∈ F, 192 * cap M0 j ≤ h →
      e j ≤ A * Real.exp (-(h / (64 * cap M0 j)) * L))
    (hebatch : ∀ j ∈ F, h ≤ cap M0 j →
      e j ≤ 3 * η ^ (4 : ℕ) * (h / cap M0 j) ^ (3 : ℕ)) :
    (∑ j ∈ F, e j) ≤ 10 * A + 3 * η ^ 2 * Real.sqrt A := by
  classical
  let small := F.filter (fun j => 192 * cap M0 j ≤ h)
  let rest := F.filter (fun j => ¬192 * cap M0 j ≤ h)
  let middle := rest.filter (fun j => cap M0 j < h)
  let large := rest.filter (fun j => ¬cap M0 j < h)
  have hsmall : (∑ j ∈ small, e j) ≤ A := by
    calc
      (∑ j ∈ small, e j) ≤ ∑ j ∈ small, A * Real.exp (-(h / (64 * cap M0 j)) * L) :=
        Finset.sum_le_sum fun j hj => hesmall j (Finset.mem_filter.mp hj).1 (Finset.mem_filter.mp hj).2
      _ = A * ∑ j ∈ small, Real.exp (-(h / (64 * cap M0 j)) * L) := (Finset.mul_sum ..).symm
      _ ≤ A := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (sum_small_factors_le hM0 hL small (fun j hj => (Finset.mem_filter.mp hj).2)) hA
  have hmiddle : (∑ j ∈ middle, e j) ≤ 9 * A := by
    have hc := intermediate_card_le hM0 middle
      (fun j hj => lt_of_not_ge (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2)
      (fun j hj => (Finset.mem_filter.mp hj).2)
    have hcard : (middle.card : ℝ) ≤ 9 := by exact_mod_cast hc
    calc
      (∑ j ∈ middle, e j) ≤ ∑ _j ∈ middle, A := Finset.sum_le_sum fun j hj =>
        heA j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
      _ = middle.card * A := by simp
      _ ≤ 9 * A := mul_le_mul_of_nonneg_right hcard hA
  have hlarge : (∑ j ∈ large, e j) ≤ 3 * η ^ 2 * Real.sqrt A :=
    sum_large_risks_le hM0 hh hA large
      (fun j hj => le_of_not_gt (Finset.mem_filter.mp hj).2) e
      (fun j hj => he0 j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1)
      (fun j hj => heA j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1)
      (fun j hj => hebatch j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
        (le_of_not_gt (Finset.mem_filter.mp hj).2))
  have hsplit : (∑ j ∈ small, e j) + (∑ j ∈ rest, e j) = ∑ j ∈ F, e j :=
    Finset.sum_filter_add_sum_filter_not F _ e
  have hsplit' : (∑ j ∈ middle, e j) + (∑ j ∈ large, e j) = ∑ j ∈ rest, e j :=
    Finset.sum_filter_add_sum_filter_not rest _ e
  linarith

/-- The manuscript's original E.10 exponential expression in the combined cap bound. -/
theorem sum_three_ranges_probability_form {M0 h A η p : ℝ}
    (hM0 : 0 < M0) (hh : 0 ≤ h) (hA : 0 ≤ A) (hp : 0 < p) (hp16 : p ≤ 1 / 16)
    (F : Finset ℕ) (e : ℕ → ℝ) (he0 : ∀ j ∈ F, 0 ≤ e j) (heA : ∀ j ∈ F, e j ≤ A)
    (hesmall : ∀ j ∈ F, 192 * cap M0 j ≤ h →
      e j ≤ A * Real.exp (-(h / (64 * cap M0 j)) * Real.log (1 / (2 * p)) + h / (64 * cap M0 j)))
    (hebatch : ∀ j ∈ F, h ≤ cap M0 j →
      e j ≤ 3 * η ^ (4 : ℕ) * (h / cap M0 j) ^ (3 : ℕ)) :
    (∑ j ∈ F, e j) ≤ 10 * A + 3 * η ^ 2 * Real.sqrt A := by
  apply sum_three_ranges_le hM0 hh hA (logarithmic_margin hp hp16) F e he0 heA _ hebatch
  intro j hj hsmall
  have heq : -(h / (64 * cap M0 j)) * (Real.log (1 / (2 * p)) - 1) =
      -(h / (64 * cap M0 j)) * Real.log (1 / (2 * p)) + h / (64 * cap M0 j) := by ring
  rw [heq]
  exact hesmall j hj hsmall

/-- Countably many dyadic attempts for one fixed core. The input event inequalities may all
hold on the same probability space; no independence of attempts or of the two large-cap tests
is used. Fresh-attempt conditioning and event inclusions are separate inputs to this summation. -/
theorem probability_iUnion_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : ℕ → Set Ω)
    {M0 h A η p : ℝ} (hM0 : 0 < M0) (hh : 0 ≤ h) (hA : 0 ≤ A)
    (hp : 0 < p) (hp16 : p ≤ 1 / 16)
    (heA : ∀ j, μ.real (E j) ≤ A)
    (hesmall : ∀ j, 192 * cap M0 j ≤ h →
      μ.real (E j) ≤ A * Real.exp
        (-(h / (64 * cap M0 j)) * Real.log (1 / (2 * p)) + h / (64 * cap M0 j)))
    (hebatch : ∀ j, h ≤ cap M0 j →
      μ.real (E j) ≤ 3 * η ^ (4 : ℕ) * (h / cap M0 j) ^ (3 : ℕ)) :
    μ (⋃ j, E j) ≤ ENNReal.ofReal (10 * A + 3 * η ^ 2 * Real.sqrt A) := by
  rw [measure_iUnion_eq_iSup_accumulate]
  apply iSup_le
  intro T
  have heq : Set.accumulate E T = ⋃ j ∈ Finset.range (T + 1), E j := by
    ext ω
    simp only [Set.accumulate_def, Set.mem_iUnion, Finset.mem_range, Nat.lt_succ_iff]
  rw [heq]
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (by positivity)).mpr
  exact (measureReal_biUnion_finset_le _ _).trans
    (sum_three_ranges_probability_form hM0 hh hA hp hp16 (Finset.range (T + 1))
      (fun j => μ.real (E j)) (fun j _ => measureReal_nonneg) (fun j _ => heA j)
      (fun j _ => hesmall j) (fun j _ => hebatch j))

end GapEntropy.DyadicCapRisk
