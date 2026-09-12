import GapEntropy.UniversalReferenceCost
import GapEntropy.ReservationBudget

/-! F.3's actual nonreference call budgets and the small-set logarithmic surcharge. -/
noncomputable section
open scoped BigOperators
namespace GapEntropy.UniversalCallCost
open UniversalCall UniversalEnvelopeCost

/-- Charging the PAC budget at every call only enlarges the actual nonreference
reservation, since later calls do not repeat PAC selection. -/
theorem nonreference_budget_le {s : ℕ} (hs : 0 < s) {d α : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    ((medianBudget s d α + laterBudget s d α : ℕ) : ℝ) ≤
      6500000 * ((s : ℝ) * (d ^ 2)⁻¹) * Real.log (128 / α) := by
  have hnat : medianBudget s d α + laterBudget s d α ≤ EliminationTape.declaredCost s d α := by
    unfold medianBudget EliminationPolicy.medianBudget laterBudget EliminationTape.declaredCost
    omega
  exact (show ((medianBudget s d α + laterBudget s d α : ℕ) : ℝ) ≤
      (EliminationTape.declaredCost s d α : ℝ) by exact_mod_cast hnat).trans
    (by simpa only [mul_assoc] using EliminationTape.declaredCost_le hs hd hd1 hα hα1)

/-- The source confidence rule written in real work units. -/
def callAlpha (δ h : ℝ) (j s : ℕ) (w : ℝ) : ℝ :=
  (δ / 1024) * w / (1024 * h) * Reservation.smallFactor j s

theorem smallFactor_pos (j s : ℕ) : 0 < Reservation.smallFactor j s := by
  unfold Reservation.smallFactor
  split_ifs <;> positivity

theorem callAlpha_pos {δ h w : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hw : 0 < w) (j s : ℕ) :
    0 < callAlpha δ h j s w := by
  unfold callAlpha
  exact mul_pos (by positivity) (smallFactor_pos j s)

/-- Exact baseline/surcharge splitting, with the small-size branch recomputed
from the current number of active arms. -/
theorem log_callAlpha {δ h w : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hw : 0 < w) (j s : ℕ) :
    Real.log (128 / callAlpha δ h j s w) =
      Real.log ((134217728 * h / δ) / w) +
        if 2 ≤ s ∧ s ≤ 7 then 2 * Real.log (j + 1 : ℝ) else 0 := by
  unfold callAlpha Reservation.smallFactor
  split_ifs with hs
  · have he : 128 / (δ / 1024 * w / (1024 * h) * (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹) =
        ((134217728 * h / δ) / w) * (j + 1 : ℝ) ^ 2 := by
      push_cast
      field_simp
      ring
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    norm_num
  · simp only [mul_one, add_zero]
    congr 1
    field_simp
    ring

theorem charge_callAlpha {δ h w : ℝ} (hδ : 0 < δ) (hh : 0 < h) (hw : 0 < w) (j s : ℕ) :
    w * Real.log (128 / callAlpha δ h j s w) =
      charge (134217728 * h / δ) w +
        if 2 ≤ s ∧ s ≤ 7 then 2 * w * Real.log (j + 1 : ℝ) else 0 := by
  rw [log_callAlpha hδ hh hw]
  unfold charge
  split_ifs <;> ring

/-- F.7's numerical summation once the actual halving trajectory has proved
that its small-set input sizes sum to at most 13 at each scale. -/
theorem small_surcharge_le {n : ℕ} (I : Instance n) (j : ℕ)
    (smallWork : ℕ → ℝ)
    (hwork : ∀ k ∈ Finset.range (I.lastBucket + 1), smallWork k ≤ 13 * (4 : ℝ) ^ k) :
    (∑ k ∈ Finset.range (I.lastBucket + 1), 2 * smallWork k * Real.log (j + 1 : ℝ)) ≤
      140 * I.twoArmHardness * Real.log (j + 1 : ℝ) := by
  have hj : 0 ≤ Real.log (j + 1 : ℝ) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hs := Finset.sum_le_sum (fun k hk =>
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hwork k hk)
      (show (0 : ℝ) ≤ 2 by norm_num)) hj)
  have he : (∑ k ∈ Finset.range (I.lastBucket + 1),
      2 * (13 * (4 : ℝ) ^ k) * Real.log (j + 1 : ℝ)) =
      26 * (∑ k ∈ Finset.range (I.lastBucket + 1), (4 : ℝ) ^ k) * Real.log (j + 1 : ℝ) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he] at hs
  have hp := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (UniversalReferenceCost.sum_four_pow_le I)
      (show (0 : ℝ) ≤ 26 by norm_num)) hj
  have hD : 0 ≤ I.twoArmHardness := by linarith [I.one_le_twoArmHardness]
  have hx := mul_nonneg hD hj
  nlinarith

/-- F.9 after separately charging baseline work, small-size surcharges, and
one full reference estimate per scale. Its execution-accounting premises are
explicit, so this algebraic assembly cannot substitute for a path proof. -/
theorem combine_favorable_costs {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) (j : ℕ) (hH : I.hardness ≤ (2 : ℝ) ^ j)
    (total baseline surcharge reference : ℝ)
    (htotal : total ≤ 6500000 * (baseline + surcharge) + reference)
    (hbase : baseline ≤ 6000 * I.hardness *
      (confidenceCost δ + I.gapEntropy + 1 + Real.log ((2 : ℝ) ^ j / I.hardness)))
    (hsurcharge : surcharge ≤ 140 * I.twoArmHardness * Real.log (j + 1 : ℝ))
    (href : reference ≤ 100000 * I.twoArmHardness *
      (confidenceCost δ + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness)) :
    total ≤ 40000000000 * UniversalCapAnalysis.favorableCost I δ j := by
  have hH0 := I.hardness_pos
  have hD0 : 0 < I.twoArmHardness := by linarith [I.one_le_twoArmHardness]
  have hL := UniversalCapAnalysis.one_le_confidenceCost hδ
  have hE := I.gapEntropy_nonneg
  have hy : 0 ≤ Real.log ((2 : ℝ) ^ j / I.hardness) :=
    Real.log_nonneg ((one_le_div hH0).mpr hH)
  have hj : 0 ≤ Real.log (j + 1 : ℝ) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)
  have hell := iteratedLog_pos hD0.le
  have hX : 0 ≤ I.hardness * (confidenceCost δ + I.gapEntropy + 1 +
      Real.log ((2 : ℝ) ^ j / I.hardness)) := by positivity
  have hY : 0 ≤ I.twoArmHardness *
      (confidenceCost δ + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness) := by positivity
  have hYj : I.twoArmHardness * Real.log (j + 1 : ℝ) ≤ I.twoArmHardness *
      (confidenceCost δ + Real.log (j + 1 : ℝ) + iteratedLog I.twoArmHardness) := by
    apply mul_le_mul_of_nonneg_left (by linarith) hD0.le
  unfold UniversalCapAnalysis.favorableCost
  nlinarith

/-- A fixed cap constant sufficient for the proved numerical favorable-cost
bound. It does not depend on any instance quantity. -/
def sampleCapConstant : ℝ := 1000000000000

theorem favorable_bound_fits_cap {n : ℕ} (I : Instance n) {δ : ℝ}
    (hδ : ValidConfidence δ) (j : ℕ)
    (hfit : UniversalCapAnalysis.complexityTarget I δ ≤ (2 : ℝ) ^ j * confidenceCost δ)
    {total : ℝ} (htotal : total ≤ 40000000000 * UniversalCapAnalysis.favorableCost I δ j) :
    total ≤ (⌈sampleCapConstant * (2 : ℝ) ^ j * confidenceCost δ⌉₊ : ℝ) := by
  have h := mul_le_mul_of_nonneg_left (UniversalCapAnalysis.favorableCost_le I hδ j hfit)
    (show (0 : ℝ) ≤ 40000000000 by norm_num)
  have hL := confidenceCost_pos hδ
  have hp : 0 ≤ (2 : ℝ) ^ j * confidenceCost δ := by positivity
  have hc := Nat.le_ceil (sampleCapConstant * (2 : ℝ) ^ j * confidenceCost δ)
  unfold sampleCapConstant at *
  nlinarith

end GapEntropy.UniversalCallCost
