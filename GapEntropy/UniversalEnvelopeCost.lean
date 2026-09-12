import GapEntropy.WorkEntropy
import GapEntropy.UniversalCapAnalysis

/-!
# Entropy of the favorable continuation envelope

The infinite continuation index has ratio 3/4. Its exact logarithmic cost
splits into the finite scale entropy and an absolute geometric entropy, as in F.6.
-/
noncomputable section
open scoped BigOperators
namespace GapEntropy.UniversalEnvelopeCost

def geometricEntropy : ℝ := Real.log 4 + 3 * Real.log (4 / 3)
def envelope (w : ℝ) (r : ℕ) : ℝ := 4 * w * (3 / 4 : ℝ) ^ r
def charge (A x : ℝ) : ℝ := x * Real.log (A / x)

theorem envelope_pos {w : ℝ} (hw : 0 < w) (r : ℕ) : 0 < envelope w r := by
  unfold envelope
  positivity

private theorem log_three_quarters : Real.log (3 / 4 : ℝ) = - Real.log (4 / 3) := by
  rw [show (3 / 4 : ℝ) = (4 / 3 : ℝ)⁻¹ by norm_num, Real.log_inv]

theorem hasSum_envelope (w : ℝ) : HasSum (envelope w) (16 * w) := by
  have h := (hasSum_geometric_of_norm_lt_one (ξ := (3 / 4 : ℝ)) (by norm_num)).mul_left (4 * w)
  convert! h using 1
  norm_num
  ring

theorem charge_envelope_eq {A w : ℝ} (hA : 0 < A) (hw : 0 < w) (r : ℕ) :
    charge A (envelope w r) = (3 / 4 : ℝ) ^ r *
      (4 * w * Real.log (A / (4 * w)) + r * (4 * w * Real.log (4 / 3))) := by
  unfold charge envelope
  rw [Real.log_div hA.ne' (by positivity),
    Real.log_mul (by positivity : 4 * w ≠ 0) (by positivity),
    Real.log_pow, log_three_quarters, Real.log_div hA.ne' (by positivity)]
  ring

theorem hasSum_charge_envelope {A w : ℝ} (hA : 0 < A) (hw : 0 < w) :
    HasSum (fun r => charge A (envelope w r))
      (16 * w * (Real.log (A / (4 * w)) + 3 * Real.log (4 / 3))) := by
  have hg := hasSum_geometric_of_norm_lt_one (ξ := (3 / 4 : ℝ)) (by norm_num)
  have hm := hasSum_coe_mul_geometric_of_norm_lt_one (r := (3 / 4 : ℝ)) (by norm_num)
  have h := (hg.mul_left (4 * w * Real.log (A / (4 * w)))).add
    (hm.mul_left (4 * w * Real.log (4 / 3)))
  convert! h using 1
  · ext r
    rw [charge_envelope_eq hA hw]
    ring
  · norm_num
    ring

/-- Exact product-entropy decomposition for any finite positive scale weights. -/
theorem sum_charge_envelope_eq {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    {A : ℝ} (hA : 0 < A) (hw : ∀ k ∈ s, 0 < w k) (hs : s.Nonempty) :
    (∑ k ∈ s, ∑' r, charge A (envelope (w k) r)) =
      16 * (∑ k ∈ s, w k) *
        (Real.log (A / (16 * ∑ k ∈ s, w k)) +
          finiteEntropy s (fun k => w k / ∑ k ∈ s, w k) + geometricEntropy) := by
  let W : ℝ := ∑ k ∈ s, w k
  have hW : 0 < W := Finset.sum_pos hw hs
  have heq (k : ι) (hk : k ∈ s) :
      Real.log (A / (4 * w k)) = Real.log (A / (16 * W)) + Real.log 4 +
        Real.log (w k / W)⁻¹ := by
    have hkw := hw k hk
    rw [Real.log_div hA.ne' (by positivity : 4 * w k ≠ 0),
      Real.log_div hA.ne' (by positivity : 16 * W ≠ 0),
      Real.log_inv, Real.log_div (hw k hk).ne' hW.ne',
      Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (hw k hk).ne',
      Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hW.ne']
    have h16 : Real.log (16 : ℝ) = 2 * Real.log 4 := by
      have h := Real.log_pow (4 : ℝ) 2
      norm_num at h
      exact h
    rw [h16]
    ring
  have hterm (k : ι) (hk : k ∈ s) :
      (∑' r, charge A (envelope (w k) r)) =
        16 * (w k * (Real.log (A / (16 * W)) + geometricEntropy) +
          W * ((w k / W) * Real.log (w k / W)⁻¹)) := by
    rw [(hasSum_charge_envelope hA (hw k hk)).tsum_eq, heq k hk]
    unfold geometricEntropy
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  change 16 * (W * (Real.log (A / (16 * W)) + geometricEntropy) +
    W * finiteEntropy s (fun k => w k / W)) =
    16 * W * (Real.log (A / (16 * W)) + finiteEntropy s (fun k => w k / W) + geometricEntropy)
  ring

/-- Monotonicity of x log(A/x) on the interval needed for the work envelope.
The proof uses log(u)≤u−1, with no differentiability assumption. -/
theorem charge_mono {A x y : ℝ} (hA : 0 < A) (hx : 0 < x) (hxy : x ≤ y)
    (hlog : 1 ≤ Real.log (A / y)) : charge A x ≤ charge A y := by
  have hy := hx.trans_le hxy
  have heq : Real.log (A / x) = Real.log (A / y) + Real.log (y / x) := by
    rw [Real.log_div hA.ne' hx.ne', Real.log_div hA.ne' hy.ne',
      Real.log_div hy.ne' hx.ne']
    ring
  have hl := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy hx)) hx.le
  have he : x * (y / x) = y := by field_simp
  unfold charge
  rw [heq]
  nlinarith

end GapEntropy.UniversalEnvelopeCost

namespace GapEntropy.Instance
open UniversalEnvelopeCost
variable {n : ℕ} (I : Instance n)

/-- The exact F.6 entropy decomposition for the original instance's dyadic profile. -/
theorem sum_envelope_charge_eq {A : ℝ} (hA : 0 < A) :
    (∑ k ∈ Finset.range (I.lastBucket + 1), ∑' r,
      charge A (envelope (I.scaleWork k) r)) =
      16 * I.workEnvelope * (Real.log (A / (16 * I.workEnvelope)) +
        I.workEntropy + geometricEntropy) := by
  have h := sum_charge_envelope_eq (Finset.range (I.lastBucket + 1)) I.scaleWork hA
    (fun k _ => I.scaleWork_pos k) (Finset.nonempty_range_iff.mpr (by omega))
  rw [← I.workEnvelope_eq_sum] at h
  exact h

end GapEntropy.Instance

namespace GapEntropy.UniversalEnvelopeCost

private theorem log_four_le_two : Real.log (4 : ℝ) ≤ 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  linarith [TargetAttempt.log_two_le_one]

theorem geometricEntropy_le : geometricEntropy ≤ 4 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  unfold geometricEntropy
  linarith [log_four_le_two]

theorem workEntropyConstant_le : WorkEnvelope.entropyConstant ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
  unfold WorkEnvelope.entropyConstant
  linarith [log_four_le_two]

/-- The baseline logarithm uses only the total envelope, not the number of scales. -/
theorem log_baseline_le {n : ℕ} (I : Instance n) {δ h : ℝ}
    (hδ : ValidConfidence δ) (hH : I.hardness ≤ h) :
    Real.log ((134217728 * h / δ) / (16 * I.workEnvelope)) ≤
      confidenceCost δ + Real.log (h / I.hardness) + 23 := by
  have hH0 := I.hardness_pos
  have hh : 0 < h := hH0.trans_le hH
  have hW0 := I.workEnvelope_pos
  have hδ0 := hδ.1
  have harg : (134217728 * h / δ) / (16 * I.workEnvelope) ≤
      (134217728 * h / δ) / (16 * I.hardness) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left I.hardness_le_workEnvelope_lt.1 (by norm_num))
  have hlog := Real.log_le_log (by positivity) harg
  have he : (134217728 * h / δ) / (16 * I.hardness) =
      (2 : ℝ) ^ 23 * (h / I.hardness) * δ⁻¹ := by
    norm_num
    ring
  rw [he, Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  unfold confidenceCost
  linarith [TargetAttempt.log_two_le_one]

/-- F.6 with an explicit universal constant for the baseline call charges. -/
theorem sum_envelope_charge_le {n : ℕ} (I : Instance n) {δ h : ℝ}
    (hδ : ValidConfidence δ) (hH : I.hardness ≤ h) :
    (∑ k ∈ Finset.range (I.lastBucket + 1), ∑' r,
      charge (134217728 * h / δ) (envelope (I.scaleWork k) r)) ≤
      6000 * I.hardness *
        (confidenceCost δ + I.gapEntropy + 1 + Real.log (h / I.hardness)) := by
  have hH0 := I.hardness_pos
  have hh : 0 < h := hH0.trans_le hH
  have hδ0 := hδ.1
  rw [I.sum_envelope_charge_eq (by positivity)]
  have hlog := log_baseline_le I hδ hH
  have hE := I.workEntropy_le
  have hEc := workEntropyConstant_le
  have hgeo := geometricEntropy_le
  have hL := UniversalCapAnalysis.one_le_confidenceCost hδ
  have hEnt := I.gapEntropy_nonneg
  have hy : 0 ≤ Real.log (h / I.hardness) :=
    Real.log_nonneg ((one_le_div hH0).mpr hH)
  have hbracket : Real.log ((134217728 * h / δ) / (16 * I.workEnvelope)) +
      I.workEntropy + geometricEntropy ≤
      35 * (confidenceCost δ + I.gapEntropy + 1 + Real.log (h / I.hardness)) := by
    linarith
  have hW := I.hardness_le_workEnvelope_lt.2
  have hW0 := I.workEnvelope_pos
  have hb0 : 0 ≤ confidenceCost δ + I.gapEntropy + 1 + Real.log (h / I.hardness) := by
    linarith
  have hm := mul_le_mul_of_nonneg_left hbracket (show 0 ≤ 16 * I.workEnvelope by positivity)
  have hWmul := mul_le_mul_of_nonneg_right
    (show 16 * I.workEnvelope ≤ 171 * I.hardness by linarith) (show 0 ≤
      35 * (confidenceCost δ + I.gapEntropy + 1 + Real.log (h / I.hardness)) by positivity)
  have hbH := mul_nonneg hH0.le hb0
  nlinarith

end GapEntropy.UniversalEnvelopeCost
