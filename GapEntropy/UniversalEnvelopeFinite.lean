import GapEntropy.UniversalEnvelopeCost
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Finite actual call sets inject into the infinite scale/continuation envelope. -/
noncomputable section
open scoped BigOperators
namespace GapEntropy.UniversalEnvelopeCost

/-- Reusable finite subset comparison for a finite-by-countable nonnegative series. -/
theorem sum_injective_product_le {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (s : Finset ι) (scale : ι → κ) (index : ι → ℕ)
    (hinj : Set.InjOn (fun t => (scale t, index t)) (s : Set ι))
    (f : κ → ℕ → ℝ) (hf : ∀ k r, 0 ≤ f k r) (hs : ∀ k, Summable (f k)) :
    (∑ t ∈ s, f (scale t) (index t)) ≤ ∑ k, ∑' r, f k r := by
  classical
  have hprod : Summable (fun kr : κ × ℕ => f kr.1 kr.2) :=
    (summable_prod_of_nonneg (fun kr => hf kr.1 kr.2)).mpr ⟨hs, (hasSum_fintype _).summable⟩
  rw [← Finset.sum_image (f := fun kr : κ × ℕ => f kr.1 kr.2) hinj]
  apply (hprod.sum_le_tsum _ (fun kr _ => hf kr.1 kr.2)).trans_eq
  rw [hprod.tsum_prod, tsum_fintype]

/-- Every point of the continuation envelope is below its total mass. -/
theorem envelope_le_total {n : ℕ} (I : Instance n) {k : ℕ} (hk : k ≤ I.lastBucket) (r : ℕ) :
    envelope (I.scaleWork k) r ≤ 16 * I.workEnvelope := by
  have hw : I.scaleWork k ≤ I.workEnvelope := by
    rw [I.workEnvelope_eq_sum]
    exact Finset.single_le_sum (fun t _ => (I.scaleWork_pos t).le)
      (Finset.mem_range.mpr (by omega))
  have hp : (3 / 4 : ℝ) ^ r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ 4 * I.scaleWork k by positivity [I.scaleWork_pos k])
  unfold envelope
  nlinarith [I.workEnvelope_pos]

/-- Logarithmic monotonicity is valid all the way up to the actual base cap. -/
theorem one_le_log_at_base_cap {δ h v : ℝ} (hδ : ValidConfidence δ) (hh : 0 < h)
    (hv : 0 < v) (hvcap : v ≤ 1024 * h) :
    1 ≤ Real.log ((134217728 * h / δ) / v) := by
  have hδ0 := hδ.1
  apply (Real.le_log_iff_exp_le (by positivity)).mpr
  apply Real.exp_one_lt_three.le.trans
  apply (le_div_iff₀ hv).mpr
  apply (le_div_iff₀ hδ0).mpr
  have h := mul_le_mul_of_nonneg_right hvcap hδ0.le
  nlinarith [hδ.2]

theorem one_le_log_envelope {n : ℕ} (I : Instance n) {δ h : ℝ}
    (hδ : ValidConfidence δ) (hH : I.hardness ≤ h) {k : ℕ} (hk : k ≤ I.lastBucket) (r : ℕ) :
    1 ≤ Real.log ((134217728 * h / δ) / envelope (I.scaleWork k) r) := by
  apply one_le_log_at_base_cap hδ (I.hardness_pos.trans_le hH)
    (envelope_pos (I.scaleWork_pos k) r)
  have hW := I.hardness_le_workEnvelope_lt.2
  have he := envelope_le_total I hk r
  linarith [I.hardness_pos]

/-- Sum of all actual positive works, with no unproved expectation premise. -/
theorem sum_work_le_envelope {n : ℕ} {ι : Type*} (I : Instance n)
    (s : Finset ι) (scale : ι → Fin (I.lastBucket + 1)) (index : ι → ℕ)
    (hinj : Set.InjOn (fun t => (scale t, index t)) (s : Set ι))
    (work : ι → ℝ)
    (hwork : ∀ t ∈ s, work t ≤ envelope (I.scaleWork (scale t)) (index t)) :
    (∑ t ∈ s, work t) ≤ 16 * I.workEnvelope := by
  have h := (Finset.sum_le_sum hwork).trans
    (sum_injective_product_le s scale index hinj
      (fun k r => envelope (I.scaleWork k) r)
      (fun k r => (envelope_pos (I.scaleWork_pos k) r).le)
      (fun k => (hasSum_envelope (I.scaleWork k)).summable))
  apply h.trans_eq
  simp_rw [(hasSum_envelope _).tsum_eq]
  rw [Fin.sum_univ_eq_sum_range (fun k => 16 * I.scaleWork k),
    ← Finset.mul_sum, ← I.workEnvelope_eq_sum]

/-- Finite charged calls may stop anywhere in the favorable envelope. Their
sum is bounded by the full F.6 entropy expression, including prospective calls. -/
theorem sum_charge_le_envelope {n : ℕ} {ι : Type*} (I : Instance n)
    {δ h : ℝ} (hδ : ValidConfidence δ) (hH : I.hardness ≤ h)
    (s : Finset ι) (scale : ι → Fin (I.lastBucket + 1)) (index : ι → ℕ)
    (hinj : Set.InjOn (fun t => (scale t, index t)) (s : Set ι))
    (work : ι → ℝ) (hwpos : ∀ t ∈ s, 0 < work t)
    (hwork : ∀ t ∈ s, work t ≤ envelope (I.scaleWork (scale t)) (index t)) :
    (∑ t ∈ s, charge (134217728 * h / δ) (work t)) ≤
      6000 * I.hardness *
        (confidenceCost δ + I.gapEntropy + 1 + Real.log (h / I.hardness)) := by
  have hh : 0 < h := I.hardness_pos.trans_le hH
  have hδ0 := hδ.1
  have hA : 0 < 134217728 * h / δ := by positivity
  have hmono := Finset.sum_le_sum (fun t ht =>
    charge_mono hA (hwpos t ht) (hwork t ht)
      (one_le_log_envelope I hδ hH (Nat.le_of_lt_succ (scale t).isLt) (index t)))
  have hnonneg (k : Fin (I.lastBucket + 1)) (r : ℕ) :
      0 ≤ charge (134217728 * h / δ) (envelope (I.scaleWork k) r) := by
    unfold charge
    exact mul_nonneg (envelope_pos (I.scaleWork_pos k) r).le
      ((show (0 : ℝ) ≤ 1 by norm_num).trans
        (one_le_log_envelope I hδ hH (Nat.le_of_lt_succ k.isLt) r))
  have hprodSum := sum_injective_product_le s scale index hinj
    (fun k r => charge (134217728 * h / δ) (envelope (I.scaleWork k) r))
    hnonneg (fun k => (hasSum_charge_envelope hA (I.scaleWork_pos k)).summable)
  apply (hmono.trans hprodSum).trans
  rw [Fin.sum_univ_eq_sum_range (fun k => ∑' r, charge (134217728 * h / δ)
    (envelope (I.scaleWork k) r))]
  exact sum_envelope_charge_le I hδ hH

end GapEntropy.UniversalEnvelopeCost
