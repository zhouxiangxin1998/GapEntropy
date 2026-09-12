import GapEntropy.WorkEnvelope
import GapEntropy.JointEntropy
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The entropy bound for the work envelope

This proves the entropy component of manuscript Lemma A.5.
The probability distributions below are finite real-valued mass functions;
entropy monotonicity and the joint chain decomposition are proved in JointEntropy.
-/

noncomputable section
open scoped BigOperators

namespace GapEntropy.WorkEnvelope

def entropyConstant : ℝ := Real.log (4 / 3) + (4 / 9) * Real.log 4

def geometricProb (t l : ℕ) : ℝ := (1 / 4 : ℝ) ^ l / geometricSum t

def geometricMoment (t : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (t + 1), (l : ℝ) * (1 / 4 : ℝ) ^ l

theorem geometricSum_pos (t : ℕ) : 0 < geometricSum t :=
  lt_of_lt_of_le zero_lt_one (one_le_geometricSum t)

theorem geometricProb_nonneg (t l : ℕ) : 0 ≤ geometricProb t l := by
  unfold geometricProb
  exact div_nonneg (pow_nonneg (by norm_num) _) (geometricSum_pos t).le

theorem sum_geometricProb (t : ℕ) :
    ∑ l ∈ Finset.range (t + 1), geometricProb t l = 1 := by
  simp only [geometricProb, ← Finset.sum_div]
  exact div_self (geometricSum_pos t).ne'

theorem geometricMoment_le (t : ℕ) : geometricMoment t ≤ 4 / 9 := by
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one
    (r := (1 / 4 : ℝ)) (by norm_num)
  have h := sum_le_hasSum (Finset.range (t + 1)) (fun l _ => by positivity) hs
  norm_num at h
  exact h

theorem normalized_geometricMoment_le (t : ℕ) :
    geometricMoment t / geometricSum t ≤ 4 / 9 := by
  apply (div_le_iff₀ (geometricSum_pos t)).mpr
  have hm := geometricMoment_le t
  have hs := one_le_geometricSum t
  linarith

theorem log_geometricProb_inv (t l : ℕ) :
    Real.log (geometricProb t l)⁻¹ = Real.log (geometricSum t) + (l : ℝ) * Real.log 4 := by
  rw [geometricProb, Real.log_inv, Real.log_div (pow_ne_zero _ (by norm_num))
    (geometricSum_pos t).ne', Real.log_pow]
  have hlog : Real.log (1 / 4 : ℝ) = -Real.log 4 := by simp [one_div]
  rw [hlog]
  ring

theorem geometric_entropy_eq (t : ℕ) :
    GapEntropy.finiteEntropy (Finset.range (t + 1)) (geometricProb t) =
      Real.log (geometricSum t) + (geometricMoment t / geometricSum t) * Real.log 4 := by
  unfold GapEntropy.finiteEntropy
  simp_rw [log_geometricProb_inv, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, sum_geometricProb, one_mul]
  congr 1
  simp only [geometricProb, geometricMoment, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  ring

theorem geometric_entropy_le (t : ℕ) :
    GapEntropy.finiteEntropy (Finset.range (t + 1)) (geometricProb t) ≤ entropyConstant := by
  rw [geometric_entropy_eq, entropyConstant]
  have hs := Real.log_le_log (geometricSum_pos t) (geometricSum_le_four_thirds t)
  have hm := mul_le_mul_of_nonneg_right (normalized_geometricMoment_le t)
    (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
  linarith

/-- Kernel taking a source scale `t` to `k=t-l` with a truncated geometric offset `l`. -/
def backwardKernel (t k : ℕ) : ℝ := if k ≤ t then geometricProb t (t - k) else 0

private theorem filter_prefix {K t : ℕ} (ht : t ≤ K) :
    (Finset.range (K + 1)).filter (fun k => k ≤ t) = Finset.range (t + 1) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem backwardKernel_nonneg (t k : ℕ) : 0 ≤ backwardKernel t k := by
  unfold backwardKernel
  split_ifs
  · exact geometricProb_nonneg _ _
  · rfl

theorem sum_backwardKernel {K t : ℕ} (ht : t ≤ K) :
    ∑ k ∈ Finset.range (K + 1), backwardKernel t k = 1 := by
  unfold backwardKernel
  rw [← Finset.sum_filter, filter_prefix ht]
  have href := Finset.sum_range_reflect (geometricProb t) (t + 1)
  simpa using href.trans (sum_geometricProb t)

theorem backwardKernel_entropy {K t : ℕ} (ht : t ≤ K) :
    GapEntropy.finiteEntropy (Finset.range (K + 1)) (backwardKernel t) =
      GapEntropy.finiteEntropy (Finset.range (t + 1)) (geometricProb t) := by
  unfold backwardKernel
  rw [GapEntropy.finiteEntropy_filter, filter_prefix ht]
  unfold GapEntropy.finiteEntropy
  simpa using Finset.sum_range_reflect
    (fun l => geometricProb t l * Real.log (geometricProb t l)⁻¹) (t + 1)

theorem backwardKernel_entropy_le {K t : ℕ} (ht : t ≤ K) :
    GapEntropy.finiteEntropy (Finset.range (K + 1)) (backwardKernel t) ≤ entropyConstant := by
  rw [backwardKernel_entropy ht]
  exact geometric_entropy_le t

theorem power_mul_reverse_geometric {k t : ℕ} (hkt : k ≤ t) :
    (4 : ℝ) ^ t * (1 / 4 : ℝ) ^ (t - k) = (4 : ℝ) ^ k := by
  rw [one_div, inv_pow, ← pow_sub₀ 4 (by norm_num) (Nat.sub_le t k)]
  congr 1
  omega

/-- The pointwise mixture identity before normalization. -/
theorem work_eq_backward_sum (counts : ℕ → ℝ) {K k : ℕ} (hk : k ≤ K) :
    work counts K k =
      ∑ t ∈ Finset.range (K + 1),
        if k ≤ t then augmentedWeight counts K t * (1 / 4 : ℝ) ^ (t - k) else 0 := by
  have hterm (t : ℕ) :
      (if k ≤ t then augmentedWeight counts K t * (1 / 4 : ℝ) ^ (t - k) else 0) =
        (if k ≤ t then counts t else 0) * (4 : ℝ) ^ k +
          (if t = K then (4 : ℝ) ^ k else 0) := by
    by_cases hkt : k ≤ t
    · simp only [if_pos hkt, augmentedWeight, mul_assoc, power_mul_reverse_geometric hkt]
      split_ifs <;> ring
    · have htK : t ≠ K := by omega
      simp [hkt, htK]
  simp_rw [hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  simp [work]
  ring

end GapEntropy.WorkEnvelope

namespace GapEntropy.Instance

open GapEntropy.WorkEnvelope

variable {n : ℕ} (I : GapEntropy.Instance n)

theorem workEnvelope_pos : 0 < I.workEnvelope :=
  I.hardness_pos.trans_le I.hardness_le_workEnvelope_lt.1

/-- Normalized scale-work distribution `q` in A.5. -/
def workMass (k : ℕ) : ℝ := I.scaleWork k / I.workEnvelope

def workEntropy : ℝ :=
  GapEntropy.finiteEntropy (Finset.range (I.lastBucket + 1)) I.workMass

/-- Source-scale distribution `r_t=v_t s_t/W` in the geometric mixture. -/
def sourceMass (t : ℕ) : ℝ :=
  augmentedWeight (fun t => (I.bucketCount t : ℝ)) I.lastBucket t * geometricSum t /
    I.workEnvelope

theorem sourceMass_nonneg (t : ℕ) : 0 ≤ I.sourceMass t := by
  exact div_nonneg
    (mul_nonneg (augmentedWeight_nonneg (Nat.cast_nonneg _)) (geometricSum_pos t).le)
    I.workEnvelope_pos.le

theorem sum_sourceMass :
    ∑ t ∈ Finset.range (I.lastBucket + 1), I.sourceMass t = 1 := by
  unfold sourceMass
  rw [← Finset.sum_div, ← totalWork_eq_augmented]
  exact div_self I.workEnvelope_pos.ne'

theorem sum_workMass :
    ∑ k ∈ Finset.range (I.lastBucket + 1), I.workMass k = 1 := by
  simp only [workMass, ← Finset.sum_div, ← I.workEnvelope_eq_sum]
  exact div_self I.workEnvelope_pos.ne'

/-- Exact representation of the normalized work distribution as a mixture. -/
theorem workMass_eq_mixture {k : ℕ} (hk : k ≤ I.lastBucket) :
    I.workMass k = ∑ t ∈ Finset.range (I.lastBucket + 1),
      I.sourceMass t * backwardKernel t k := by
  unfold workMass scaleWork
  rw [work_eq_backward_sum _ hk, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro t _
  by_cases hkt : k ≤ t
  · simp only [if_pos hkt, sourceMass, backwardKernel, geometricProb]
    field_simp [(geometricSum_pos t).ne', I.workEnvelope_pos.ne']
  · simp [hkt, backwardKernel]

theorem workMass_nonneg {k : ℕ} (hk : k ≤ I.lastBucket) : 0 ≤ I.workMass k := by
  rw [I.workMass_eq_mixture hk]
  exact Finset.sum_nonneg (fun t _ => mul_nonneg (I.sourceMass_nonneg t)
    (backwardKernel_nonneg t k))

theorem workEntropy_nonneg : 0 ≤ I.workEntropy :=
  GapEntropy.finiteEntropy_nonneg _ _
    (fun k hk => I.workMass_nonneg (by simpa using Finset.mem_range.mp hk)) I.sum_workMass

theorem occupiedBuckets_subset_scales :
    I.occupiedBuckets ⊆ Finset.range (I.lastBucket + 1) := by
  intro t ht
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' _ _ ht))

theorem sourceMass_eq_zero_of_not_occupied {t : ℕ} (ht : t ∉ I.occupiedBuckets) :
    I.sourceMass t = 0 := by
  have hg : I.gapGroup t = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro i hi
    obtain ⟨his, hit⟩ := Finset.mem_filter.mp hi
    exact ht (Finset.mem_image.mpr ⟨i, his, hit⟩)
  have htK : t ≠ I.lastBucket := by
    rintro rfl
    exact ht I.lastBucket_mem
  simp [sourceMass, augmentedWeight, bucketCount, hg, htK]

theorem sum_sourceMass_occupied : ∑ t ∈ I.occupiedBuckets, I.sourceMass t = 1 := by
  have h := Finset.sum_subset I.occupiedBuckets_subset_scales
    (fun t _ ht => I.sourceMass_eq_zero_of_not_occupied ht)
  exact h.trans I.sum_sourceMass

theorem sourceEntropy_eq_occupied :
    GapEntropy.finiteEntropy (Finset.range (I.lastBucket + 1)) I.sourceMass =
      GapEntropy.finiteEntropy I.occupiedBuckets I.sourceMass := by
  symm
  exact Finset.sum_subset I.occupiedBuckets_subset_scales
    (fun t _ ht => by simp [I.sourceMass_eq_zero_of_not_occupied ht])

theorem bucketCount_power_le_four_groupHardness (t : ℕ) :
    (I.bucketCount t : ℝ) * (4 : ℝ) ^ t ≤ 4 * I.groupHardness t := by
  calc
    (I.bucketCount t : ℝ) * (4 : ℝ) ^ t = ∑ i ∈ I.gapGroup t, (4 : ℝ) ^ t := by
      simp [bucketCount]
    _ ≤ ∑ i ∈ I.gapGroup t, 4 * I.weight i := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨his, hit⟩ := Finset.mem_filter.mp hi
      rw [← hit]
      exact (I.bucket_power_lt_four_weight his).le
    _ = 4 * I.groupHardness t := by rw [← Finset.mul_sum]; rfl

theorem augmentedWeight_le_eight_groupHardness (t : ℕ) :
    augmentedWeight (fun t => (I.bucketCount t : ℝ)) I.lastBucket t ≤
      8 * I.groupHardness t := by
  have hb := I.bucketCount_power_le_four_groupHardness t
  have hH := I.groupHardness_nonneg t
  have hpow : 0 ≤ (4 : ℝ) ^ t := by positivity
  by_cases ht : t = I.lastBucket
  · have hn : 1 ≤ (I.bucketCount t : ℝ) := by
      rw [ht]
      exact_mod_cast I.bucketCount_lastBucket_pos
    simp only [augmentedWeight, if_pos ht]
    nlinarith
  · simp only [augmentedWeight, if_neg ht, add_zero]
    linarith

/-- The source distribution is dominated by `(32/3)` times the hardness distribution. -/
theorem sourceMass_le_bucketMass (t : ℕ) :
    I.sourceMass t ≤ (32 / 3 : ℝ) * I.bucketMass t := by
  have hv := I.augmentedWeight_le_eight_groupHardness t
  have hgs := geometricSum_le_four_thirds t
  have hnv := augmentedWeight_nonneg (counts := fun t => (I.bucketCount t : ℝ))
    (K := I.lastBucket) (t := t)
    (show (0 : ℝ) ≤ (I.bucketCount t : ℝ) by positivity)
  have hvg : augmentedWeight (fun t => (I.bucketCount t : ℝ)) I.lastBucket t *
      geometricSum t ≤ (32 / 3 : ℝ) * I.groupHardness t := by nlinarith
  have hp := I.bucketMass_nonneg t
  have hw := I.hardness_le_workEnvelope_lt.1
  have hmass : I.bucketMass t * I.hardness = I.groupHardness t := by
    unfold bucketMass
    field_simp [I.hardness_pos.ne']
  have hprod := mul_le_mul_of_nonneg_left hw
    (show 0 ≤ (32 / 3 : ℝ) * I.bucketMass t by positivity)
  unfold sourceMass
  apply (div_le_iff₀ I.workEnvelope_pos).mpr
  nlinarith

theorem sourceEntropy_le_gapEntropy :
    GapEntropy.finiteEntropy (Finset.range (I.lastBucket + 1)) I.sourceMass ≤
      (32 / 3 : ℝ) * I.gapEntropy := by
  rw [I.sourceEntropy_eq_occupied]
  calc
    _ ≤ ∑ t ∈ I.occupiedBuckets, I.sourceMass t * Real.log (I.bucketMass t)⁻¹ :=
      GapEntropy.finiteEntropy_le_cross _ _ _ (fun t _ => I.sourceMass_nonneg t)
        I.sum_sourceMass_occupied (fun t ht => I.bucketMass_pos ht) I.sum_bucketMass.le
    _ ≤ ∑ t ∈ I.occupiedBuckets,
        ((32 / 3 : ℝ) * I.bucketMass t) * Real.log (I.bucketMass t)⁻¹ := by
      apply Finset.sum_le_sum
      intro t ht
      apply mul_le_mul_of_nonneg_right (I.sourceMass_le_bucketMass t)
      rw [Real.log_inv]
      exact neg_nonneg.mpr (Real.log_nonpos (I.bucketMass_nonneg t) (I.bucketMass_le_one t))
    _ = (32 / 3 : ℝ) * I.gapEntropy := by
      rw [gapEntropy, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

/-- The full entropy component of manuscript Lemma A.5, with its stated constant. -/
theorem workEntropy_le :
    I.workEntropy ≤ (32 / 3 : ℝ) * I.gapEntropy + entropyConstant := by
  have hweighted :
      (∑ t ∈ Finset.range (I.lastBucket + 1), I.sourceMass t *
        GapEntropy.finiteEntropy (Finset.range (I.lastBucket + 1)) (backwardKernel t)) ≤
      entropyConstant := by
    calc
      _ ≤ ∑ t ∈ Finset.range (I.lastBucket + 1), I.sourceMass t * entropyConstant := by
        apply Finset.sum_le_sum
        intro t ht
        exact mul_le_mul_of_nonneg_left
          (backwardKernel_entropy_le (by simpa using Finset.mem_range.mp ht))
          (I.sourceMass_nonneg t)
      _ = entropyConstant := by rw [← Finset.sum_mul, I.sum_sourceMass, one_mul]
  calc
    I.workEntropy = GapEntropy.finiteEntropy (Finset.range (I.lastBucket + 1))
        (fun k => ∑ t ∈ Finset.range (I.lastBucket + 1), I.sourceMass t * backwardKernel t k) := by
      unfold workEntropy GapEntropy.finiteEntropy
      apply Finset.sum_congr rfl
      intro k hk
      rw [I.workMass_eq_mixture (by simpa using Finset.mem_range.mp hk)]
    _ ≤ GapEntropy.finiteEntropy (Finset.range (I.lastBucket + 1)) I.sourceMass +
        ∑ t ∈ Finset.range (I.lastBucket + 1), I.sourceMass t *
          GapEntropy.finiteEntropy (Finset.range (I.lastBucket + 1)) (backwardKernel t) :=
      GapEntropy.finiteEntropy_mixture_le _ _ I.sourceMass backwardKernel
        (fun t _ => I.sourceMass_nonneg t) (fun t _ k _ => backwardKernel_nonneg t k)
        (fun t ht => sum_backwardKernel (by simpa using Finset.mem_range.mp ht))
    _ ≤ (32 / 3 : ℝ) * I.gapEntropy + entropyConstant :=
      add_le_add I.sourceEntropy_le_gapEntropy hweighted

/-- All three assertions of manuscript Lemma A.5, for the original Gaussian-arm instance. -/
theorem workEnvelope_estimates :
    I.hardness ≤ I.workEnvelope ∧
      I.workEnvelope < (32 / 3 : ℝ) * I.hardness ∧
      I.workEntropy ≤ (32 / 3 : ℝ) * I.gapEntropy +
        (Real.log (4 / 3) + (4 / 9) * Real.log 4) ∧
      (4 : ℝ) ^ I.lastBucket ≤ 4 * I.twoArmHardness :=
  ⟨I.hardness_le_workEnvelope_lt.1, I.hardness_le_workEnvelope_lt.2,
    I.workEntropy_le, I.lastBucket_power_le_four_twoArmHardness⟩

end GapEntropy.Instance
