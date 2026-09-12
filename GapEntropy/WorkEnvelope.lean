import GapEntropy.Instance
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Geometrically smoothed work weights

The deterministic weight estimates of manuscript Lemma A.5.
Existing mathlib APIs used here include `geom_sum_mul_neg`,
`Finset.sum_range_reflect`, `Finset.sum_comm`, and finite fiberwise summation.
The entropy part and the combined A.5 theorem are proved in `WorkEntropy.lean`.
-/

open scoped BigOperators

namespace GapEntropy.WorkEnvelope

noncomputable section

/-- The truncated backwards geometric distribution's normalizer. -/
def geometricSum (t : ℕ) : ℝ := ∑ l ∈ Finset.range (t + 1), (1 / 4 : ℝ) ^ l

/-- The unnormalized sum of geometric work up through scale `t`. -/
def powerSum (t : ℕ) : ℝ := ∑ k ∈ Finset.range (t + 1), (4 : ℝ) ^ k

/-- The original scale weight `4^k (1 + ∑_{t≥k} n_t)`, with support truncated at `K`. -/
def work (counts : ℕ → ℝ) (K k : ℕ) : ℝ :=
  (4 : ℝ) ^ k * (1 + ∑ t ∈ Finset.range (K + 1), if k ≤ t then counts t else 0)

def totalWork (counts : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (K + 1), work counts K k

/-- Add the fictitious best arm at the hardest scale. -/
def augmentedWeight (counts : ℕ → ℝ) (K t : ℕ) : ℝ :=
  (counts t + if t = K then 1 else 0) * (4 : ℝ) ^ t

theorem one_le_geometricSum (t : ℕ) : 1 ≤ geometricSum t := by
  have h := Finset.single_le_sum
    (s := Finset.range (t + 1)) (f := fun l => (1 / 4 : ℝ) ^ l)
    (fun l _ => pow_nonneg (by norm_num) l) (show 0 ∈ Finset.range (t + 1) by simp)
  simpa [geometricSum] using h

theorem geometricSum_lt_four_thirds (t : ℕ) : geometricSum t < 4 / 3 := by
  have h := geom_sum_mul_neg (1 / 4 : ℝ) (t + 1)
  have hp : 0 < (1 / 4 : ℝ) ^ (t + 1) := by positivity
  change geometricSum t * (1 - 1 / 4) = 1 - (1 / 4 : ℝ) ^ (t + 1) at h
  linarith

theorem geometricSum_le_four_thirds (t : ℕ) : geometricSum t ≤ 4 / 3 :=
  (geometricSum_lt_four_thirds t).le

theorem pow_mul_geometricSum (t : ℕ) : (4 : ℝ) ^ t * geometricSum t = powerSum t := by
  unfold geometricSum powerSum
  rw [Finset.mul_sum]
  calc
    (∑ l ∈ Finset.range (t + 1), (4 : ℝ) ^ t * (1 / 4 : ℝ) ^ l) =
        ∑ l ∈ Finset.range (t + 1), (4 : ℝ) ^ (t - l) := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlt : l ≤ t := by simpa using (Finset.mem_range.mp hl)
      rw [pow_sub₀ 4 (by norm_num) hlt]
      simp [one_div, inv_pow]
    _ = ∑ k ∈ Finset.range (t + 1), (4 : ℝ) ^ k := by
      simpa using Finset.sum_range_reflect (fun k => (4 : ℝ) ^ k) (t + 1)

private theorem filter_scales {K t : ℕ} (ht : t ≤ K) :
    (Finset.range (K + 1)).filter (fun k => k ≤ t) = Finset.range (t + 1) := by
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

private theorem sum_truncated_powers {K t : ℕ} (ht : t ≤ K) :
    (∑ k ∈ Finset.range (K + 1), if k ≤ t then (4 : ℝ) ^ k else 0) = powerSum t := by
  rw [← Finset.sum_filter, filter_scales ht]
  rfl

/-- Exchange the scale and bucket sums before inserting the geometric normalizers. -/
theorem totalWork_eq_powerSum (counts : ℕ → ℝ) (K : ℕ) :
    totalWork counts K = powerSum K +
      ∑ t ∈ Finset.range (K + 1), counts t * powerSum t := by
  unfold totalWork work
  simp only [mul_add, mul_one, Finset.sum_add_distrib, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  change powerSum K + _ = powerSum K + _
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  have htK : t ≤ K := by simpa using Finset.mem_range.mp ht
  calc
    (∑ k ∈ Finset.range (K + 1), if k ≤ t then (4 : ℝ) ^ k * counts t else 0) =
        (∑ k ∈ Finset.range (K + 1), if k ≤ t then (4 : ℝ) ^ k else 0) * counts t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> simp
    _ = counts t * powerSum t := by rw [sum_truncated_powers htK]; ring

/-- The exact smoothing identity `W = ∑_t v_t s_t` from A.5. -/
theorem totalWork_eq_augmented (counts : ℕ → ℝ) (K : ℕ) :
    totalWork counts K =
      ∑ t ∈ Finset.range (K + 1), augmentedWeight counts K t * geometricSum t := by
  rw [totalWork_eq_powerSum]
  simp_rw [augmentedWeight, mul_assoc, pow_mul_geometricSum, add_mul]
  simp only [Finset.sum_add_distrib, ite_mul, one_mul, zero_mul]
  simp [add_comm]

theorem sum_augmentedWeight (counts : ℕ → ℝ) (K : ℕ) :
    (∑ t ∈ Finset.range (K + 1), augmentedWeight counts K t) =
      (∑ t ∈ Finset.range (K + 1), counts t * (4 : ℝ) ^ t) + (4 : ℝ) ^ K := by
  simp [augmentedWeight, add_mul, Finset.sum_add_distrib, ite_mul]

theorem augmentedWeight_nonneg {counts : ℕ → ℝ} {K t : ℕ}
    (hcounts : 0 ≤ counts t) : 0 ≤ augmentedWeight counts K t := by
  unfold augmentedWeight
  positivity

/-- Smoothing increases total mass by at most the constant `4/3`. -/
theorem totalWork_bounds {counts : ℕ → ℝ} (K : ℕ)
    (hcounts : ∀ t ≤ K, 0 ≤ counts t) :
    (∑ t ∈ Finset.range (K + 1), augmentedWeight counts K t) ≤ totalWork counts K ∧
      totalWork counts K ≤ (4 / 3 : ℝ) *
        ∑ t ∈ Finset.range (K + 1), augmentedWeight counts K t := by
  rw [totalWork_eq_augmented]
  constructor
  · apply Finset.sum_le_sum
    intro t ht
    have hn := augmentedWeight_nonneg (K := K) (hcounts t (by simpa using Finset.mem_range.mp ht))
    nlinarith [one_le_geometricSum t]
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t ht
    have hn := augmentedWeight_nonneg (K := K) (hcounts t (by simpa using Finset.mem_range.mp ht))
    nlinarith [geometricSum_le_four_thirds t]

end
end GapEntropy.WorkEnvelope

namespace GapEntropy.Instance

noncomputable section

variable {n : ℕ} (I : GapEntropy.Instance n)

/-- Last occupied dyadic gap group. The instance has at least one suboptimal arm. -/
def lastBucket : ℕ := I.occupiedBuckets.max' I.occupiedBuckets_nonempty

theorem lastBucket_mem : I.lastBucket ∈ I.occupiedBuckets :=
  Finset.max'_mem _ _

theorem bucket_le_lastBucket {i : Fin n} (hi : i ∈ I.suboptimal) :
    I.bucket i ≤ I.lastBucket :=
  Finset.le_max' _ _ (Finset.mem_image_of_mem I.bucket hi)

def bucketCount (k : ℕ) : ℕ := (I.gapGroup k).card

theorem bucketCount_lastBucket_pos : 0 < I.bucketCount I.lastBucket := by
  apply Finset.card_pos.mpr
  obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp I.lastBucket_mem
  exact ⟨i, Finset.mem_filter.mpr ⟨hi, hik⟩⟩

theorem gapGroup_empty_of_lastBucket_lt {k : ℕ} (hk : I.lastBucket < k) :
    I.gapGroup k = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro i hi
  obtain ⟨his, hik⟩ := Finset.mem_filter.mp hi
  have h := I.bucket_le_lastBucket his
  omega

theorem bucketCount_eq_zero_of_lastBucket_lt {k : ℕ} (hk : I.lastBucket < k) :
    I.bucketCount k = 0 := by
  simp [bucketCount, I.gapGroup_empty_of_lastBucket_lt hk]

/-- Manuscript scale work `W_k`, with the original best contributing one arm. -/
def scaleWork (k : ℕ) : ℝ :=
  GapEntropy.WorkEnvelope.work (fun t => (I.bucketCount t : ℝ)) I.lastBucket k

/-- Manuscript total smoothed work `W = ∑_{k=0}^K W_k`. -/
def workEnvelope : ℝ :=
  GapEntropy.WorkEnvelope.totalWork (fun t => (I.bucketCount t : ℝ)) I.lastBucket

theorem workEnvelope_eq_sum :
    I.workEnvelope = ∑ k ∈ Finset.range (I.lastBucket + 1), I.scaleWork k := rfl

private theorem inv_dyadic_square (k : ℕ) :
    (((1 / 2 : ℝ) ^ k) ^ 2)⁻¹ = (4 : ℝ) ^ k := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, ← inv_pow]
  norm_num

/-- The closed lower endpoint of a gap bucket gives `Δ_i⁻² ≤ 4^k`. -/
theorem weight_le_bucket_power {i : Fin n} (hi : i ∈ I.suboptimal) :
    I.weight i ≤ (4 : ℝ) ^ I.bucket i := by
  have hlo : 0 < (1 / 2 : ℝ) ^ I.bucket i := by positivity
  have hd := I.gap_pos ((I.mem_suboptimal i).mp hi)
  have hsq : ((1 / 2 : ℝ) ^ I.bucket i) ^ 2 ≤ I.gap i ^ 2 := by
    nlinarith [(I.bucket_bounds hi).1]
  calc
    I.weight i = (I.gap i ^ 2)⁻¹ := rfl
    _ ≤ (((1 / 2 : ℝ) ^ I.bucket i) ^ 2)⁻¹ := inv_anti₀ (sq_pos_of_pos hlo) hsq
    _ = (4 : ℝ) ^ I.bucket i := inv_dyadic_square _

/-- The open upper endpoint of a gap bucket gives the strict opposite bound. -/
theorem bucket_power_lt_four_weight {i : Fin n} (hi : i ∈ I.suboptimal) :
    (4 : ℝ) ^ I.bucket i < 4 * I.weight i := by
  have hlo : 0 < (1 / 2 : ℝ) ^ I.bucket i := by positivity
  have hd := I.gap_pos ((I.mem_suboptimal i).mp hi)
  have hsq : I.gap i ^ 2 < (2 * (1 / 2 : ℝ) ^ I.bucket i) ^ 2 := by
    nlinarith [(I.bucket_bounds hi).2]
  have hinv := (inv_lt_inv₀
    (sq_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hlo)) (sq_pos_of_pos hd)).mpr hsq
  have hid : ((2 * (1 / 2 : ℝ) ^ I.bucket i) ^ 2)⁻¹ =
      (4 : ℝ) ^ I.bucket i / 4 := by
    rw [mul_pow, mul_inv_rev, inv_dyadic_square]
    norm_num
    ring
  rw [hid] at hinv
  change (4 : ℝ) ^ I.bucket i / 4 < I.weight i at hinv
  linarith

theorem lastBucket_power_lt_four_twoArmHardness :
    (4 : ℝ) ^ I.lastBucket < 4 * I.twoArmHardness := by
  obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp I.lastBucket_mem
  have hp := I.bucket_power_lt_four_weight hi
  have hw : I.weight i ≤ I.twoArmHardness := Finset.le_sup' I.weight hi
  rw [hik] at hp
  linarith

/-- The scale of the hardest bucket is controlled by the two-arm hardness `D`. -/
theorem lastBucket_power_le_four_twoArmHardness :
    (4 : ℝ) ^ I.lastBucket ≤ 4 * I.twoArmHardness :=
  I.lastBucket_power_lt_four_twoArmHardness.le

/-- Histogram summation is exactly summation over the original suboptimal arms. -/
theorem sum_bucketCount_power :
    (∑ t ∈ Finset.range (I.lastBucket + 1), (I.bucketCount t : ℝ) * (4 : ℝ) ^ t) =
      ∑ i ∈ I.suboptimal, (4 : ℝ) ^ I.bucket i := by
  classical
  have hmaps : ∀ i ∈ I.suboptimal, I.bucket i ∈ Finset.range (I.lastBucket + 1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (I.bucket_le_lastBucket hi))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun i => (4 : ℝ) ^ I.bucket i)]
  apply Finset.sum_congr rfl
  intro t _
  change (I.bucketCount t : ℝ) * (4 : ℝ) ^ t =
    ∑ i ∈ I.gapGroup t, (4 : ℝ) ^ I.bucket i
  calc
    (I.bucketCount t : ℝ) * (4 : ℝ) ^ t = ∑ i ∈ I.gapGroup t, (4 : ℝ) ^ t := by
      simp [bucketCount]
    _ = ∑ i ∈ I.gapGroup t, (4 : ℝ) ^ I.bucket i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]

theorem bucket_power_sum_bounds :
    I.hardness ≤ (∑ i ∈ I.suboptimal, (4 : ℝ) ^ I.bucket i) ∧
      (∑ i ∈ I.suboptimal, (4 : ℝ) ^ I.bucket i) < 4 * I.hardness := by
  constructor
  · exact Finset.sum_le_sum (fun i hi => I.weight_le_bucket_power hi)
  · calc
      (∑ i ∈ I.suboptimal, (4 : ℝ) ^ I.bucket i) < ∑ i ∈ I.suboptimal, 4 * I.weight i := by
        apply Finset.sum_lt_sum (fun i hi => (I.bucket_power_lt_four_weight hi).le)
        obtain ⟨i, hi⟩ := I.suboptimal_nonempty
        exact ⟨i, hi, I.bucket_power_lt_four_weight hi⟩
      _ = 4 * I.hardness := by rw [← Finset.mul_sum]; rfl

/-- The augmented histogram has mass between `H` and `8H`. -/
theorem augmented_sum_bounds :
    I.hardness ≤
      (∑ t ∈ Finset.range (I.lastBucket + 1),
        GapEntropy.WorkEnvelope.augmentedWeight (fun t => (I.bucketCount t : ℝ)) I.lastBucket t) ∧
    (∑ t ∈ Finset.range (I.lastBucket + 1),
        GapEntropy.WorkEnvelope.augmentedWeight (fun t => (I.bucketCount t : ℝ)) I.lastBucket t) <
      8 * I.hardness := by
  rw [GapEntropy.WorkEnvelope.sum_augmentedWeight, I.sum_bucketCount_power]
  have hs := I.bucket_power_sum_bounds
  have hp := I.lastBucket_power_lt_four_twoArmHardness
  have hd := I.twoArmHardness_le_hardness
  have hn : 0 ≤ (4 : ℝ) ^ I.lastBucket := by positivity
  constructor <;> linarith

/-- The principal deterministic mass estimate of Lemma A.5, for the actual instance. -/
theorem hardness_le_workEnvelope_lt :
    I.hardness ≤ I.workEnvelope ∧ I.workEnvelope < (32 / 3 : ℝ) * I.hardness := by
  have hw := GapEntropy.WorkEnvelope.totalWork_bounds
    (counts := fun t => (I.bucketCount t : ℝ)) I.lastBucket (fun t _ => Nat.cast_nonneg _)
  have hv := I.augmented_sum_bounds
  change _ ≤ I.workEnvelope ∧ I.workEnvelope ≤ _ at hw
  constructor
  · exact hv.1.trans hw.1
  · linarith [hw.2, hv.2]

end
end GapEntropy.Instance
