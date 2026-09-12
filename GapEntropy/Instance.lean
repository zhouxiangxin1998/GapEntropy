import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Gaussian best-arm instances and dyadic gap profiles

Definitions 3.3 of Chen–Li (2016) and §2.1–2.2 of the supplied manuscript.
The best label is stored with a proof of uniqueness; it is mathematical instance
data, not information supplied to an algorithm.

We use the least valid dyadic index to preserve the source's closed lower endpoint.
-/

open scoped BigOperators

namespace GapEntropy

structure Instance (n : ℕ) where
  mean : Fin n → ℝ
  mean_mem : ∀ i, mean i ∈ Set.Icc 0 1
  best : Fin n
  best_unique : ∀ i, i ≠ best → mean i < mean best
  two_le : 2 ≤ n

namespace Instance

variable {n : ℕ} (I : Instance n)

def gap (i : Fin n) : ℝ := I.mean I.best - I.mean i

def suboptimal : Finset (Fin n) := Finset.univ.erase I.best

@[simp] theorem mem_suboptimal (i : Fin n) : i ∈ I.suboptimal ↔ i ≠ I.best := by
  simp [suboptimal]

@[simp] theorem gap_best : I.gap I.best = 0 := by simp [gap]

theorem gap_pos {i : Fin n} (hi : i ≠ I.best) : 0 < I.gap i :=
  sub_pos.mpr (I.best_unique i hi)

theorem gap_nonneg (i : Fin n) : 0 ≤ I.gap i := by
  by_cases hi : i = I.best
  · subst i; simp
  · exact (I.gap_pos hi).le

theorem gap_le_one (i : Fin n) : I.gap i ≤ 1 := by
  have htop := (I.mean_mem I.best).2
  have hbot := (I.mean_mem i).1
  dsimp [gap]
  linarith

theorem suboptimal_nonempty : I.suboptimal.Nonempty := by
  have hn := I.two_le
  by_cases h : (⟨0, by omega⟩ : Fin n) = I.best
  · refine ⟨⟨1, by omega⟩, (I.mem_suboptimal _).2 ?_⟩
    rw [← h]
    simp [Fin.ext_iff]
  · exact ⟨⟨0, by omega⟩, (I.mem_suboptimal _).2 h⟩

noncomputable def weight (i : Fin n) : ℝ := (I.gap i ^ 2)⁻¹

noncomputable def hardness : ℝ := ∑ i ∈ I.suboptimal, I.weight i

noncomputable def twoArmHardness : ℝ :=
  I.suboptimal.sup' I.suboptimal_nonempty I.weight

theorem weight_nonneg (i : Fin n) : 0 ≤ I.weight i := by
  exact inv_nonneg.mpr (sq_nonneg _)

@[simp] theorem weight_best : I.weight I.best = 0 := by
  simp [weight]

theorem hardness_eq_sum : I.hardness = ∑ i, I.weight i := by
  change (∑ i ∈ Finset.univ.erase I.best, I.weight i) = _
  have h := Finset.sum_erase_add (s := Finset.univ) (f := I.weight)
    (a := I.best) (Finset.mem_univ I.best)
  simpa only [I.weight_best, add_zero] using h

theorem weight_pos {i : Fin n} (hi : i ∈ I.suboptimal) : 0 < I.weight i := by
  exact inv_pos.mpr (sq_pos_of_pos (I.gap_pos ((I.mem_suboptimal i).1 hi)))

theorem one_le_weight {i : Fin n} (hi : i ∈ I.suboptimal) : 1 ≤ I.weight i := by
  have hpos := I.gap_pos ((I.mem_suboptimal i).1 hi)
  have hle := I.gap_le_one i
  have hs : I.gap i ^ 2 ≤ 1 := by nlinarith
  exact (one_le_inv₀ (sq_pos_of_pos hpos)).2 hs

theorem hardness_pos : 0 < I.hardness := by
  exact Finset.sum_pos (fun i hi => I.weight_pos hi) I.suboptimal_nonempty

theorem weight_le_hardness {i : Fin n} (hi : i ∈ I.suboptimal) :
    I.weight i ≤ I.hardness := by
  exact Finset.single_le_sum (fun j _ => I.weight_nonneg j) hi

theorem twoArmHardness_le_hardness : I.twoArmHardness ≤ I.hardness := by
  exact Finset.sup'_le _ _ (fun i hi => I.weight_le_hardness hi)

theorem one_le_twoArmHardness : 1 ≤ I.twoArmHardness := by
  obtain ⟨i, hi⟩ := I.suboptimal_nonempty
  exact (I.one_le_weight hi).trans (Finset.le_sup' I.weight hi)

/-- Relabeling convention: the new arm `i` is the old arm `π⁻¹ i`. -/
def permute (π : Equiv.Perm (Fin n)) : Instance n where
  mean i := I.mean (π.symm i)
  mean_mem i := I.mean_mem _
  best := π I.best
  best_unique i hi := by
    simp only [Equiv.symm_apply_apply]
    apply I.best_unique (π.symm i)
    intro h
    exact hi ((π.apply_symm_apply i).symm.trans (congrArg π h))
  two_le := I.two_le

@[simp] theorem permute_gap (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (I.permute π).gap i = I.gap (π.symm i) := by
  simp [gap, permute]

@[simp] theorem permute_weight (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (I.permute π).weight i = I.weight (π.symm i) := by
  simp [weight]

@[simp] theorem permute_hardness (π : Equiv.Perm (Fin n)) :
    (I.permute π).hardness = I.hardness := by
  rw [(I.permute π).hardness_eq_sum, I.hardness_eq_sum]
  simp only [permute_weight]
  exact Equiv.sum_comp π.symm I.weight

@[simp] theorem permute_twoArmHardness (π : Equiv.Perm (Fin n)) :
    (I.permute π).twoArmHardness = I.twoArmHardness := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro i hi
    rw [I.permute_weight]
    apply Finset.le_sup'
    apply (I.mem_suboptimal _).2
    intro h
    have hne := ((I.permute π).mem_suboptimal i).1 hi
    apply hne
    exact (π.apply_symm_apply i).symm.trans (congrArg π h)
  · apply Finset.sup'_le
    intro i hi
    have hp : π i ∈ (I.permute π).suboptimal := by
      apply ((I.permute π).mem_suboptimal _).2
      exact fun h => (I.mem_suboptimal i).1 hi (π.injective h)
    calc
      I.weight i = (I.permute π).weight (π i) := by simp
      _ ≤ _ := Finset.le_sup' (I.permute π).weight hp

end Instance

/-- Least dyadic scale whose lower boundary is at most the positive gap. -/
noncomputable def dyadicIndex (d : ℝ) : ℕ :=
  if hd : 0 < d then
    Nat.find ((exists_pow_lt_of_lt_one hd (show (1 / 2 : ℝ) < 1 by norm_num)).imp
      (fun _ h => h.le))
  else 0

theorem dyadicIndex_lower {d : ℝ} (hd : 0 < d) :
    (1 / 2 : ℝ) ^ dyadicIndex d ≤ d := by
  simp only [dyadicIndex, dif_pos hd]
  exact Nat.find_spec ((exists_pow_lt_of_lt_one hd
    (show (1 / 2 : ℝ) < 1 by norm_num)).imp (fun _ h => h.le))

theorem dyadicIndex_upper {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) :
    d < 2 * (1 / 2 : ℝ) ^ dyadicIndex d := by
  by_cases hk : dyadicIndex d = 0
  · rw [hk]; norm_num; linarith
  · have hprev : dyadicIndex d - 1 < dyadicIndex d := by omega
    have hnot : ¬ (1 / 2 : ℝ) ^ (dyadicIndex d - 1) ≤ d := by
      unfold dyadicIndex at hprev ⊢
      simp only [dif_pos hd] at hprev ⊢
      exact Nat.find_min _ hprev
    have heq : dyadicIndex d = (dyadicIndex d - 1) + 1 := by omega
    rw [heq, pow_succ]
    nlinarith [lt_of_not_ge hnot]

@[simp] theorem dyadicIndex_one : dyadicIndex 1 = 0 := by
  simp only [dyadicIndex, zero_lt_one, dif_pos]
  apply Nat.eq_zero_of_le_zero
  apply Nat.find_min'
  norm_num

theorem dyadicIndex_eq_iff {d : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (k : ℕ) :
    dyadicIndex d = k ↔ (1 / 2 : ℝ) ^ k ≤ d ∧ d < 2 * (1 / 2 : ℝ) ^ k := by
  constructor
  · rintro rfl
    exact ⟨dyadicIndex_lower hd, dyadicIndex_upper hd hd1⟩
  · rintro ⟨hl, hu⟩
    have hle : dyadicIndex d ≤ k := by
      unfold dyadicIndex
      simp only [dif_pos hd]
      exact Nat.find_min' _ hl
    apply le_antisymm hle
    by_contra h
    have hk : dyadicIndex d + 1 ≤ k := by omega
    have hp := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num) hk
    rw [pow_succ] at hp
    nlinarith [dyadicIndex_lower hd]

namespace Instance

variable {n : ℕ} (I : Instance n)

noncomputable def bucket (i : Fin n) : ℕ := dyadicIndex (I.gap i)

noncomputable def gapGroup (k : ℕ) : Finset (Fin n) :=
  I.suboptimal.filter (fun i => I.bucket i = k)

noncomputable def occupiedBuckets : Finset ℕ := I.suboptimal.image I.bucket

noncomputable def groupHardness (k : ℕ) : ℝ := ∑ i ∈ I.gapGroup k, I.weight i

noncomputable def bucketMass (k : ℕ) : ℝ := I.groupHardness k / I.hardness

/-- Finite support avoids summability conventions for empty dyadic groups. -/
noncomputable def gapEntropy : ℝ :=
  ∑ k ∈ I.occupiedBuckets, I.bucketMass k * Real.log (I.bucketMass k)⁻¹

theorem bucket_bounds {i : Fin n} (hi : i ∈ I.suboptimal) :
    (1 / 2 : ℝ) ^ I.bucket i ≤ I.gap i ∧
      I.gap i < 2 * (1 / 2 : ℝ) ^ I.bucket i := by
  have hp := I.gap_pos ((I.mem_suboptimal i).1 hi)
  exact ⟨dyadicIndex_lower hp, dyadicIndex_upper hp (I.gap_le_one i)⟩

theorem mem_gapGroup (k : ℕ) (i : Fin n) :
    i ∈ I.gapGroup k ↔ i ≠ I.best ∧
      (1 / 2 : ℝ) ^ k ≤ I.gap i ∧ I.gap i < 2 * (1 / 2 : ℝ) ^ k := by
  classical
  change i ∈ I.suboptimal.filter (fun j => I.bucket j = k) ↔ _
  rw [Finset.mem_filter, I.mem_suboptimal]
  change (i ≠ I.best ∧ dyadicIndex (I.gap i) = k) ↔ _
  constructor
  · rintro ⟨hi, hk⟩
    exact ⟨hi, (dyadicIndex_eq_iff (I.gap_pos hi) (I.gap_le_one i) k).1 hk⟩
  · rintro ⟨hi, hb⟩
    exact ⟨hi, (dyadicIndex_eq_iff (I.gap_pos hi) (I.gap_le_one i) k).2 hb⟩

theorem sum_groupHardness :
    ∑ k ∈ I.occupiedBuckets, I.groupHardness k = I.hardness := by
  exact Finset.sum_fiberwise_of_maps_to
    (fun i hi => Finset.mem_image_of_mem I.bucket hi) I.weight

theorem sum_bucketMass : ∑ k ∈ I.occupiedBuckets, I.bucketMass k = 1 := by
  simp only [bucketMass, ← Finset.sum_div, I.sum_groupHardness,
    div_self I.hardness_pos.ne']

theorem occupiedBuckets_nonempty : I.occupiedBuckets.Nonempty := by
  exact I.suboptimal_nonempty.image I.bucket

theorem groupHardness_pos {k : ℕ} (hk : k ∈ I.occupiedBuckets) :
    0 < I.groupHardness k := by
  obtain ⟨i, hi, hik⟩ := Finset.mem_image.mp hk
  apply Finset.sum_pos
  · intro j hj
    exact I.weight_pos (Finset.mem_filter.mp hj).1
  · exact ⟨i, Finset.mem_filter.mpr ⟨hi, hik⟩⟩

theorem bucketMass_pos {k : ℕ} (hk : k ∈ I.occupiedBuckets) :
    0 < I.bucketMass k := div_pos (I.groupHardness_pos hk) I.hardness_pos

theorem groupHardness_nonneg (k : ℕ) : 0 ≤ I.groupHardness k := by
  exact Finset.sum_nonneg (fun i _ => I.weight_nonneg i)

theorem groupHardness_le_hardness (k : ℕ) : I.groupHardness k ≤ I.hardness := by
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun i _ _ => I.weight_nonneg i)

theorem bucketMass_nonneg (k : ℕ) : 0 ≤ I.bucketMass k :=
  div_nonneg (I.groupHardness_nonneg k) I.hardness_pos.le

theorem bucketMass_le_one (k : ℕ) : I.bucketMass k ≤ 1 := by
  exact (div_le_one I.hardness_pos).2 (I.groupHardness_le_hardness k)

theorem gapEntropy_nonneg : 0 ≤ I.gapEntropy := by
  apply Finset.sum_nonneg
  intro k _
  rw [Real.log_inv, mul_neg]
  simpa only [Real.negMulLog_def, neg_mul] using
    Real.negMulLog_nonneg (I.bucketMass_nonneg k) (I.bucketMass_le_one k)

@[simp] theorem permute_bucket (π : Equiv.Perm (Fin n)) (i : Fin n) :
    (I.permute π).bucket i = I.bucket (π.symm i) := by
  simp [bucket]

@[simp] theorem permute_groupHardness (π : Equiv.Perm (Fin n)) (k : ℕ) :
    (I.permute π).groupHardness k = I.groupHardness k := by
  apply Finset.sum_equiv π.symm
  · intro i
    classical
    simp only [gapGroup, Finset.mem_filter, mem_suboptimal, permute_bucket]
    have h : i ≠ (I.permute π).best ↔ π.symm i ≠ I.best := by
      simp [permute, Equiv.symm_apply_eq]
    rw [h]
  · intro i _
    exact I.permute_weight π i

@[simp] theorem permute_bucketMass (π : Equiv.Perm (Fin n)) (k : ℕ) :
    (I.permute π).bucketMass k = I.bucketMass k := by
  simp [bucketMass]

@[simp] theorem permute_occupiedBuckets (π : Equiv.Perm (Fin n)) :
    (I.permute π).occupiedBuckets = I.occupiedBuckets := by
  classical
  ext k
  simp only [occupiedBuckets, Finset.mem_image, mem_suboptimal, permute_bucket]
  constructor
  · rintro ⟨i, hi, hk⟩
    refine ⟨π.symm i, ?_, hk⟩
    intro h
    exact hi ((π.apply_symm_apply i).symm.trans (congrArg π h))
  · rintro ⟨i, hi, hk⟩
    refine ⟨π i, (fun h => hi (π.injective h)), ?_⟩
    simpa using hk

@[simp] theorem permute_gapEntropy (π : Equiv.Perm (Fin n)) :
    (I.permute π).gapEntropy = I.gapEntropy := by
  simp [gapEntropy]

end Instance
end GapEntropy
