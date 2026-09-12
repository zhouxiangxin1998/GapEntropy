import GapEntropy.TargetProfile
import GapEntropy.Elimination

/-!
# Exact target near-arm counts and their relabeling bridge

The original best is counted as near at every scale. A suboptimal arm is near
precisely when its occupied dyadic bucket is strictly beyond the current scale.
The finite count remains an upper bound for every active subset and every
labeling of the target, as required for the success part of C.2.
-/

open scoped BigOperators Classical

namespace GapEntropy.Instance

variable {n : ℕ} (I : Instance n)

theorem targetTolerance_le_gap_iff {i : Fin n} (hi : i ∈ I.suboptimal) (k : ℕ) :
    I.targetTolerance k ≤ I.gap i ↔ I.bucket i ≤ k := by
  obtain ⟨hl, hu⟩ := I.bucket_bounds hi
  constructor
  · intro h
    by_contra hnot
    have hk : k + 1 ≤ I.bucket i := by omega
    have hp := pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num) hk
    rw [pow_succ] at hp
    unfold targetTolerance at h
    nlinarith
  · intro hk
    exact (pow_le_pow_of_le_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 / 2 : ℝ) ≤ 1 by norm_num) hk).trans hl

theorem gap_lt_targetTolerance_iff {i : Fin n} (hi : i ∈ I.suboptimal) (k : ℕ) :
    I.gap i < I.targetTolerance k ↔ k < I.bucket i := by
  simpa only [not_le] using not_congr (I.targetTolerance_le_gap_iff hi k)

theorem near_univ_eq_insert_filter (k : ℕ) :
    Elimination.near Finset.univ I.mean (I.mean I.best) (I.targetTolerance k) =
      insert I.best (I.suboptimal.filter (fun i => k < I.bucket i)) := by
  ext i
  by_cases hi : i = I.best
  · subst i
    simp [Elimination.near, I.targetTolerance_pos k]
  · have his : i ∈ I.suboptimal := (I.mem_suboptimal i).2 hi
    simp only [Elimination.near, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, hi, false_or, his]
    exact I.gap_lt_targetTolerance_iff his k

theorem card_buckets_beyond (k : ℕ) :
    (I.suboptimal.filter fun i => k < I.bucket i).card =
      ∑ t ∈ Finset.range (I.lastBucket + 1), if k < t then I.bucketCount t else 0 := by
  have hm : ∀ i ∈ I.suboptimal, I.bucket i ∈ Finset.range (I.lastBucket + 1) :=
    fun i hi => Finset.mem_range.2 (Nat.lt_succ_of_le (I.bucket_le_lastBucket hi))
  have hf := Finset.sum_fiberwise_of_maps_to hm (fun i => if k < I.bucket i then (1 : ℕ) else 0)
  calc
    _ = ∑ i ∈ I.suboptimal, if k < I.bucket i then (1 : ℕ) else 0 := by simp
    _ = ∑ t ∈ Finset.range (I.lastBucket + 1),
        ∑ i ∈ I.gapGroup t, if k < I.bucket i then (1 : ℕ) else 0 := hf.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      have he : (∑ i ∈ I.gapGroup t, if k < I.bucket i then (1 : ℕ) else 0) =
          ∑ _i ∈ I.gapGroup t, if k < t then (1 : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.1 hi).2]
      rw [he]
      by_cases hkt : k < t <;> simp [hkt, bucketCount]

theorem near_univ_card_eq_targetCount (k : ℕ) :
    (Elimination.near Finset.univ I.mean (I.mean I.best) (I.targetTolerance k)).card =
      I.targetCount k := by
  rw [I.near_univ_eq_insert_filter]
  have hb : I.best ∉ I.suboptimal.filter (fun i => k < I.bucket i) := by simp
  rw [Finset.card_insert_of_notMem hb, I.card_buckets_beyond]
  unfold targetCount
  omega

theorem near_card_le_targetCount (S : Finset (Fin n)) (k : ℕ) :
    (Elimination.near S I.mean (I.mean I.best) (I.targetTolerance k)).card ≤ I.targetCount k := by
  rw [← I.near_univ_card_eq_targetCount k]
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩

/-- The fixed target profile bounds the actual near count after every labeling,
even for an arbitrary active set that no longer contains the original best. -/
theorem permuted_near_card_le_targetCount (π : Equiv.Perm (Fin n))
    (S : Finset (Fin n)) (k : ℕ) :
    (Elimination.near S (I.permute π).mean ((I.permute π).mean (I.permute π).best)
      (I.targetTolerance k)).card ≤ I.targetCount k := by
  have hsub : Elimination.near S (I.permute π).mean
      ((I.permute π).mean (I.permute π).best) (I.targetTolerance k) ⊆
      (Elimination.near Finset.univ I.mean (I.mean I.best) (I.targetTolerance k)).image π := by
    intro i hi
    refine Finset.mem_image.2 ⟨π.symm i, ?_, π.apply_symm_apply i⟩
    have hg : (I.permute π).gap i < I.targetTolerance k := (Finset.mem_filter.1 hi).2
    rw [I.permute_gap] at hg
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hg⟩
  calc
    _ ≤ ((Elimination.near Finset.univ I.mean (I.mean I.best)
      (I.targetTolerance k)).image π).card := Finset.card_le_card hsub
    _ ≤ (Elimination.near Finset.univ I.mean (I.mean I.best) (I.targetTolerance k)).card :=
      Finset.card_image_le
    _ = _ := I.near_univ_card_eq_targetCount k

theorem last_targetTolerance_le_gap {i : Fin n} (hi : i ≠ I.best) :
    I.targetTolerance I.lastBucket ≤ I.gap i :=
  (I.targetTolerance_le_gap_iff ((I.mem_suboptimal i).2 hi) I.lastBucket).2
    (I.bucket_le_lastBucket ((I.mem_suboptimal i).2 hi))

theorem permuted_last_targetTolerance_le_gap (π : Equiv.Perm (Fin n)) {i : Fin n}
    (hi : i ≠ (I.permute π).best) :
    I.targetTolerance I.lastBucket ≤ (I.permute π).mean (I.permute π).best - (I.permute π).mean i := by
  change I.targetTolerance I.lastBucket ≤ (I.permute π).gap i
  rw [I.permute_gap]
  apply I.last_targetTolerance_le_gap
  intro h
  exact hi ((π.apply_symm_apply i).symm.trans (congrArg π h))

end GapEntropy.Instance
