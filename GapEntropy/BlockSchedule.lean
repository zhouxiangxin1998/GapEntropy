import GapEntropy.StoppedBlocks

/-! A positive deterministic block schedule partitions every sampling time exactly once. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy

structure BlockSchedule where
  size : ℕ → ℕ
  size_pos : ∀ j, 0 < size j

namespace BlockSchedule
variable (S : BlockSchedule)

def start (j : ℕ) : ℕ := ∑ k ∈ Finset.range j, S.size k

@[simp] theorem start_zero : S.start 0 = 0 := by simp [start]

@[simp] theorem start_succ (j : ℕ) : S.start (j + 1) = S.start j + S.size j :=
  Finset.sum_range_succ _ _

theorem start_strictMono : StrictMono S.start := by
  apply strictMono_nat_of_lt_succ
  intro j
  rw [S.start_succ]
  exact Nat.lt_add_of_pos_right (S.size_pos j)

theorem index_le_start (j : ℕ) : j ≤ S.start j := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [S.start_succ]
      have h := S.size_pos j
      omega

theorem exists_end_after (t : ℕ) : ∃ j, t < S.start (j + 1) :=
  ⟨t, (Nat.lt_succ_self t).trans_le (S.index_le_start (t + 1))⟩

def index (t : ℕ) : ℕ := Nat.find (S.exists_end_after t)

theorem lt_end_index (t : ℕ) : t < S.start (S.index t + 1) :=
  Nat.find_spec (S.exists_end_after t)

theorem start_index_le (t : ℕ) : S.start (S.index t) ≤ t := by
  cases he : S.index t with
  | zero => simp
  | succ j =>
      have h := Nat.find_min (S.exists_end_after t)
        (show j < Nat.find (S.exists_end_after t) by change j < S.index t; omega)
      exact le_of_not_gt h

theorem index_eq_of_bounds {t j : ℕ} (hlo : S.start j ≤ t) (hhi : t < S.start (j + 1)) :
    S.index t = j := by
  apply (Nat.find_eq_iff (S.exists_end_after t)).mpr
  refine ⟨hhi, ?_⟩
  intro k hk hbad
  have h : S.start (k + 1) ≤ S.start j := S.start_strictMono.monotone (by omega)
  omega

@[simp] theorem index_start_add (j : ℕ) (s : Fin (S.size j)) :
    S.index (S.start j + s) = j := by
  apply S.index_eq_of_bounds (Nat.le_add_right _ _)
  rw [S.start_succ]
  have hs := s.isLt
  omega

@[simp] theorem index_start (j : ℕ) : S.index (S.start j) = j := by
  simpa only [Nat.add_zero] using S.index_start_add j ⟨0, S.size_pos j⟩

theorem offset_lt_size (t : ℕ) : t - S.start (S.index t) < S.size (S.index t) := by
  have hlo := S.start_index_le t
  have hhi := S.lt_end_index t
  rw [S.start_succ] at hhi
  omega

/-- The bijection from (attempt, local sample) to global sample time. -/
def timeEquiv : (Σ j, Fin (S.size j)) ≃ ℕ :=
  Equiv.ofBijective (fun p => S.start p.1 + p.2) (by
    constructor
    · rintro ⟨j, s⟩ ⟨k, t⟩ he
      have hjk : j = k := by
        have h := congrArg S.index he
        simpa only [S.index_start_add] using h
      subst k
      apply congrArg (Sigma.mk j)
      exact Fin.ext (Nat.add_left_cancel he)
    · intro t
      exact ⟨⟨S.index t, ⟨t - S.start (S.index t), S.offset_lt_size t⟩⟩,
        Nat.add_sub_of_le (S.start_index_le t)⟩)

def blocks {n : ℕ} (ω : SampleSpace n) : ∀ j, Fin (S.size j) → Fin n → ℝ :=
  fun j s => ω.2 (S.start j + s)

theorem measurable_blocks (n : ℕ) : Measurable (S.blocks (n := n)) := by
  unfold blocks
  fun_prop

/-- All complete blocks jointly have the independent product Gaussian law. -/
theorem measurePreserving_blocks {n : ℕ} (mean : Fin n → ℝ) :
    MeasurePreserving S.blocks (sampleLawOfMeans mean)
      (Measure.infinitePi (fun j => GaussianBlocks.blockLaw mean (S.size j))) := by
  let μ := Measure.pi (fun i => gaussianReal (mean i) 1)
  have hflat : MeasurePreserving
      (fun ω : SampleSpace n => fun p : Σ j, Fin (S.size j) => ω.2 (S.timeEquiv p))
      (sampleLawOfMeans mean) (Measure.infinitePi (fun _ : Σ j, Fin (S.size j) => μ)) := by
    have hr : MeasurePreserving
        (fun x : ℕ → Fin n → ℝ => fun p : Σ j, Fin (S.size j) => x (S.timeEquiv p))
        (rewardLaw mean) (Measure.infinitePi (fun _ : Σ j, Fin (S.size j) => μ)) := by
      exact ⟨by fun_prop, Measure.map_infinitePi_infinitePi_of_inj S.timeEquiv.injective⟩
    exact hr.comp (measurePreserving_snd (μ := seedLaw) (ν := rewardLaw mean))
  have hc : MeasurePreserving
      (MeasurableEquiv.piCurry (fun j (_ : Fin (S.size j)) => Fin n → ℝ))
      (Measure.infinitePi (fun _ : Σ j, Fin (S.size j) => μ))
      (Measure.infinitePi (fun j => GaussianBlocks.blockLaw mean (S.size j))) := by
    refine ⟨MeasurableEquiv.measurable _, ?_⟩
    exact Measure.infinitePi_map_piCurry (fun j (_ : Fin (S.size j)) => μ)
  exact hc.comp hflat

/-- Every nonnegative chronological sum can be grouped by completed attempt blocks. -/
theorem tsum_eq_blocks (f : ℕ → ℝ≥0∞) :
    (∑' t, f t) = ∑' j, ∑ s : Fin (S.size j), f (S.start j + s) := by
  rw [← S.timeEquiv.tsum_eq f]
  change (∑' p : Σ j, Fin (S.size j), f (S.start p.1 + p.2)) = _
  simpa only [tsum_fintype] using
    (ENNReal.tsum_sigma (fun j (s : Fin (S.size j)) => f (S.start j + s)))

end BlockSchedule
end GapEntropy
