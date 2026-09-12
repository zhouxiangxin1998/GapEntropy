import GapEntropy.WindowGeometry
import GapEntropy.IntervalPacking

/-!
# Cheap representative windows imply the scale-counting inequality

This instantiates bounded overlap with the actual instance's dyadic buckets.
The largest-gap cheap representative selects one common comparison law for all
cheap windows. Probability bounds for the windows are explicit hypotheses;
the final statistical application supplies them from the real marked experiment.
-/

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.Instance

variable {n : ℕ} (I : Instance n)

noncomputable def cheapBuckets (c : Fin n → ℝ) (x : ℝ) : Finset ℕ :=
  I.occupiedBuckets.filter (fun k => I.representativeCost c k ≤ x)

theorem cheapBuckets_subset (c : Fin n → ℝ) (x : ℝ) :
    I.cheapBuckets c x ⊆ I.occupiedBuckets := Finset.filter_subset _ _

theorem cheap_representative_cost_le (c : Fin n → ℝ) {x : ℝ} {k : ℕ}
    (hk : k ∈ I.cheapBuckets c x) : c (I.representativeArm c k) ≤ x := by
  obtain ⟨hko, hc⟩ := Finset.mem_filter.1 hk
  rwa [I.representativeCost_eq_cost_arm c hko] at hc

/-- A largest-gap cheap representative is a common pivot for every cheap scale. -/
theorem exists_cheap_pivot (c : Fin n → ℝ) (x : ℝ)
    (hs : (I.cheapBuckets c x).Nonempty) :
    ∃ a ∈ I.suboptimal, c a ≤ x ∧
      ∀ k ∈ I.cheapBuckets c x, I.gap (I.representativeArm c k) ≤ I.gap a := by
  obtain ⟨k, hk, hmax⟩ := (I.cheapBuckets c x).exists_max_image
    (fun k => I.gap (I.representativeArm c k)) hs
  exact ⟨I.representativeArm c k,
    I.representativeArm_suboptimal c (I.cheapBuckets_subset c x hk),
    I.cheap_representative_cost_le c hk, hmax⟩

/-- Equation B.13 from common-null window probabilities and the true dyadic
geometry. No independence or pairwise disjointness of the windows is assumed. -/
theorem scale_count_of_windows {Ω : Type*} [MeasurableSpace Ω]
    (c : Fin n → ℝ) (hc : ∀ i ∈ I.suboptimal, 0 < c i)
    (Q : Fin n → Measure Ω) (E : Fin n → Set Ω) (F : Set Ω) (N : Ω → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hE : ∀ i ∈ I.suboptimal, MeasurableSet (E i)) (hF : MeasurableSet F)
    (hsub : ∀ i ∈ I.suboptimal, E i ⊆ F)
    (hwindow : ∀ i ∈ I.suboptimal, ∀ ω ∈ E i,
      I.weight i / 100 ≤ N ω ∧ N ω ≤ 16 * c i * I.weight i)
    (hnull : ∀ a ∈ I.suboptimal, Q a F ≤ ENNReal.ofReal δ)
    (hlower : ∀ a ∈ I.suboptimal, ∀ d ∈ I.suboptimal, I.gap d ≤ I.gap a →
      ENNReal.ofReal (Real.exp (-(c d + c a)) / 4) ≤ Q a (E d))
    (x : ℝ) (hx : 1 ≤ x) :
    ((I.cheapBuckets c x).card : ℝ) ≤
      4 * δ * (Real.log (1600 * x) / Real.log 4 + 2) * Real.exp (2 * x) := by
  have hℓ := windowLength_nonneg hx
  by_cases hs : (I.cheapBuckets c x).Nonempty
  · obtain ⟨a, ha, hax, hmax⟩ := I.exists_cheap_pivot c x hs
    have hi (k : ℕ) (hk : k ∈ I.cheapBuckets c x) : I.representativeArm c k ∈ I.suboptimal :=
      I.representativeArm_suboptimal c (I.cheapBuckets_subset c x hk)
    have hcell (k : ℕ) (hk : k ∈ I.cheapBuckets c x) :
        (k : ℝ) - 1 < I.windowStart (I.representativeArm c k) ∧
          I.windowStart (I.representativeArm c k) ≤ k := by
      rw [I.representativeArm_of_mem c (I.cheapBuckets_subset c x hk)]
      exact I.windowStart_costRepresentative c k (I.cheapBuckets_subset c x hk)
    have hw (k : ℕ) (hk : k ∈ I.cheapBuckets c x) (ω : Ω)
        (hω : ω ∈ E (I.representativeArm c k)) :
        I.windowStart (I.representativeArm c k) ≤ Real.log (100 * N ω) / Real.log 4 ∧
          Real.log (100 * N ω) / Real.log 4 ≤
            I.windowStart (I.representativeArm c k) + windowLength x := by
      obtain ⟨hlo, hhi⟩ := hwindow _ (hi k hk) ω hω
      have hg := sample_window_implies_log_window (I.weight_pos (hi k hk))
        (hc _ (hi k hk)) hlo hhi
      exact ⟨hg.1, hg.2.trans (add_le_add le_rfl
        (windowLength_mono (hc _ (hi k hk)) (I.cheap_representative_cost_le c hk)))⟩
    have hl (k : ℕ) (hk : k ∈ I.cheapBuckets c x) :
        ENNReal.ofReal (Real.exp (-(2 * x)) / 4) ≤ Q a (E (I.representativeArm c k)) := by
      apply le_trans _ (hlower a ha _ (hi k hk) (hmax k hk))
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 4)
      apply Real.exp_le_exp.mpr
      linarith [I.cheap_representative_cost_le c hk]
    have hp := stopping_window_card_mul_le (Q a) (I.cheapBuckets c x)
      (fun k => E (I.representativeArm c k)) F (fun k => I.windowStart (I.representativeArm c k))
      (fun ω => Real.log (100 * N ω) / Real.log 4) hℓ
      (show 0 ≤ Real.exp (-(2 * x)) / 4 by positivity) hδ hcell
      (fun k hk => hE _ (hi k hk)) hF (fun k hk => hsub _ (hi k hk)) hw hl (hnull a ha)
    have hid : Real.exp (-(2 * x)) * Real.exp (2 * x) = 1 := by
      rw [← Real.exp_add]
      simp
    calc
      ((I.cheapBuckets c x).card : ℝ) =
          (((I.cheapBuckets c x).card : ℝ) * (Real.exp (-(2 * x)) / 4)) *
            (4 * Real.exp (2 * x)) := by
        calc
          _ = ((I.cheapBuckets c x).card : ℝ) *
              (Real.exp (-(2 * x)) * Real.exp (2 * x)) := by rw [hid, mul_one]
          _ = _ := by ring
      _ ≤ ((windowLength x + 2) * δ) * (4 * Real.exp (2 * x)) :=
        mul_le_mul_of_nonneg_right hp (by positivity)
      _ = _ := by unfold windowLength; ring
  · have he := Finset.not_nonempty_iff_eq_empty.1 hs
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hl : 0 ≤ Real.log (1600 * x) / Real.log 4 + 2 := by
      change 0 ≤ windowLength x + 2
      linarith
    positivity

end GapEntropy.Instance
