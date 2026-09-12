import GapEntropy.UniversalPathCounting
import GapEntropy.UniversalCallCost

/-! Actual favorable path budgets, with prospective calls included. -/
noncomputable section
open scoped Classical BigOperators
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram UniversalCall UniversalEnvelopeCost UniversalCallCost
variable {n : ℕ}

theorem alpha_eq_callAlpha (c : Config) (a : Metadata n) :
    a.alpha c = callAlpha c.confidence ((2 : ℝ) ^ c.attempt) c.attempt
      a.active.card ((a.active.card : ℝ) * (4 : ℝ) ^ a.scale) := by
  simp only [Metadata.alpha, Reservation.callConfidence, Config.errorBudget, Config.workCap,
    Metadata.baseCall, Reservation.Call.work, callAlpha, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem favorable_pending_alpha (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) (hδ : ValidConfidence c.confidence)
    (hH : I.hardness ≤ (2 : ℝ) ^ c.attempt) (t : ℕ) (ht : t ∈ pendingCalls c x T) :
    0 < (metadataAt c x t).alpha c ∧ (metadataAt c x t).alpha c ≤ 1 := by
  have hδ0 := hδ.1
  have hw := pendingWork_pos I.two_le c x T t ht
  have hbound := (pendingWork_le_envelope I c x T hgood t ht).trans
    (envelope_le_total I (Nat.le_of_lt_succ (boundedScale I c x t).isLt) _)
  have hW := I.hardness_le_workEnvelope_lt.2
  have hcap : pendingWork c x t ≤ 1024 * (2 : ℝ) ^ c.attempt := by
    linarith [I.hardness_pos]
  rw [alpha_eq_callAlpha]
  change 0 < callAlpha _ _ _ _ (pendingWork c x t) ∧ callAlpha _ _ _ _ (pendingWork c x t) ≤ 1
  refine ⟨callAlpha_pos hδ.1 (by positivity) hw _ _, ?_⟩
  unfold callAlpha
  have he : c.confidence / 1024 * pendingWork c x t / (1024 * (2 : ℝ) ^ c.attempt) ≤
      c.confidence / 1024 := by
    apply (div_le_iff₀ (by positivity)).mpr
    exact mul_le_mul_of_nonneg_left hcap (by positivity)
  have hs := mul_le_of_le_one_right
    (show 0 ≤ c.confidence / 1024 * pendingWork c x t / (1024 * (2 : ℝ) ^ c.attempt) by positivity)
    (Reservation.smallFactor_le_one c.attempt (metadataAt c x t).active.card)
  have hδ1 := hδ.2
  linarith

def pendingReference (c : Config) (x : Values n) (t : ℕ) : ℝ :=
  if (metadataAt c x t).entry then
    referenceBudget (metadataAt c x t).tolerance ((metadataAt c x t).beta c) else 0

def pendingSurcharge (c : Config) (x : Values n) (t : ℕ) : ℝ :=
  if 2 ≤ (metadataAt c x t).active.card ∧ (metadataAt c x t).active.card ≤ 7
  then 2 * pendingWork c x t * Real.log (c.attempt + 1 : ℝ) else 0

theorem favorable_call_samples_le (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) (hδ : ValidConfidence c.confidence)
    (hH : I.hardness ≤ (2 : ℝ) ^ c.attempt) (t : ℕ) (ht : t ∈ pendingCalls c x T) :
    (((metadataAt c x t).call c).samples : ℝ) ≤
      6500000 * (charge (134217728 * (2 : ℝ) ^ c.attempt / c.confidence) (pendingWork c x t) +
        pendingSurcharge c x t) + pendingReference c x t := by
  let a := metadataAt c x t
  have ha2 : 2 ≤ a.active.card := by
    obtain ⟨_, a', z, hs⟩ := (mem_pendingCalls c x T t).mp ht
    simpa only [a, metadataAt_of_pending c x t a' z hs] using pending_active_two I.two_le c x t a' z hs
  obtain ⟨hα, hα1⟩ := favorable_pending_alpha I c x T hgood hδ hH t ht
  have hd := I.targetTolerance_pos a.scale
  have hd1 := I.targetTolerance_le_one a.scale
  rw [← tolerance_eq_target I a] at hd hd1
  have hd2 : (a.tolerance ^ 2)⁻¹ = (4 : ℝ) ^ a.scale := by
    rw [tolerance_eq_target I a]
    exact I.targetTolerance_inv_square a.scale
  have hnr := nonreference_budget_le (show 0 < a.active.card by omega) hd hd1 hα hα1
  rw [hd2] at hnr
  have hlog := charge_callAlpha hδ.1 (by positivity : 0 < (2 : ℝ) ^ c.attempt)
    (pendingWork_pos I.two_le c x T t ht) c.attempt a.active.card
  have hαeq : a.alpha c = callAlpha c.confidence ((2 : ℝ) ^ c.attempt) c.attempt
      a.active.card (pendingWork c x t) := alpha_eq_callAlpha c a
  rw [← hαeq] at hlog
  change pendingWork c x t * Real.log (128 / a.alpha c) = _ at hlog
  change _ ≤ 6500000 * (charge _ _ + pendingSurcharge c x t) + pendingReference c x t
  have hle : ((a.call c).samples : ℝ) ≤
      6500000 * (pendingWork c x t * Real.log (128 / a.alpha c)) + pendingReference c x t := by
    change ((if a.entry then entryBudget _ _ _ _ else laterBudget _ _ _ : ℕ) : ℝ) ≤ _
    unfold pendingReference
    change _ ≤ _ + if a.entry then (referenceBudget a.tolerance (a.beta c) : ℝ) else 0
    by_cases he : a.entry = true
    · simp only [he, ↓reduceIte, entryBudget, activeStart, Nat.cast_add]
      change (medianBudget _ _ _ : ℝ) + _ + _ ≤ _
      push_cast at hnr
      dsimp only [pendingWork] at *
      nlinarith
    · simp only [he, Bool.false_eq_true, ↓reduceIte, add_zero]
      have hm : (0 : ℝ) ≤ medianBudget a.active.card a.tolerance (a.alpha c) := Nat.cast_nonneg _
      push_cast at hnr
      dsimp only [pendingWork] at *
      nlinarith
  rw [hlog] at hle
  exact hle

def smallWorkAt (c : Config) (x : Values n) (T k : ℕ) : ℝ :=
  ∑ t ∈ smallCallsAt c x T k, pendingWork c x t

theorem smallWorkAt_le (hn : 2 ≤ n) (c : Config) (x : Values n) (T k : ℕ) :
    smallWorkAt c x T k ≤ 13 * (4 : ℝ) ^ k := by
  have he : smallWorkAt c x T k =
      ((∑ t ∈ smallCallsAt c x T k, (metadataAt c x t).active.card : ℕ) : ℝ) * (4 : ℝ) ^ k := by
    rw [Nat.cast_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [pendingWork, (Finset.mem_filter.mp ht).2.1]
  rw [he]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast small_input_sum_le_thirteen hn c x T k) (by positivity)


theorem favorable_sum_surcharge_le (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) :
    (∑ t ∈ pendingCalls c x T, pendingSurcharge c x t) ≤
      140 * I.twoArmHardness * Real.log (c.attempt + 1 : ℝ) := by
  let s := (pendingCalls c x T).filter (fun t => (metadataAt c x t).active.card ≤ 7)
  let g := fun t => (metadataAt c x t).scale
  let f := fun t => 2 * pendingWork c x t * Real.log (c.attempt + 1 : ℝ)
  have hmaps : ∀ t ∈ s, g t ∈ Finset.range (I.lastBucket + 1) := by
    intro t ht
    have hp := (Finset.mem_filter.mp ht).1
    have hh := (boundedScale I c x t).isLt
    rw [boundedScale_eq I c x T hgood t hp] at hh
    exact Finset.mem_range.mpr hh
  have heq : (∑ t ∈ pendingCalls c x T, pendingSurcharge c x t) = ∑ t ∈ s, f t := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t ht
    obtain ⟨_, a, z, hs⟩ := (mem_pendingCalls c x T t).mp ht
    have htwo : 2 ≤ (metadataAt c x t).active.card := by
      rw [metadataAt_of_pending c x t a z hs]
      exact pending_active_two I.two_le c x t a z hs
    simp only [pendingSurcharge, htwo, true_and, f]
  rw [heq, ← Finset.sum_fiberwise_of_maps_to hmaps f]
  have hfilters (k : ℕ) : s.filter (fun t => g t = k) = smallCallsAt c x T k := by
    ext t
    simp only [s, g, smallCallsAt, Finset.mem_filter]
    tauto
  simp_rw [hfilters]
  have heqsum (k : ℕ) : (∑ t ∈ smallCallsAt c x T k, f t) =
      2 * smallWorkAt c x T k * Real.log (c.attempt + 1 : ℝ) := by
    simp only [f, smallWorkAt, Finset.mul_sum, Finset.sum_mul]
  simp_rw [heqsum]
  exact small_surcharge_le I c.attempt (smallWorkAt c x T)
    (fun k _ => smallWorkAt_le I.two_le c x T k)

theorem favorable_sum_reference_le (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) (hδ : ValidConfidence c.confidence) :
    (∑ t ∈ pendingCalls c x T, pendingReference c x t) ≤
      100000 * I.twoArmHardness *
        (confidenceCost c.confidence + Real.log (c.attempt + 1 : ℝ) + iteratedLog I.twoArmHardness) := by
  let e := (pendingCalls c x T).filter (fun t => (metadataAt c x t).entry = true)
  let g := fun t => (metadataAt c x t).scale
  let f := fun k => (referenceBudget (I.targetTolerance k)
    (referenceError c.confidence c.attempt k) : ℝ)
  have heq : (∑ t ∈ pendingCalls c x T, pendingReference c x t) = ∑ t ∈ e, f (g t) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro t _
    simp only [pendingReference, Metadata.beta, tolerance_eq_target I, f, g]
  have hsub : e.image g ⊆ Finset.range (I.lastBucket + 1) := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    have hp := (Finset.mem_filter.mp ht).1
    have hh := (boundedScale I c x t).isLt
    rw [boundedScale_eq I c x T hgood t hp] at hh
    exact Finset.mem_range.mpr hh
  calc
    _ = ∑ t ∈ e, f (g t) := heq
    _ = ∑ k ∈ e.image g, f k := (Finset.sum_image (entry_scale_injOn c x T)).symm
    _ ≤ ∑ k ∈ Finset.range (I.lastBucket + 1), f k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ _ := UniversalReferenceCost.total_referenceBudget_le I hδ c.attempt I.targetTolerance
      I.targetTolerance_inv_square

/-- The full F.9 declared sample bound is now instantiated by the actual
controller, including each pending prospective call before its cap decision. -/
theorem favorable_sum_samples_le (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) (hδ : ValidConfidence c.confidence)
    (hH : I.hardness ≤ (2 : ℝ) ^ c.attempt) :
    (∑ t ∈ pendingCalls c x T, (((metadataAt c x t).call c).samples : ℝ)) ≤
      40000000000 * UniversalCapAnalysis.favorableCost I c.confidence c.attempt := by
  apply combine_favorable_costs I hδ c.attempt hH _
    (∑ t ∈ pendingCalls c x T,
      charge (134217728 * (2 : ℝ) ^ c.attempt / c.confidence) (pendingWork c x t))
    (∑ t ∈ pendingCalls c x T, pendingSurcharge c x t)
    (∑ t ∈ pendingCalls c x T, pendingReference c x t)
  · have hh := Finset.sum_le_sum (fun t ht => favorable_call_samples_le I c x T hgood hδ hH t ht)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hh
  · exact favorable_sum_charge_le I c x T hgood hδ hH
  · exact favorable_sum_surcharge_le I c x T hgood
  · exact favorable_sum_reference_le I c x T hgood hδ

end GapEntropy.UniversalAttempt
