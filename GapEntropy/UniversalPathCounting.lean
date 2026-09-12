import GapEntropy.UniversalPathIndices
import GapEntropy.UniversalEnvelopeFinite

/-! Finite actual pending calls inject into scale/continuation coordinates. -/
noncomputable section
open scoped Classical BigOperators
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram
variable {n : ℕ}

/-- Metadata projection, also defined on absorbing terminal stages. -/
def metadataAt (c : Config) (x : Values n) (t : ℕ) : Metadata n :=
  match stage c x t with
  | .inl ((a, _), _) => a
  | .inr (a, _) => a

@[simp] theorem metadataAt_of_pending (c : Config) (x : Values n) (t : ℕ)
    (a : Metadata n) (z : ℝ) (ht : stage c x t = .inr (a, z)) : metadataAt c x t = a := by
  simp only [metadataAt, ht]

/-- Includes a pending prospective call before its cap check. -/
def pendingCalls (c : Config) (x : Values n) (T : ℕ) : Finset ℕ :=
  (Finset.range T).filter (fun t => ∃ a z, stage c x t = .inr (a, z))

theorem mem_pendingCalls (c : Config) (x : Values n) (T t : ℕ) :
    t ∈ pendingCalls c x T ↔ t < T ∧ ∃ a z, stage c x t = .inr (a, z) := by
  simp only [pendingCalls, Finset.mem_filter, Finset.mem_range]

def pendingWork (c : Config) (x : Values n) (t : ℕ) : ℝ :=
  ((metadataAt c x t).active.card : ℝ) * (4 : ℝ) ^ (metadataAt c x t).scale

def boundedScale (I : Instance n) (c : Config) (x : Values n) (t : ℕ) : Fin (I.lastBucket + 1) :=
  ⟨min (metadataAt c x t).scale I.lastBucket, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

theorem boundedScale_eq (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) (t : ℕ) (ht : t ∈ pendingCalls c x T) :
    (boundedScale I c x t : ℕ) = (metadataAt c x t).scale := by
  obtain ⟨htt, a, z, hs⟩ := (mem_pendingCalls c x T t).mp ht
  have hk := (favorable_pending_envelope I c x T hgood t (by omega) a z hs).2.1
  simp only [boundedScale, metadataAt_of_pending c x t a z hs, Nat.min_eq_left hk]

theorem pending_coordinates_injOn (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) :
    Set.InjOn (fun t => (boundedScale I c x t, continuationIndex c x t))
      (pendingCalls c x T : Set ℕ) := by
  intro s hs t ht he
  have hk := congrArg (fun p : Fin (I.lastBucket + 1) × ℕ => (p.1 : ℕ)) he
  have hi := congrArg Prod.snd he
  rw [boundedScale_eq I c x T hgood s hs, boundedScale_eq I c x T hgood t ht] at hk
  obtain ⟨_, a, z, ha⟩ := (mem_pendingCalls c x T s).mp hs
  obtain ⟨_, b, w, hb⟩ := (mem_pendingCalls c x T t).mp ht
  rw [metadataAt_of_pending c x s a z ha, metadataAt_of_pending c x t b w hb] at hk
  exact pending_pair_injective c x s t a b z w ha hb hk hi

theorem pendingWork_pos (hn : 2 ≤ n) (c : Config) (x : Values n) (T t : ℕ)
    (ht : t ∈ pendingCalls c x T) : 0 < pendingWork c x t := by
  obtain ⟨_, a, z, hs⟩ := (mem_pendingCalls c x T t).mp ht
  have hp := pending_active_two hn c x t a z hs
  rw [pendingWork, metadataAt_of_pending c x t a z hs]
  positivity

theorem pendingWork_le_envelope (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) (t : ℕ) (ht : t ∈ pendingCalls c x T) :
    pendingWork c x t ≤ UniversalEnvelopeCost.envelope
      (I.scaleWork (boundedScale I c x t)) (continuationIndex c x t) := by
  rw [boundedScale_eq I c x T hgood t ht]
  obtain ⟨htt, a, z, hs⟩ := (mem_pendingCalls c x T t).mp ht
  rw [pendingWork, metadataAt_of_pending c x t a z hs]
  exact (favorable_pending_envelope I c x T hgood t (by omega) a z hs).2.2

/-- F.2's total base-work bound for actual calls, including a prospective call. -/
theorem favorable_sum_work_le (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) :
    (∑ t ∈ pendingCalls c x T, pendingWork c x t) ≤ 16 * I.workEnvelope :=
  UniversalEnvelopeCost.sum_work_le_envelope I (pendingCalls c x T) (boundedScale I c x)
    (continuationIndex c x) (pending_coordinates_injOn I c x T hgood) (pendingWork c x)
    (pendingWork_le_envelope I c x T hgood)

/-- F.6's baseline charge on the actual finite invocation set. -/
theorem favorable_sum_charge_le (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) {δ h : ℝ} (hδ : ValidConfidence δ)
    (hH : I.hardness ≤ h) :
    (∑ t ∈ pendingCalls c x T,
      UniversalEnvelopeCost.charge (134217728 * h / δ) (pendingWork c x t)) ≤
      6000 * I.hardness *
        (confidenceCost δ + I.gapEntropy + 1 + Real.log (h / I.hardness)) :=
  UniversalEnvelopeCost.sum_charge_le_envelope I hδ hH (pendingCalls c x T)
    (boundedScale I c x) (continuationIndex c x) (pending_coordinates_injOn I c x T hgood)
    (pendingWork c x) (pendingWork_pos I.two_le c x T)
    (pendingWork_le_envelope I c x T hgood)

/-- The three possible small-input bands have maxima two, four, and seven. -/
def smallBand (s : ℕ) : Fin 3 := if 5 ≤ s then 2 else if 3 ≤ s then 1 else 0

def smallBandBound (q : Fin 3) : ℕ := if q = 0 then 2 else if q = 1 then 4 else 7

theorem smallBand_bound {s : ℕ} (hs : s ≤ 7) : s ≤ smallBandBound (smallBand s) := by
  unfold smallBand smallBandBound
  split_ifs <;> norm_num at * <;> omega

theorem smallBand_ne_of_half {s t : ℕ} (hs : 2 ≤ s) (ht : 2 ≤ t)
    (hs7 : s ≤ 7) (ht7 : t ≤ 7) (hh : t ≤ (s + 1) / 2) : smallBand s ≠ smallBand t := by
  unfold smallBand
  split_ifs <;> norm_num <;> omega

def smallCallsAt (c : Config) (x : Values n) (T k : ℕ) : Finset ℕ :=
  (pendingCalls c x T).filter (fun t =>
    (metadataAt c x t).scale = k ∧ (metadataAt c x t).active.card ≤ 7)

theorem smallBand_injOn (hn : 2 ≤ n) (c : Config) (x : Values n) (T k : ℕ) :
    Set.InjOn (fun t => smallBand (metadataAt c x t).active.card)
      (smallCallsAt c x T k : Set ℕ) := by
  intro s hs t ht he
  dsimp only at he
  obtain ⟨hs, hsk, hs7⟩ := Finset.mem_filter.mp hs
  obtain ⟨ht, htk, ht7⟩ := Finset.mem_filter.mp ht
  obtain ⟨_, a, z, ha⟩ := (mem_pendingCalls c x T s).mp hs
  obtain ⟨_, b, w, hb⟩ := (mem_pendingCalls c x T t).mp ht
  rw [metadataAt_of_pending c x s a z ha] at hsk hs7 he
  rw [metadataAt_of_pending c x t b w hb] at htk ht7 he
  have ha2 := pending_active_two hn c x s a z ha
  have hb2 := pending_active_two hn c x t b w hb
  rcases lt_trichotomy s t with hst | hst | hts
  · exact False.elim ((smallBand_ne_of_half ha2 hb2 hs7 ht7
      (pending_same_scale_half c x s t hst a b z w ha hb (hsk.trans htk.symm))) he)
  · exact hst
  · exact False.elim ((smallBand_ne_of_half hb2 ha2 ht7 hs7
      (pending_same_scale_half c x t s hts b a w z hb ha (htk.trans hsk.symm))) he.symm)

/-- F.7's 7 + 4 + 2 bound follows from actual halving transitions. -/
theorem small_input_sum_le_thirteen (hn : 2 ≤ n) (c : Config) (x : Values n) (T k : ℕ) :
    (∑ t ∈ smallCallsAt c x T k, (metadataAt c x t).active.card) ≤ 13 := by
  calc
    _ ≤ ∑ t ∈ smallCallsAt c x T k, smallBandBound (smallBand (metadataAt c x t).active.card) :=
      Finset.sum_le_sum (fun t ht => smallBand_bound (Finset.mem_filter.mp ht).2.2)
    _ = ∑ q ∈ (smallCallsAt c x T k).image (fun t => smallBand (metadataAt c x t).active.card),
        smallBandBound q := (Finset.sum_image (smallBand_injOn hn c x T k)).symm
    _ ≤ ∑ q : Fin 3, smallBandBound q :=
      Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = 13 := by
      norm_num [Fin.sum_univ_succ, smallBandBound]
      split_ifs with hh
      · have hv := congrArg Fin.val hh
        norm_num at hv
      · norm_num

/-- At most one scale-entry call is present at any given scale. -/
theorem entry_scale_injOn (c : Config) (x : Values n) (T : ℕ) :
    Set.InjOn (fun t => (metadataAt c x t).scale)
      (((pendingCalls c x T).filter (fun t => (metadataAt c x t).entry = true)) : Set ℕ) := by
  intro s hs t ht hk
  dsimp only at hk
  obtain ⟨hs, hse⟩ := Finset.mem_filter.mp hs
  obtain ⟨ht, hte⟩ := Finset.mem_filter.mp ht
  obtain ⟨_, a, z, ha⟩ := (mem_pendingCalls c x T s).mp hs
  obtain ⟨_, b, w, hb⟩ := (mem_pendingCalls c x T t).mp ht
  rw [metadataAt_of_pending c x s a z ha] at hk hse
  rw [metadataAt_of_pending c x t b w hb] at hk hte
  exact pending_entry_scale_injective c x s t a b z w ha hb hse hte hk

end GapEntropy.UniversalAttempt
