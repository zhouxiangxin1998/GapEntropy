import GapEntropy.UniversalFavorablePath

/-! Ordered call indices and finite counting facts for the actual universal controller. -/
noncomputable section
open scoped Classical BigOperators
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram
variable {n : ℕ}

theorem pending_scale_le (c : Config) (x : Values n) (a a' : Metadata n)
    (z z' : ℝ) (he : stageStep c x (.inr (a, z)) = .inr (a', z')) :
    a.scale ≤ a'.scale := by
  obtain ⟨ha, _, rfl, _⟩ := stageStep_pending_result c x a a' z z' he
  change a.scale ≤ if _ then a.scale else a.scale + 1
  split_ifs
  · exact le_rfl
  · exact Nat.le_succ _

/-- Pending states at equal scales are separated by exactly their call-index
increments. A terminal state cannot occur between two pending states. -/
theorem pending_order (c : Config) (x : Values n) (s t : ℕ) (hst : s ≤ t)
    (a b : Metadata n) (z w : ℝ)
    (hs : stage c x s = .inr (a, z)) (ht : stage c x t = .inr (b, w)) :
    a.scale ≤ b.scale ∧ (a.scale = b.scale →
      continuationIndex c x s + (t - s) = continuationIndex c x t) := by
  induction t, hst using Nat.le_induction generalizing b w with
  | base =>
      have hab : a = b := congrArg Prod.fst (Sum.inr.inj (hs.symm.trans ht))
      exact ⟨by rw [hab], fun _ => by simp⟩
  | succ t hst ih =>
      obtain ⟨b₀, w₀, hp, hstep⟩ := stage_pending_previous c x t b w ht
      obtain ⟨hk, hi⟩ := ih b₀ w₀ hp
      have hnext := pending_scale_le c x b₀ b w₀ w hstep
      refine ⟨hk.trans hnext, ?_⟩
      intro he
      have he₀ : a.scale = b₀.scale := by omega
      have he₁ : b.scale = b₀.scale := by omega
      rw [continuationIndex_step c x t b₀ b w₀ w hp ht, if_pos he₁]
      have := hi he₀
      omega

theorem pending_pair_injective (c : Config) (x : Values n) (s t : ℕ)
    (a b : Metadata n) (z w : ℝ)
    (hs : stage c x s = .inr (a, z)) (ht : stage c x t = .inr (b, w))
    (hk : a.scale = b.scale) (hi : continuationIndex c x s = continuationIndex c x t) : s = t := by
  rcases le_total s t with hst | hts
  · have hh := (pending_order c x s t hst a b z w hs ht).2 hk
    omega
  · have hh := (pending_order c x t s hts b a w z ht hs).2 hk.symm
    omega

/-- Active sets decrease along the actual execution, irrespective of favorable
statistical events. -/
theorem pending_active_subset (c : Config) (x : Values n) (s t : ℕ) (hst : s ≤ t)
    (a b : Metadata n) (z w : ℝ)
    (hs : stage c x s = .inr (a, z)) (ht : stage c x t = .inr (b, w)) : b.active ⊆ a.active := by
  induction t, hst using Nat.le_induction generalizing b w with
  | base =>
      have hab : a = b := congrArg Prod.fst (Sum.inr.inj (hs.symm.trans ht))
      rw [hab]
  | succ t hst ih =>
      obtain ⟨b₀, w₀, hp, hstep⟩ := stage_pending_previous c x t b w ht
      obtain ⟨ha, _, hadv, _⟩ := stageStep_pending_result c x b₀ b w₀ w hstep
      rw [hadv]
      exact (callResult_subset c x b₀ ha w₀).trans (ih b₀ w₀ hp)

theorem pending_same_scale_half (c : Config) (x : Values n) (s t : ℕ) (hst : s < t)
    (a b : Metadata n) (z w : ℝ)
    (hs : stage c x s = .inr (a, z)) (ht : stage c x t = .inr (b, w))
    (hk : a.scale = b.scale) : b.active.card ≤ (a.active.card + 1) / 2 := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : t ≠ 0)
  obtain ⟨b₀, w₀, hp, hstep⟩ := stage_pending_previous c x t b w ht
  have hprev := (pending_order c x s t (by omega) a b₀ z w₀ hs hp).1
  have hnext := pending_scale_le c x b₀ b w₀ w hstep
  have he : b.scale = b₀.scale := by omega
  have hh := (pending_same_scale_contracts c x b₀ b w₀ w hstep he).1
  have hsub := Finset.card_le_card (pending_active_subset c x s t (by omega) a b₀ z w₀ hs hp)
  omega

theorem pending_active_two (hn : 2 ≤ n) (c : Config) (x : Values n) (t : ℕ)
    (a : Metadata n) (z : ℝ) (ht : stage c x t = .inr (a, z)) : 2 ≤ a.active.card := by
  cases t with
  | zero =>
      have ha : a = initial n := (congrArg Prod.fst (Sum.inr.inj ht)).symm
      simpa only [ha, initial, Metadata.active, Finset.card_univ, Fintype.card_fin] using hn
  | succ t =>
      obtain ⟨b, w, _, hstep⟩ := stage_pending_previous c x t a z ht
      obtain ⟨ha, hnot, rfl, _⟩ := stageStep_pending_result c x b a w z hstep
      have hp := (callResult_nonempty c x b ha w).card_pos
      change 2 ≤ (callResult c x b ha w).2.card
      omega

/-- A scale-entry flag is exactly its zero invocation index. -/
theorem pending_entry_iff_index_zero (c : Config) (x : Values n) (t : ℕ)
    (a : Metadata n) (z : ℝ) (ht : stage c x t = .inr (a, z)) :
    a.entry = true ↔ continuationIndex c x t = 0 := by
  cases t with
  | zero =>
      have ha : a = initial n := (congrArg Prod.fst (Sum.inr.inj ht)).symm
      simp only [ha, initial, Metadata.entry, continuationIndex]
  | succ t =>
      obtain ⟨b, w, hp, hstep⟩ := stage_pending_previous c x t a z ht
      obtain ⟨ha, _, hadv, _⟩ := stageStep_pending_result c x b a w z hstep
      rw [continuationIndex_step c x t b a w z hp ht]
      rw [hadv]
      change (!(decide ((callResult c x b ha w).2.card ≤ (b.active.card + 1) / 2))) = true ↔
        (if (if _ then b.scale else b.scale + 1) = b.scale then _ + 1 else 0) = 0
      split_ifs with hh <;> simp_all

theorem pending_entry_scale_injective (c : Config) (x : Values n) (s t : ℕ)
    (a b : Metadata n) (z w : ℝ)
    (hs : stage c x s = .inr (a, z)) (ht : stage c x t = .inr (b, w))
    (ha : a.entry = true) (hb : b.entry = true) (hk : a.scale = b.scale) : s = t := by
  apply pending_pair_injective c x s t a b z w hs ht hk
  rw [(pending_entry_iff_index_zero c x s a z hs).mp ha,
    (pending_entry_iff_index_zero c x t b w ht).mp hb]

end GapEntropy.UniversalAttempt
