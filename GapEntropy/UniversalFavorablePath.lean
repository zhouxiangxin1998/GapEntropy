import GapEntropy.UniversalStages
import GapEntropy.TargetNearCount
import GapEntropy.UniversalEnvelopeCost

/-!
# Geometric work envelope of actual favorable universal-attempt paths

Favorable conditions concern the actual completed call readouts in `stage`.
The controller and its reward tape are unchanged; this is a deterministic
analysis of those actual transitions, not a substitute abstract algorithm.
-/
noncomputable section
open scoped BigOperators Classical
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram
variable {n : ℕ}

def callResult (c : Config) (x : Values n) (a : Metadata n) (ha : a.Allowed c) (z : ℝ) :
    ℝ × Finset (Fin n) :=
  (callProcedure c a ha.1 z).evaluate (firstBlock (a.call c).samples (shiftValues a.samples x))

theorem callResult_subset (c : Config) (x : Values n) (a : Metadata n) (ha : a.Allowed c) (z : ℝ) :
    (callResult c x a ha z).2 ⊆ a.active := readout_subset c a z _

theorem callResult_card_ge_half (c : Config) (x : Values n) (a : Metadata n)
    (ha : a.Allowed c) (z : ℝ) :
    (a.active.card + 1) / 2 ≤ (callResult c x a ha z).2.card := readout_card_ge_half c a z _

theorem callResult_nonempty (c : Config) (x : Values n) (a : Metadata n)
    (ha : a.Allowed c) (z : ℝ) : (callResult c x a ha z).2.Nonempty :=
  readout_nonempty c a z _ (Finset.card_pos.mp (by have := ha.1; omega))

theorem stageStep_pending_result (c : Config) (x : Values n) (a a' : Metadata n)
    (z z' : ℝ) (he : stageStep c x (.inr (a, z)) = .inr (a', z')) :
    ∃ ha : a.Allowed c, (callResult c x a ha z).2.card ≠ 1 ∧
      a' = a.advance c (callResult c x a ha z).2 ∧
      z' = retainedReference a (callResult c x a ha z).1 (callResult c x a ha z).2 := by
  by_cases ha : a.Allowed c
  · rw [stageStep, dif_pos ha] at he
    change (if (callResult c x a ha z).2.card = 1 then
        Sum.inl ((a.advance c (callResult c x a ha z).2, (callResult c x a ha z).1),
          singletonAnswer (callResult c x a ha z).2)
      else Sum.inr (a.advance c (callResult c x a ha z).2,
        retainedReference a (callResult c x a ha z).1 (callResult c x a ha z).2)) = .inr (a', z') at he
    by_cases hs : (callResult c x a ha z).2.card = 1
    · rw [if_pos hs] at he
      cases he
    · rw [if_neg hs] at he
      exact ⟨ha, hs, (congrArg Prod.fst (Sum.inr.inj he)).symm,
        (congrArg Prod.snd (Sum.inr.inj he)).symm⟩
  · rw [stageStep, dif_neg ha] at he
    cases he

theorem stage_pending_previous (c : Config) (x : Values n) (t : ℕ) (a' : Metadata n) (z' : ℝ)
    (he : stage c x (t + 1) = .inr (a', z')) :
    ∃ a z, stage c x t = .inr (a, z) ∧ stageStep c x (.inr (a, z)) = .inr (a', z') := by
  cases hs : stage c x t with
  | inl result => simp only [stage, hs, stageStep] at he; cases he
  | inr st => exact ⟨st.1, st.2, rfl, by simpa only [stage, hs] using he⟩

/-- Actual same-scale pending transitions are exact rounded halves. Input size
must be at least three because size two would have returned its singleton. -/
theorem pending_same_scale_contracts (c : Config) (x : Values n) (a a' : Metadata n)
    (z z' : ℝ) (he : stageStep c x (.inr (a, z)) = .inr (a', z'))
    (hk : a'.scale = a.scale) :
    a'.active.card = (a.active.card + 1) / 2 ∧ 3 ≤ a.active.card ∧
      4 * a'.active.card ≤ 3 * a.active.card := by
  obtain ⟨ha, hnot, rfl, _⟩ := stageStep_pending_result c x a a' z z' he
  let R := (callResult c x a ha z).2
  have hhalf : R.card ≤ (a.active.card + 1) / 2 := by
    by_contra! h
    have hn : ¬ R.card ≤ (a.active.card + 1) / 2 := by omega
    change (if R.card ≤ (a.active.card + 1) / 2 then a.scale else a.scale + 1) = a.scale at hk
    rw [if_neg hn] at hk
    omega
  have heq : R.card = (a.active.card + 1) / 2 :=
    Nat.le_antisymm hhalf (callResult_card_ge_half c x a ha z)
  have hlarge : 3 ≤ a.active.card := by have := ha.1; change R.card ≠ 1 at hnot; omega
  have hc := Elimination.rounded_half_contracts hlarge
  exact ⟨heq, hlarge, by change 4 * R.card ≤ _; omega⟩

/-- Runtime-favorable local outputs preserve the best and enforce required
large-set progress. At the final occupied bucket every call must halve; F.1's
large-set and separated small-set bounds establish that sufficient condition. -/
def CallFavorable (I : Instance n) (a : Metadata n) (R : Finset (Fin n)) : Prop :=
  I.best ∈ R ∧
    (4 * I.targetCount a.scale < a.active.card → R.card ≤ (a.active.card + 1) / 2) ∧
    (a.scale = I.lastBucket → R.card ≤ (a.active.card + 1) / 2)

def FavorableThrough (I : Instance n) (c : Config) (x : Values n) (T : ℕ) : Prop :=
  ∀ t < T, ∀ a z, stage c x t = .inr (a, z) → ∀ ha : a.Allowed c,
    CallFavorable I a (callResult c x a ha z).2

/-- Zero-based invocation index within the current scale. -/
def continuationIndex (c : Config) (x : Values n) : ℕ → ℕ
  | 0 => 0
  | t + 1 => match stage c x t, stage c x (t + 1) with
    | .inr (a, _), .inr (a', _) =>
        if a'.scale = a.scale then continuationIndex c x t + 1 else 0
    | _, _ => 0

theorem continuationIndex_step (c : Config) (x : Values n) (t : ℕ)
    (a a' : Metadata n) (z z' : ℝ) (ht : stage c x t = .inr (a, z))
    (ht' : stage c x (t + 1) = .inr (a', z')) :
    continuationIndex c x (t + 1) =
      if a'.scale = a.scale then continuationIndex c x t + 1 else 0 := by
  simp only [continuationIndex, ht, ht']

theorem tolerance_eq_target (I : Instance n) (a : Metadata n) :
    a.tolerance = I.targetTolerance a.scale := by
  simp only [Metadata.tolerance, Instance.targetTolerance, zpow_neg, zpow_natCast,
    one_div, inv_pow]

/-- The final-scale clause follows from the usual large-set and separated
small-set progress conditions; no extra statistical success is required. -/
theorem callFavorable_of_progress (I : Instance n) (a : Metadata n) (R : Finset (Fin n))
    (hb : I.best ∈ R)
    (hlarge : 4 * I.targetCount a.scale < a.active.card → R.card ≤ (a.active.card + 1) / 2)
    (hsmall : a.active.card ≤ 4 →
      (∀ i ∈ a.active, i ≠ I.best → a.tolerance ≤ I.mean I.best - I.mean i) →
      R.card ≤ (a.active.card + 1) / 2) : CallFavorable I a R := by
  refine ⟨hb, hlarge, ?_⟩
  intro hk
  by_cases hs : 4 < a.active.card
  · apply hlarge
    simpa only [hk, I.targetCount_last, mul_one] using hs
  · apply hsmall (by omega)
    intro i _ hi
    rw [tolerance_eq_target I a, hk]
    exact I.last_targetTolerance_le_gap hi

/-- Every actual pending call on a favorable prefix has the source's geometric
work envelope, and no favorable call reaches a scale beyond the last gap bucket. -/
theorem favorable_pending_envelope (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) (t : ℕ) (ht : t ≤ T) (a : Metadata n) (z : ℝ)
    (hstate : stage c x t = .inr (a, z)) :
    I.best ∈ a.active ∧ a.scale ≤ I.lastBucket ∧
      (a.active.card : ℝ) * (4 : ℝ) ^ a.scale ≤
        UniversalEnvelopeCost.envelope (I.scaleWork a.scale) (continuationIndex c x t) := by
  induction t generalizing a z with
  | zero =>
      have he : (initial n, (0 : ℝ)) = (a, z) := Sum.inr.inj hstate
      have ha : a = initial n := (congrArg Prod.fst he).symm
      rw [ha]
      refine ⟨Finset.mem_univ _, Nat.zero_le _, ?_⟩
      simp only [initial, Metadata.active, Metadata.scale, Finset.card_univ,
        Fintype.card_fin, pow_zero, mul_one, continuationIndex, UniversalEnvelopeCost.envelope,
        I.scaleWork_zero]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  | succ t ih =>
      obtain ⟨a₀, z₀, hprev, hstep⟩ := stage_pending_previous c x t a z hstate
      obtain ⟨hbest₀, hscale₀, hwork₀⟩ := ih (by omega) a₀ z₀ hprev
      obtain ⟨ha, hnot, hadv, hz⟩ := stageStep_pending_result c x a₀ a z₀ z hstep
      let R := (callResult c x a₀ ha z₀).2
      have hcall := hgood t (by omega) a₀ z₀ hprev ha
      have hab : a.active = R := by rw [hadv]; rfl
      have hbest : I.best ∈ a.active := by rw [hab]; exact hcall.1
      have hsizes : R.card ≤ a₀.active.card := Finset.card_le_card (callResult_subset c x a₀ ha z₀)
      by_cases hk : a.scale = a₀.scale
      · obtain ⟨hhalf, _, hcontract⟩ := pending_same_scale_contracts c x a₀ a z₀ z hstep hk
        refine ⟨hbest, by omega, ?_⟩
        rw [continuationIndex_step c x t a₀ a z₀ z hprev hstate, if_pos hk, hk]
        have hreal : (a.active.card : ℝ) ≤ (a₀.active.card : ℝ) * (3 / 4 : ℝ) := by
          have hh : (4 : ℝ) * a.active.card ≤ 3 * a₀.active.card := by exact_mod_cast hcontract
          linarith
        calc
          _ ≤ ((a₀.active.card : ℝ) * (3 / 4 : ℝ)) * (4 : ℝ) ^ a₀.scale :=
            mul_le_mul_of_nonneg_right hreal (by positivity)
          _ = ((a₀.active.card : ℝ) * (4 : ℝ) ^ a₀.scale) * (3 / 4 : ℝ) := by ring
          _ ≤ UniversalEnvelopeCost.envelope (I.scaleWork a₀.scale) (continuationIndex c x t) * (3 / 4 : ℝ) :=
            mul_le_mul_of_nonneg_right hwork₀ (by norm_num)
          _ = _ := by simp only [UniversalEnvelopeCost.envelope, pow_succ]; ring
      · have hstall : (a₀.active.card + 1) / 2 < R.card := by
          by_contra! hh
          apply hk
          rw [hadv]
          change (if R.card ≤ (a₀.active.card + 1) / 2 then a₀.scale else a₀.scale + 1) = a₀.scale
          exact if_pos hh
        have hscale : a.scale = a₀.scale + 1 := by
          rw [hadv]
          change (if R.card ≤ (a₀.active.card + 1) / 2 then a₀.scale else a₀.scale + 1) = a₀.scale + 1
          exact if_neg (not_le_of_gt hstall)
        have hnlast : a₀.scale ≠ I.lastBucket := by
          intro he
          exact (not_lt_of_ge (hcall.2.2 he)) hstall
        have hsmall : a₀.active.card ≤ 4 * I.targetCount a₀.scale := by
          by_contra! hh
          exact (not_lt_of_ge (hcall.2.1 hh)) hstall
        refine ⟨hbest, by omega, ?_⟩
        rw [continuationIndex_step c x t a₀ a z₀ z hprev hstate, if_neg hk, hscale,
          UniversalEnvelopeCost.envelope, pow_zero, mul_one, I.scaleWork_succ]
        have hcard : (a.active.card : ℝ) ≤ 4 * (I.targetCount a₀.scale : ℝ) := by
          rw [hab]
          exact_mod_cast hsizes.trans hsmall
        calc
          _ ≤ (4 * (I.targetCount a₀.scale : ℝ)) * (4 : ℝ) ^ (a₀.scale + 1) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
          _ = _ := by ring

end GapEntropy.UniversalAttempt
