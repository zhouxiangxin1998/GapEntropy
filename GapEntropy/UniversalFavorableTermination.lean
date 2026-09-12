import GapEntropy.UniversalPathCost

/-! Favorable actual attempts pass their prospective caps and return the best arm. -/
noncomputable section
open scoped Classical BigOperators
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram UniversalCallCost
variable {n : ℕ}

theorem pending_before (c : Config) (x : Values n) (s t : ℕ) (hst : s ≤ t)
    (a : Metadata n) (z : ℝ) (ht : stage c x t = .inr (a, z)) :
    ∃ b w, stage c x s = .inr (b, w) := by
  induction t generalizing a z with
  | zero =>
      have hs : s = 0 := by omega
      exact ⟨a, z, by simpa only [hs] using ht⟩
  | succ t ih =>
      by_cases hs : s = t + 1
      · exact ⟨a, z, hs ▸ ht⟩
      · obtain ⟨b, w, hp, _⟩ := stage_pending_previous c x t a z ht
        exact ih (by omega) b w hp

/-- Every earlier call was fully executed if the present stage is still pending. -/
theorem pending_counters_eq (c : Config) (x : Values n) (t : ℕ)
    (a : Metadata n) (z : ℝ) (ht : stage c x t = .inr (a, z)) :
    a.work = ∑ s ∈ Finset.range t, ((metadataAt c x s).call c).work ∧
    a.samples = ∑ s ∈ Finset.range t, ((metadataAt c x s).call c).samples := by
  induction t generalizing a z with
  | zero =>
      have ha : a = initial n := (congrArg Prod.fst (Sum.inr.inj ht)).symm
      simp only [ha, initial, Metadata.work, Metadata.samples, Finset.range_zero, Finset.sum_empty, and_self]
  | succ t ih =>
      obtain ⟨b, w, hp, hstep⟩ := stage_pending_previous c x t a z ht
      obtain ⟨_, _, hadv, _⟩ := stageStep_pending_result c x b a w z hstep
      obtain ⟨hw, hs⟩ := ih b w hp
      rw [hadv]
      change b.work + (b.call c).work = _ ∧ b.samples + (b.call c).samples = _
      rw [hw, hs, Finset.sum_range_succ, Finset.sum_range_succ, metadataAt_of_pending c x t b w hp]
      exact ⟨rfl, rfl⟩

theorem pending_range_subset (c : Config) (x : Values n) (T t : ℕ) (htT : t < T)
    (a : Metadata n) (z : ℝ) (ht : stage c x t = .inr (a, z)) :
    Finset.range (t + 1) ⊆ pendingCalls c x T := by
  intro s hs
  have hst := Finset.mem_range.mp hs
  exact (mem_pendingCalls c x T s).mpr ⟨by omega, pending_before c x s t (by omega) a z ht⟩

theorem pending_work_with_next (c : Config) (x : Values n) (t : ℕ)
    (a : Metadata n) (z : ℝ) (ht : stage c x t = .inr (a, z)) :
    ((a.work + (a.call c).work : ℕ) : ℝ) = ∑ s ∈ Finset.range (t + 1), pendingWork c x s := by
  rw [Nat.cast_add, (pending_counters_eq c x t a z ht).1, Nat.cast_sum, Finset.sum_range_succ]
  have hw (s : ℕ) : (((metadataAt c x s).call c).work : ℝ) = pendingWork c x s := by
    simp only [Metadata.call, Reservation.Call.work, pendingWork, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  simp_rw [hw]
  rw [pendingWork, metadataAt_of_pending c x t a z ht]
  simp only [Metadata.call, Reservation.Call.work, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem pending_samples_with_next (c : Config) (x : Values n) (t : ℕ)
    (a : Metadata n) (z : ℝ) (ht : stage c x t = .inr (a, z)) :
    ((a.samples + (a.call c).samples : ℕ) : ℝ) =
      ∑ s ∈ Finset.range (t + 1), (((metadataAt c x s).call c).samples : ℝ) := by
  rw [Nat.cast_add, (pending_counters_eq c x t a z ht).2, Nat.cast_sum,
    Finset.sum_range_succ, metadataAt_of_pending c x t a z ht]

/-- Both exact reservation checks pass on every favorable pending prefix once
the guessed complexity reaches the fixed sufficient threshold. -/
theorem favorable_pending_allowed (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T) (hδ : ValidConfidence c.confidence)
    (hH : I.hardness ≤ (2 : ℝ) ^ c.attempt)
    (hfit : UniversalCapAnalysis.complexityTarget I c.confidence ≤
      (2 : ℝ) ^ c.attempt * confidenceCost c.confidence)
    (hC : c.sampleConstant = sampleCapConstant)
    (t : ℕ) (htT : t < T) (a : Metadata n) (z : ℝ) (ht : stage c x t = .inr (a, z)) :
    a.Allowed c := by
  have hsub := pending_range_subset c x T t htT a z ht
  have hwork : ((a.work + (a.call c).work : ℕ) : ℝ) ≤ 16 * I.workEnvelope := by
    rw [pending_work_with_next c x t a z ht]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun s hs _ => (pendingWork_pos I.two_le c x T s hs).le)).trans
        (favorable_sum_work_le I c x T hgood)
  have hsamples : ((a.samples + (a.call c).samples : ℕ) : ℝ) ≤
      40000000000 * UniversalCapAnalysis.favorableCost I c.confidence c.attempt := by
    rw [pending_samples_with_next c x t a z ht]
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)).trans
      (favorable_sum_samples_le I c x T hgood hδ hH)
  refine ⟨pending_active_two I.two_le c x t a z ht, ?_, ?_⟩
  · have hW := I.hardness_le_workEnvelope_lt.2
    have hh : ((a.work + (a.call c).work : ℕ) : ℝ) ≤ (c.workCap : ℝ) := by
      simp only [Config.workCap, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      linarith [I.hardness_pos]
    exact_mod_cast hh
  · have hh := favorable_bound_fits_cap I hδ c.attempt hfit hsamples
    change a.samples + (a.call c).samples ≤ ⌈c.sampleConstant * (2 : ℝ) ^ c.attempt * confidenceCost c.confidence⌉₊
    rw [hC]
    exact_mod_cast hh

theorem singletonAnswer_eq_of_mem {R : Finset (Fin n)} {i : Fin n}
    (hcard : R.card = 1) (hi : i ∈ R) : singletonAnswer R = some i := by
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hcard
  have he : i = j := by simpa only [hj, Finset.mem_singleton] using hi
  rw [he, hj]
  simp only [singletonAnswer, Finset.card_singleton, ↓reduceDIte, Finset.min'_singleton]

/-- A favorable terminal state carries the actual unique best label. -/
theorem favorable_terminal_best (I : Instance n) (c : Config) (x : Values n) (T : ℕ)
    (hgood : FavorableThrough I c x T)
    (hallowed : ∀ t < T, ∀ a z, stage c x t = .inr (a, z) → a.Allowed c)
    (t : ℕ) (htT : t ≤ T) (st : State n) (ans : Option (Fin n))
    (ht : stage c x t = .inl (st, ans)) : ans = some I.best := by
  induction t generalizing st ans with
  | zero => cases ht
  | succ t ih =>
      cases hp : stage c x t with
      | inl result =>
          have he : result = (st, ans) := Sum.inl.inj (by simpa only [stage, hp, stageStep] using ht)
          obtain ⟨st', ans'⟩ := result
          cases he
          exact ih (by omega) st ans hp
      | inr state =>
          obtain ⟨a, z⟩ := state
          have ha := hallowed t (by omega) a z hp
          have hg := hgood t (by omega) a z hp ha
          have he : stageStep c x (.inr (a, z)) = .inl (st, ans) := by
            simpa only [stage, hp] using ht
          rw [stageStep, dif_pos ha] at he
          change (if (callResult c x a ha z).2.card = 1 then
            Sum.inl ((a.advance c (callResult c x a ha z).2, (callResult c x a ha z).1),
              singletonAnswer (callResult c x a ha z).2)
            else Sum.inr (a.advance c (callResult c x a ha z).2,
              retainedReference a (callResult c x a ha z).1 (callResult c x a ha z).2)) = Sum.inl (st, ans) at he
          by_cases hr : (callResult c x a ha z).2.card = 1
          · rw [if_pos hr] at he
            have hans := congrArg Prod.snd (Sum.inl.inj he)
            dsimp only at hans
            rw [← hans]
            exact singletonAnswer_eq_of_mem hr hg.1
          · rw [if_neg hr] at he
            cases he

/-- The actual bounded procedure succeeds on every favorable tape, with no
termination or cap-passing premise left to an abstract execution model. -/
theorem favorable_actualOutput_eq_best (I : Instance n) (c : Config) (ω : SampleSpace n)
    (hgood : FavorableThrough I c ω.2 c.fuel) (hδ : ValidConfidence c.confidence)
    (hH : I.hardness ≤ (2 : ℝ) ^ c.attempt)
    (hfit : UniversalCapAnalysis.complexityTarget I c.confidence ≤
      (2 : ℝ) ^ c.attempt * confidenceCost c.confidence)
    (hC : c.sampleConstant = sampleCapConstant) :
    (procedure c I.two_le).actualOutput ω = some I.best := by
  obtain ⟨st, hs⟩ := actualOutput_eq_stage c I.two_le ω
  exact favorable_terminal_best I c ω.2 c.fuel hgood
    (favorable_pending_allowed I c ω.2 c.fuel hgood hδ hH hfit hC)
    c.fuel le_rfl st _ hs

end GapEntropy.UniversalAttempt
