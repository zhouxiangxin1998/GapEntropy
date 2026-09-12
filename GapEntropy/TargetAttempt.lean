import GapEntropy.TargetProfile
import GapEntropy.AttemptScale
import GapEntropy.EliminationA3

/-!
# C.1 finite target-profile attempt control

The raw oracle is called at precisely the specified scale/round and input set.
`loopTolerance` and `loopConfidence` are its declared A.3 parameters. The final
oracle uses `d_K` and `ε/2`. This file proves deterministic control facts; replacing
the oracle by fresh canonical A.3 calls and an interactive `Policy` embedding are
separate proof obligations.
-/

noncomputable section
open scoped BigOperators

namespace GapEntropy.TargetAttempt
variable {n : ℕ}
abbrev Oracle (n : ℕ) := ℕ → GapEntropy.AttemptScale.Oracle n

def finishScale (I : Instance n) (oracle : Oracle n) (k : ℕ) :
    Option (Finset (Fin n)) → Option (Finset (Fin n))
  | none => none
  | some S => GapEntropy.AttemptScale.run (I.targetCount k) (oracle k) S n

def entry (I : Instance n) (oracle : Oracle n) : ℕ → Option (Finset (Fin n))
  | 0 => some Finset.univ
  | k + 1 => finishScale I oracle k (entry I oracle k)

def loopRequest (I : Instance n) (oracle : Oracle n) (k r : ℕ) : Option (Finset (Fin n)) :=
  match entry I oracle k with
  | none => none
  | some S => GapEntropy.AttemptScale.request (I.targetCount k) (oracle k) S r

def finalRequest (I : Instance n) (oracle : Oracle n) : Option (Finset (Fin n)) :=
  match entry I oracle (I.lastBucket + 1) with
  | none => none
  | some S => if S.card = 1 then none else some S

def singletonReturn (S : Finset (Fin n)) : Option (Fin n) :=
  if h : S.card = 1 then some (S.min' (Finset.card_pos.mp (by omega))) else none

def result (I : Instance n) (oracle : Oracle n) (finalOracle : Finset (Fin n) → Finset (Fin n)) :
    Option (Fin n) :=
  match entry I oracle (I.lastBucket + 1) with
  | none => none
  | some S => if S.card = 1 then singletonReturn S else singletonReturn (finalOracle S)

def loopCost (I : Instance n) (ε : ℝ) (oracle : Oracle n) (k r : ℕ) : ℕ :=
  match loopRequest I oracle k r with
  | none => 0
  | some S => GapEntropy.EliminationTape.declaredCost S.card (I.targetTolerance k) (I.callConfidence ε k r)

def finalCost (I : Instance n) (ε : ℝ) (oracle : Oracle n) : ℕ :=
  match finalRequest I oracle with
  | none => 0
  | some S => GapEntropy.EliminationTape.declaredCost S.card (I.targetTolerance I.lastBucket) (ε / 2)

def totalCost (I : Instance n) (ε : ℝ) (oracle : Oracle n) : ℕ :=
  (∑ k ∈ Finset.range (I.lastBucket + 1), ∑ r ∈ Finset.range n, loopCost I ε oracle k r) +
    finalCost I ε oracle

def confidenceSpent (I : Instance n) (ε : ℝ) (oracle : Oracle n) : ℝ :=
  (∑ k ∈ Finset.range (I.lastBucket + 1), ∑ r ∈ Finset.range n,
    if (loopRequest I oracle k r).isSome then I.callConfidence ε k r else 0) +
  if (finalRequest I oracle).isSome then ε / 2 else 0

theorem finishScale_some {I : Instance n} {oracle : Oracle n} {k : ℕ}
    {start : Option (Finset (Fin n))} {T : Finset (Fin n)}
    (h : finishScale I oracle k start = some T) :
    ∃ S, start = some S ∧ GapEntropy.AttemptScale.run (I.targetCount k) (oracle k) S n = some T := by
  cases start with
  | none => cases h
  | some S => exact ⟨S, rfl, h⟩

theorem entry_nonempty {I : Instance n} {oracle : Oracle n} {k : ℕ} {T : Finset (Fin n)}
    (h : entry I oracle k = some T) : T.Nonempty := by
  induction k generalizing T with
  | zero =>
    have he := Option.some.inj h
    subst T
    have hn := I.two_le
    exact ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  | succ k ih =>
    obtain ⟨S, hS, hrun⟩ := finishScale_some h
    exact GapEntropy.AttemptScale.run_nonempty (ih hS) hrun

theorem entry_bound_succ {I : Instance n} {oracle : Oracle n} {k : ℕ} {T : Finset (Fin n)}
    (h : entry I oracle (k + 1) = some T) : T.card ≤ 4 * I.targetCount k := by
  obtain ⟨S, _, hrun⟩ := finishScale_some h
  apply GapEntropy.AttemptScale.run_finished (I.targetCount_pos k) (S := S) _ hrun
  simpa using Finset.card_le_univ S

theorem final_entry_card {I : Instance n} {oracle : Oracle n} {T : Finset (Fin n)}
    (h : entry I oracle (I.lastBucket + 1) = some T) : T.card ≤ 4 := by
  simpa only [I.targetCount_last, mul_one] using entry_bound_succ h

theorem finalRequest_some {I : Instance n} {oracle : Oracle n} {T : Finset (Fin n)}
    (h : finalRequest I oracle = some T) : T.Nonempty ∧ 2 ≤ T.card ∧ T.card ≤ 4 := by
  unfold finalRequest at h
  cases he : entry I oracle (I.lastBucket + 1) with
  | none => simp [he] at h
  | some S =>
    simp only [he] at h
    split_ifs at h with hcard
    have heq := Option.some.inj h
    subst T
    have hnon := entry_nonempty he
    exact ⟨hnon, by have := hnon.card_pos; omega, final_entry_card he⟩

theorem loopRequest_some {I : Instance n} {oracle : Oracle n} {k r : ℕ} {T : Finset (Fin n)}
    (h : loopRequest I oracle k r = some T) :
    ∃ S, entry I oracle k = some S ∧
      GapEntropy.AttemptScale.request (I.targetCount k) (oracle k) S r = some T := by
  unfold loopRequest at h
  cases he : entry I oracle k with
  | none => simp [he] at h
  | some S => exact ⟨S, rfl, by simpa only [he] using h⟩

theorem loopRequest_nonempty {I : Instance n} {oracle : Oracle n} {k r : ℕ} {T : Finset (Fin n)}
    (h : loopRequest I oracle k r = some T) : T.Nonempty := by
  obtain ⟨S, hS, hreq⟩ := loopRequest_some h
  exact GapEntropy.AttemptScale.run_nonempty (entry_nonempty hS)
    (GapEntropy.AttemptScale.request_some_iff.mp hreq).1

theorem entry_work_bound {I : Instance n} {oracle : Oracle n} {k : ℕ} {S : Finset (Fin n)}
    (h : entry I oracle k = some S) :
    (S.card : ℝ) * (4 : ℝ) ^ k ≤ 4 * I.scaleWork k := by
  cases k with
  | zero =>
    have he := Option.some.inj h
    subst S
    simp only [Finset.card_univ, Fintype.card_fin, pow_zero, mul_one, I.scaleWork_zero]
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  | succ k =>
    have hb : (S.card : ℝ) ≤ 4 * (I.targetCount k : ℝ) := by exact_mod_cast entry_bound_succ h
    have hp := mul_le_mul_of_nonneg_right hb (show (0 : ℝ) ≤ 4 ^ (k + 1) by positivity)
    rw [I.scaleWork_succ]
    nlinarith

/-- C.2's geometric work bound applies to every requested call, even an aborting call. -/
theorem loopRequest_work_bound {I : Instance n} {oracle : Oracle n} {k r : ℕ}
    {T : Finset (Fin n)} (h : loopRequest I oracle k r = some T) :
    (T.card : ℝ) * (I.targetTolerance k ^ 2)⁻¹ ≤ 4 * I.scaleWork k * (3 / 4 : ℝ) ^ r := by
  obtain ⟨S, hS, hreq⟩ := loopRequest_some h
  have hg := GapEntropy.AttemptScale.request_geometric (I.targetCount_pos k) hreq
  have hgm := mul_le_mul_of_nonneg_right hg (show (0 : ℝ) ≤ 4 ^ k by positivity)
  have hw := mul_le_mul_of_nonneg_right (entry_work_bound hS) (show (0 : ℝ) ≤ (3 / 4) ^ r by positivity)
  rw [I.targetTolerance_inv_square]
  nlinarith

/-- Confidence spent by the actual finite call path, including its optional final call. -/
theorem confidenceSpent_le (I : Instance n) {ε : ℝ} (hε : 0 ≤ ε) (oracle : Oracle n) :
    confidenceSpent I ε oracle ≤ ε := by
  have hnon (k r : ℕ) : 0 ≤ I.callConfidence ε k r := by
    unfold Instance.callConfidence Instance.scaleConfidence
    exact mul_nonneg (mul_nonneg (by positivity) (I.workMass_pos k).le) (by positivity)
  have hlo : (∑ k ∈ Finset.range (I.lastBucket + 1), ∑ r ∈ Finset.range n,
      if (loopRequest I oracle k r).isSome then I.callConfidence ε k r else 0) ≤
      ∑ k ∈ Finset.range (I.lastBucket + 1), ∑ r ∈ Finset.range n, I.callConfidence ε k r := by
    apply Finset.sum_le_sum
    intro k _
    apply Finset.sum_le_sum
    intro r _
    split_ifs <;> simp_all
  have hfinal : (if (finalRequest I oracle).isSome then ε / 2 else 0) ≤ ε / 2 := by
    split_ifs
    · exact le_rfl
    · positivity
  exact (add_le_add hlo hfinal).trans (I.all_callConfidence_le hε n)

/-- The fixed `n` slots at a scale omit no possible later while-loop call. -/
theorem loopRequest_none_after_n (I : Instance n) (oracle : Oracle n) (k r : ℕ) (hr : n ≤ r) :
    loopRequest I oracle k r = none := by
  unfold loopRequest
  cases he : entry I oracle k with
  | none => rfl
  | some S =>
    apply GapEntropy.AttemptScale.request_none_of_card_le (I.targetCount_pos k)
    have hs : S.card ≤ n := by simpa using Finset.card_le_univ S
    omega

def callCount (I : Instance n) (oracle : Oracle n) : ℕ :=
  (∑ k ∈ Finset.range (I.lastBucket + 1), ∑ r ∈ Finset.range n,
    if (loopRequest I oracle k r).isSome then 1 else 0) +
  if (finalRequest I oracle).isSome then 1 else 0

/-- A universal finite call cap for the implemented control flow. -/
theorem callCount_le (I : Instance n) (oracle : Oracle n) :
    callCount I oracle ≤ (I.lastBucket + 1) * n + 1 := by
  have hinner (k : ℕ) : (∑ r ∈ Finset.range n,
      if (loopRequest I oracle k r).isSome then 1 else 0) ≤ n := by
    calc
      _ ≤ ∑ _r ∈ Finset.range n, 1 := Finset.sum_le_sum (fun r _ => by split_ifs <;> omega)
      _ = n := by simp
  have houter : (∑ k ∈ Finset.range (I.lastBucket + 1), ∑ r ∈ Finset.range n,
      if (loopRequest I oracle k r).isSome then 1 else 0) ≤ (I.lastBucket + 1) * n := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (I.lastBucket + 1), n := Finset.sum_le_sum (fun k _ => hinner k)
      _ = _ := by simp
  unfold callCount
  split_ifs <;> omega

end GapEntropy.TargetAttempt
