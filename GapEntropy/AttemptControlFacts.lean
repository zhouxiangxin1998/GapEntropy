import GapEntropy.AttemptInterface

/-!
# Deterministic control facts for the finite target attempt

This module proves oracle-congruence and best-arm-preservation facts for the C.1 attempt control
flow of `AttemptScale` and `TargetAttempt`. The functions `step`, `run`, `request`, `entry`,
`loopRequest`, and `finalRequest` depend only on the oracle responses at strictly earlier keys,
so oracles agreeing on those keys produce the same requests.

If every good raw call keeps the best arm and returns at most the rounded half of its input,
then no scale aborts and the best arm survives every scale. Consequently `result` returns the
best arm whenever every visited call is good, and any label it returns equals the best arm as
soon as the best is merely protected by every visited call.
-/

noncomputable section
namespace GapEntropy.AttemptScale
variable {n : ℕ}

theorem step_congr {N r : ℕ} {f g : Oracle n} (h : ∀ S, f r S = g r S)
    (state : Option (Finset (Fin n))) : step N f r state = step N g r state := by
  cases state with
  | none => rfl
  | some S => simp only [step, h S]

theorem run_congr {N R : ℕ} {f g : Oracle n} (S : Finset (Fin n))
    (h : ∀ r < R, ∀ T, f r T = g r T) : run N f S R = run N g S R := by
  induction R with
  | zero => rfl
  | succ R ih =>
    rw [run, run, ih (fun r hr => h r (Nat.lt_succ_of_lt hr))]
    exact step_congr (h R (Nat.lt_succ_self R)) _

theorem request_congr {N r : ℕ} {f g : Oracle n} (S : Finset (Fin n))
    (h : ∀ j < r, ∀ T, f j T = g j T) : request N f S r = request N g S r := by
  unfold request
  rw [run_congr S h]

theorem run_preserves_best {N R : ℕ} {f : Oracle n} {S : Finset (Fin n)} {best : Fin n}
    (hbest : best ∈ S)
    (hsafe : ∀ r < R, ∀ T, request N f S r = some T → best ∈ T → best ∈ f r T)
    {T : Finset (Fin n)} (h : run N f S R = some T) : best ∈ T := by
  induction R generalizing T with
  | zero => have he := Option.some.inj h; subst T; exact hbest
  | succ R ih =>
    obtain ⟨U, hU, hstep⟩ := run_succ_some_previous h
    have hb := ih (fun r hr => hsafe r (Nat.lt_succ_of_lt hr)) hU
    rcases step_some_cases hstep with ⟨_, rfl⟩ | ⟨hbig, rfl, _, _⟩
    · exact hb
    · exact hsafe R (Nat.lt_succ_self R) U (request_some_iff.mpr ⟨hU, hbig⟩) hb

/-- Good raw calls prevent abort and preserve the best, with the exact size test. -/
theorem run_survives {N R : ℕ} {f : Oracle n} {S : Finset (Fin n)} {best : Fin n}
    (hbest : best ∈ S)
    (hsafe : ∀ r < R, ∀ T, request N f S r = some T → best ∈ T →
      best ∈ f r T ∧ (f r T).card ≤ (T.card + 1) / 2) :
    ∃ T, run N f S R = some T ∧ best ∈ T := by
  induction R with
  | zero => exact ⟨S, rfl, hbest⟩
  | succ R ih =>
    obtain ⟨T, hT, hb⟩ := ih (fun r hr => hsafe r (Nat.lt_succ_of_lt hr))
    by_cases hbig : 4 * N < T.card
    · have hg := hsafe R (Nat.lt_succ_self R) T (request_some_iff.mpr ⟨hT, hbig⟩) hb
      refine ⟨f R T, ?_, hg.1⟩
      rw [run, hT]
      simp [step, hbig, show (f R T).Nonempty from ⟨best, hg.1⟩, hg.2]
    · refine ⟨T, ?_, hb⟩
      rw [run, hT]
      simp [step, hbig]

end GapEntropy.AttemptScale

namespace GapEntropy.TargetAttempt
variable {n : ℕ}

theorem entry_congr {I : Instance n} {f g : Oracle n} {K : ℕ}
    (h : ∀ k < K, ∀ r < n, ∀ S, f k r S = g k r S) : entry I f K = entry I g K := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [entry, entry, ih (fun k hk => h k (Nat.lt_succ_of_lt hk))]
    cases entry I g K with
    | none => rfl
    | some S => exact GapEntropy.AttemptScale.run_congr S (h K (Nat.lt_succ_self K))

theorem loopRequest_congr {I : Instance n} {f g : Oracle n} {k r : ℕ}
    (hpast : ∀ j < k, ∀ u < n, ∀ S, f j u S = g j u S)
    (hcurrent : ∀ u < r, ∀ S, f k u S = g k u S) :
    loopRequest I f k r = loopRequest I g k r := by
  unfold loopRequest
  rw [entry_congr hpast]
  cases entry I g k with
  | none => rfl
  | some S => exact GapEntropy.AttemptScale.request_congr S hcurrent

theorem finalRequest_congr {I : Instance n} {f g : Oracle n}
    (h : ∀ k < I.lastBucket + 1, ∀ r < n, ∀ S, f k r S = g k r S) :
    finalRequest I f = finalRequest I g := by
  unfold finalRequest
  rw [entry_congr h]

theorem entry_preserves_best {I : Instance n} {f : Oracle n} {K : ℕ} {best : Fin n}
    (hsafe : ∀ k < K, ∀ r < n, ∀ S, loopRequest I f k r = some S → best ∈ S → best ∈ f k r S)
    {T : Finset (Fin n)} (h : entry I f K = some T) : best ∈ T := by
  induction K generalizing T with
  | zero => have he := Option.some.inj h; subst T; exact Finset.mem_univ _
  | succ K ih =>
    obtain ⟨S, hS, hrun⟩ := finishScale_some h
    have hb := ih (fun k hk => hsafe k (Nat.lt_succ_of_lt hk)) hS
    apply GapEntropy.AttemptScale.run_preserves_best hb _ hrun
    intro r hr U hreq hU
    apply hsafe K (Nat.lt_succ_self K) r hr U _ hU
    simpa only [loopRequest, hS] using hreq

theorem entry_survives {I : Instance n} {f : Oracle n} {K : ℕ} {best : Fin n}
    (hsafe : ∀ k < K, ∀ r < n, ∀ S, loopRequest I f k r = some S → best ∈ S →
      best ∈ f k r S ∧ (f k r S).card ≤ (S.card + 1) / 2) :
    ∃ T, entry I f K = some T ∧ best ∈ T := by
  induction K with
  | zero => exact ⟨Finset.univ, rfl, Finset.mem_univ _⟩
  | succ K ih =>
    obtain ⟨S, hS, hb⟩ := ih (fun k hk => hsafe k (Nat.lt_succ_of_lt hk))
    obtain ⟨T, hT, hbest⟩ := GapEntropy.AttemptScale.run_survives hb
      (R := n) (N := I.targetCount K) (f := f K) (fun r hr U hreq hU =>
        hsafe K (Nat.lt_succ_self K) r hr U (by simpa only [loopRequest, hS] using hreq) hU)
    exact ⟨T, by simpa only [entry, hS, finishScale] using hT, hbest⟩

theorem singletonReturn_eq_of_mem {S : Finset (Fin n)} {best : Fin n}
    (hbest : best ∈ S) (hcard : S.card = 1) : singletonReturn S = some best := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
  have hb : best = a := by simpa only [ha, Finset.mem_singleton] using hbest
  subst S
  subst best
  simp [singletonReturn]

theorem singletonReturn_correct {S : Finset (Fin n)} {best a : Fin n}
    (hbest : best ∈ S) (h : singletonReturn S = some a) : a = best := by
  by_cases hc : S.card = 1
  · rw [singletonReturn_eq_of_mem hbest hc] at h
    exact (Option.some.inj h).symm
  · simp [singletonReturn, hc] at h

theorem result_correct_of_protection {I : Instance n} {f : Oracle n}
    {last : Finset (Fin n) → Finset (Fin n)} {best a : Fin n}
    (hloop : ∀ k < I.lastBucket + 1, ∀ r < n, ∀ S,
      loopRequest I f k r = some S → best ∈ S → best ∈ f k r S)
    (hfinal : ∀ S, finalRequest I f = some S → best ∈ S → best ∈ last S)
    (hret : result I f last = some a) : a = best := by
  unfold result at hret
  cases he : entry I f (I.lastBucket + 1) with
  | none => simp [he] at hret
  | some S =>
    have hb := entry_preserves_best hloop he
    simp only [he] at hret
    split_ifs at hret with hc
    · exact singletonReturn_correct hb hret
    · exact singletonReturn_correct (hfinal S (by simp [finalRequest, he, hc]) hb) hret

theorem result_success_of_good_calls {I : Instance n} {f : Oracle n}
    {last : Finset (Fin n) → Finset (Fin n)} {best : Fin n}
    (hloop : ∀ k < I.lastBucket + 1, ∀ r < n, ∀ S,
      loopRequest I f k r = some S → best ∈ S →
        best ∈ f k r S ∧ (f k r S).card ≤ (S.card + 1) / 2)
    (hfinal : ∀ S, finalRequest I f = some S → best ∈ S → last S = {best}) :
    result I f last = some best := by
  obtain ⟨S, he, hb⟩ := entry_survives hloop
  unfold result
  rw [he]
  dsimp only
  by_cases hc : S.card = 1
  · rw [if_pos hc]
    exact singletonReturn_eq_of_mem hb hc
  · rw [if_neg hc, hfinal S (by simp [finalRequest, he, hc]) hb]
    exact singletonReturn_eq_of_mem (Finset.mem_singleton_self best) (by simp)

end GapEntropy.TargetAttempt
