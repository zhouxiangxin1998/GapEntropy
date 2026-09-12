import GapEntropy.BoundedProcedure
import GapEntropy.HistoryConsistency

/-!
# Prefix and matching-request simulation for bounded procedures

These deterministic lemmas support interpreters that concatenate local calls.
Different procedures may have different budgets and output types. Only requests
and reward rows used in the compared prefix need agree.
-/

namespace GapEntropy.BoundedProcedure

variable {n : ℕ} {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem simulate_congr_of_requests (R : BoundedProcedure n α) (Q : BoundedProcedure n β)
    (x : R.Tape) (y : Q.Tape) (t : ℕ) (hR : t ≤ R.budget) (hQ : t ≤ Q.budget)
    (hrows : ∀ s (hs : s < t), x ⟨s, hs.trans_le hR⟩ = y ⟨s, hs.trans_le hQ⟩)
    (hreq : ∀ s (hs : s < t) (h : History n s),
      R.request s (hs.trans_le hR) h = Q.request s (hs.trans_le hQ) h) :
    R.simulate x t hR = Q.simulate y t hQ := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hp := ih (by omega) (by omega) (fun s hs => hrows s (by omega))
        (fun s hs => hreq s (by omega))
      simp only [simulate, hp, hreq t (Nat.lt_succ_self t), hrows t (Nat.lt_succ_self t)]

theorem simulate_congr_prefix (R : BoundedProcedure n α) (x y : R.Tape)
    (t : ℕ) (ht : t ≤ R.budget)
    (hrows : ∀ s (hs : s < t), x ⟨s, hs.trans_le ht⟩ = y ⟨s, hs.trans_le ht⟩) :
    R.simulate x t ht = R.simulate y t ht :=
  simulate_congr_of_requests R R x y t ht ht hrows (fun _ _ _ => rfl)

theorem simulate_prefix (R : BoundedProcedure n α) (x : R.Tape)
    (T : ℕ) (hT : T ≤ R.budget) (t : ℕ) (ht : t ≤ T) :
    Policy.historyPrefix (R.simulate x T hT) t ht = R.simulate x t (ht.trans hT) := by
  induction T generalizing t with
  | zero =>
      have he : t = 0 := by omega
      subst t
      rfl
  | succ T ih =>
      by_cases htT : t ≤ T
      · have hp := ih (by omega) t htT
        rw [← hp]
        funext i
        unfold Policy.historyPrefix
        simp only [simulate]
        have hei : (⟨i, lt_of_lt_of_le i.isLt ht⟩ : Fin (T + 1)) =
            (⟨i, lt_of_lt_of_le i.isLt htT⟩ : Fin T).castSucc := rfl
        rw [hei, Fin.snoc_castSucc]
      · have he : t = T + 1 := by omega
        subst t
        rfl

/-- An actual policy with matching requests has exactly the procedure's
simulated history up to the compared horizon; its completion marker may differ. -/
theorem run_eq_simulate_of_requests (R : BoundedProcedure n α) (A : Policy n)
    (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) (ht : t ≤ R.budget)
    (hreq : ∀ s (hs : s < t) (h : History n s),
      A.choose hn s (ω.1, h) = Sum.inl (R.request s (hs.trans_le ht) h)) :
    A.run hn ω t = Sum.inr (R.simulate (GaussianBlocks.rewardBlock 0 R.budget ω) t ht) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Policy.run_succ, Policy.step, ih (by omega) (fun s hs => hreq s (by omega))]
      simp only [Sum.elim_inr, hreq t (Nat.lt_succ_self t), Sum.elim_inl,
        simulate, GaussianBlocks.rewardBlock, Nat.zero_add]

theorem simulate_decision (R : BoundedProcedure n α) (x : R.Tape)
    (T : ℕ) (hT : T ≤ R.budget) (s : ℕ) (hs : s < T) :
    R.request s (hs.trans_le hT) (Policy.historyPrefix (R.simulate x T hT) s hs.le) =
      (R.simulate x T hT ⟨s, hs⟩).1 ∧
    (R.simulate x T hT ⟨s, hs⟩).2 =
      x ⟨s, hs.trans_le hT⟩ (R.simulate x T hT ⟨s, hs⟩).1 := by
  have hp := R.simulate_prefix x T hT (s + 1) (by omega)
  have he := congrFun hp (Fin.last s)
  simp only [Policy.historyPrefix, simulate, Fin.snoc_last] at he
  rw [R.simulate_prefix x T hT s hs.le]
  constructor
  · exact (congrArg Prod.fst he).symm
  · exact (congrArg Prod.snd he).trans (congrArg (x ⟨s, hs.trans_le hT⟩) (congrArg Prod.fst he).symm)

end GapEntropy.BoundedProcedure
