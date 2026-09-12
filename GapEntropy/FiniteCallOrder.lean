import GapEntropy.FiniteCallProgram

/-!
# Ordered call keys in finite call programs

`Ordered rank lo hi p` states that the call keys of the program `p` have strictly increasing
ranks along every branch, all lying in `[lo, hi)`. Ordering is monotone in the bounds and is
preserved by `bind`. On an ordered program, the cost and the evaluation depend only on the
oracle's values at keys of rank at least `lo`.

The finite branch maximum `capacity` is attained by one ordinary nonanticipating addressed
oracle, because strictly increasing keys keep its assignments consistent. Similarly, every
completed history parse follows one consistent addressed-oracle path, with both the terminal
result and the consumed sample count preserved.
-/

noncomputable section
open scoped Classical

namespace GapEntropy.FiniteCallProgram
open TargetAttempt
variable {n : ℕ} {α β : Type*}

/-- Call ranks strictly increase on every branch and remain in the stated interval. -/
def Ordered (rank : CallKey → ℕ) (lo hi : ℕ) : Program n α → Prop
  | .pure _ => True
  | .call key _ _ _ _ next =>
      lo ≤ rank key ∧ rank key < hi ∧ ∀ R, Ordered rank (rank key + 1) hi (next R)

theorem ordered_mono {rank : CallKey → ℕ} {lo hi lo' hi' : ℕ} {p : Program n α}
    (hp : Ordered rank lo hi p) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') :
    Ordered rank lo' hi' p := by
  induction p generalizing lo lo' with
  | pure _ => trivial
  | call key S hS d δ next ih =>
    exact ⟨hlo.trans hp.1, hp.2.1.trans_le hhi,
      fun R => ih R (hp.2.2 R) le_rfl⟩

theorem ordered_bind {rank : CallKey → ℕ} {lo mid hi : ℕ} {p : Program n α}
    {f : α → Program n β} (hlo : lo ≤ mid) (hhi : mid ≤ hi)
    (hp : Ordered rank lo mid p) (hf : ∀ a, Ordered rank mid hi (f a)) :
    Ordered rank lo hi (bind p f) := by
  induction p generalizing lo with
  | pure a => exact ordered_mono (hf a) hlo le_rfl
  | call key S hS d δ next ih =>
    exact ⟨hp.1, hp.2.1.trans_le hhi,
      fun R => ih R (Nat.succ_le_of_lt hp.2.1) (hp.2.2 R)⟩

theorem cost_congr_above {rank : CallKey → ℕ} {lo hi : ℕ} {p : Program n α}
    (hp : Ordered rank lo hi p) {f g : Oracle n}
    (hfg : ∀ key, lo ≤ rank key → ∀ S, f key S = g key S) : cost f p = cost g p := by
  induction p generalizing lo with
  | pure _ => rfl
  | call key S hS d δ next ih =>
    simp only [cost, hfg key hp.1 S]
    congr 1
    exact ih _ (hp.2.2 _) (fun key' hkey' S' =>
      hfg key' (hp.1.trans ((Nat.le_succ _).trans hkey')) S')

theorem eval_congr_above {rank : CallKey → ℕ} {lo hi : ℕ} {p : Program n α}
    (hp : Ordered rank lo hi p) {f g : Oracle n}
    (hfg : ∀ key, lo ≤ rank key → ∀ S, f key S = g key S) : eval f p = eval g p := by
  induction p generalizing lo with
  | pure _ => rfl
  | call key S hS d δ next ih =>
    simp only [eval, hfg key hp.1 S]
    exact ih _ (hp.2.2 _) (fun key' hkey' S' =>
      hfg key' (hp.1.trans ((Nat.le_succ _).trans hkey')) S')

/-- The finite branch maximum is attained by one ordinary, nonanticipating
addressed oracle. Strictly increasing keys make its assignments consistent. -/
theorem capacity_attained {rank : CallKey → ℕ} {lo hi : ℕ} {p : Program n α}
    (hp : Ordered rank lo hi p) : ∃ f : Oracle n, cost f p = capacity p := by
  induction p generalizing lo with
  | pure _ => exact ⟨fun _ _ => ∅, rfl⟩
  | call key S hS d δ next ih =>
    obtain ⟨R, _, hR⟩ := Finset.exists_mem_eq_sup Finset.univ
      (Finset.univ_nonempty : (Finset.univ : Finset (Finset (Fin n))).Nonempty)
      (fun R => capacity (next R))
    obtain ⟨f, hf⟩ := ih R (hp.2.2 R)
    let g : Oracle n := fun key' S' => if key' = key then R else f key' S'
    have hgf : cost g (next R) = cost f (next R) :=
      cost_congr_above (hp.2.2 R) (fun key' hkey' S' => by
        have hne : key' ≠ key := by intro he; subst key'; omega
        simp only [g, if_neg hne])
    refine ⟨g, ?_⟩
    simp only [cost, g, if_pos rfl, capacity]
    change EliminationPolicy.budget S.card d δ + cost g (next R) = _
    rw [hgf, hf, hR]

/-- Any completed history parser follows one consistent addressed-oracle path,
with both its terminal result and its complete consumed cost preserved. -/
theorem parse_terminal_eq_oracle {rank : CallKey → ℕ} {lo hi : ℕ} {p : Program n α}
    (hp : Ordered rank lo hi p) {t s : ℕ} {a : α} (h : History n t)
    (hparse : parse p h = .inr (s, a)) :
    ∃ f : Oracle n, eval f p = a ∧ cost f p = s := by
  induction p generalizing lo t s with
  | pure b =>
    have he : (0 : ℕ) = s ∧ b = a := by
      simpa only [parse, Sum.inr.injEq, Prod.mk.injEq] using hparse
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨fun _ _ => ∅, rfl, rfl⟩
  | call key S hS d δ next ih =>
    let m := EliminationPolicy.budget S.card d δ
    change (if hm : m ≤ t then addCost m (parse
      (next (EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h)))
      (historySuffix m hm h)) else _) = _ at hparse
    by_cases hm : m ≤ t
    · rw [dif_pos hm] at hparse
      let R := EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h)
      change addCost m (parse (next R) (historySuffix m hm h)) = .inr (s, a) at hparse
      cases he : parse (next R) (historySuffix m hm h) with
      | inl i => simp only [he, addCost] at hparse; cases hparse
      | inr out =>
        obtain ⟨s', b⟩ := out
        have heq : m + s' = s ∧ b = a := by
          simpa only [he, addCost, Sum.inr.injEq, Prod.mk.injEq] using hparse
        obtain ⟨hs, hb⟩ := heq
        subst b
        obtain ⟨f, hf, hc⟩ := ih R (hp.2.2 R) (historySuffix m hm h) he
        let g : Oracle n := fun key' S' => if key' = key then R else f key' S'
        have hgf : ∀ key', rank key + 1 ≤ rank key' → ∀ S', g key' S' = f key' S' := by
          intro key' hkey' S'
          have hne : key' ≠ key := by intro he'; subst key'; omega
          simp only [g, if_neg hne]
        have hge := eval_congr_above (hp.2.2 R) hgf
        have hgc := cost_congr_above (hp.2.2 R) hgf
        refine ⟨g, ?_, ?_⟩
        · change eval g (next (g key S)) = a
          have hcur : g key S = R := by simp only [g, if_pos rfl]
          rw [hcur, hge, hf]
        · change m + cost g (next (g key S)) = s
          have hcur : g key S = R := by simp only [g, if_pos rfl]
          rw [hcur, hgc, hc, hs]
    · rw [dif_neg hm] at hparse
      cases hparse

end GapEntropy.FiniteCallProgram
