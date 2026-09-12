import GapEntropy.EliminationPolicy
import GapEntropy.AttemptMeasurability

/-!
# Finite sequential programs of actual elimination samplers

The interpreter sees only its observed history. It consumes a completed call's
exact budget, reads the raw set, and continues directly, bypassing the sampler's
terminal arm marker. A terminal result includes the exact consumed sample count.
The finite maximum cost supplies a deterministic padding boundary.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace GapEntropy.FiniteCallProgram
open TargetAttempt

inductive Program (n : ℕ) (α : Type*) where
  | pure (result : α)
  | call (key : CallKey) (active : Finset (Fin n)) (nonempty : active.Nonempty)
      (tolerance confidence : ℝ) (next : Finset (Fin n) → Program n α)

variable {n : ℕ} {α β : Type*}

def bind (p : Program n α) (f : α → Program n β) : Program n β :=
  match p with
  | .pure a => f a
  | .call key S hS d δ next => .call key S hS d δ (fun R => bind (next R) f)

abbrev Oracle (n : ℕ) := CallKey → Finset (Fin n) → Finset (Fin n)

def eval (f : Oracle n) : Program n α → α
  | .pure a => a
  | .call key S _ _ _ next => eval f (next (f key S))

def cost (f : Oracle n) : Program n α → ℕ
  | .pure _ => 0
  | .call key S _ d δ next => EliminationPolicy.budget S.card d δ + cost f (next (f key S))

def capacity : Program n α → ℕ
  | .pure _ => 0
  | .call _ S _ d δ next =>
      EliminationPolicy.budget S.card d δ + Finset.univ.sup (fun R => capacity (next R))

theorem eval_bind (f : Oracle n) (p : Program n α) (g : α → Program n β) :
    eval f (bind p g) = eval f (g (eval f p)) := by
  induction p with
  | pure a => rfl
  | call key S hS d δ next ih => exact ih (f key S)

theorem cost_bind (f : Oracle n) (p : Program n α) (g : α → Program n β) :
    cost f (bind p g) = cost f p + cost f (g (eval f p)) := by
  induction p with
  | pure a => simp [bind, cost, eval]
  | call key S hS d δ next ih => simp only [bind, cost, eval, ih, Nat.add_assoc]

theorem cost_le_capacity (f : Oracle n) (p : Program n α) : cost f p ≤ capacity p := by
  induction p with
  | pure a => exact le_rfl
  | call key S hS d δ next ih =>
    exact Nat.add_le_add_left ((ih _).trans (Finset.le_sup (f := fun R => capacity (next R))
      (Finset.mem_univ (f key S)))) _

def historyPrefix {t : ℕ} (m : ℕ) (hm : m ≤ t) (h : History n t) : History n m :=
  fun i => h ⟨i, lt_of_lt_of_le i.isLt hm⟩

def historySuffix {t : ℕ} (m : ℕ) (hm : m ≤ t) (h : History n t) : History n (t - m) :=
  fun i => h ⟨m + i, by have := i.isLt; omega⟩

theorem historyPrefix_measurable {t : ℕ} (m : ℕ) (hm : m ≤ t) :
    Measurable (historyPrefix (n := n) m hm) := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

theorem historySuffix_measurable {t : ℕ} (m : ℕ) (hm : m ≤ t) :
    Measurable (historySuffix (n := n) m hm) := measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

abbrev Parsed (n : ℕ) (α : Type*) := Fin n ⊕ (ℕ × α)

def addCost (m : ℕ) : Parsed n α → Parsed n α
  | .inl i => .inl i
  | .inr (s, a) => .inr (m + s, a)

theorem addCost_measurable [MeasurableSpace α] (m : ℕ) : Measurable (addCost (n := n) (α := α) m) := by
  exact measurable_inl.sumElim (measurable_inr.comp
    ((measurable_const.add measurable_fst).prodMk measurable_snd))

/-- Parse all completed subcalls in a finite observed history. If a call is
unfinished, return precisely its next requested arm. -/
def parse (p : Program n α) {t : ℕ} (h : History n t) : Parsed n α :=
  match p with
  | .pure a => .inr (0, a)
  | .call _ S hS d δ next =>
      let m := EliminationPolicy.budget S.card d δ
      if hm : m ≤ t then
        addCost m (parse (next (EliminationPolicy.rawOutputFromHistory S hS d δ
          (historyPrefix m hm h))) (historySuffix m hm h))
      else .inl (EliminationPolicy.requestedFromHistory S hS d δ t h)

theorem parse_measurable [MeasurableSpace α] (p : Program n α) (t : ℕ) :
    Measurable (parse p (t := t)) := by
  induction p generalizing t with
  | pure a => exact measurable_const
  | call key S hS d δ next ih =>
    let m := EliminationPolicy.budget S.card d δ
    change Measurable (fun h : History n t => if hm : m ≤ t then
      addCost m (parse (next (EliminationPolicy.rawOutputFromHistory S hS d δ
        (historyPrefix m hm h))) (historySuffix m hm h))
      else .inl (EliminationPolicy.requestedFromHistory S hS d δ t h))
    by_cases hm : m ≤ t
    · have hread : Measurable (fun h : History n t =>
          EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h)) :=
        (EliminationPolicy.measurable_rawOutputFromHistory S hS d δ).comp (historyPrefix_measurable m hm)
      have hnext : Measurable (fun h : History n t =>
          parse (next (EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h)))
            (historySuffix m hm h)) :=
        measurable_finite_choice
          (F := fun h R => parse (next R) (historySuffix m hm h))
          hread (fun R => (ih R (t - m)).comp (historySuffix_measurable m hm))
      simpa only [dif_pos hm, Function.comp_def] using (addCost_measurable m).comp hnext
    · simpa only [dif_neg hm, Function.comp_def] using
        measurable_inl.comp (EliminationPolicy.measurable_requestedFromHistory S hS d δ t)

/-- Every observed history at or beyond the finite maximum cost parses to a
completed result, even if the recorded observations are atypical. -/
theorem parse_complete (p : Program n α) {t : ℕ} (h : History n t) (ht : capacity p ≤ t) :
    ∃ s a, parse p h = .inr (s, a) ∧ s ≤ capacity p := by
  induction p generalizing t with
  | pure a => exact ⟨0, a, rfl, le_rfl⟩
  | call key S hS d δ next ih =>
    let m := EliminationPolicy.budget S.card d δ
    have hm : m ≤ t := (Nat.le_add_right m _).trans ht
    let R := EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h)
    have hR : capacity (next R) ≤ Finset.univ.sup (fun T => capacity (next T)) :=
      Finset.le_sup (f := fun T => capacity (next T)) (Finset.mem_univ R)
    have hRt : capacity (next R) ≤ t - m := by change m + _ ≤ t at ht; omega
    obtain ⟨s, a, hp, hs⟩ := ih R (historySuffix m hm h) hRt
    refine ⟨m + s, a, ?_, Nat.add_le_add_left (hs.trans hR) m⟩
    change (if hm : m ≤ t then addCost m (parse
      (next (EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h)))
      (historySuffix m hm h)) else _) = _
    rw [dif_pos hm]
    change addCost m (parse (next R) (historySuffix m hm h)) = _
    rw [hp]
    rfl

/-- Once completed, extending the history leaves both the result and the exact
consumed count unchanged. This justifies fixed-budget padding. -/
theorem parse_terminal_stable (p : Program n α) {t T : ℕ} (h : History n t)
    (h' : History n T) (ht : t ≤ T)
    (heq : ∀ i : Fin t, h i = h' ⟨i, lt_of_lt_of_le i.isLt ht⟩)
    {s : ℕ} {a : α} (hp : parse p h = .inr (s, a)) : parse p h' = .inr (s, a) := by
  induction p generalizing t T s with
  | pure b => exact hp
  | call key S hS d δ next ih =>
    let m := EliminationPolicy.budget S.card d δ
    change (if hm : m ≤ t then addCost m (parse
      (next (EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h)))
      (historySuffix m hm h)) else _) = _ at hp
    by_cases hm : m ≤ t
    · rw [dif_pos hm] at hp
      have hmT := hm.trans ht
      have hpre : historyPrefix m hm h = historyPrefix m hmT h' := by
        funext i
        exact heq ⟨i, lt_of_lt_of_le i.isLt hm⟩
      let R := EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h)
      change addCost m (parse (next R) (historySuffix m hm h)) = .inr (s, a) at hp
      cases hparse : parse (next R) (historySuffix m hm h) with
      | inl i => simp only [hparse, addCost] at hp; cases hp
      | inr p =>
        obtain ⟨s', b⟩ := p
        have he : m + s' = s ∧ b = a := by
          simpa only [hparse, addCost, Sum.inr.injEq, Prod.mk.injEq] using hp
        obtain ⟨hs, hb⟩ := he
        subst b
        have htail : parse (next R) (historySuffix m hmT h') = .inr (s', a) := by
          apply ih R (historySuffix m hm h) (historySuffix m hmT h') (Nat.sub_le_sub_right ht m)
          · intro i
            exact heq ⟨m + i, by have := i.isLt; omega⟩
          · exact hparse
        change (if hm : m ≤ T then addCost m (parse
          (next (EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h')))
          (historySuffix m hm h')) else _) = _
        rw [dif_pos hmT, ← hpre]
        change addCost m (parse (next R) (historySuffix m hmT h')) = _
        rw [htail]
        simp only [addCost, hs]
    · rw [dif_neg hm] at hp
      cases hp

end GapEntropy.FiniteCallProgram
