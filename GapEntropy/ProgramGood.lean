import GapEntropy.ProgramExecution
import GapEntropy.FiniteCallOrder

/-!
# Good calls along oracle paths and sequential executions

A good-call predicate `Good` judges each call by its key, input set, and response. `oracleGood`
asks that every call on an addressed oracle's path is good; `executionGood` asks the same of the
actual sequential execution on a reward table. `confidenceSpent` sums the declared confidences
along an oracle path, and `risk` is its maximum over all response branches.

The good-execution event is measurable and depends only on the capacity prefix of the table. On
ordered programs, `confidenceSpent` and `oracleGood` depend only on the oracle at keys above the
lower rank, the risk is attained by a consistent addressed oracle, and every good sequential
execution realizes a consistent addressed oracle with the same response and every visited call
good.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace GapEntropy.FiniteCallProgram
open TargetAttempt
variable {n : ℕ} {α β : Type*}

abbrev Good (n : ℕ) := CallKey → Finset (Fin n) → Finset (Fin n) → Prop

def oracleGood (G : Good n) (f : Oracle n) : Program n α → Prop
  | .pure _ => True
  | .call key S _ _ _ next => G key S (f key S) ∧ oracleGood G f (next (f key S))

def executionGood (G : Good n) (p : Program n α) (hn : 2 ≤ n) (x : Values n) : Prop :=
  match p with
  | .pure _ => True
  | .call key S hS d δ next =>
      let m := EliminationPolicy.budget S.card d δ
      let R := EliminationPolicy.rawOutputFromBlock S hS d δ hn (firstBlock m x)
      G key S R ∧ executionGood G (next R) hn (shiftValues m x)

def confidenceSpent (f : Oracle n) : Program n α → ℝ
  | .pure _ => 0
  | .call key S _ _ δ next => δ + confidenceSpent f (next (f key S))

def risk : Program n α → ℝ
  | .pure _ => 0
  | .call _ _ _ _ δ next => δ + Finset.univ.sup' Finset.univ_nonempty (fun R => risk (next R))

theorem confidenceSpent_bind (f : Oracle n) (p : Program n α) (g : α → Program n β) :
    confidenceSpent f (bind p g) = confidenceSpent f p + confidenceSpent f (g (eval f p)) := by
  induction p with
  | pure a => simp [bind, confidenceSpent, eval]
  | call key S hS d δ next ih => simp only [bind, confidenceSpent, eval, ih, add_assoc]

theorem oracleGood_bind (G : Good n) (f : Oracle n) (p : Program n α) (g : α → Program n β) :
    oracleGood G f (bind p g) ↔ oracleGood G f p ∧ oracleGood G f (g (eval f p)) := by
  induction p with
  | pure a => simp [bind, oracleGood, eval]
  | call key S hS d δ next ih => simp only [bind, oracleGood, eval, ih, and_assoc]

theorem executionGood_measurable (G : Good n) (p : Program n α) (hn : 2 ≤ n) :
    MeasurableSet {x | executionGood G p hn x} := by
  induction p with
  | pure _ => exact MeasurableSet.univ
  | call key S hS d δ next ih =>
    let m := EliminationPolicy.budget S.card d δ
    let F := fun x : Values n => EliminationPolicy.rawOutputFromBlock S hS d δ hn (firstBlock m x)
    have hF : Measurable F :=
      (EliminationPolicy.measurable_rawOutputFromBlock S hS d δ hn).comp (firstBlock_measurable m)
    have hrep : {x | executionGood G (.call key S hS d δ next) hn x} =
        ⋃ R : Finset (Fin n), (F ⁻¹' {R}) ∩
          (if G key S R then shiftValues m ⁻¹' {x | executionGood G (next R) hn x} else ∅) := by
      ext x
      simp only [executionGood, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_preimage, Set.mem_singleton_iff]
      change (G key S (F x) ∧ executionGood G (next (F x)) hn (shiftValues m x)) ↔ _
      constructor
      · intro hx
        exact ⟨F x, rfl, by simpa only [if_pos hx.1, Set.mem_preimage, Set.mem_ofPred_eq] using hx.2⟩
      · rintro ⟨R, hR, hx⟩
        subst R
        by_cases hg : G key S (F x)
        · exact ⟨hg, by simpa only [if_pos hg, Set.mem_preimage, Set.mem_ofPred_eq] using hx⟩
        · simp only [if_neg hg, Set.mem_empty_iff_false] at hx
    rw [hrep]
    apply MeasurableSet.iUnion
    intro R
    apply (hF (measurableSet_singleton R)).inter
    by_cases hg : G key S R
    · simpa only [if_pos hg] using (shiftValues_measurable m) (ih R)
    · simpa only [if_neg hg] using MeasurableSet.empty

theorem executionGood_congr_prefix (G : Good n) (p : Program n α) (hn : 2 ≤ n) (x y : Values n)
    (hxy : ∀ j < capacity p, x j = y j) : executionGood G p hn x ↔ executionGood G p hn y := by
  induction p generalizing x y with
  | pure _ => rfl
  | call key S hS d δ next ih =>
    let m := EliminationPolicy.budget S.card d δ
    have hblock : firstBlock m x = firstBlock m y := by
      funext j
      exact hxy j (j.isLt.trans_le (Nat.le_add_right _ _))
    let R := EliminationPolicy.rawOutputFromBlock S hS d δ hn (firstBlock m x)
    have ht : executionGood G (next R) hn (shiftValues m x) ↔
        executionGood G (next R) hn (shiftValues m y) := by
      apply ih R
      intro j hj
      have hcap : capacity (next R) ≤ Finset.univ.sup (fun T => capacity (next T)) :=
        Finset.le_sup (f := fun T => capacity (next T)) (Finset.mem_univ R)
      exact hxy (m + j) (Nat.add_lt_add_left (hj.trans_le hcap) m)
    dsimp only [executionGood]
    rw [← hblock]
    exact and_congr_right (fun _ => ht)

theorem confidenceSpent_congr_above {rank : CallKey → ℕ} {lo hi : ℕ} {p : Program n α}
    (hp : Ordered rank lo hi p) {f g : Oracle n}
    (hfg : ∀ key, lo ≤ rank key → ∀ S, f key S = g key S) :
    confidenceSpent f p = confidenceSpent g p := by
  induction p generalizing lo with
  | pure _ => rfl
  | call key S hS d δ next ih =>
    simp only [confidenceSpent, hfg key hp.1 S]
    congr 1
    exact ih _ (hp.2.2 _) (fun key' hkey' S' =>
      hfg key' (hp.1.trans ((Nat.le_succ _).trans hkey')) S')

theorem risk_attained {rank : CallKey → ℕ} {lo hi : ℕ} {p : Program n α}
    (hp : Ordered rank lo hi p) : ∃ f : Oracle n, confidenceSpent f p = risk p := by
  induction p generalizing lo with
  | pure _ => exact ⟨fun _ _ => ∅, rfl⟩
  | call key S hS d δ next ih =>
    obtain ⟨R, _, hR⟩ := Finset.exists_mem_eq_sup'
      (Finset.univ_nonempty : (Finset.univ : Finset (Finset (Fin n))).Nonempty)
      (fun R => risk (next R))
    obtain ⟨f, hf⟩ := ih R (hp.2.2 R)
    let g : Oracle n := fun key' S' => if key' = key then R else f key' S'
    have hgf : confidenceSpent g (next R) = confidenceSpent f (next R) :=
      confidenceSpent_congr_above (hp.2.2 R) (fun key' hkey' S' => by
        have hne : key' ≠ key := by intro he; subst key'; omega
        simp only [g, if_neg hne])
    refine ⟨g, ?_⟩
    simp only [confidenceSpent, g, if_pos rfl, risk]
    change δ + confidenceSpent g (next R) = _
    rw [hgf, hf, hR]

theorem oracleGood_congr_above (G : Good n) {rank : CallKey → ℕ} {lo hi : ℕ} {p : Program n α}
    (hp : Ordered rank lo hi p) {f g : Oracle n}
    (hfg : ∀ key, lo ≤ rank key → ∀ S, f key S = g key S) :
    oracleGood G f p ↔ oracleGood G g p := by
  induction p generalizing lo with
  | pure _ => rfl
  | call key S hS d δ next ih =>
    simp only [oracleGood, hfg key hp.1 S]
    apply and_congr_right
    intro _
    exact ih _ (hp.2.2 _) (fun key' hkey' S' =>
      hfg key' (hp.1.trans ((Nat.le_succ _).trans hkey')) S')

/-- A good sequential execution realizes a consistent addressed oracle with the
same response and with every visited call good. -/
theorem execute_good_oracle (G : Good n) {rank : CallKey → ℕ} {lo hi : ℕ} {p : Program n α}
    (hp : Ordered rank lo hi p) (hn : 2 ≤ n) (x : Values n)
    (hx : executionGood G p hn x) :
    ∃ f : Oracle n, eval f p = (execute p hn x).2 ∧ oracleGood G f p := by
  induction p generalizing lo x with
  | pure _ => exact ⟨fun _ _ => ∅, rfl, trivial⟩
  | call key S hS d δ next ih =>
    let m := EliminationPolicy.budget S.card d δ
    let R := EliminationPolicy.rawOutputFromBlock S hS d δ hn (firstBlock m x)
    obtain ⟨f, hf, hg⟩ := ih R (hp.2.2 R) (shiftValues m x) hx.2
    let g : Oracle n := fun key' S' => if key' = key then R else f key' S'
    have hcur : g key S = R := by simp only [g, if_pos rfl]
    have hgf : ∀ key', rank key + 1 ≤ rank key' → ∀ S', g key' S' = f key' S' := by
      intro key' hkey' S'
      have hne : key' ≠ key := by intro he; subst key'; omega
      simp only [g, if_neg hne]
    refine ⟨g, ?_, ?_⟩
    · change eval g (next (g key S)) = (execute (next R) hn (shiftValues m x)).2
      rw [hcur, eval_congr_above (hp.2.2 R) hgf, hf]
    · change G key S (g key S) ∧ oracleGood G g (next (g key S))
      rw [hcur]
      exact ⟨hx.1, (oracleGood_congr_above G (hp.2.2 R) hgf).mpr hg⟩

end GapEntropy.FiniteCallProgram
