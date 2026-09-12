import GapEntropy.FiniteCallProgram
import GapEntropy.EliminationProcedure

/-!
# Sequential finite-block execution of call programs on a reward table

`execute` runs a finite call program on a table of reward rows: each call reads exactly its
budget of rows, applies the actual raw elimination output of `EliminationPolicy` to that block,
and the next call starts after the consumed rows. The result pairs the total consumed count with
the terminal value. Execution is measurable, its cost is at most the program's `capacity`, and
it depends only on the first `capacity` rows, so it may be evaluated on a finite block extended
by zeros.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace GapEntropy.FiniteCallProgram
variable {n : ℕ} {α : Type*}

abbrev Values (n : ℕ) := ℕ → Fin n → ℝ

def firstBlock (m : ℕ) (x : Values n) : Fin m → Fin n → ℝ := fun j => x j

def shiftValues (m : ℕ) (x : Values n) : Values n := fun j => x (m + j)

theorem firstBlock_measurable (m : ℕ) : Measurable (firstBlock (n := n) m) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

theorem shiftValues_measurable (m : ℕ) : Measurable (shiftValues (n := n) m) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- Actual sequential finite-block execution on a reward-row table. Every call
reads only its budget, and the next call starts after those consumed rows. -/
def execute (p : Program n α) (hn : 2 ≤ n) (x : Values n) : ℕ × α :=
  match p with
  | .pure a => (0, a)
  | .call _ S hS d δ next =>
      let m := EliminationPolicy.budget S.card d δ
      let R := EliminationPolicy.rawOutputFromBlock S hS d δ hn (firstBlock m x)
      let tail := execute (next R) hn (shiftValues m x)
      (m + tail.1, tail.2)

theorem execute_measurable [MeasurableSpace α] (p : Program n α) (hn : 2 ≤ n) :
    Measurable (execute p hn) := by
  induction p with
  | pure _ => exact measurable_const
  | call key S hS d δ next ih =>
    let m := EliminationPolicy.budget S.card d δ
    have hR : Measurable (fun x : Values n =>
        EliminationPolicy.rawOutputFromBlock S hS d δ hn (firstBlock m x)) :=
      (EliminationPolicy.measurable_rawOutputFromBlock S hS d δ hn).comp (firstBlock_measurable m)
    have ht : Measurable (fun x : Values n => execute
        (next (EliminationPolicy.rawOutputFromBlock S hS d δ hn (firstBlock m x))) hn (shiftValues m x)) :=
      measurable_finite_choice (F := fun x R => execute (next R) hn (shiftValues m x)) hR
        (fun R => (ih R).comp (shiftValues_measurable m))
    exact (measurable_const.add ht.fst).prodMk ht.snd

theorem execute_cost_le_capacity (p : Program n α) (hn : 2 ≤ n) (x : Values n) :
    (execute p hn x).1 ≤ capacity p := by
  induction p generalizing x with
  | pure _ => exact le_rfl
  | call key S hS d δ next ih =>
    exact Nat.add_le_add_left ((ih _ _).trans
      (Finset.le_sup (f := fun R => capacity (next R)) (Finset.mem_univ _))) _

/-- The sequential experiment depends only on its finite capacity prefix. -/
theorem execute_congr_prefix (p : Program n α) (hn : 2 ≤ n) (x y : Values n)
    (hxy : ∀ j < capacity p, x j = y j) : execute p hn x = execute p hn y := by
  induction p generalizing x y with
  | pure _ => rfl
  | call key S hS d δ next ih =>
    let m := EliminationPolicy.budget S.card d δ
    have hblock : firstBlock m x = firstBlock m y := by
      funext j
      exact hxy j (j.isLt.trans_le (Nat.le_add_right _ _))
    let R := EliminationPolicy.rawOutputFromBlock S hS d δ hn (firstBlock m x)
    have ht : execute (next R) hn (shiftValues m x) = execute (next R) hn (shiftValues m y) := by
      apply ih R
      intro j hj
      have hcap : capacity (next R) ≤ Finset.univ.sup (fun T => capacity (next T)) :=
        Finset.le_sup (f := fun T => capacity (next T)) (Finset.mem_univ R)
      exact hxy (m + j) (Nat.add_lt_add_left (hj.trans_le hcap) m)
    dsimp only [execute]
    rw [← hblock]
    change (m + (execute (next R) hn (shiftValues m x)).1,
      (execute (next R) hn (shiftValues m x)).2) = _
    rw [ht]

def extendBlock (m : ℕ) (x : Fin m → Fin n → ℝ) : Values n :=
  fun j => if hj : j < m then x ⟨j, hj⟩ else fun _ => 0

theorem extendBlock_measurable (m : ℕ) : Measurable (extendBlock (n := n) m) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j < m
  · simpa only [extendBlock, dif_pos hj] using measurable_pi_apply (⟨j, hj⟩ : Fin m)
  · simpa only [extendBlock, dif_neg hj] using
      (measurable_const : Measurable (fun _ : Fin m → Fin n → ℝ => fun _ : Fin n => (0 : ℝ)))

theorem execute_eq_extendBlock (p : Program n α) (hn : 2 ≤ n) (m : ℕ) (hm : capacity p ≤ m)
    (x : Values n) : execute p hn x = execute p hn (extendBlock m (firstBlock m x)) := by
  apply execute_congr_prefix p hn
  intro j hj
  simp only [extendBlock, dif_pos (hj.trans_le hm), firstBlock]

end GapEntropy.FiniteCallProgram
