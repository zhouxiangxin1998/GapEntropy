import GapEntropy.UniversalStages

/-! Uniform controller calls are exactly the already analyzed entry and later
bounded procedures. The later wrapper only retains z in the output pair. -/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GapEntropy.UniversalAttempt
open UniversalCall
variable {n : ℕ}

/-- Retain a fixed numerical reference alongside a bounded set-valued readout. -/
def carryReference (R : BoundedProcedure n (Finset (Fin n))) (z : ℝ) :
    BoundedProcedure n (ℝ × Finset (Fin n)) where
  budget := R.budget
  request := R.request
  measurable_request := R.measurable_request
  output h := (z, R.output h)
  measurable_output := measurable_const.prodMk R.measurable_output

theorem carryReference_simulate (R : BoundedProcedure n (Finset (Fin n))) (z : ℝ)
    (v : R.Tape) (t : ℕ) (ht : t ≤ R.budget) :
    (carryReference R z).simulate v t ht = R.simulate v t ht := by
  apply BoundedProcedure.simulate_congr_of_requests
  · intro s hs; rfl
  · intro s hs h; rfl

theorem carryReference_evaluate (R : BoundedProcedure n (Finset (Fin n))) (z : ℝ)
    (v : R.Tape) : (carryReference R z).evaluate v = (z, R.evaluate v) := by
  change (z, R.output ((carryReference R z).simulate v R.budget le_rfl)) = _
  rw [carryReference_simulate]
  rfl

theorem callProcedure_eq_entry (c : Config) (a : Metadata n) (ha : 2 ≤ a.active.card)
    (z : ℝ) (he : a.entry = true) :
    callProcedure c a ha z = entryProcedure a.active
      (Finset.card_pos.mp (show 0 < a.active.card by omega))
      a.tolerance (a.alpha c) (a.beta c) := by
  rcases a with ⟨S, k, entry, w, q⟩
  change entry = true at he
  subst entry
  rfl

theorem callProcedure_eq_later (c : Config) (a : Metadata n) (ha : 2 ≤ a.active.card)
    (z : ℝ) (he : a.entry = false) :
    callProcedure c a ha z = carryReference (laterProcedure a.active
      (Finset.card_pos.mp (show 0 < a.active.card by omega)) a.tolerance (a.alpha c) z) z := by
  rcases a with ⟨S, k, entry, w, q⟩
  change entry = false at he
  subst entry
  rfl

end GapEntropy.UniversalAttempt
