import GapEntropy.UniversalExecution

/-!
# Call-indexed states with absolute reward-row boundaries

These are the same universal controller transitions written on an absolute
tape. The metadata's sample counter is the next call boundary. This interface
is intended for predictable-call and stopped-block probability arguments.
-/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram
variable {n : ℕ}

/-- Terminal result on the left, pending controller state on the right. -/
abbrev Stage (n : ℕ) := (State n × Option (Fin n)) ⊕ State n

theorem callProcedure_simulate_reference_independent (c : Config) (a : Metadata n)
    (ha : 2 ≤ a.active.card) (z z' : ℝ) (v : Fin (a.call c).samples → Fin n → ℝ) :
    (callProcedure c a ha z).simulate v (a.call c).samples le_rfl =
      (callProcedure c a ha z').simulate v (a.call c).samples le_rfl := by
  apply BoundedProcedure.simulate_congr_of_requests
  · intro s hs; rfl
  · intro s hs h; rfl

/-- Joint real-reference measurability of a completed uniform call. Its actual
sampling requests do not depend on z; its threshold readout does. -/
theorem measurable_call_evaluate (c : Config) (a : Metadata n) (ha : 2 ≤ a.active.card) :
    Measurable (fun p : ℝ × (Fin (a.call c).samples → Fin n → ℝ) =>
      (callProcedure c a ha p.1).evaluate p.2) := by
  have he (p : ℝ × (Fin (a.call c).samples → Fin n → ℝ)) :
      (callProcedure c a ha p.1).evaluate p.2 =
      readout c a p.1 ((callProcedure c a ha 0).simulate p.2 (a.call c).samples le_rfl) := by
    change readout c a p.1 _ = _
    exact congrArg (readout c a p.1)
      (callProcedure_simulate_reference_independent c a ha p.1 0 p.2)
  simp_rw [he]
  exact (measurable_readout c a _).comp (measurable_fst.prodMk
    (((callProcedure c a ha 0).measurable_simulate _ le_rfl).comp measurable_snd))

attribute [local irreducible] BoundedProcedure.evaluate

def stageStep (c : Config) (x : Values n) : Stage n → Stage n
  | .inl result => .inl result
  | .inr (a, z) =>
    if ha : a.Allowed c then
      let r := (callProcedure c a ha.1 z).evaluate
        (firstBlock (a.call c).samples (shiftValues a.samples x))
      if r.2.card = 1 then .inl ((a.advance c r.2, r.1), singletonAnswer r.2)
      else .inr (a.advance c r.2, retainedReference a r.1 r.2)
    else .inl ((a, z), none)

def stage (c : Config) (x : Values n) : ℕ → Stage n
  | 0 => .inr (initial n, 0)
  | r + 1 => stageStep c x (stage c x r)

theorem measurable_stageStep_fixed (c : Config) (a : Metadata n) :
    Measurable (fun p : ℝ × Values n => stageStep c p.2 (.inr (a, p.1))) := by
  by_cases ha : a.Allowed c
  · let r := fun p : ℝ × Values n => (callProcedure c a ha.1 p.1).evaluate
        (firstBlock (a.call c).samples (shiftValues a.samples p.2))
    have hr : Measurable r := (measurable_call_evaluate c a ha.1).comp
      (measurable_fst.prodMk ((firstBlock_measurable _).comp
        ((shiftValues_measurable _).comp measurable_snd)))
    have hnext : Measurable (fun p : ℝ × Values n =>
        if (r p).2.card = 1 then Sum.inl ((a.advance c (r p).2, (r p).1), singletonAnswer (r p).2)
        else Sum.inr (a.advance c (r p).2, retainedReference a (r p).1 (r p).2)) := by
      apply measurable_finite_choice
        (F := fun p R => if R.card = 1 then
          Sum.inl ((a.advance c R, (r p).1), singletonAnswer R)
          else Sum.inr (a.advance c R, retainedReference a (r p).1 R)) hr.snd
      intro R
      split_ifs
      · exact measurable_inl.comp ((measurable_const.prodMk hr.fst).prodMk measurable_const)
      · exact measurable_inr.comp (measurable_const.prodMk
          ((measurable_retainedReference a R).comp hr.fst))
    simpa only [stageStep, dif_pos ha, r] using hnext
  · simpa only [stageStep, dif_neg ha, Function.comp_def] using
      measurable_inl.comp ((measurable_const.prodMk measurable_fst).prodMk
        (measurable_const : Measurable (fun _ : ℝ × Values n => (none : Option (Fin n)))))

theorem measurable_stageStep (c : Config) :
    Measurable (fun p : Stage n × Values n => stageStep c p.2 p.1) := by
  have hm : Measurable (fun p : Metadata n × (ℝ × Values n) =>
      stageStep c p.2.2 (.inr (p.1, p.2.1))) :=
    measurable_from_prod_countable_right (measurable_stageStep_fixed c)
  have hr : Measurable (fun p : State n × Values n => stageStep c p.2 (.inr p.1)) :=
    hm.comp ((measurable_fst.fst).prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hl : Measurable (fun p : (State n × Option (Fin n)) × Values n =>
      (Sum.inl p.1 : Stage n)) := measurable_inl.comp measurable_fst
  convert (hl.sumElim hr).comp
    (MeasurableEquiv.sumProdDistrib (State n × Option (Fin n)) (State n) (Values n)).measurable using 1
  funext p
  rcases p with ⟨st, x⟩
  cases st <;> rfl

theorem measurable_stage (c : Config) (r : ℕ) : Measurable (fun x : Values n => stage c x r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih => exact (measurable_stageStep c).comp (ih.prodMk measurable_id)

/-- A pending state's sample counter is the exact absolute boundary; accepted
calls charge its complete sample reservation before the following state. -/
theorem stageStep_pending_samples (c : Config) (x : Values n) (a a' : Metadata n)
    (z z' : ℝ) (he : stageStep c x (.inr (a, z)) = .inr (a', z')) :
    a'.samples = a.samples + (a.call c).samples := by
  simp only [stageStep] at he
  split_ifs at he with ha hs
  simp only [Sum.inr.injEq, Prod.mk.injEq] at he
  rw [← he.1]
  rfl

theorem stageStep_terminal_absorbing (c : Config) (x : Values n) (result : State n × Option (Fin n)) :
    stageStep c x (.inl result) = .inl result := rfl

theorem iterate_terminal (c : Config) (x : Values n) (fuel : ℕ)
    (result : State n × Option (Fin n)) :
    (stageStep c x)^[fuel] (.inl result) = .inl result := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply, stageStep_terminal_absorbing, ih]

theorem iterate_eq_execute (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    (x : Values n) (hw : a.work ≤ c.workCap) (hf : c.workCap < a.work + 2 * fuel) :
    (stageStep c x)^[fuel] (.inr (a, z)) =
      .inl (execute c fuel a z (shiftValues a.samples x)) := by
  induction fuel generalizing a z with
  | zero => simp only [Nat.mul_zero, Nat.add_zero] at hf; omega
  | succ fuel ih =>
    rw [Function.iterate_succ_apply]
    by_cases ha : a.Allowed c
    · let r := (callProcedure c a ha.1 z).evaluate
        (firstBlock (a.call c).samples (shiftValues a.samples x))
      by_cases hr : r.2.card = 1
      · simpa only [stageStep, execute, dif_pos ha, if_pos hr, r] using
          iterate_terminal c x fuel ((a.advance c r.2, r.1), singletonAnswer r.2)
      · have hcw : 2 ≤ (a.call c).work := Reservation.two_le_call_work _ ha.1
        have hwork : (a.advance c r.2).work = a.work + (a.call c).work := rfl
        have hi := ih (a.advance c r.2) (retainedReference a r.1 r.2)
          (by rw [hwork]; exact ha.2.1) (by rw [hwork]; omega)
        have hx : shiftValues (a.advance c r.2).samples x =
            shiftValues (a.call c).samples (shiftValues a.samples x) := by
          funext i
          change x ((a.samples + (a.call c).samples) + i) = x (a.samples + ((a.call c).samples + i))
          rw [Nat.add_assoc]
        rw [hx] at hi
        simpa only [stageStep, execute, dif_pos ha, if_neg hr, r] using hi
    · simpa only [stageStep, execute, dif_neg ha] using iterate_terminal c x fuel ((a, z), none)

theorem stage_eq_iterate (c : Config) (x : Values n) (r : ℕ) :
    stage c x r = (stageStep c x)^[r] (.inr (initial n, 0)) := by
  induction r with
  | zero => rfl
  | succ r ih => rw [stage, ih, Function.iterate_succ_apply']

/-- The call-indexed process reaches exactly the real execution's terminal
result within the deterministic work-based fuel. -/
theorem stage_fuel_eq_execute (c : Config) (x : Values n) :
    stage c x c.fuel = .inl (execute c c.fuel (initial n) 0 x) := by
  rw [stage_eq_iterate]
  have he := iterate_eq_execute c c.fuel (initial n) 0 x (Nat.zero_le _)
    (by change c.workCap < 0 + 2 * (c.workCap / 2 + 1); omega)
  have hx : shiftValues (initial n).samples x = x := by
    funext i
    simp [shiftValues, initial, Metadata.samples]
  rwa [hx] at he

/-- Actual procedure output and the terminal call-indexed state agree pathwise. -/
theorem actualOutput_eq_stage (c : Config) (hn : 2 ≤ n) (ω : SampleSpace n) :
    ∃ st, stage c ω.2 c.fuel = .inl (st, (procedure c hn).actualOutput ω) := by
  rw [actualOutput_eq_execute]
  exact ⟨(execute c c.fuel (initial n) 0 ω.2).1, stage_fuel_eq_execute c ω.2⟩

end GapEntropy.UniversalAttempt
