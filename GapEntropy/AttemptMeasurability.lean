import GapEntropy.AttemptInterface
import GapEntropy.Model
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of the finite attempt control flow

The finite type `Option (Finset (Fin n))` carries the discrete measurable structure, so a
measurable finite-valued choice may select among measurable functions
(`measurable_finite_choice`). When the oracle responses are measurable functions of the sample
point, so are `AttemptScale.step`, `run`, and `request`, and likewise
`TargetAttempt.finishScale`, `entry`, `loopRequest`, `finalRequest`, and `result`.
-/

noncomputable section
open MeasureTheory

namespace GapEntropy

instance optionFinsetMeasurableSpace (n : ℕ) : MeasurableSpace (Option (Finset (Fin n))) := ⊤
instance optionFinsetMeasurableSingleton (n : ℕ) : MeasurableSingletonClass (Option (Finset (Fin n))) :=
  ⟨fun _ => trivial⟩

/-- A measurable random finite choice can select among measurable functions. -/
theorem measurable_finite_choice {Ω A B : Type*} [MeasurableSpace Ω]
    [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A] [MeasurableSpace B]
    {Z : Ω → A} {F : Ω → A → B} (hZ : Measurable Z)
    (hF : ∀ a, Measurable (fun ω => F ω a)) : Measurable (fun ω => F ω (Z ω)) :=
  (measurable_from_prod_countable_right (f := fun p : A × Ω => F p.2 p.1) hF).comp
    (hZ.prodMk measurable_id)

namespace AttemptScale
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

theorem step_measurable (N r : ℕ) {F : Ω → Oracle n} {Z : Ω → Option (Finset (Fin n))}
    (hF : ∀ S, Measurable (fun ω => F ω r S)) (hZ : Measurable Z) :
    Measurable (fun ω => step N (F ω) r (Z ω)) := by
  apply measurable_finite_choice hZ
  intro state
  cases state with
  | none => exact measurable_const
  | some S =>
    by_cases hs : 4 * N < S.card
    · let accept : Finset (Fin n) → Option (Finset (Fin n)) :=
        fun R => if R.Nonempty ∧ R.card ≤ (S.card + 1) / 2 then some R else none
      simpa only [step, if_pos hs, accept, Function.comp_def] using
        (measurable_of_finite accept).comp (hF S)
    · simpa only [step, if_neg hs] using (measurable_const : Measurable (fun _ : Ω => some S))

theorem run_measurable (N R : ℕ) {F : Ω → Oracle n} {S : Ω → Finset (Fin n)}
    (hF : ∀ r T, Measurable (fun ω => F ω r T)) (hS : Measurable S) :
    Measurable (fun ω => run N (F ω) (S ω) R) := by
  induction R with
  | zero => exact (measurable_of_finite (@some (Finset (Fin n)))).comp hS
  | succ R ih => exact step_measurable N R (hF R) ih

theorem request_measurable (N r : ℕ) {F : Ω → Oracle n} (S : Finset (Fin n))
    (hF : ∀ j T, Measurable (fun ω => F ω j T)) :
    Measurable (fun ω => request N (F ω) S r) := by
  let choose : Option (Finset (Fin n)) → Option (Finset (Fin n)) := fun st =>
    match st with
    | none => none
    | some T => if 4 * N < T.card then some T else none
  exact (measurable_of_finite choose).comp (run_measurable N r hF measurable_const)

end AttemptScale

namespace TargetAttempt
variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

theorem finishScale_measurable (I : Instance n) (k : ℕ) {F : Ω → Oracle n}
    {Z : Ω → Option (Finset (Fin n))}
    (hF : ∀ r S, Measurable (fun ω => F ω k r S)) (hZ : Measurable Z) :
    Measurable (fun ω => finishScale I (F ω) k (Z ω)) := by
  apply measurable_finite_choice hZ
  intro state
  cases state with
  | none => exact measurable_const
  | some S => exact AttemptScale.run_measurable (I.targetCount k) n hF measurable_const

theorem entry_measurable (I : Instance n) {F : Ω → Oracle n}
    (hF : ∀ k r S, Measurable (fun ω => F ω k r S)) (k : ℕ) :
    Measurable (fun ω => entry I (F ω) k) := by
  induction k with
  | zero => exact measurable_const
  | succ k ih => exact finishScale_measurable I k (hF k) ih

theorem loopRequest_measurable (I : Instance n) {F : Ω → Oracle n}
    (hF : ∀ k r S, Measurable (fun ω => F ω k r S)) (k r : ℕ) :
    Measurable (fun ω => loopRequest I (F ω) k r) := by
  refine measurable_finite_choice
    (F := fun ω st => match st with
      | none => none
      | some S => AttemptScale.request (I.targetCount k) (F ω k) S r)
    (entry_measurable I hF k) ?_
  intro state
  cases state with
  | none => exact measurable_const
  | some S => exact AttemptScale.request_measurable (I.targetCount k) r S (hF k)

theorem finalRequest_measurable (I : Instance n) {F : Ω → Oracle n}
    (hF : ∀ k r S, Measurable (fun ω => F ω k r S)) :
    Measurable (fun ω => finalRequest I (F ω)) := by
  let choose : Option (Finset (Fin n)) → Option (Finset (Fin n)) := fun st =>
    match st with
    | none => none
    | some S => if S.card = 1 then none else some S
  exact (measurable_of_finite choose).comp (entry_measurable I hF (I.lastBucket + 1))

theorem result_measurable (I : Instance n) {F : Ω → Oracle n}
    {last : Ω → Finset (Fin n) → Finset (Fin n)}
    (hF : ∀ k r S, Measurable (fun ω => F ω k r S))
    (hlast : ∀ S, Measurable (fun ω => last ω S)) :
    Measurable (fun ω => result I (F ω) (last ω)) := by
  refine measurable_finite_choice
    (F := fun ω st => match st with
      | none => none
      | some S => if S.card = 1 then singletonReturn S else singletonReturn (last ω S))
    (entry_measurable I hF (I.lastBucket + 1)) ?_
  intro state
  cases state with
  | none => exact measurable_const
  | some S =>
    by_cases hs : S.card = 1
    · simpa only [if_pos hs] using (measurable_const : Measurable (fun _ : Ω => singletonReturn S))
    · simpa only [if_neg hs, Function.comp_def] using
        (measurable_of_finite singletonReturn).comp (hlast S)

end TargetAttempt
end GapEntropy
