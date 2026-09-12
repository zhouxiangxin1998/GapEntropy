import GapEntropy.StoppedBlocks
import GapEntropy.ActiveCounts

/-!
# Deterministic-budget interactive procedures with general outputs

A procedure requests samples using only its finite observed history. Its readout
may be a set, an abort-or-answer value, or any other measurable output. The
sampling policy's return label is just a completion marker; the procedure readout
is separate, so set-valued subroutine results are never confused with answers to
the best-arm problem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace GapEntropy

structure BoundedProcedure (n : ℕ) (α : Type*) [MeasurableSpace α] where
  budget : ℕ
  request : (t : ℕ) → t < budget → History n t → Fin n
  measurable_request : ∀ t ht, Measurable (request t ht)
  output : History n budget → α
  measurable_output : Measurable output

namespace BoundedProcedure

variable {n : ℕ} {α : Type*} [MeasurableSpace α] (R : BoundedProcedure n α)

abbrev Tape := Fin R.budget → Fin n → ℝ

/-- Run every requested sample on the given finite reward table. -/
def simulate (x : R.Tape) : (t : ℕ) → t ≤ R.budget → History n t
  | 0, _ => Fin.elim0
  | t + 1, ht =>
      let h := simulate x t (by omega)
      let i := R.request t (by omega) h
      Fin.snoc h (i, x ⟨t, by omega⟩ i)

def evaluate (x : R.Tape) : α := R.output (R.simulate x R.budget le_rfl)

private theorem measurable_snoc {t : ℕ} :
    Measurable (fun p : History n t × Observation n =>
      (Fin.snoc p.1 p.2 : History n (t + 1))) := by
  apply measurable_pi_lambda
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using
      (measurable_snd : Measurable (fun p : History n t × Observation n => p.2))
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (measurable_pi_apply j).comp
        (measurable_fst : Measurable (fun p : History n t × Observation n => p.1))

theorem measurable_simulate (t : ℕ) (ht : t ≤ R.budget) :
    Measurable (fun x : R.Tape => R.simulate x t ht) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hprev := ih (by omega : t ≤ R.budget)
      have hreq := (R.measurable_request t (by omega : t < R.budget)).comp hprev
      have hev : Measurable (fun p : Fin n × (Fin n → ℝ) => p.2 p.1) := by
        apply measurable_from_prod_countable_right
        intro i
        exact measurable_pi_apply i
      exact measurable_snoc.comp (hprev.prodMk
        (hreq.prodMk (hev.comp (hreq.prodMk (measurable_pi_apply ⟨t, by omega⟩)))))

theorem measurable_evaluate : Measurable R.evaluate :=
  R.measurable_output.comp (R.measurable_simulate R.budget le_rfl)

/-- Samples exactly the fixed budget, then returns the label zero as a done marker. -/
def samplingPolicy : Policy n where
  choose hn t p := if ht : t < R.budget then .inl (R.request t ht p.2)
    else .inr ⟨0, by omega⟩
  measurable_choose hn t := by
    by_cases ht : t < R.budget
    · simpa only [dif_pos ht, Function.comp_def] using
        measurable_inl.comp ((R.measurable_request t ht).comp measurable_snd)
    · simpa only [dif_neg ht] using
        (measurable_const : Measurable (fun _ : Seed × History n t =>
          (Sum.inr (⟨0, by omega⟩ : Fin n) : Decision n)))

def actualOutput (ω : SampleSpace n) : α :=
  R.evaluate (GaussianBlocks.rewardBlock 0 R.budget ω)

theorem measurable_actualOutput : Measurable R.actualOutput :=
  R.measurable_evaluate.comp (GaussianBlocks.measurable_rewardBlock 0 R.budget)

theorem request_congr_history {s t : ℕ} (hs : s < R.budget) (ht : t < R.budget)
    (hst : s = t) (h : History n s) (h' : History n t)
    (heq : ∀ i : Fin s, h i = h' ⟨i, by have := i.isLt; omega⟩) :
    R.request s hs h = R.request t ht h' := by
  subst t
  have hh : h = h' := funext heq
  rw [hh]

/-- Any observed history satisfying the procedure's requests and rewards is its
canonical simulation. This is a direct operational identity, independent of laws. -/
theorem simulate_eq_of_decisions (x : R.Tape) (t : ℕ) (ht : t ≤ R.budget)
    (h : History n t)
    (hdec : ∀ s (hs : s < t),
      R.request s (by omega) (Policy.historyPrefix h s hs.le) = (h ⟨s, hs⟩).1 ∧
        (h ⟨s, hs⟩).2 = x ⟨s, by omega⟩ (h ⟨s, hs⟩).1) :
    R.simulate x t ht = h := by
  induction t with
  | zero => exact Subsingleton.elim _ _
  | succ t ih =>
      have hprev : R.simulate x t (by omega) = Fin.init h := by
        apply ih (by omega) (Fin.init h)
        intro s hs
        exact hdec s (by omega)
      have hlast := hdec t (Nat.lt_succ_self t)
      change R.request t _ (Fin.init h) = (h (Fin.last t)).1 ∧
        (h (Fin.last t)).2 = x ⟨t, by omega⟩ (h (Fin.last t)).1 at hlast
      simp only [simulate, hprev, hlast.1, ← hlast.2, Prod.mk.eta]
      exact Fin.snoc_init_self h

/-- The canonical finite table simulation is exactly the actual observed policy history. -/
theorem run_eq_simulate (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) (ht : t ≤ R.budget) :
    R.samplingPolicy.run hn ω t =
      Sum.inr (R.simulate (GaussianBlocks.rewardBlock 0 R.budget ω) t ht) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have hlt : t < R.budget := by omega
      rw [Policy.run_succ, Policy.step, ih (by omega)]
      simp only [Sum.elim_inr, samplingPolicy, dif_pos hlt, Sum.elim_inl, simulate,
        GaussianBlocks.rewardBlock, Nat.zero_add]

/-- Completion is reached after exactly the public number of requested observations. -/
theorem run_return_at_budget (hn : 2 ≤ n) (ω : SampleSpace n) :
    R.samplingPolicy.run hn ω (R.budget + 1) = Sum.inl ⟨0, by omega⟩ := by
  rw [Policy.run_succ, Policy.step, R.run_eq_simulate hn ω _ le_rfl]
  simp [samplingPolicy]

theorem sampleCount_eq_budget (hn : 2 ≤ n) (ω : SampleSpace n) :
    R.samplingPolicy.sampleCount hn ω = R.budget :=
  R.samplingPolicy.sampleCount_eq_time_of_return_transition hn ω R.budget _
    (R.run_eq_simulate hn ω _ le_rfl) _ (R.run_return_at_budget hn ω)

/-- The readout distribution is the actual Gaussian simulation distribution. -/
theorem actualOutput_map (mean : Fin n → ℝ) :
    (sampleLawOfMeans mean).map R.actualOutput =
      (GaussianBlocks.blockLaw mean R.budget).map R.evaluate := by
  change (sampleLawOfMeans mean).map
    (R.evaluate ∘ GaussianBlocks.rewardBlock 0 R.budget) = _
  rw [← Measure.map_map R.measurable_evaluate
    (GaussianBlocks.measurable_rewardBlock 0 R.budget),
    (GaussianBlocks.measurePreserving_rewardBlock mean 0 R.budget).map_eq]

/-- The exact law transfer for any measurable subroutine event. -/
theorem actualOutput_event (mean : Fin n → ℝ) (S : Set α) (hS : MeasurableSet S) :
    sampleLawOfMeans mean (R.actualOutput ⁻¹' S) =
      GaussianBlocks.blockLaw mean R.budget (R.evaluate ⁻¹' S) := by
  rw [← Measure.map_apply R.measurable_actualOutput hS, R.actualOutput_map mean,
    Measure.map_apply R.measurable_evaluate hS]

end BoundedProcedure
end GapEntropy
