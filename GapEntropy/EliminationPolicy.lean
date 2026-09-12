import GapEntropy.MedianPolicyGaussian
import GapEntropy.EliminationA3

/-!
# An actual fixed-budget sampler for the A.3 elimination call

The terminal arm label is a completion marker. The subroutine's actual result
is the raw or padded finite set read from its completed observation history.
A surrounding interpreter continues with that set at the budget boundary.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.EliminationPolicy
open EliminationTape

abbrev budget (s : ℕ) (d α : ℝ) : ℕ := EliminationTape.declaredCost s d α

def medianBudget (s : ℕ) (d α : ℝ) : ℕ :=
  MedianElimination.declaredCost s (d / 8) (α / 16)

def activeStart (s : ℕ) (d α : ℝ) : ℕ := medianBudget s d α + referenceSamples d α

theorem budget_eq (s : ℕ) (d α : ℝ) :
    budget s d α = activeStart s d α + s * activeSamples d α := rfl

theorem medianBudget_le_budget (s : ℕ) (d α : ℝ) : medianBudget s d α ≤ budget s d α := by
  rw [budget_eq]
  unfold activeStart
  omega

def referenceFromHistory {n t : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (h : History n t) : Fin n :=
  MedianPolicy.outputFromHistory S hS (d / 8) (α / 16) h

theorem measurable_referenceFromHistory {n t : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) : Measurable (referenceFromHistory (t := t) S hS d α) :=
  MedianPolicy.measurable_outputFromHistory S hS _ _

def requestedFromHistory {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (t : ℕ) (h : History n t) : Fin n :=
  if ht : t < medianBudget S.card d α then
    MedianPolicy.requestedFromHistory S hS (d / 8) (α / 16) t ht h
  else if t < activeStart S.card d α then referenceFromHistory S hS d α h
  else MedianPolicy.armAt (S.min' hS) S
    ((t - activeStart S.card d α) / activeSamples d α)

theorem measurable_requestedFromHistory {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (t : ℕ) : Measurable (requestedFromHistory S hS d α t) := by
  unfold requestedFromHistory
  split_ifs with ht ht'
  · exact MedianPolicy.measurable_requestedFromHistory S hS _ _ t ht
  · exact measurable_referenceFromHistory S hS d α
  · exact measurable_const

def referenceEstimateFromHistory {n t : ℕ} (S : Finset (Fin n)) (d α : ℝ)
    (h : History n t) : ℝ :=
  (∑ j : Fin (referenceSamples d α),
    MedianPolicy.historyValues h (medianBudget S.card d α + j)) / (referenceSamples d α : ℝ)

def activeEstimateFromHistory {n t : ℕ} (S : Finset (Fin n)) (d α : ℝ)
    (h : History n t) (i : Fin n) : ℝ :=
  (∑ j : Fin (activeSamples d α), MedianPolicy.historyValues h
    (activeStart S.card d α + MedianPolicy.armRank S i * activeSamples d α + j)) /
      (activeSamples d α : ℝ)

theorem measurable_referenceEstimateFromHistory {n t : ℕ} (S : Finset (Fin n)) (d α : ℝ) :
    Measurable (referenceEstimateFromHistory (t := t) S d α) := by
  unfold referenceEstimateFromHistory
  exact (Finset.measurable_fun_sum _ (fun j _ => MedianPolicy.measurable_historyValues _)).div_const _

theorem measurable_activeEstimateFromHistory {n t : ℕ} (S : Finset (Fin n)) (d α : ℝ)
    (i : Fin n) : Measurable (fun h : History n t => activeEstimateFromHistory S d α h i) := by
  unfold activeEstimateFromHistory
  exact (Finset.measurable_fun_sum _ (fun j _ => MedianPolicy.measurable_historyValues _)).div_const _

def rawOutputFromHistory {n t : ℕ} (S : Finset (Fin n)) (_hS : S.Nonempty)
    (d α : ℝ) (h : History n t) : Finset (Fin n) :=
  Elimination.raw S (activeEstimateFromHistory S d α h) (referenceEstimateFromHistory S d α h) d

def paddedOutputFromHistory {n t : ℕ} (S : Finset (Fin n)) (_hS : S.Nonempty)
    (d α : ℝ) (h : History n t) : Finset (Fin n) :=
  Elimination.padded S (activeEstimateFromHistory S d α h) (referenceEstimateFromHistory S d α h) d

theorem measurable_rawOutputFromHistory {n t : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) : Measurable (rawOutputFromHistory (t := t) S hS d α) :=
  SortingMeasurability.raw_measurable measurable_const
    (measurable_activeEstimateFromHistory S d α) (measurable_referenceEstimateFromHistory S d α)
    measurable_const

theorem measurable_paddedOutputFromHistory {n t : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) : Measurable (paddedOutputFromHistory (t := t) S hS d α) :=
  SortingMeasurability.padded_measurable measurable_const
    (measurable_activeEstimateFromHistory S d α) (measurable_referenceEstimateFromHistory S d α)
    measurable_const

/-- The final label marks completion and is not a best-arm answer. The raw/padded
subroutine result is obtained by applying the readout to the completed history. -/
def policy {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (d α : ℝ) : Policy n where
  choose _ t p := if t < budget S.card d α then .inl (requestedFromHistory S hS d α t p.2)
    else .inr (referenceFromHistory S hS d α p.2)
  measurable_choose _ t := by
    by_cases ht : t < budget S.card d α
    · simpa only [if_pos ht, Function.comp_def] using
        measurable_inl.comp ((measurable_requestedFromHistory S hS d α t).comp measurable_snd)
    · simpa only [if_neg ht, Function.comp_def] using
        measurable_inr.comp ((measurable_referenceFromHistory S hS d α).comp measurable_snd)

theorem run_active_before_budget {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) (ht : t ≤ budget S.card d α) :
    ∃ h, (policy S hS d α).run hn ω t = .inr h := by
  induction t with
  | zero => exact ⟨Fin.elim0, rfl⟩
  | succ t ih =>
      obtain ⟨h, hh⟩ := ih (by omega)
      have ht' : t < budget S.card d α := by omega
      refine ⟨Fin.snoc h (requestedFromHistory S hS d α t h,
        ω.2 t (requestedFromHistory S hS d α t h)), ?_⟩
      simp only [Policy.run_succ, Policy.step, hh, Sum.elim_inr]
      simp [policy, ht']

def historyAt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (d α : ℝ)
    (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) : History n t :=
  ((policy S hS d α).run hn ω t).elim (fun _ _ => (S.min' hS, 0)) id

theorem measurable_historyAt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (d α : ℝ)
    (hn : 2 ≤ n) (t : ℕ) : Measurable (historyAt S hS d α hn t) :=
  (measurable_const.sumElim measurable_id).comp ((policy S hS d α).measurable_run hn t)

theorem run_eq_historyAt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) (ht : t ≤ budget S.card d α) :
    (policy S hS d α).run hn ω t = .inr (historyAt S hS d α hn t ω) := by
  obtain ⟨h, hh⟩ := run_active_before_budget S hS d α hn ω t ht
  simp only [historyAt, hh, Sum.elim_inr, id_eq]

def completedHistory {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) : History n (budget S.card d α) :=
  historyAt S hS d α hn (budget S.card d α) ω

def rawOutput {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) : Finset (Fin n) :=
  rawOutputFromHistory S hS d α (completedHistory S hS d α hn ω)

def paddedOutput {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) : Finset (Fin n) :=
  paddedOutputFromHistory S hS d α (completedHistory S hS d α hn ω)

theorem measurable_rawOutput {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) : Measurable (rawOutput S hS d α hn) :=
  (measurable_rawOutputFromHistory S hS d α).comp (measurable_historyAt S hS d α hn _)

theorem measurable_paddedOutput {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) : Measurable (paddedOutput S hS d α hn) :=
  (measurable_paddedOutputFromHistory S hS d α).comp (measurable_historyAt S hS d α hn _)

theorem run_marker_at_budget {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy S hS d α).returnedAt hn (budget S.card d α + 1) ω =
      some (referenceFromHistory S hS d α (completedHistory S hS d α hn ω)) := by
  have hh := run_eq_historyAt S hS d α hn ω (budget S.card d α) le_rfl
  simp only [Policy.returnedAt, Policy.run_succ, Policy.step, hh, Sum.elim_inr]
  simp [policy, completedHistory]

theorem sampleIndicator_eq_one_before_budget {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) (ht : t < budget S.card d α) :
    (policy S hS d α).sampleIndicator hn t ω = 1 := by
  obtain ⟨h, hh⟩ := run_active_before_budget S hS d α hn ω t ht.le
  simp only [Policy.sampleIndicator, Policy.sampleRequested, Policy.requestedArm, hh, Sum.elim_inr]
  simp [policy, ht]

theorem sampleCount_eq_budget {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy S hS d α).sampleCount hn ω = budget S.card d α := by
  rw [(policy S hS d α).sampleCount_eq_truncatedSamples_of_returned hn ω _
    (run_marker_at_budget S hS d α hn ω), Policy.truncatedSamples_succ]
  have hh := run_eq_historyAt S hS d α hn ω (budget S.card d α) le_rfl
  have hz : (policy S hS d α).sampleIndicator hn (budget S.card d α) ω = 0 := by
    simp only [Policy.sampleIndicator, Policy.sampleRequested, Policy.requestedArm, hh, Sum.elim_inr]
    simp [policy]
  rw [hz, add_zero, Policy.truncatedSamples]
  have he : ∑ t ∈ Finset.range (budget S.card d α), (policy S hS d α).sampleIndicator hn t ω =
      ∑ _t ∈ Finset.range (budget S.card d α), (1 : ℝ≥0∞) :=
    Finset.sum_congr rfl (fun t ht =>
      sampleIndicator_eq_one_before_budget S hS d α hn ω t (Finset.mem_range.mp ht))
  simpa using he

theorem expectedSamples_eq_budget {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (I : Instance n) : (policy S hS d α).expectedSamples I = budget S.card d α := by
  simp only [Policy.expectedSamples, sampleCount_eq_budget, lintegral_const, measure_univ, mul_one]

end GapEntropy.EliminationPolicy
