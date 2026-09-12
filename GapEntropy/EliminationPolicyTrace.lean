import GapEntropy.EliminationPolicy

/-! # Actual phase observations of the elimination sampler -/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.EliminationPolicy
open EliminationTape

theorem completedHistory_consistent {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy S hS d α).historyConsistent hn ω (budget S.card d α)
      (completedHistory S hS d α hn ω) :=
  ((policy S hS d α).run_eq_active_iff_historyConsistent hn ω _ _).mp
    (run_eq_historyAt S hS d α hn ω _ le_rfl)

theorem run_prefix_completedHistory {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) (ht : t ≤ budget S.card d α) :
    (policy S hS d α).run hn ω t =
      .inr (Policy.historyPrefix (completedHistory S hS d α hn ω) t ht) :=
  ((policy S hS d α).run_eq_active_iff_historyConsistent hn ω _ _).mpr
    ((policy S hS d α).historyConsistent_prefix hn ω _
      (completedHistory_consistent S hS d α hn ω) t ht)

theorem choose_eq_median_before {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (t : ℕ) (ht : t < medianBudget S.card d α)
    (p : Seed × History n t) :
    (policy S hS d α).choose hn t p = (MedianPolicy.policy S hS (d / 8) (α / 16)).choose hn t p := by
  have hfull := ht.trans_le (medianBudget_le_budget S.card d α)
  have ht' : t < MedianElimination.declaredCost S.card (d / 8) (α / 16) := ht
  simp only [policy, if_pos hfull, MedianPolicy.policy, requestedFromHistory, dif_pos ht, dif_pos ht']

theorem run_eq_median_before {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) (ht : t ≤ medianBudget S.card d α) :
    (policy S hS d α).run hn ω t = (MedianPolicy.policy S hS (d / 8) (α / 16)).run hn ω t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      have ht' : t < medianBudget S.card d α := by omega
      simp only [Policy.run_succ, Policy.step, ih (by omega), choose_eq_median_before S hS d α hn t ht']

theorem completedHistory_median_prefix {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    Policy.historyPrefix (completedHistory S hS d α hn ω) (medianBudget S.card d α)
      (medianBudget_le_budget S.card d α) =
        MedianPolicy.completedHistory S hS (d / 8) (α / 16) hn ω := by
  apply Sum.inr.inj
  calc
    _ = (policy S hS d α).run hn ω (medianBudget S.card d α) :=
      (run_prefix_completedHistory S hS d α hn ω _ (medianBudget_le_budget S.card d α)).symm
    _ = (MedianPolicy.policy S hS (d / 8) (α / 16)).run hn ω (medianBudget S.card d α) :=
      run_eq_median_before S hS d α hn ω _ le_rfl
    _ = _ := MedianPolicy.run_eq_historyAt S hS (d / 8) (α / 16) hn ω _ le_rfl

theorem referenceFromHistory_prefix {n T : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (h : History n T) (t : ℕ) (ht : t ≤ T) (hp : medianBudget S.card d α ≤ t) :
    referenceFromHistory S hS d α (Policy.historyPrefix h t ht) = referenceFromHistory S hS d α h := by
  unfold referenceFromHistory MedianPolicy.outputFromHistory
  congr 1
  apply MedianPolicy.reconstruct_historyPrefix hS
  simpa only [MedianPolicy.start_terminal, medianBudget] using hp

def referenceArm {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) : Fin n :=
  referenceFromHistory S hS d α (completedHistory S hS d α hn ω)

theorem referenceArm_eq_median_output {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    referenceArm S hS d α hn ω = MedianPolicy.output S hS (d / 8) (α / 16) hn ω := by
  have hp := referenceFromHistory_prefix S hS d α (completedHistory S hS d α hn ω)
    (medianBudget S.card d α) (medianBudget_le_budget S.card d α) le_rfl
  rw [completedHistory_median_prefix] at hp
  exact hp.symm

theorem measurable_referenceArm {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) : Measurable (referenceArm S hS d α hn) :=
  (measurable_referenceFromHistory S hS d α).comp (measurable_historyAt S hS d α hn _)

theorem referenceArm_mem {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) : referenceArm S hS d α hn ω ∈ S :=
  MedianPolicy.outputFromHistory_mem S hS _ _ _

theorem completedHistory_requested {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) (ht : t < budget S.card d α) :
    let H := completedHistory S hS d α hn ω
    let i := requestedFromHistory S hS d α t (Policy.historyPrefix H t ht.le)
    H ⟨t, ht⟩ = (i, ω.2 t i) := by
  have hd := (policy S hS d α).historyConsistent_decision hn ω _
    (completedHistory_consistent S hS d α hn ω) t ht
  have hi : requestedFromHistory S hS d α t
      (Policy.historyPrefix (completedHistory S hS d α hn ω) t ht.le) =
      (completedHistory S hS d α hn ω ⟨t, ht⟩).1 := by
    simpa only [policy, if_pos ht, Sum.inl.injEq] using hd.1
  exact Prod.ext hi.symm (hd.2.trans (congrArg (ω.2 t) hi.symm))

theorem reference_observation_eq_reward {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (j : Fin (referenceSamples d α)) :
    MedianPolicy.historyValues (completedHistory S hS d α hn ω) (medianBudget S.card d α + j) =
      ω.2 (medianBudget S.card d α + j) (referenceArm S hS d α hn ω) := by
  have ht : medianBudget S.card d α + j < budget S.card d α := by
    rw [budget_eq]
    unfold activeStart
    have := j.isLt
    omega
  have hnot : ¬ medianBudget S.card d α + j < medianBudget S.card d α := by omega
  have href : medianBudget S.card d α + j < activeStart S.card d α := by
    unfold activeStart
    exact Nat.add_lt_add_left j.isLt _
  have ho := congrArg Prod.snd (completedHistory_requested S hS d α hn ω _ ht)
  simp only [requestedFromHistory, dif_neg hnot, if_pos href] at ho
  rw [referenceFromHistory_prefix S hS d α _ _ ht.le (by omega)] at ho
  simpa only [MedianPolicy.historyValues, dif_pos ht, referenceArm] using ho

theorem active_index_lt_budget {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (i : Fin n) (j : Fin (activeSamples d α)) :
    activeStart S.card d α + MedianPolicy.armRank S i * activeSamples d α + j < budget S.card d α := by
  have hi := MedianPolicy.armRank_lt hS i
  have hm := Nat.mul_le_mul_right (activeSamples d α) hi
  have hj := j.isLt
  rw [budget_eq]
  nlinarith

theorem active_observation_eq_reward {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (i : Fin n) (hi : i ∈ S)
    (j : Fin (activeSamples d α)) :
    let t := activeStart S.card d α + MedianPolicy.armRank S i * activeSamples d α + j
    MedianPolicy.historyValues (completedHistory S hS d α hn ω) t = ω.2 t i := by
  let t := activeStart S.card d α + MedianPolicy.armRank S i * activeSamples d α + j
  have ht : t < budget S.card d α := active_index_lt_budget S hS d α i j
  have htact : ¬ t < activeStart S.card d α := by dsimp [t]; omega
  have htmed : ¬ t < medianBudget S.card d α := by dsimp [t, activeStart]; omega
  have hm : 0 < activeSamples d α := by have := j.isLt; omega
  have hdiv : (t - activeStart S.card d α) / activeSamples d α = MedianPolicy.armRank S i := by
    dsimp [t]
    rw [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_mul_div_right _ _ hm,
      Nat.div_eq_of_lt j.isLt, zero_add]
  have ho := congrArg Prod.snd (completedHistory_requested S hS d α hn ω t ht)
  simp only [requestedFromHistory, dif_neg htmed, if_neg htact, hdiv,
    MedianPolicy.armAt_armRank (S.min' hS) hi] at ho
  change MedianPolicy.historyValues (completedHistory S hS d α hn ω) t = ω.2 t i
  simpa only [MedianPolicy.historyValues, dif_pos ht] using ho

def referenceEstimate {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) : ℝ :=
  referenceEstimateFromHistory S d α (completedHistory S hS d α hn ω)

def activeEstimate {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (i : Fin n) (ω : SampleSpace n) : ℝ :=
  activeEstimateFromHistory S d α (completedHistory S hS d α hn ω) i

theorem measurable_referenceEstimate {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) : Measurable (referenceEstimate S hS d α hn) :=
  (measurable_referenceEstimateFromHistory S d α).comp (measurable_historyAt S hS d α hn _)

theorem measurable_activeEstimate {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (i : Fin n) : Measurable (activeEstimate S hS d α hn i) :=
  (measurable_activeEstimateFromHistory S d α i).comp (measurable_historyAt S hS d α hn _)

theorem referenceEstimate_eq_rawMean {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    referenceEstimate S hS d α hn ω =
      (∑ j : Fin (referenceSamples d α),
        ω.2 (medianBudget S.card d α + j) (referenceArm S hS d α hn ω)) /
          (referenceSamples d α : ℝ) := by
  unfold referenceEstimate referenceEstimateFromHistory
  congr 1
  exact Finset.sum_congr rfl (fun j _ => reference_observation_eq_reward S hS d α hn ω j)

theorem activeEstimate_eq_sampleMean {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (i : Fin n) (hi : i ∈ S) :
    activeEstimate S hS d α hn i ω =
      Gaussian.sampleMean (MedianPolicy.fixedObservation (m := activeSamples d α) S
        (activeStart S.card d α) i) ω := by
  unfold activeEstimate activeEstimateFromHistory Gaussian.sampleMean MedianPolicy.fixedObservation
  congr 1
  exact Finset.sum_congr rfl (fun j _ => active_observation_eq_reward S hS d α hn ω i hi j)

end GapEntropy.EliminationPolicy
