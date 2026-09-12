import GapEntropy.UniversalCall

/-! # Exact observations of the universal bounded primitives -/
noncomputable section
open MeasureTheory
open scoped BigOperators Classical
namespace GapEntropy.UniversalCall
open EliminationTape GaussianBlocks
variable {n : ℕ}

theorem completedHistory_requested {γ : Type*} [MeasurableSpace γ]
    (R : BoundedProcedure n γ) (ω : SampleSpace n) (t : ℕ) (ht : t < R.budget) :
    let H := completedHistory R ω
    let i := R.request t ht (Policy.historyPrefix H t ht.le)
    H ⟨t, ht⟩ = (i, ω.2 t i) := by
  have hd := R.simulate_decision (rewardBlock 0 R.budget ω) R.budget le_rfl t ht
  change R.request t ht (Policy.historyPrefix (completedHistory R ω) t ht.le) =
      (completedHistory R ω ⟨t, ht⟩).1 ∧
    (completedHistory R ω ⟨t, ht⟩).2 =
      rewardBlock 0 R.budget ω ⟨t, ht⟩ (completedHistory R ω ⟨t, ht⟩).1 at hd
  simp only [rewardBlock, Nat.zero_add] at hd
  exact Prod.ext hd.1.symm (hd.2.trans (congrArg (ω.2 t) hd.1.symm))

theorem entry_median_prefix (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (hn : 2 ≤ n) (ω : SampleSpace n) :
    Policy.historyPrefix (completedHistory (entryProcedure S hS d α β) ω)
      (medianBudget S.card d α) (medianBudget_le_entryBudget S.card d α β) =
      MedianPolicy.completedHistory S hS (d / 8) (α / 16) hn ω := by
  let R := entryProcedure S hS d α β
  have hr := R.run_eq_simulate_of_requests (MedianPolicy.policy S hS (d / 8) (α / 16)) hn ω
    (medianBudget S.card d α) (medianBudget_le_entryBudget S.card d α β)
    (fun t ht h => by
      have ht' : t < MedianElimination.declaredCost S.card (d / 8) (α / 16) := ht
      simp only [MedianPolicy.policy, R, entryProcedure, entryRequest, dif_pos ht, dif_pos ht'])
  have hm := MedianPolicy.run_eq_historyAt S hS (d / 8) (α / 16) hn ω
    (medianBudget S.card d α) le_rfl
  exact (R.simulate_prefix (rewardBlock 0 R.budget ω) R.budget le_rfl _
    (medianBudget_le_entryBudget S.card d α β)).trans (Sum.inr.inj (hr.symm.trans hm))

def referenceArm (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (ω : SampleSpace n) : Fin n :=
  referenceFromHistory S hS d α (completedHistory (entryProcedure S hS d α β) ω)

theorem referenceArm_eq_median (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (hn : 2 ≤ n) (ω : SampleSpace n) :
    referenceArm S hS d α β ω = EliminationPolicy.referenceArm S hS d α hn ω := by
  rw [EliminationPolicy.referenceArm_eq_median_output]
  have hp := EliminationPolicy.referenceFromHistory_prefix S hS d α
    (completedHistory (entryProcedure S hS d α β) ω) (medianBudget S.card d α)
    (medianBudget_le_entryBudget S.card d α β) le_rfl
  rw [entry_median_prefix S hS d α β hn ω] at hp
  exact hp.symm

theorem measurable_referenceArm (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ) :
    Measurable (referenceArm S hS d α β) :=
  (EliminationPolicy.measurable_referenceFromHistory S hS d α).comp
    (measurable_completedHistory _)

theorem referenceArm_mem (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (ω : SampleSpace n) : referenceArm S hS d α β ω ∈ S :=
  MedianPolicy.outputFromHistory_mem S hS _ _ _

def referenceEstimate (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (ω : SampleSpace n) : ℝ :=
  referenceEstimateFromHistory S d α β (completedHistory (entryProcedure S hS d α β) ω)

def entryEstimate (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (ω : SampleSpace n) (i : Fin n) : ℝ :=
  estimateFromHistory S (activeStart S.card d α β) (activeSamples d α)
    (completedHistory (entryProcedure S hS d α β) ω) i

def laterEstimate (S : Finset (Fin n)) (hS : S.Nonempty) (d α z : ℝ)
    (ω : SampleSpace n) (i : Fin n) : ℝ :=
  estimateFromHistory S 0 (activeSamples d α)
    (completedHistory (laterProcedure S hS d α z) ω) i

theorem reference_observation (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (ω : SampleSpace n) (j : Fin (referenceBudget d β)) :
    MedianPolicy.historyValues (completedHistory (entryProcedure S hS d α β) ω)
      (medianBudget S.card d α + j) =
      ω.2 (medianBudget S.card d α + j) (referenceArm S hS d α β ω) := by
  have ht : medianBudget S.card d α + j < entryBudget S.card d α β := by
    unfold entryBudget activeStart
    have := j.isLt
    omega
  have hnot : ¬ medianBudget S.card d α + j < medianBudget S.card d α := by omega
  have href : medianBudget S.card d α + j < activeStart S.card d α β :=
    Nat.add_lt_add_left j.isLt _
  have ho := congrArg Prod.snd (completedHistory_requested (entryProcedure S hS d α β) ω _ ht)
  simp only [entryProcedure, entryRequest, dif_neg hnot, if_pos href] at ho
  change (completedHistory (entryProcedure S hS d α β) ω ⟨_, ht⟩).2 =
    ω.2 (medianBudget S.card d α + j) (EliminationPolicy.referenceFromHistory S hS d α
      (Policy.historyPrefix (completedHistory (entryProcedure S hS d α β) ω)
        (medianBudget S.card d α + j) ht.le)) at ho
  have hp := EliminationPolicy.referenceFromHistory_prefix S hS d α
    (completedHistory (entryProcedure S hS d α β) ω) _ ht.le (Nat.le_add_right _ _)
  exact (show MedianPolicy.historyValues (completedHistory (entryProcedure S hS d α β) ω)
    (medianBudget S.card d α + j) = (completedHistory (entryProcedure S hS d α β) ω ⟨_, ht⟩).2
      from dif_pos ht).trans (ho.trans (congrArg (ω.2 (medianBudget S.card d α + j)) hp))

theorem referenceEstimate_eq_mean (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (ω : SampleSpace n) :
    referenceEstimate S hS d α β ω = EliminationPolicy.rawReferenceMean
      (rewardBlock (medianBudget S.card d α) (referenceBudget d β) ω)
      (referenceArm S hS d α β ω) := by
  unfold referenceEstimate referenceEstimateFromHistory EliminationPolicy.rawReferenceMean rewardBlock
  congr 1
  exact Finset.sum_congr rfl (fun j _ => reference_observation S hS d α β ω j)

theorem active_index_lt (S : Finset (Fin n)) (hS : S.Nonempty) (start m : ℕ)
    (i : Fin n) (j : Fin m) : start + MedianPolicy.armRank S i * m + j < start + S.card * m := by
  have hi := MedianPolicy.armRank_lt hS i
  have hm := Nat.mul_le_mul_right m hi
  have hj := j.isLt
  nlinarith

theorem entry_observation (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (ω : SampleSpace n) (i : Fin n) (hi : i ∈ S) (j : Fin (activeSamples d α)) :
    let t := activeStart S.card d α β + MedianPolicy.armRank S i * activeSamples d α + j
    MedianPolicy.historyValues (completedHistory (entryProcedure S hS d α β) ω) t = ω.2 t i := by
  let t := activeStart S.card d α β + MedianPolicy.armRank S i * activeSamples d α + j
  have ht : t < entryBudget S.card d α β := active_index_lt S hS _ _ i j
  have htact : ¬ t < activeStart S.card d α β := by dsimp [t]; omega
  have htmed : ¬ t < medianBudget S.card d α := by dsimp [t, activeStart]; omega
  have hm : 0 < activeSamples d α := by have := j.isLt; omega
  have hdiv : (t - activeStart S.card d α β) / activeSamples d α = MedianPolicy.armRank S i := by
    dsimp [t]
    rw [Nat.add_assoc, Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_mul_div_right _ _ hm,
      Nat.div_eq_of_lt j.isLt, zero_add]
  have ho := congrArg Prod.snd (completedHistory_requested (entryProcedure S hS d α β) ω t ht)
  simp only [entryProcedure, entryRequest, dif_neg htmed, if_neg htact, hdiv,
    MedianPolicy.armAt_armRank (S.min' hS) hi] at ho
  change MedianPolicy.historyValues _ t = ω.2 t i
  exact (dif_pos ht).trans ho

theorem later_observation (S : Finset (Fin n)) (hS : S.Nonempty) (d α z : ℝ)
    (ω : SampleSpace n) (i : Fin n) (hi : i ∈ S) (j : Fin (activeSamples d α)) :
    let t := MedianPolicy.armRank S i * activeSamples d α + j
    MedianPolicy.historyValues (completedHistory (laterProcedure S hS d α z) ω) t = ω.2 t i := by
  let t := MedianPolicy.armRank S i * activeSamples d α + j
  have ht : t < laterBudget S.card d α := by
    simpa only [Nat.zero_add, laterBudget, t] using active_index_lt S hS 0 (activeSamples d α) i j
  have hm : 0 < activeSamples d α := by have := j.isLt; omega
  have hdiv : t / activeSamples d α = MedianPolicy.armRank S i := by
    dsimp [t]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt j.isLt, zero_add]
  have ho := congrArg Prod.snd (completedHistory_requested (laterProcedure S hS d α z) ω t ht)
  simp only [laterProcedure, laterRequest, hdiv, MedianPolicy.armAt_armRank (S.min' hS) hi] at ho
  change MedianPolicy.historyValues _ t = ω.2 t i
  exact (dif_pos ht).trans ho

def scheduleEstimate (S : Finset (Fin n)) (start m : ℕ) (ω : SampleSpace n) (i : Fin n) : ℝ :=
  Gaussian.sampleMean (MedianPolicy.fixedObservation (m := m) S start i) ω

theorem entryEstimate_eq_schedule (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (ω : SampleSpace n) (i : Fin n) (hi : i ∈ S) :
    entryEstimate S hS d α β ω i =
      scheduleEstimate S (activeStart S.card d α β) (activeSamples d α) ω i := by
  unfold entryEstimate estimateFromHistory scheduleEstimate Gaussian.sampleMean MedianPolicy.fixedObservation
  congr 1
  exact Finset.sum_congr rfl (fun j _ => entry_observation S hS d α β ω i hi j)

theorem laterEstimate_eq_schedule (S : Finset (Fin n)) (hS : S.Nonempty) (d α z : ℝ)
    (ω : SampleSpace n) (i : Fin n) (hi : i ∈ S) :
    laterEstimate S hS d α z ω i = scheduleEstimate S 0 (activeSamples d α) ω i := by
  unfold laterEstimate estimateFromHistory scheduleEstimate Gaussian.sampleMean MedianPolicy.fixedObservation
  congr 1
  exact Finset.sum_congr rfl (fun j _ => by simpa only [Nat.zero_add] using later_observation S hS d α z ω i hi j)

end GapEntropy.UniversalCall
