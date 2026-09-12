import GapEntropy.EliminationPolicyBlock
import GapEntropy.ProcedureSimulation

/-!
# BoundedProcedure wrappers for actual raw and padded elimination

The request functions and set readouts are precisely those of the proved actual
elimination sampler. Their finite-table evaluations agree pointwise with its
finite-block output, so the Gaussian A.3 guarantees transfer exactly.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Classical

namespace GapEntropy.EliminationPolicy
open GaussianBlocks

def rawProcedure {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (d α : ℝ)
    (_hn : 2 ≤ n) : BoundedProcedure n (Finset (Fin n)) where
  budget := budget S.card d α
  request t _ := requestedFromHistory S hS d α t
  measurable_request t _ := measurable_requestedFromHistory S hS d α t
  output := rawOutputFromHistory S hS d α
  measurable_output := measurable_rawOutputFromHistory S hS d α

def paddedProcedure {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (d α : ℝ)
    (_hn : 2 ≤ n) : BoundedProcedure n (Finset (Fin n)) where
  budget := budget S.card d α
  request t _ := requestedFromHistory S hS d α t
  measurable_request t _ := measurable_requestedFromHistory S hS d α t
  output := paddedOutputFromHistory S hS d α
  measurable_output := measurable_paddedOutputFromHistory S hS d α

theorem rewardBlock_sampleFromBlock {n : ℕ} (B : ℕ) (v : Fin B → Fin n → ℝ) :
    rewardBlock 0 B (sampleFromBlock B v) = v := by
  funext j
  simp [rewardBlock, sampleFromBlock, extendPrefix, j.isLt]

theorem rawProcedure_simulate_eq_completed {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (v : Fin (budget S.card d α) → Fin n → ℝ) :
    (rawProcedure S hS d α hn).simulate v (budget S.card d α) le_rfl =
      completedHistory S hS d α hn (sampleFromBlock (budget S.card d α) v) := by
  have hr := (rawProcedure S hS d α hn).run_eq_simulate_of_requests (policy S hS d α) hn
    (sampleFromBlock (budget S.card d α) v) (budget S.card d α) le_rfl
    (fun t ht h => by simp only [policy, if_pos ht, rawProcedure])
  change (policy S hS d α).run hn (sampleFromBlock (budget S.card d α) v) (budget S.card d α) =
    Sum.inr ((rawProcedure S hS d α hn).simulate
      (rewardBlock 0 (budget S.card d α) (sampleFromBlock (budget S.card d α) v))
      (budget S.card d α) le_rfl) at hr
  rw [rewardBlock_sampleFromBlock] at hr
  have hh := run_eq_historyAt S hS d α hn (sampleFromBlock (budget S.card d α) v)
    (budget S.card d α) le_rfl
  exact Sum.inr.inj (hr.symm.trans hh)

theorem paddedProcedure_simulate_eq_raw {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (v : Fin (budget S.card d α) → Fin n → ℝ)
    (t : ℕ) (ht : t ≤ budget S.card d α) :
    (paddedProcedure S hS d α hn).simulate v t ht =
      (rawProcedure S hS d α hn).simulate v t ht :=
  BoundedProcedure.simulate_congr_of_requests (paddedProcedure S hS d α hn)
    (rawProcedure S hS d α hn) v v t ht ht (fun _ _ => rfl) (fun _ _ _ => rfl)

theorem rawProcedure_evaluate_eq {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) :
    (rawProcedure S hS d α hn).evaluate = rawOutputFromBlock S hS d α hn := by
  funext v
  exact congrArg (rawOutputFromHistory S hS d α)
    (rawProcedure_simulate_eq_completed S hS d α hn v)

theorem paddedProcedure_evaluate_eq {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) :
    (paddedProcedure S hS d α hn).evaluate = paddedOutputFromBlock S hS d α hn := by
  funext v
  exact congrArg (paddedOutputFromHistory S hS d α)
    ((paddedProcedure_simulate_eq_raw S hS d α hn v (budget S.card d α) le_rfl).trans
      (rawProcedure_simulate_eq_completed S hS d α hn v))

theorem rawProcedure_actualOutput_eq {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) :
    (rawProcedure S hS d α hn).actualOutput = rawOutput S hS d α hn := by
  funext ω
  change (rawProcedure S hS d α hn).evaluate (rewardBlock 0 (budget S.card d α) ω) = _
  rw [rawProcedure_evaluate_eq]
  exact (rawOutput_eq_fromBlock S hS d α hn ω).symm

theorem paddedProcedure_actualOutput_eq {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) :
    (paddedProcedure S hS d α hn).actualOutput = paddedOutput S hS d α hn := by
  funext ω
  change (paddedProcedure S hS d α hn).evaluate (rewardBlock 0 (budget S.card d α) ω) = _
  rw [paddedProcedure_evaluate_eq]
  exact (paddedOutput_eq_fromBlock S hS d α hn ω).symm

theorem rawProcedure_evaluate_subset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (v : (rawProcedure S hS d α hn).Tape) :
    (rawProcedure S hS d α hn).evaluate v ⊆ S :=
  Elimination.raw_subset _ _ _ _

theorem paddedProcedure_evaluate_subset {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (v : (paddedProcedure S hS d α hn).Tape) :
    (paddedProcedure S hS d α hn).evaluate v ⊆ S :=
  Elimination.padded_subset _ _ _ _

theorem paddedProcedure_evaluate_nonempty {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (v : (paddedProcedure S hS d α hn).Tape) :
    ((paddedProcedure S hS d α hn).evaluate v).Nonempty := by
  apply Finset.card_pos.mp
  have hhalf := Elimination.padded_card_ge_half S
    (activeEstimateFromHistory S d α ((paddedProcedure S hS d α hn).simulate v _ le_rfl))
    (referenceEstimateFromHistory S d α ((paddedProcedure S hS d α hn).simulate v _ le_rfl)) d
  change (S.card + 1) / 2 ≤ ((paddedProcedure S hS d α hn).evaluate v).card at hhalf
  have hp := hS.card_pos
  omega

variable {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (hn : 2 ≤ n) (mean : Fin n → ℝ)
  {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, mean i ≤ mean best)
  {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1)

include hbest hmax hd hα hα1

theorem rawProcedure_best_failure :
    (blockLaw mean (budget S.card d α)).real
      {v | best ∉ (rawProcedure S hS d α hn).evaluate v} ≤ α := by
  rw [rawProcedure_evaluate_eq]
  exact rawBlock_best_failure S hS hn mean hbest hmax hd hα hα1

theorem paddedProcedure_best_failure :
    (blockLaw mean (budget S.card d α)).real
      {v | best ∉ (paddedProcedure S hS d α hn).evaluate v} ≤ α := by
  rw [paddedProcedure_evaluate_eq]
  exact paddedBlock_best_failure S hS hn mean hbest hmax hd hα hα1

theorem rawProcedure_large_failure {N : ℕ}
    (hnear : (Elimination.near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (blockLaw mean (budget S.card d α)).real
      {v | best ∉ (rawProcedure S hS d α hn).evaluate v ∨
        (S.card + 1) / 2 < ((rawProcedure S hS d α hn).evaluate v).card} ≤ α := by
  rw [rawProcedure_evaluate_eq]
  exact rawBlock_large_failure S hS hn mean hbest hmax hd hα hα1 hnear hs

theorem paddedProcedure_large_failure {N : ℕ}
    (hnear : (Elimination.near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (blockLaw mean (budget S.card d α)).real
      {v | best ∉ (paddedProcedure S hS d α hn).evaluate v ∨
        ((paddedProcedure S hS d α hn).evaluate v).card ≠ (S.card + 1) / 2} ≤ α := by
  rw [paddedProcedure_evaluate_eq]
  exact paddedBlock_large_failure S hS hn mean hbest hmax hd hα hα1 hnear hs

theorem rawProcedure_small_failure (hs : S.card ≤ 4)
    (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    (blockLaw mean (budget S.card d α)).real
      {v | (rawProcedure S hS d α hn).evaluate v ≠ {best}} ≤ α := by
  rw [rawProcedure_evaluate_eq]
  exact rawBlock_small_failure S hS hn mean hbest hmax hd hα hα1 hs hgaps

theorem paddedProcedure_small_failure (hs : S.card ≤ 4)
    (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    (blockLaw mean (budget S.card d α)).real
      {v | best ∉ (paddedProcedure S hS d α hn).evaluate v ∨
        ((paddedProcedure S hS d α hn).evaluate v).card ≠ (S.card + 1) / 2} ≤ α := by
  rw [paddedProcedure_evaluate_eq]
  exact paddedBlock_small_failure S hS hn mean hbest hmax hd hα hα1 hs hgaps

end GapEntropy.EliminationPolicy
