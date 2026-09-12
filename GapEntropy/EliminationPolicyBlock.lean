import GapEntropy.EliminationPolicyA3
import GapEntropy.StoppedBlocks

/-!
# Finite block readouts for compiling actual elimination calls

The input is exactly the finite table covering the charged budget. No seed is
needed. The readouts have the same law as the actual policy's completed-history
outputs, and satisfy A.3 under the finite Gaussian block law.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Classical

namespace GapEntropy.EliminationPolicy
open GaussianBlocks

theorem run_congr_rows {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (d α : ℝ)
    (hn : 2 ≤ n) (t : ℕ) {ω ω' : SampleSpace n}
    (hrows : ∀ s < t, ω.2 s = ω'.2 s) :
    (policy S hS d α).run hn ω t = (policy S hS d α).run hn ω' t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Policy.run_succ, Policy.run_succ, ih (fun s hs => hrows s (by omega))]
      cases hr : (policy S hS d α).run hn ω' t with
      | inl i => simp only [Policy.step, Sum.elim_inl]
      | inr h =>
          simp only [Policy.step, Sum.elim_inr]
          simp only [policy, hrows t (Nat.lt_succ_self t)]

def sampleFromBlock {n : ℕ} (B : ℕ) (v : Fin B → Fin n → ℝ) : SampleSpace n :=
  extendPrefix B ((fun _ => 0), v)

theorem measurable_sampleFromBlock {n : ℕ} (B : ℕ) :
    Measurable (sampleFromBlock (n := n) B) :=
  (measurable_extendPrefix B).comp (measurable_const.prodMk measurable_id)

def rawOutputFromBlock {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (v : Fin (budget S.card d α) → Fin n → ℝ) : Finset (Fin n) :=
  rawOutput S hS d α hn (sampleFromBlock (budget S.card d α) v)

def paddedOutputFromBlock {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (v : Fin (budget S.card d α) → Fin n → ℝ) : Finset (Fin n) :=
  paddedOutput S hS d α hn (sampleFromBlock (budget S.card d α) v)

theorem measurable_rawOutputFromBlock {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) : Measurable (rawOutputFromBlock S hS d α hn) :=
  (measurable_rawOutput S hS d α hn).comp (measurable_sampleFromBlock _)

theorem measurable_paddedOutputFromBlock {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) : Measurable (paddedOutputFromBlock S hS d α hn) :=
  (measurable_paddedOutput S hS d α hn).comp (measurable_sampleFromBlock _)

theorem run_eq_from_block {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy S hS d α).run hn ω (budget S.card d α) =
      (policy S hS d α).run hn
        (sampleFromBlock (budget S.card d α) (rewardBlock 0 (budget S.card d α) ω))
        (budget S.card d α) := by
  apply run_congr_rows S hS d α hn
  intro s hs
  simp [sampleFromBlock, extendPrefix, hs, rewardBlock]

theorem rawOutput_eq_fromBlock {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    rawOutput S hS d α hn ω =
      rawOutputFromBlock S hS d α hn (rewardBlock 0 (budget S.card d α) ω) := by
  unfold rawOutputFromBlock rawOutput completedHistory historyAt
  rw [run_eq_from_block S hS d α hn ω]

theorem paddedOutput_eq_fromBlock {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    paddedOutput S hS d α hn ω =
      paddedOutputFromBlock S hS d α hn (rewardBlock 0 (budget S.card d α) ω) := by
  unfold paddedOutputFromBlock paddedOutput completedHistory historyAt
  rw [run_eq_from_block S hS d α hn ω]

theorem rawOutput_event_real_eq_block {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (mean : Fin n → ℝ) (E : Set (Finset (Fin n))) :
    (sampleLawOfMeans mean).real {ω | rawOutput S hS d α hn ω ∈ E} =
      (blockLaw mean (budget S.card d α)).real {v | rawOutputFromBlock S hS d α hn v ∈ E} := by
  have hE := (measurable_rawOutputFromBlock S hS d α hn) (Set.toFinite E).measurableSet
  have h := (measurePreserving_rewardBlock mean 0 (budget S.card d α)).measureReal_preimage
    hE.nullMeasurableSet
  have he : {ω | rawOutput S hS d α hn ω ∈ E} =
      rewardBlock 0 (budget S.card d α) ⁻¹' {v | rawOutputFromBlock S hS d α hn v ∈ E} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, rawOutput_eq_fromBlock S hS d α hn ω]
  rwa [he]

theorem paddedOutput_event_real_eq_block {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α : ℝ) (hn : 2 ≤ n) (mean : Fin n → ℝ) (E : Set (Finset (Fin n))) :
    (sampleLawOfMeans mean).real {ω | paddedOutput S hS d α hn ω ∈ E} =
      (blockLaw mean (budget S.card d α)).real {v | paddedOutputFromBlock S hS d α hn v ∈ E} := by
  have hE := (measurable_paddedOutputFromBlock S hS d α hn) (Set.toFinite E).measurableSet
  have h := (measurePreserving_rewardBlock mean 0 (budget S.card d α)).measureReal_preimage
    hE.nullMeasurableSet
  have he : {ω | paddedOutput S hS d α hn ω ∈ E} =
      rewardBlock 0 (budget S.card d α) ⁻¹' {v | paddedOutputFromBlock S hS d α hn v ∈ E} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, paddedOutput_eq_fromBlock S hS d α hn ω]
  rwa [he]

variable {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (hn : 2 ≤ n) (mean : Fin n → ℝ)
  {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, mean i ≤ mean best)
  {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1)

include hbest hmax hd hα hα1

theorem rawBlock_best_failure :
    (blockLaw mean (budget S.card d α)).real {v | best ∉ rawOutputFromBlock S hS d α hn v} ≤ α := by
  have h := raw_best_failure S hS hn mean hbest hmax hd hα hα1
  exact (rawOutput_event_real_eq_block S hS d α hn mean {U | best ∉ U}) ▸ h

theorem paddedBlock_best_failure :
    (blockLaw mean (budget S.card d α)).real {v | best ∉ paddedOutputFromBlock S hS d α hn v} ≤ α := by
  have h := padded_best_failure S hS hn mean hbest hmax hd hα hα1
  exact (paddedOutput_event_real_eq_block S hS d α hn mean {U | best ∉ U}) ▸ h

theorem rawBlock_large_failure {N : ℕ}
    (hnear : (Elimination.near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (blockLaw mean (budget S.card d α)).real {v | best ∉ rawOutputFromBlock S hS d α hn v ∨
      (S.card + 1) / 2 < (rawOutputFromBlock S hS d α hn v).card} ≤ α := by
  have h := raw_large_failure S hS hn mean hbest hmax hd hα hα1 hnear hs
  exact (rawOutput_event_real_eq_block S hS d α hn mean
    {U | best ∉ U ∨ (S.card + 1) / 2 < U.card}) ▸ h

theorem paddedBlock_large_failure {N : ℕ}
    (hnear : (Elimination.near S mean (mean best) d).card ≤ N) (hs : 4 * N < S.card) :
    (blockLaw mean (budget S.card d α)).real {v | best ∉ paddedOutputFromBlock S hS d α hn v ∨
      (paddedOutputFromBlock S hS d α hn v).card ≠ (S.card + 1) / 2} ≤ α := by
  have h := padded_large_failure S hS hn mean hbest hmax hd hα hα1 hnear hs
  exact (paddedOutput_event_real_eq_block S hS d α hn mean
    {U | best ∉ U ∨ U.card ≠ (S.card + 1) / 2}) ▸ h

theorem rawBlock_small_failure (hs : S.card ≤ 4)
    (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    (blockLaw mean (budget S.card d α)).real {v | rawOutputFromBlock S hS d α hn v ≠ {best}} ≤ α := by
  have h := raw_small_failure S hS hn mean hbest hmax hd hα hα1 hs hgaps
  exact (rawOutput_event_real_eq_block S hS d α hn mean {U | U ≠ {best}}) ▸ h

theorem paddedBlock_small_failure (hs : S.card ≤ 4)
    (hgaps : ∀ i ∈ S, i ≠ best → d ≤ mean best - mean i) :
    (blockLaw mean (budget S.card d α)).real {v | best ∉ paddedOutputFromBlock S hS d α hn v ∨
      (paddedOutputFromBlock S hS d α hn v).card ≠ (S.card + 1) / 2} ≤ α := by
  have h := padded_small_failure S hS hn mean hbest hmax hd hα hα1 hs hgaps
  exact (paddedOutput_event_real_eq_block S hS d α hn mean
    {U | best ∉ U ∨ U.card ≠ (S.card + 1) / 2}) ▸ h

end GapEntropy.EliminationPolicy
