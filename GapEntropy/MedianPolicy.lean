import GapEntropy.MedianSchedule

/-!
# Median elimination as an actual interactive policy

The public parameters are an initial nonempty arm set and two budgets. The
policy reconstructs earlier completed rounds from its observed history, samples
the prescribed sorted arm block, and returns the terminal singleton. It reads
neither the input means nor unobserved reward-table coordinates.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.MedianPolicy
open MedianElimination

theorem exists_block {s : ℕ} {ε β : ℝ} {t : ℕ}
    (ht : t < declaredCost s ε β) : ∃ r, r < s ∧ t < start s ε β (r + 1) := by
  have hs : 0 < s := by
    by_contra hs
    have hz : s = 0 := by omega
    simp [hz, declaredCost] at ht
  refine ⟨s - 1, by omega, ?_⟩
  have he : s - 1 + 1 = s := by omega
  simpa only [he, start_terminal] using ht

def blockAt (s : ℕ) (ε β : ℝ) (t : ℕ) (ht : t < declaredCost s ε β) : ℕ :=
  Nat.find (exists_block ht)

theorem blockAt_lt (s : ℕ) (ε β : ℝ) (t : ℕ) (ht : t < declaredCost s ε β) :
    blockAt s ε β t ht < s := (Nat.find_spec (exists_block ht)).1

theorem blockAt_bounds (s : ℕ) (ε β : ℝ) (t : ℕ) (ht : t < declaredCost s ε β) :
    start s ε β (blockAt s ε β t ht) ≤ t ∧
      t < start s ε β (blockAt s ε β t ht + 1) := by
  refine ⟨?_, (Nat.find_spec (exists_block ht)).2⟩
  cases hr : blockAt s ε β t ht with
  | zero => simp [start]
  | succ r =>
      have hmin := Nat.find_min (exists_block ht) (show r < Nat.find (exists_block ht) by
        change r < blockAt s ε β t ht
        omega)
      have hrs := blockAt_lt s ε β t ht
      change ¬ (r < s ∧ t < start s ε β (r + 1)) at hmin
      omega

theorem blockAt_active (s : ℕ) (ε β : ℝ) (t : ℕ) (ht : t < declaredCost s ε β) :
    2 ≤ cardinalSchedule s (blockAt s ε β t ht) := by
  have hb := blockAt_bounds s ε β t ht
  by_contra hc
  simp only [start, blockSize, if_neg hc, Nat.add_zero] at hb
  omega

theorem blockAt_sample_pos (s : ℕ) (ε β : ℝ) (t : ℕ) (ht : t < declaredCost s ε β) :
    0 < roundSamples ε β (blockAt s ε β t ht) := by
  have hb := blockAt_bounds s ε β t ht
  have hc := blockAt_active s ε β t ht
  by_contra hm
  have hm0 : roundSamples ε β (blockAt s ε β t ht) = 0 := by omega
  simp only [start, blockSize, if_pos hc, hm0, Nat.mul_zero, Nat.add_zero] at hb
  omega

theorem blockAt_rank_lt (s : ℕ) (ε β : ℝ) (t : ℕ) (ht : t < declaredCost s ε β) :
    (t - start s ε β (blockAt s ε β t ht)) / roundSamples ε β (blockAt s ε β t ht) <
      cardinalSchedule s (blockAt s ε β t ht) := by
  have hb := blockAt_bounds s ε β t ht
  have hc := blockAt_active s ε β t ht
  apply (Nat.div_lt_iff_lt_mul (blockAt_sample_pos s ε β t ht)).mpr
  simp only [start, blockSize, if_pos hc] at hb
  omega

def historyValues {n t : ℕ} (h : History n t) (s : ℕ) : ℝ :=
  if hs : s < t then (h ⟨s, hs⟩).2 else 0

theorem measurable_historyValues {n t : ℕ} (s : ℕ) :
    Measurable (fun h : History n t => historyValues h s) := by
  unfold historyValues
  split_ifs with hs
  · exact measurable_snd.comp (measurable_pi_apply (⟨s, hs⟩ : Fin t))
  · exact measurable_const

def requestedFromHistory {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (t : ℕ) (ht : t < declaredCost S.card ε β) (h : History n t) : Fin n :=
  let r := blockAt S.card ε β t ht
  armAt (S.min' hS) (reconstruct S ε β (historyValues h) r)
    ((t - start S.card ε β r) / roundSamples ε β r)

def outputFromHistory {n t : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (h : History n t) : Fin n :=
  selectedArm (S.min' hS) (reconstruct S ε β (historyValues h) S.card)

theorem measurable_requestedFromHistory {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (t : ℕ) (ht : t < declaredCost S.card ε β) :
    Measurable (requestedFromHistory S hS ε β t ht) := by
  exact (measurable_of_finite (fun U : Finset (Fin n) => armAt (S.min' hS) U
    ((t - start S.card ε β (blockAt S.card ε β t ht)) /
      roundSamples ε β (blockAt S.card ε β t ht)))).comp
    (reconstruct_measurable S ε β measurable_historyValues _)

theorem measurable_outputFromHistory {n t : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) : Measurable (outputFromHistory (t := t) S hS ε β) :=
  (measurable_of_finite (selectedArm (S.min' hS))).comp
    (reconstruct_measurable S ε β measurable_historyValues S.card)

/-- The policy's only inputs besides history are its visible active set and budgets. -/
def policy {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (ε β : ℝ) : Policy n where
  choose _ t p := if ht : t < declaredCost S.card ε β then
    .inl (requestedFromHistory S hS ε β t ht p.2)
    else .inr (outputFromHistory S hS ε β p.2)
  measurable_choose _ t := by
    by_cases ht : t < declaredCost S.card ε β
    · simpa only [dif_pos ht, Function.comp_def] using
        measurable_inl.comp ((measurable_requestedFromHistory S hS ε β t ht).comp measurable_snd)
    · simpa only [dif_neg ht, Function.comp_def] using
        measurable_inr.comp ((measurable_outputFromHistory S hS ε β).comp measurable_snd)

theorem requestedFromHistory_mem {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (t : ℕ) (ht : t < declaredCost S.card ε β) (h : History n t) :
    requestedFromHistory S hS ε β t ht h ∈
      reconstruct S ε β (historyValues h) (blockAt S.card ε β t ht) := by
  apply armAt_mem
  rw [reconstruct_card]
  exact blockAt_rank_lt S.card ε β t ht

theorem outputFromHistory_eq_medianEliminate {n t : ℕ} (S : Finset (Fin n))
    (hS : S.Nonempty) (ε β : ℝ) (h : History n t) :
    outputFromHistory S hS ε β h =
      medianEliminate S hS (estimates S ε β (historyValues h)) := by
  simp only [outputFromHistory, medianEliminate, reconstruct_eq_activeSets]

theorem outputFromHistory_mem {n t : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (h : History n t) : outputFromHistory S hS ε β h ∈ S :=
  (reconstruct_subset S ε β _ _)
    (selectedArm_mem _ (reconstruct_nonempty hS ε β _ _))

theorem run_active_before_budget {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ)
    (ht : t ≤ declaredCost S.card ε β) :
    ∃ h, (policy S hS ε β).run hn ω t = .inr h := by
  induction t with
  | zero => exact ⟨Fin.elim0, rfl⟩
  | succ t ih =>
      obtain ⟨h, hh⟩ := ih (by omega)
      have ht' : t < declaredCost S.card ε β := by omega
      refine ⟨Fin.snoc h (requestedFromHistory S hS ε β t ht' h,
        ω.2 t (requestedFromHistory S hS ε β t ht' h)), ?_⟩
      simp only [Policy.run_succ, Policy.step, hh, Sum.elim_inr]
      simp [policy, ht']

def historyAt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (ε β : ℝ)
    (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) : History n t :=
  ((policy S hS ε β).run hn ω t).elim (fun _ _ => (S.min' hS, 0)) id

theorem measurable_historyAt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (ε β : ℝ)
    (hn : 2 ≤ n) (t : ℕ) : Measurable (historyAt S hS ε β hn t) :=
  (measurable_const.sumElim measurable_id).comp ((policy S hS ε β).measurable_run hn t)

theorem run_eq_historyAt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ)
    (ht : t ≤ declaredCost S.card ε β) :
    (policy S hS ε β).run hn ω t = .inr (historyAt S hS ε β hn t ω) := by
  obtain ⟨h, hh⟩ := run_active_before_budget S hS ε β hn ω t ht
  simp only [historyAt, hh, Sum.elim_inr, id_eq]

def completedHistory {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) : History n (declaredCost S.card ε β) :=
  historyAt S hS ε β hn (declaredCost S.card ε β) ω

theorem run_return_at_budget {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy S hS ε β).returnedAt hn (declaredCost S.card ε β + 1) ω =
      some (outputFromHistory S hS ε β (completedHistory S hS ε β hn ω)) := by
  have hh := run_eq_historyAt S hS ε β hn ω (declaredCost S.card ε β) le_rfl
  simp only [Policy.returnedAt, Policy.run_succ, Policy.step, hh, Sum.elim_inr]
  simp [policy, completedHistory]

theorem sampleIndicator_eq_one_before_budget {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ)
    (ht : t < declaredCost S.card ε β) : (policy S hS ε β).sampleIndicator hn t ω = 1 := by
  obtain ⟨h, hh⟩ := run_active_before_budget S hS ε β hn ω t ht.le
  simp only [Policy.sampleIndicator, Policy.sampleRequested, Policy.requestedArm, hh, Sum.elim_inr]
  simp [policy, ht]

/-- Every path uses exactly the public declared budget, including atypical samples. -/
theorem sampleCount_eq_declaredCost {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy S hS ε β).sampleCount hn ω = declaredCost S.card ε β := by
  rw [(policy S hS ε β).sampleCount_eq_truncatedSamples_of_returned hn ω _
    (run_return_at_budget S hS ε β hn ω), Policy.truncatedSamples_succ]
  have hh := run_eq_historyAt S hS ε β hn ω (declaredCost S.card ε β) le_rfl
  have hz : (policy S hS ε β).sampleIndicator hn (declaredCost S.card ε β) ω = 0 := by
    simp only [Policy.sampleIndicator, Policy.sampleRequested, Policy.requestedArm, hh, Sum.elim_inr]
    simp [policy]
  rw [hz, add_zero, Policy.truncatedSamples]
  have he : ∑ t ∈ Finset.range (declaredCost S.card ε β),
      (policy S hS ε β).sampleIndicator hn t ω =
      ∑ _t ∈ Finset.range (declaredCost S.card ε β), (1 : ℝ≥0∞) :=
    Finset.sum_congr rfl (fun t ht =>
      sampleIndicator_eq_one_before_budget S hS ε β hn ω t (Finset.mem_range.mp ht))
  simpa using he

end GapEntropy.MedianPolicy
