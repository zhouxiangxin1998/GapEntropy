import GapEntropy.MedianPolicy

/-!
# Actual median-policy trace and round observations

Every prefix of the completed history is the corresponding actual active run.
The round reconstruction is stable under later observations. Thus the recorded
samples in an active arm's block are exactly that arm's actual reward-table
coordinates, and the returned label is the existing median recursion's output.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.MedianPolicy
open MedianElimination

theorem blockAt_eq_of_bounds (s : ℕ) (ε β : ℝ) (t : ℕ) (ht : t < declaredCost s ε β)
    {r : ℕ} (hrs : r < s) (hlo : start s ε β r ≤ t) (hhi : t < start s ε β (r + 1)) :
    blockAt s ε β t ht = r := by
  have hle : blockAt s ε β t ht ≤ r := Nat.find_le ⟨hrs, hhi⟩
  by_contra he
  have hlt : blockAt s ε β t ht + 1 ≤ r := by omega
  have hmono := start_mono s ε β hlt
  have hb := (blockAt_bounds s ε β t ht).2
  omega

theorem historyValues_prefix {n T : ℕ} (h : History n T) (t : ℕ) (ht : t ≤ T)
    (s : ℕ) (hs : s < t) :
    historyValues (Policy.historyPrefix h t ht) s = historyValues h s := by
  simp only [historyValues, dif_pos hs, dif_pos (hs.trans_le ht), Policy.historyPrefix]

theorem reconstruct_historyPrefix {n T : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty)
    (ε β : ℝ) (h : History n T) (t : ℕ) (ht : t ≤ T) (r : ℕ)
    (hr : start S.card ε β r ≤ t) :
    reconstruct S ε β (historyValues (Policy.historyPrefix h t ht)) r =
      reconstruct S ε β (historyValues h) r :=
  reconstruct_congr_before hS ε β r (fun s hs => historyValues_prefix h t ht s (hs.trans_le hr))

theorem completedHistory_consistent {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy S hS ε β).historyConsistent hn ω (declaredCost S.card ε β)
      (completedHistory S hS ε β hn ω) :=
  ((policy S hS ε β).run_eq_active_iff_historyConsistent hn ω _ _).mp
    (run_eq_historyAt S hS ε β hn ω _ le_rfl)

theorem run_prefix_completedHistory {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ)
    (ht : t ≤ declaredCost S.card ε β) :
    (policy S hS ε β).run hn ω t =
      .inr (Policy.historyPrefix (completedHistory S hS ε β hn ω) t ht) :=
  ((policy S hS ε β).run_eq_active_iff_historyConsistent hn ω _ _).mpr
    ((policy S hS ε β).historyConsistent_prefix hn ω _
      (completedHistory_consistent S hS ε β hn ω) t ht)

/-- A request in the actual run is the sorted active-arm block determined by
the median recursion on the complete observed rewards. Future observations do
not change the reconstructed active set used for this request. -/
theorem requestedArm_eq_from_completed {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ)
    (ht : t < declaredCost S.card ε β) :
    (policy S hS ε β).requestedArm hn t ω =
      some (armAt (S.min' hS)
        (reconstruct S ε β (historyValues (completedHistory S hS ε β hn ω))
          (blockAt S.card ε β t ht))
        ((t - start S.card ε β (blockAt S.card ε β t ht)) /
          roundSamples ε β (blockAt S.card ε β t ht))) := by
  rw [Policy.requestedArm, run_prefix_completedHistory S hS ε β hn ω t ht.le]
  simp only [Sum.elim_inr, policy, dif_pos ht, Sum.elim_inl, requestedFromHistory]
  rw [reconstruct_historyPrefix hS ε β _ t ht.le _ (blockAt_bounds S.card ε β t ht).1]

theorem completedHistory_observation {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ)
    (ht : t < declaredCost S.card ε β) :
    let i := armAt (S.min' hS)
      (reconstruct S ε β (historyValues (completedHistory S hS ε β hn ω))
        (blockAt S.card ε β t ht))
      ((t - start S.card ε β (blockAt S.card ε β t ht)) /
        roundSamples ε β (blockAt S.card ε β t ht))
    (completedHistory S hS ε β hn ω) ⟨t, ht⟩ = (i, ω.2 t i) := by
  have hd := (policy S hS ε β).historyConsistent_decision hn ω _
    (completedHistory_consistent S hS ε β hn ω) t ht
  have hreq : (policy S hS ε β).requestedArm hn t ω =
      some ((completedHistory S hS ε β hn ω) ⟨t, ht⟩).1 := by
    simp only [Policy.requestedArm, run_prefix_completedHistory S hS ε β hn ω t ht.le,
      Sum.elim_inr, hd.1, Sum.elim_inl]
  have hi := Option.some.inj (hreq.symm.trans (requestedArm_eq_from_completed S hS ε β hn ω t ht))
  apply Prod.ext hi
  exact hd.2.trans (congrArg (ω.2 t) hi)

/-- For an active arm, each reconstructed observation is precisely a real
sample requested at its prescribed original reward-table row. -/
theorem round_observation_eq_reward {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) (r : ℕ) (hrs : r < S.card)
    (hr : 2 ≤ cardinalSchedule S.card r) (i : Fin n)
    (hi : i ∈ reconstruct S ε β (historyValues (completedHistory S hS ε β hn ω)) r)
    (j : Fin (roundSamples ε β r)) :
    let U := reconstruct S ε β (historyValues (completedHistory S hS ε β hn ω)) r
    let t := start S.card ε β r + armRank U i * roundSamples ε β r + j
    historyValues (completedHistory S hS ε β hn ω) t = ω.2 t i := by
  let y := historyValues (completedHistory S hS ε β hn ω)
  let U := reconstruct S ε β y r
  let t := start S.card ε β r + armRank U i * roundSamples ε β r + j
  have hupper : t < start S.card ε β (r + 1) := block_index_lt hS ε β y r hr i j
  have ht : t < declaredCost S.card ε β := by
    rw [← start_terminal]
    exact hupper.trans_le (start_mono S.card ε β (by omega))
  have hb : blockAt S.card ε β t ht = r :=
    blockAt_eq_of_bounds S.card ε β t ht hrs (by dsimp [t]; omega) hupper
  have hm : 0 < roundSamples ε β r := by have := j.isLt; omega
  have hdiv : (t - start S.card ε β r) / roundSamples ε β r = armRank U i := by
    dsimp [t]
    rw [Nat.add_assoc, Nat.add_sub_cancel_left]
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt j.isLt, zero_add]
  have ho := congrArg Prod.snd (completedHistory_observation S hS ε β hn ω t ht)
  simp only [hb, hdiv] at ho
  have hai : armAt (S.min' hS) U (armRank U i) = i := armAt_armRank _ hi
  change (completedHistory S hS ε β hn ω ⟨t, ht⟩).2 =
    ω.2 t (armAt (S.min' hS) U (armRank U i)) at ho
  rw [hai] at ho
  change y t = ω.2 t i
  simpa only [y, historyValues, dif_pos ht] using ho

/-- The label returned by the actual policy is exactly the existing median
elimination recursion evaluated on the actual completed observations. -/
theorem returned_eq_medianEliminate {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy S hS ε β).returnedAt hn (declaredCost S.card ε β + 1) ω =
      some (medianEliminate S hS
        (estimates S ε β (historyValues (completedHistory S hS ε β hn ω)))) := by
  rw [run_return_at_budget, outputFromHistory_eq_medianEliminate]

theorem expectedSamples_eq_declaredCost {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (I : Instance n) :
    (policy S hS ε β).expectedSamples I = declaredCost S.card ε β := by
  simp only [Policy.expectedSamples, sampleCount_eq_declaredCost, lintegral_const,
    measure_univ, mul_one]

theorem sampleCount_le_A2_bound {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    {ε β : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy S hS ε β).sampleCount hn ω ≤
      ENNReal.ofReal (100000 * (S.card : ℝ) * (ε ^ 2)⁻¹ * Real.log (8 / β)) := by
  rw [sampleCount_eq_declaredCost, ← ENNReal.ofReal_natCast]
  exact ENNReal.ofReal_le_ofReal (declaredCost_le hS.card_pos hε hε1 hβ hβ1)

end GapEntropy.MedianPolicy
