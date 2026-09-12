import GapEntropy.MedianPolicyTrace
import GapEntropy.GaussianBlocks

/-!
# Fresh round blocks for the actual median policy

The current active set is a function of the seed and reward prefix ending at
the fixed round start. It is independent of a finite fresh Gaussian block.
Fixed-set estimates in that block have the genuine Gaussian sample laws.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.MedianPolicy
open MedianElimination GaussianBlocks

def activeAt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (ε β : ℝ)
    (hn : 2 ≤ n) (r : ℕ) (ω : SampleSpace n) : Finset (Fin n) :=
  reconstruct S ε β (historyValues (historyAt S hS ε β hn (start S.card ε β r) ω)) r

theorem measurable_activeAt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (ε β : ℝ)
    (hn : 2 ≤ n) (r : ℕ) : Measurable (activeAt S hS ε β hn r) :=
  reconstruct_measurable S ε β (fun t => (measurable_historyValues t).comp
    (measurable_historyAt S hS ε β hn (start S.card ε β r))) r

theorem activeAt_eq_fromPrefix {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) (ε β : ℝ)
    (hn : 2 ≤ n) (r : ℕ) (ω : SampleSpace n) :
    activeAt S hS ε β hn r ω = activeAt S hS ε β hn r
      (extendPrefix (start S.card ε β r) (seedPrefix (start S.card ε β r) ω)) := by
  unfold activeAt historyAt
  rw [(policy S hS ε β).run_eq_runFromPrefix hn (start S.card ε β r) ω]
  rfl

theorem indepFun_activeAt_rewardBlock {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (mean : Fin n → ℝ) (r m : ℕ) :
    IndepFun (activeAt S hS ε β hn r) (rewardBlock (start S.card ε β r) m)
      (sampleLawOfMeans mean) := by
  have h := (indepFun_seedPrefix_rewardBlock mean (start S.card ε β r) m).comp
    ((measurable_activeAt S hS ε β hn r).comp (measurable_extendPrefix _)) measurable_id
  convert! h using 1
  · funext ω
    exact activeAt_eq_fromPrefix S hS ε β hn r ω

theorem activeAt_eq_completed {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty)
    (ε β : ℝ) (hn : 2 ≤ n) (r : ℕ) (hr : r ≤ S.card) (ω : SampleSpace n) :
    activeAt S hS ε β hn r ω =
      reconstruct S ε β (historyValues (completedHistory S hS ε β hn ω)) r := by
  have ht : start S.card ε β r ≤ declaredCost S.card ε β := by
    rw [← start_terminal]
    exact start_mono S.card ε β hr
  have hh := Sum.inr.inj ((run_eq_historyAt S hS ε β hn ω _ ht).symm.trans
    (run_prefix_completedHistory S hS ε β hn ω _ ht))
  unfold activeAt
  rw [hh]
  exact reconstruct_historyPrefix hS ε β _ _ ht r le_rfl

theorem armRank_lt_n {n : ℕ} (hn : 2 ≤ n) (U : Finset (Fin n)) (i : Fin n) :
    armRank U i < n := by
  by_cases hU : U.Nonempty
  · exact (armRank_lt hU i).trans_le (by simpa using U.card_le_univ)
  · have hU0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    simpa [hU0, armRank] using (show 0 < n by omega)

def rawIndex {n m : ℕ} (hn : 2 ≤ n) (U : Finset (Fin n)) (i : Fin n) (j : Fin m) :
    Fin (n * m) :=
  ⟨armRank U i * m + j, by
    have hi := armRank_lt_n hn U i
    have hm := Nat.mul_le_mul_right m hi
    have hj := j.isLt
    nlinarith⟩

def rawMean {n m : ℕ} (hn : 2 ≤ n) (U : Finset (Fin n))
    (v : Fin (n * m) → Fin n → ℝ) (i : Fin n) : ℝ :=
  (∑ j : Fin m, v (rawIndex hn U i j) i) / (m : ℝ)

theorem measurable_rawMean {n m : ℕ} (hn : 2 ≤ n) (U : Finset (Fin n)) :
    Measurable (rawMean (m := m) hn U) := by
  apply measurable_pi_lambda
  intro i
  unfold rawMean
  fun_prop

def fixedObservation {n m : ℕ} (U : Finset (Fin n)) (t : ℕ)
    (i : Fin n) (j : Fin m) (ω : SampleSpace n) : ℝ :=
  ω.2 (t + armRank U i * m + j) i

theorem measurable_fixedObservation {n m : ℕ} (U : Finset (Fin n)) (t : ℕ)
    (i : Fin n) (j : Fin m) : Measurable (fixedObservation U t i j) := by
  unfold fixedObservation
  fun_prop

theorem fixedObservation_hasLaw {n m : ℕ} (U : Finset (Fin n)) (t : ℕ)
    (mean : Fin n → ℝ) (i : Fin n) (j : Fin m) :
    HasLaw (fixedObservation U t i j) (gaussianReal (mean i) 1) (sampleLawOfMeans mean) :=
  ⟨(measurable_fixedObservation U t i j).aemeasurable, sampleLawOfMeans_map_reward mean _ _⟩

theorem fixedObservation_independent {n m : ℕ} (U : Finset (Fin n)) (t : ℕ)
    (mean : Fin n → ℝ) (i : Fin n) :
    iIndepFun (fixedObservation (m := m) U t i) (sampleLawOfMeans mean) :=
  observations_independent mean i (t + armRank U i * m)

theorem rawMean_rewardBlock_eq_sampleMean {n m : ℕ} (hn : 2 ≤ n) (U : Finset (Fin n))
    (t : ℕ) (ω : SampleSpace n) :
    rawMean (m := m) hn U (rewardBlock t (n * m) ω) =
      fun i => Gaussian.sampleMean (fixedObservation (m := m) U t i) ω := by
  funext i
  simp only [rawMean, rewardBlock, rawIndex, Gaussian.sampleMean, fixedObservation, Nat.add_assoc]

/-- Each fixed active-set interpretation of the fresh block satisfies the exact
Gaussian one-round guarantee used by median elimination. -/
theorem rawMean_badNext_le {n : ℕ} (hn : 2 ≤ n) (S U : Finset (Fin n))
    (mean : Fin n → ℝ) {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (r : ℕ) :
    (sampleLawOfMeans mean).real
      ((fun ω => rawMean hn U (rewardBlock (start S.card ε β r)
        (n * roundSamples ε β r) ω)) ⁻¹' badNext mean (roundEpsilon ε r) U) ≤ roundBeta β r := by
  have he : (fun ω => rawMean hn U (rewardBlock (start S.card ε β r)
      (n * roundSamples ε β r) ω)) = fun ω i => Gaussian.sampleMean
        (fixedObservation (m := roundSamples ε β r) U (start S.card ε β r) i) ω := by
    funext ω
    exact rawMean_rewardBlock_eq_sampleMean hn U _ ω
  rw [he]
  exact gaussian_badNext_le (roundSamples_pos hε hβ hβ1 r)
    (roundEpsilon_pos hε r) (roundBeta_pos hβ r) ((roundBeta_le hβ.le r).trans hβ1)
    (roundSamples_budget ε β r) (measurable_fixedObservation U _)
    (fixedObservation_independent U _ mean) (fixedObservation_hasLaw U _ mean)

end GapEntropy.MedianPolicy
