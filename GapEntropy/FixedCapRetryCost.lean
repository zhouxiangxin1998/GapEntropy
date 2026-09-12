import GapEntropy.FixedCapRetryTrace
import GapEntropy.RetryExperiment

/-! Pathwise cost accounting for the actual fixed-cap retry policy, including infinite runs. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.FixedCapRetry
variable {n : ℕ} (R : ℕ → BoundedProcedure n (Option (Fin n)))
  (hpos : ∀ j, 0 < (R j).budget)

local instance : MeasurableSingletonClass (Option (Fin n)) := ⟨fun _ => trivial⟩

def reach (j : ℕ) : Set (SampleSpace n) := {ω | ∀ k < j, answer R hpos k ω = none}

theorem measurableSet_reach (j : ℕ) : MeasurableSet (reach R hpos j) :=
  (Measurable.forall fun k => Measurable.forall fun _hk =>
    (measurable_answer R hpos k).eq_const none).setOf

/-- Requesting any sample in block `j` requires all previous attempt readouts to
be aborts. In particular no subsequent block is charged after an earlier answer. -/
theorem sampleRequested_imp_reach (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ)
    (hsample : (policy R hpos).sampleRequested hn t ω) :
    ω ∈ reach R hpos (currentIndex R hpos t) := by
  cases hr : (policy R hpos).run hn ω t with
  | inl i => simp [Policy.sampleRequested, Policy.requestedArm, hr] at hsample
  | inr h =>
      cases hd : (policy R hpos).choose hn t (ω.1, h) with
      | inr i => simp [Policy.sampleRequested, Policy.requestedArm, hr, hd] at hsample
      | inl i =>
          have hh : (policy R hpos).run hn ω (t + 1) = .inr (Fin.snoc h (i, ω.2 t i)) := by
            simp only [Policy.run_succ, Policy.step, hr, Sum.elim_inr, hd, Sum.elim_inl]
          have hc := ((policy R hpos).run_eq_active_iff_historyConsistent hn ω (t + 1) _).mp hh
          intro k hk
          have hbefore : (schedule R hpos).start (k + 1) ≤ t :=
            ((schedule R hpos).start_strictMono.monotone (show k + 1 ≤ currentIndex R hpos t by
              omega)).trans ((schedule R hpos).start_index_le t)
          exact answer_none_of_consistent_after_end R hpos hn ω _ hc k (by omega)

def cappedCharge (j : ℕ) (ω : SampleSpace n) : ℝ≥0∞ :=
  (reach R hpos j).indicator (fun _ => ((R j).budget : ℝ≥0∞)) ω

theorem measurable_cappedCharge (j : ℕ) : Measurable (cappedCharge R hpos j) :=
  measurable_const.indicator (measurableSet_reach R hpos j)

theorem block_cost_le_charge (hn : 2 ≤ n) (ω : SampleSpace n) (j : ℕ) :
    (∑ s : Fin (R j).budget,
      (policy R hpos).sampleIndicator hn ((schedule R hpos).start j + s) ω) ≤
      cappedCharge R hpos j ω := by
  by_cases hr : ω ∈ reach R hpos j
  · simp only [cappedCharge, Set.indicator_of_mem hr]
    calc
      (∑ s : Fin (R j).budget,
        (policy R hpos).sampleIndicator hn ((schedule R hpos).start j + s) ω) ≤
          ∑ _s : Fin (R j).budget, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum (fun _ _ => (policy R hpos).sampleIndicator_le_one hn _ ω)
      _ = _ := by simp
  · simp only [cappedCharge, Set.indicator_of_notMem hr, nonpos_iff_eq_zero]
    apply Finset.sum_eq_zero
    intro s _
    have hnot : ¬ (policy R hpos).sampleRequested hn ((schedule R hpos).start j + s) ω := by
      intro hs
      have h := sampleRequested_imp_reach R hpos hn ω _ hs
      rw [currentIndex_start_add R hpos j s s.isLt] at h
      exact hr h
    simp only [Policy.sampleIndicator, if_neg hnot]

/-- Full actual count versus reached complete-call charges. No termination or
finite expectation is assumed, and infinite executions are retained as infinity. -/
theorem sampleCount_le_charges (hn : 2 ≤ n) (ω : SampleSpace n) :
    (policy R hpos).sampleCount hn ω ≤ ∑' j, cappedCharge R hpos j ω := by
  rw [Policy.sampleCount, (schedule R hpos).tsum_eq_blocks]
  exact ENNReal.tsum_le_tsum (fun j => block_cost_le_charge R hpos hn ω j)

/-- The actual reach event is the preimage of the canonical independent-attempt reach event. -/
theorem reach_eq_preimage (j : ℕ) :
    reach R hpos j = blocks R hpos ⁻¹'
      RetryExperiment.reach (fun k => (R k).evaluate) j := rfl

/-- Tonelli turns the pathwise bound into a sum of unconditional reached charges. -/
theorem expectedSamples_le_reach_sum (I : Instance n) :
    (policy R hpos).expectedSamples I ≤
      ∑' j, ((R j).budget : ℝ≥0∞) * sampleLaw I (reach R hpos j) := by
  apply (lintegral_mono (sampleCount_le_charges R hpos I.two_le)).trans_eq
  rw [lintegral_tsum (fun j => (measurable_cappedCharge R hpos j).aemeasurable)]
  congr 1
  funext j
  exact lintegral_indicator_const (measurableSet_reach R hpos j) _

/-- The actual stream reach probability is exactly the product of its complete
private block abort probabilities. -/
theorem measure_reach_eq_prod (mean : Fin n → ℝ) (j : ℕ) :
    sampleLawOfMeans mean (reach R hpos j) =
      ∏ k ∈ Finset.range j, GaussianBlocks.blockLaw mean (R k).budget
        {x | (R k).evaluate x = none} := by
  rw [reach_eq_preimage]
  have hm := (schedule R hpos).measurePreserving_blocks mean
  change sampleLawOfMeans mean ((schedule R hpos).blocks ⁻¹' _) = _
  rw [hm.measure_preimage
    (RetryExperiment.measurableSet_reach (fun k => (R k).evaluate)
      (fun k => (R k).measurable_evaluate) j).nullMeasurableSet]
  exact RetryExperiment.measure_reach (fun k => GaussianBlocks.blockLaw mean (R k).budget)
    (fun k => (R k).evaluate) (fun k => (R k).measurable_evaluate) j

end GapEntropy.FixedCapRetry
