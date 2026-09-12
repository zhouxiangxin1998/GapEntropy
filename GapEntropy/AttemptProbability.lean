import GapEntropy.AttemptBadEvents

/-!
# C.2 for the actual finite statistical attempt

All A.3 calls are canonical Gaussian product experiments. Their active sets are
chosen adaptively by the C.1 control flow. The independence needed to lift the
local bounds is proved from the finite past-coordinate dependency, and the local
probability bounds are the previously proved A.3 theorems. The `Policy` embedding
of this statistical experiment is a separate obligation.
-/

noncomputable section
open MeasureTheory

namespace GapEntropy.AttemptExperiment
open GapEntropy.TargetAttempt
variable {n : ℕ}

theorem response_correct_outside_removal (I J : Instance n) (ε : ℝ) (ω : Space I ε)
    (hω : ω ∉ allBad I (removalEvent I J ε)) {a : Fin n}
    (hret : response I J ε ω = some a) : a = J.best := by
  apply result_correct_of_protection (I := I) (f := loopOracle I J ε ω)
    (last := finalOracle I J ε ω) (best := J.best) (hret := hret)
  · intro k hk r hr S hreq hb
    by_contra hbad
    apply hω
    apply loop_subset_allBad I (removalEvent I J ε) hk hr
    change ω (.loop k r) ∈ removalBad I J ε (.loop k r)
      (request I J ε (.loop k r) ω)
    change ω (.loop k r) ∈ removalBad I J ε (.loop k r)
      (loopRequest I (loopOracle I J ε ω) k r)
    rw [hreq]
    simpa only [removalBad, if_pos hb, Set.mem_ofPred_eq, loopOracle] using hbad
  · intro S hreq hb
    by_contra hbad
    apply hω
    apply final_subset_allBad I (removalEvent I J ε)
    change ω .final ∈ removalBad I J ε .final (request I J ε .final ω)
    change ω .final ∈ removalBad I J ε .final (finalRequest I (loopOracle I J ε ω))
    rw [hreq]
    simpa only [removalBad, if_pos hb, Set.mem_ofPred_eq, finalOracle] using hbad

theorem response_success_outside_target (I J : Instance n) (ε : ℝ) (ω : Space I ε)
    (hω : ω ∉ allBad I (targetEvent I J ε)) : response I J ε ω = some J.best := by
  apply result_success_of_good_calls (I := I) (f := loopOracle I J ε ω)
    (last := finalOracle I J ε ω) (best := J.best)
  · intro k hk r hr S hreq hb
    obtain ⟨U, _, hU⟩ := loopRequest_some hreq
    have hbig := (GapEntropy.AttemptScale.request_some_iff.mp hU).2
    have hn : ¬ (J.best ∉ loopOracle I J ε ω k r S ∨
        (S.card + 1) / 2 < (loopOracle I J ε ω k r S).card) := by
      intro hbad
      apply hω
      apply loop_subset_allBad I (targetEvent I J ε) hk hr
      change ω (.loop k r) ∈ targetBad I J ε (.loop k r)
        (loopRequest I (loopOracle I J ε ω) k r)
      rw [hreq]
      simpa only [targetBad, if_pos (And.intro hb hbig), Set.mem_ofPred_eq, loopOracle] using hbad
    exact ⟨not_not.mp (not_or.mp hn).1, le_of_not_gt (not_or.mp hn).2⟩
  · intro S hreq hb
    have hcard := (finalRequest_some hreq).2.2
    by_contra hbad
    apply hω
    apply final_subset_allBad I (targetEvent I J ε)
    change ω .final ∈ targetBad I J ε .final (finalRequest I (loopOracle I J ε ω))
    rw [hreq]
    simpa only [targetBad, if_pos (And.intro hb hcard), Set.mem_ofPred_eq, finalOracle] using hbad

/-- C.2(1): on every actual normalized unique-best instance, incorrect return has
probability at most ε. Aborting is represented by `none`. -/
theorem universal_incorrect_le (I J : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (law I J ε).real {ω | ∃ a, response I J ε ω = some a ∧ a ≠ J.best} ≤ ε := by
  apply (measureReal_mono (μ := law I J ε) (s₂ := allBad I (removalEvent I J ε)) ?_).trans
    (all_removalEvent_le I J hε hε10)
  intro ω ⟨a, hret, hneq⟩
  by_contra hω
  exact hneq (response_correct_outside_removal I J ε ω hω hret)

/-- C.2(2), failure form: every permutation of the target returns its best arm
except on an event of probability at most ε. -/
theorem target_failure_le (I : Instance n) (π : Equiv.Perm (Fin n)) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (law I (I.permute π) ε).real
      {ω | response I (I.permute π) ε ω ≠ some (I.permute π).best} ≤ ε := by
  apply (measureReal_mono (μ := law I (I.permute π) ε)
    (s₂ := allBad I (targetEvent I (I.permute π) ε)) ?_).trans
    (all_targetEvent_le I π hε hε10)
  intro ω hfail
  by_contra hω
  exact hfail (response_success_outside_target I (I.permute π) ε ω hω)

theorem response_eq_measurable (I J : Instance n) (ε : ℝ) (a : Option (Fin n)) :
    MeasurableSet {ω | response I J ε ω = a} :=
  (response_measurable I J ε) (show MeasurableSet {a} from trivial)

/-- C.2(2): the complete target-labeling success probability for the actual
fresh Gaussian finite attempt. -/
theorem target_success_ge (I : Instance n) (π : Equiv.Perm (Fin n)) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    1 - ε ≤ (law I (I.permute π) ε).real
      {ω | response I (I.permute π) ε ω = some (I.permute π).best} := by
  have hf := target_failure_le I π hε hε10
  have hm := measureReal_add_measureReal_compl
    (μ := law I (I.permute π) ε)
    (response_eq_measurable I (I.permute π) ε (some (I.permute π).best))
  rw [probReal_univ] at hm
  change (law I (I.permute π) ε).real
    {ω | response I (I.permute π) ε ω = some (I.permute π).best} +
    (law I (I.permute π) ε).real
    {ω | response I (I.permute π) ε ω ≠ some (I.permute π).best} = 1 at hm
  linarith

/-- C.2(3), attached to the same sampled response: every trajectory's full
declared sample budget obeys the target entropy bound. -/
theorem declaredCost_le (I J : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) (ω : Space I ε) :
    (totalCost I ε (loopOracle I J ε ω) : ℝ) ≤
      1000000000000 * I.hardness * (Real.log ε⁻¹ + I.gapEntropy) :=
  totalCost_le I hε hε10 _

/-- The three C.2 conclusions for an actual canonical statistical attempt.
This theorem makes no claim of a `Policy` implementation. -/
theorem finite_attempt_C2 (I : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (∀ J : Instance n, Measurable (response I J ε)) ∧
    (∀ J : Instance n, (law I J ε).real
      {ω | ∃ a, response I J ε ω = some a ∧ a ≠ J.best} ≤ ε) ∧
    (∀ π : Equiv.Perm (Fin n), 1 - ε ≤ (law I (I.permute π) ε).real
      {ω | response I (I.permute π) ε ω = some (I.permute π).best}) ∧
    (∀ (J : Instance n) (ω : Space I ε),
      (totalCost I ε (loopOracle I J ε ω) : ℝ) ≤
        1000000000000 * I.hardness * (Real.log ε⁻¹ + I.gapEntropy)) :=
  ⟨fun J => response_measurable I J ε,
    fun J => universal_incorrect_le I J hε hε10,
    fun π => target_success_ge I π hε hε10,
    fun J ω => declaredCost_le I J hε hε10 ω⟩

end GapEntropy.AttemptExperiment
