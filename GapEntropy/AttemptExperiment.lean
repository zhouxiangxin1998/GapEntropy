import GapEntropy.AttemptMeasurability
import GapEntropy.AttemptControlFacts
import GapEntropy.FiniteFreshness
import GapEntropy.FiniteAdaptivity

/-!
# Fresh Gaussian call tapes for the actual finite attempt

The target and ε fix the tape dimension at every call key before sampling. The
random active set does not change that space. The product is over whole canonical
A.3 tapes; this makes each requested call fresh. This is a statistical experiment,
not an assertion that a `Policy` implementation has already been constructed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MeasureTheory.Measure

namespace GapEntropy.AttemptExperiment
open GapEntropy.TargetAttempt
variable {n : ℕ}

abbrev CallTape (I : Instance n) (ε : ℝ) (key : CallKey) :=
  GapEntropy.EliminationTape.Tape n (callTolerance I key) (callConfidence I ε key)

abbrev Space (I : Instance n) (ε : ℝ) := ∀ key, CallTape I ε key

def defaultTape (I : Instance n) (ε : ℝ) (key : CallKey) : CallTape I ε key :=
  ⟨fun _ _ _ => 0, fun _ => 0, fun _ _ => 0⟩

def localLaw (I J : Instance n) (ε : ℝ) (key : CallKey) : Measure (CallTape I ε key) :=
  GapEntropy.EliminationTape.law J.mean (callTolerance I key) (callConfidence I ε key)

instance (I J : Instance n) (ε : ℝ) (key : CallKey) : IsProbabilityMeasure (localLaw I J ε key) := by
  unfold localLaw
  infer_instance

def law (I J : Instance n) (ε : ℝ) : Measure (Space I ε) := infinitePi (localLaw I J ε)

instance (I J : Instance n) (ε : ℝ) : IsProbabilityMeasure (law I J ε) := by
  unfold law
  infer_instance

def rawResponse (I J : Instance n) (ε : ℝ) (key : CallKey) (S : Finset (Fin n))
    (ω : CallTape I ε key) : Finset (Fin n) :=
  if hS : S.Nonempty then GapEntropy.EliminationTape.rawOutput J.mean S hS ω else ∅

theorem rawResponse_measurable (I J : Instance n) (ε : ℝ) (key : CallKey) (S : Finset (Fin n)) :
    Measurable (rawResponse I J ε key S) := by
  change Measurable (fun ω : CallTape I ε key =>
    if hS : S.Nonempty then GapEntropy.EliminationTape.rawOutput J.mean S hS ω else ∅)
  by_cases hS : S.Nonempty
  · simpa only [rawResponse, dif_pos hS] using GapEntropy.EliminationTape.rawOutput_measurable
      (d := callTolerance I key) (α := callConfidence I ε key) J.mean S hS
  · simpa only [rawResponse, dif_neg hS] using (measurable_const :
      Measurable (fun _ : CallTape I ε key => (∅ : Finset (Fin n))))

theorem rawResponse_joint_measurable (I J : Instance n) (ε : ℝ) (key : CallKey) :
    Measurable (fun p : Finset (Fin n) × CallTape I ε key => rawResponse I J ε key p.1 p.2) :=
  measurable_from_prod_countable_right (rawResponse_measurable I J ε key)

def primitive (I J : Instance n) (ε : ℝ) (ω : Space I ε) : Primitive n :=
  fun key input => rawResponse I J ε key input.active (ω key)

def loopOracle (I J : Instance n) (ε : ℝ) (ω : Space I ε) : Oracle n :=
  fun k r S => rawResponse I J ε (.loop k r) S (ω (.loop k r))

def finalOracle (I J : Instance n) (ε : ℝ) (ω : Space I ε) (S : Finset (Fin n)) : Finset (Fin n) :=
  rawResponse I J ε .final S (ω .final)

/-- Canonical Option-valued finite-attempt response, parameterized by target and actual input. -/
def response (I J : Instance n) (ε : ℝ) (ω : Space I ε) : Option (Fin n) :=
  result I (loopOracle I J ε ω) (finalOracle I J ε ω)

theorem response_eq_attempt (I J : Instance n) (ε : ℝ) (ω : Space I ε) :
    response I J ε ω = attempt I ε (primitive I J ε ω) := rfl

def request (I J : Instance n) (ε : ℝ) (key : CallKey) (ω : Space I ε) : Option (Finset (Fin n)) :=
  match key with
  | .loop k r => loopRequest I (loopOracle I J ε ω) k r
  | .final => finalRequest I (loopOracle I J ε ω)

theorem loopOracle_measurable (I J : Instance n) (ε : ℝ) (k r : ℕ) (S : Finset (Fin n)) :
    Measurable (fun ω => loopOracle I J ε ω k r S) := by
  have he : Measurable (fun ω : Space I ε => ω (.loop k r)) := measurable_pi_apply _
  exact (rawResponse_measurable I J ε (.loop k r) S).comp he

theorem finalOracle_measurable (I J : Instance n) (ε : ℝ) (S : Finset (Fin n)) :
    Measurable (fun ω => finalOracle I J ε ω S) := by
  have he : Measurable (fun ω : Space I ε => ω .final) := measurable_pi_apply _
  exact (rawResponse_measurable I J ε .final S).comp he

theorem response_measurable (I J : Instance n) (ε : ℝ) : Measurable (response I J ε) :=
  result_measurable I (loopOracle_measurable I J ε) (finalOracle_measurable I J ε)

theorem request_measurable (I J : Instance n) (ε : ℝ) (key : CallKey) :
    Measurable (request I J ε key) := by
  cases key with
  | loop k r => exact loopRequest_measurable I (loopOracle_measurable I J ε) k r
  | final => exact finalRequest_measurable I (loopOracle_measurable I J ε)

theorem call_tapes_independent (I J : Instance n) (ε : ℝ) :
    iIndepFun (fun key (ω : Space I ε) => ω key) (law I J ε) :=
  iIndepFun_infinitePi (P := localLaw I J ε) (X := fun _ x => x) (fun _ => measurable_id)

theorem call_preserving (I J : Instance n) (ε : ℝ) (key : CallKey) :
    MeasurePreserving (fun ω : Space I ε => ω key) (law I J ε) (localLaw I J ε key) :=
  measurePreserving_eval_infinitePi (localLaw I J ε) key

/-- All completed earlier scales and earlier calls of the current scale. -/
def pastLoop (k r : ℕ) : Finset CallKey :=
  ((Finset.range k ×ˢ Finset.range n).image (fun p => CallKey.loop p.1 p.2)) ∪
    ((Finset.range r).image (fun u => CallKey.loop k u))

def pastFinal (I : Instance n) : Finset CallKey :=
  (Finset.range (I.lastBucket + 1) ×ˢ Finset.range n).image (fun p => CallKey.loop p.1 p.2)

theorem loop_not_past (k r : ℕ) : CallKey.loop k r ∉ pastLoop (n := n) k r := by
  simp [pastLoop]

theorem final_not_past (I : Instance n) : CallKey.final ∉ pastFinal I := by simp [pastFinal]

theorem request_depends_loop (I J : Instance n) (ε : ℝ) (k r : ℕ)
    (ω ω' : Space I ε) (h : ∀ key ∈ pastLoop (n := n) k r, ω key = ω' key) :
    request I J ε (.loop k r) ω = request I J ε (.loop k r) ω' := by
  apply loopRequest_congr
  · intro j hj u hu S
    have hm : CallKey.loop j u ∈ pastLoop (n := n) k r :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(j, u),
        Finset.mem_product.mpr ⟨Finset.mem_range.mpr hj, Finset.mem_range.mpr hu⟩, rfl⟩)
    simp only [loopOracle, h _ hm]
  · intro u hu S
    have hm : CallKey.loop k u ∈ pastLoop (n := n) k r :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr hu, rfl⟩)
    simp only [loopOracle, h _ hm]

theorem request_depends_final (I J : Instance n) (ε : ℝ)
    (ω ω' : Space I ε) (h : ∀ key ∈ pastFinal I, ω key = ω' key) :
    request I J ε .final ω = request I J ε .final ω' := by
  apply finalRequest_congr
  intro k hk r hr S
  have hm : CallKey.loop k r ∈ pastFinal I := Finset.mem_image.mpr
    ⟨(k, r), Finset.mem_product.mpr ⟨Finset.mem_range.mpr hk, Finset.mem_range.mpr hr⟩, rfl⟩
  simp only [loopOracle, h _ hm]

/-- Freshness of the actual adaptive request is derived from the product measure and causality. -/
theorem request_independent_current (I J : Instance n) (ε : ℝ) (key : CallKey) :
    IndepFun (request I J ε key) (fun ω : Space I ε => ω key) (law I J ε) := by
  cases key with
  | loop k r =>
    exact GapEntropy.FiniteFreshness.indep_of_finite_dependence (call_tapes_independent I J ε)
      (defaultTape I ε) (request_measurable I J ε (.loop k r))
      (pastLoop (n := n) k r) (.loop k r) (loop_not_past k r) (request_depends_loop I J ε k r)
  | final =>
    exact GapEntropy.FiniteFreshness.indep_of_finite_dependence (call_tapes_independent I J ε)
      (defaultTape I ε) (request_measurable I J ε .final)
      (pastFinal I) .final (final_not_past I) (request_depends_final I J ε)

end GapEntropy.AttemptExperiment
