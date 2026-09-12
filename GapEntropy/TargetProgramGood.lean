import GapEntropy.TargetProgramOrder
import GapEntropy.ProgramGood

/-!
# Good calls and confidence risk of the target program

If every call on an oracle path through `TargetProgram.program` is good, then every loop request
and the final request of the corresponding `TargetAttempt` control flow receive a good response.
The confidence spent along an oracle path equals `TargetAttempt.confidenceSpent`, so the `risk`
of the program, the maximum spent confidence over all response branches, is at most `ε`.
-/

noncomputable section
open scoped Classical BigOperators

namespace GapEntropy.TargetProgram
open FiniteCallProgram TargetAttempt
variable {n : ℕ}

theorem good_run_request (I : Instance n) (ε : ℝ) (G : Good n) (f : FiniteCallProgram.Oracle n)
    (k : ℕ) (S : Finset (Fin n)) {R : ℕ} (hp : oracleGood G f (run I ε k S R))
    {r : ℕ} (hr : r < R) {T : Finset (Fin n)}
    (hreq : AttemptScale.request (I.targetCount k) (loopOracle f k) S r = some T) :
    G (.loop k r) T (f (.loop k r) T) := by
  induction R with
  | zero => omega
  | succ R ih =>
    have hg := (oracleGood_bind G f (run I ε k S R) (step I ε k R)).mp hp
    by_cases hrR : r < R
    · exact ih hg.1 hrR
    · have he : r = R := by omega
      subst r
      have hst := AttemptScale.request_some_iff.mp hreq
      rw [eval_run, hst.1] at hg
      have hh := hg.2
      simp only [step, dif_pos hst.2, oracleGood] at hh
      exact hh.1

theorem good_entry_request (I : Instance n) (ε : ℝ) (G : Good n) (f : FiniteCallProgram.Oracle n)
    {K : ℕ} (hp : oracleGood G f (entry I ε K)) {k r : ℕ}
    (hk : k < K) (hr : r < n) {T : Finset (Fin n)}
    (hreq : TargetAttempt.loopRequest I (loopOracle f) k r = some T) :
    G (.loop k r) T (f (.loop k r) T) := by
  induction K with
  | zero => omega
  | succ K ih =>
    have hg := (oracleGood_bind G f (entry I ε K) (finishScale I ε K)).mp hp
    by_cases hkK : k < K
    · exact ih hg.1 hkK
    · have he : k = K := by omega
      subst k
      obtain ⟨S, hS, hT⟩ := TargetAttempt.loopRequest_some hreq
      have hh := hg.2
      rw [eval_entry, hS] at hh
      exact good_run_request I ε G f K S hh hr hT

theorem good_program_requests (I : Instance n) (ε : ℝ) (G : Good n) (f : FiniteCallProgram.Oracle n)
    (hp : oracleGood G f (program I ε)) :
    (∀ k < I.lastBucket + 1, ∀ r < n, ∀ S,
      TargetAttempt.loopRequest I (loopOracle f) k r = some S → G (.loop k r) S (f (.loop k r) S)) ∧
    (∀ S, TargetAttempt.finalRequest I (loopOracle f) = some S → G .final S (f .final S)) := by
  have hg := (oracleGood_bind G f (entry I ε (I.lastBucket + 1)) (finish I ε)).mp hp
  refine ⟨fun k hk r hr S hreq => good_entry_request I ε G f hg.1 hk hr hreq, ?_⟩
  intro S hreq
  have hS := TargetAttempt.finalRequest_some hreq
  have hh := hg.2
  rw [eval_entry] at hh
  unfold TargetAttempt.finalRequest at hreq
  cases he : TargetAttempt.entry I (loopOracle f) (I.lastBucket + 1) with
  | none => simp [he] at hreq
  | some T =>
    simp only [he] at hreq
    split_ifs at hreq with hc
    have hTS := Option.some.inj hreq
    subst T
    rw [he] at hh
    simp only [finish, if_neg hc, dif_pos hS.1, oracleGood] at hh
    exact hh.1

def confidenceCharge (I : Instance n) (ε : ℝ) (k r : ℕ) : ArmState n → ℝ
  | none => 0
  | some S => if 4 * I.targetCount k < S.card then I.callConfidence ε k r else 0

theorem spent_step (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n)
    (k r : ℕ) (state : ArmState n) :
    FiniteCallProgram.confidenceSpent f (step I ε k r state) = confidenceCharge I ε k r state := by
  cases state with
  | none => rfl
  | some S =>
    by_cases hbig : 4 * I.targetCount k < S.card
    · simp only [step, confidenceCharge, dif_pos hbig, if_pos hbig, FiniteCallProgram.confidenceSpent, add_zero]
    · simp only [step, confidenceCharge, dif_neg hbig, if_neg hbig, FiniteCallProgram.confidenceSpent]

theorem spent_run (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n)
    (k : ℕ) (S : Finset (Fin n)) (R : ℕ) :
    FiniteCallProgram.confidenceSpent f (run I ε k S R) = ∑ r ∈ Finset.range R,
      confidenceCharge I ε k r (AttemptScale.run (I.targetCount k) (loopOracle f k) S r) := by
  induction R with
  | zero => simp [run, FiniteCallProgram.confidenceSpent]
  | succ R ih => rw [run, FiniteCallProgram.confidenceSpent_bind, ih, eval_run, spent_step, Finset.sum_range_succ]

theorem confidenceCharge_eq_request (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n)
    (k r : ℕ) (S : Finset (Fin n)) :
    confidenceCharge I ε k r (AttemptScale.run (I.targetCount k) (loopOracle f k) S r) =
      if (AttemptScale.request (I.targetCount k) (loopOracle f k) S r).isSome then I.callConfidence ε k r else 0 := by
  unfold AttemptScale.request
  cases AttemptScale.run (I.targetCount k) (loopOracle f k) S r with
  | none => rfl
  | some T => by_cases hb : 4 * I.targetCount k < T.card <;> simp [confidenceCharge, hb]

theorem spent_finishScale_entry (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n) (k : ℕ) :
    FiniteCallProgram.confidenceSpent f (finishScale I ε k (TargetAttempt.entry I (loopOracle f) k)) =
      ∑ r ∈ Finset.range n, if (TargetAttempt.loopRequest I (loopOracle f) k r).isSome then I.callConfidence ε k r else 0 := by
  cases he : TargetAttempt.entry I (loopOracle f) k with
  | none => simp [finishScale, FiniteCallProgram.confidenceSpent, TargetAttempt.loopRequest, he]
  | some S =>
    rw [finishScale, spent_run]
    apply Finset.sum_congr rfl
    intro r _
    rw [confidenceCharge_eq_request]
    simp only [TargetAttempt.loopRequest, he]

theorem spent_entry (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n) (K : ℕ) :
    FiniteCallProgram.confidenceSpent f (entry I ε K) = ∑ k ∈ Finset.range K,
      ∑ r ∈ Finset.range n, if (TargetAttempt.loopRequest I (loopOracle f) k r).isSome then I.callConfidence ε k r else 0 := by
  induction K with
  | zero => simp [entry, FiniteCallProgram.confidenceSpent]
  | succ K ih => rw [entry, FiniteCallProgram.confidenceSpent_bind, eval_entry, ih, spent_finishScale_entry, Finset.sum_range_succ]

theorem spent_program (I : Instance n) (ε : ℝ) (f : FiniteCallProgram.Oracle n) :
    FiniteCallProgram.confidenceSpent f (program I ε) = TargetAttempt.confidenceSpent I ε (loopOracle f) := by
  rw [program, FiniteCallProgram.confidenceSpent_bind, spent_entry, eval_entry]
  unfold TargetAttempt.confidenceSpent
  congr 1
  cases he : TargetAttempt.entry I (loopOracle f) (I.lastBucket + 1) with
  | none => simp [finish, FiniteCallProgram.confidenceSpent, TargetAttempt.finalRequest, he]
  | some S =>
    have hS := TargetAttempt.entry_nonempty he
    by_cases hc : S.card = 1
    · simp [finish, FiniteCallProgram.confidenceSpent, TargetAttempt.finalRequest, he, hc]
    · simp [finish, FiniteCallProgram.confidenceSpent, TargetAttempt.finalRequest, he, hc, hS]

theorem risk_le (I : Instance n) {ε : ℝ} (hε : 0 ≤ ε) : risk (program I ε) ≤ ε := by
  obtain ⟨f, hf⟩ := risk_attained (program_ordered I ε)
  rw [← hf, spent_program]
  exact TargetAttempt.confidenceSpent_le I hε _

end GapEntropy.TargetProgram
