import GapEntropy.TargetProgramOrder
import GapEntropy.BoundedProcedure

/-!
# A fixed-budget actual finite-attempt sampler

The request interpreter samples actual A.3 calls and reads their raw finite-set
results from completed observed-history slices. It continues C.1's control flow
without returning any subroutine's completion marker. After the finite script
finishes, samples of arm zero fill the deterministic entropy cap. The Option
readout preserves the script's completed result under this padding.

The actual Gaussian probability transfer is a further theorem, not a premise
silently attached to this construction.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace GapEntropy.AttemptProcedure
open FiniteCallProgram
variable {n : ℕ}

def realCap (I : Instance n) (ε : ℝ) : ℝ :=
  1000000000000 * I.hardness * (Real.log ε⁻¹ + I.gapEntropy)

def cap (I : Instance n) (ε : ℝ) : ℕ := max 1 ⌈realCap I ε⌉₊

theorem cap_pos (I : Instance n) (ε : ℝ) : 0 < cap I ε :=
  lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)

theorem capacity_le_cap (I : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    capacity (TargetProgram.program I ε) ≤ cap I ε := by
  have h := (TargetProgram.capacity_le I hε hε10).trans (Nat.le_ceil (realCap I ε))
  exact (Nat.cast_le.mp h).trans (le_max_right _ _)

theorem realCap_ge_one (I : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    1 ≤ realCap I ε := by
  have hH := I.one_le_twoArmHardness.trans I.twoArmHardness_le_hardness
  have hL : 1 ≤ Real.log ε⁻¹ := TargetAttempt.one_le_log_inv hε (by linarith)
  have hE := I.gapEntropy_nonneg
  have hm := mul_le_mul (show (1 : ℝ) ≤ 1000000000000 * I.hardness by linarith)
    (show (1 : ℝ) ≤ Real.log ε⁻¹ + I.gapEntropy by linarith) (by norm_num) (by positivity : 0 ≤ 1000000000000 * I.hardness)
  simpa only [one_mul, realCap] using hm

theorem cap_le_twice_realCap (I : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) :
    (cap I ε : ℝ) ≤ 2 * realCap I ε := by
  have hX := realCap_ge_one I hε hε10
  have hceil : 1 ≤ ⌈realCap I ε⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  rw [cap, max_eq_right hceil]
  have hb := Nat.ceil_lt_add_one (show 0 ≤ realCap I ε by linarith)
  linarith

def nextRequest (I : Instance n) (ε : ℝ) (t : ℕ) (h : History n t) : Fin n :=
  match parse (TargetProgram.program I ε) h with
  | .inl i => i
  | .inr _ => ⟨0, lt_of_lt_of_le (by norm_num) I.two_le⟩

def readout (I : Instance n) (ε : ℝ) {t : ℕ} (h : History n t) : Option (Fin n) :=
  match parse (TargetProgram.program I ε) h with
  | .inl _ => none
  | .inr (_, a) => a

theorem nextRequest_measurable (I : Instance n) (ε : ℝ) (t : ℕ) :
    Measurable (nextRequest I ε t) := by
  have hm : Measurable (Sum.elim (id : Fin n → Fin n)
      (fun _ : ℕ × Option (Fin n) => (⟨0, lt_of_lt_of_le (by norm_num) I.two_le⟩ : Fin n))) :=
    measurable_id.sumElim measurable_const
  convert hm.comp (parse_measurable (TargetProgram.program I ε) t) using 1
  funext h
  cases hp : parse (TargetProgram.program I ε) h <;> simp [nextRequest, hp]

theorem readout_measurable (I : Instance n) (ε : ℝ) (t : ℕ) :
    Measurable (readout I ε (t := t)) := by
  have hm : Measurable (Sum.elim (fun _ : Fin n => (none : Option (Fin n)))
      (Prod.snd : ℕ × Option (Fin n) → Option (Fin n))) :=
    measurable_const.sumElim measurable_snd
  convert hm.comp (parse_measurable (TargetProgram.program I ε) t) using 1
  funext h
  cases hp : parse (TargetProgram.program I ε) h <;> simp [readout, hp]

/-- An actual bounded, history-based procedure with an abort-or-answer readout. -/
def procedure (I : Instance n) (ε : ℝ) : BoundedProcedure n (Option (Fin n)) where
  budget := cap I ε
  request t _ := nextRequest I ε t
  measurable_request t _ := nextRequest_measurable I ε t
  output := readout I ε
  measurable_output := readout_measurable I ε _

theorem readout_at_cap_follows_control (I : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) (h : History n (cap I ε)) :
    ∃ f : FiniteCallProgram.Oracle n,
      readout I ε h = TargetAttempt.result I (TargetProgram.loopOracle f) (f .final) ∧
      TargetAttempt.totalCost I ε (TargetProgram.loopOracle f) ≤ cap I ε := by
  obtain ⟨s, a, hp, hs⟩ := parse_complete (TargetProgram.program I ε) h (capacity_le_cap I hε hε10)
  obtain ⟨f, hf, hc⟩ := parse_terminal_eq_oracle (TargetProgram.program_ordered I ε) h hp
  refine ⟨f, ?_, ?_⟩
  · simp only [readout, hp]
    rw [← TargetProgram.eval_program, hf]
  · rw [← TargetProgram.cost_program, hc]
    exact hs.trans (capacity_le_cap I hε hε10)

/-- Padding observations cannot alter a result after the finite script finishes. -/
theorem readout_padding_stable (I : Instance n) (ε : ℝ) {t T : ℕ}
    (h : History n t) (h' : History n T) (ht : t ≤ T)
    (heq : ∀ i : Fin t, h i = h' ⟨i, lt_of_lt_of_le i.isLt ht⟩)
    (hcomplete : capacity (TargetProgram.program I ε) ≤ t) :
    readout I ε h' = readout I ε h := by
  obtain ⟨s, a, hp, _⟩ := parse_complete (TargetProgram.program I ε) h hcomplete
  have hp' := parse_terminal_stable (TargetProgram.program I ε) h h' ht heq hp
  simp only [readout, hp, hp']

theorem sampleCount_eq_cap (I : Instance n) (ε : ℝ) (ω : SampleSpace n) :
    (procedure I ε).samplingPolicy.sampleCount I.two_le ω = cap I ε :=
  (procedure I ε).sampleCount_eq_budget I.two_le ω

end GapEntropy.AttemptProcedure
