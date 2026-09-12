import GapEntropy.UniversalAttempt

/-!
# A bounded, observable implementation of one universal attempt

The parser's requests depend only on the given observed history and the known
parameters. At its fixed sample cap, parsing is always complete. Terminal
paths are padded with arm zero, preserving their answer and their call
reservations; the entire procedure therefore uses exactly the declared cap.
-/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GapEntropy.UniversalAttempt
variable {n : ℕ}
attribute [local irreducible] Config.fuel

def nextRequest (c : Config) (hn : 2 ≤ n) {t : ℕ} (h : History n t) : Fin n :=
  match parse c c.fuel (initial n) 0 h with
  | .inl i => i
  | .inr _ => ⟨0, by omega⟩

def answer (c : Config) {t : ℕ} (h : History n t) : Option (Fin n) :=
  match parse c c.fuel (initial n) 0 h with
  | .inl _ => none
  | .inr (_, a) => a

theorem measurable_initial_parse (c : Config) (t : ℕ) :
    Measurable (fun h : History n t => parse c c.fuel (initial n) 0 h) :=
  (measurable_parse c c.fuel (initial n) t).comp (measurable_const.prodMk measurable_id)

theorem measurable_nextRequest (c : Config) (hn : 2 ≤ n) (t : ℕ) :
    Measurable (nextRequest c hn (t := t)) := by
  have hf : Measurable (fun p : Parsed n => p.elim id (fun _ => (⟨0, by omega⟩ : Fin n))) :=
    measurable_id.sumElim measurable_const
  convert hf.comp (measurable_initial_parse c t) using 1
  funext h
  cases hp : parse c c.fuel (initial n) 0 h <;> simp [nextRequest, hp]

theorem measurable_answer (c : Config) (t : ℕ) :
    Measurable (answer c (n := n) (t := t)) := by
  have hf : Measurable (fun p : Parsed n => p.elim (fun _ => none) Prod.snd) :=
    measurable_const.sumElim measurable_snd
  convert hf.comp (measurable_initial_parse c t) using 1
  funext h
  cases hp : parse c c.fuel (initial n) 0 h <;> simp [answer, hp]

def procedure (c : Config) (hn : 2 ≤ n) : BoundedProcedure n (Option (Fin n)) where
  budget := c.sampleCap
  request _ _ := nextRequest c hn
  measurable_request t _ := measurable_nextRequest c hn t
  output := answer c
  measurable_output := measurable_answer c c.sampleCap

@[simp] theorem procedure_budget (c : Config) (hn : 2 ≤ n) :
    (procedure c hn).budget = c.sampleCap := rfl

theorem procedure_samples (c : Config) (hn : 2 ≤ n) (ω : SampleSpace n) :
    (procedure c hn).samplingPolicy.sampleCount hn ω = c.sampleCap :=
  (procedure c hn).sampleCount_eq_budget hn ω

theorem procedure_evaluate (c : Config) (hn : 2 ≤ n)
    (v : (procedure c hn).Tape) :
    (procedure c hn).evaluate v =
      answer c ((procedure c hn).simulate v c.sampleCap le_rfl) := rfl

theorem procedure_evaluate_complete (c : Config) (hn : 2 ≤ n)
    (v : (procedure c hn).Tape) :
    ∃ st, parse c c.fuel (initial n) 0
      ((procedure c hn).simulate v c.sampleCap le_rfl) =
      .inr (st, (procedure c hn).evaluate v) := by
  obtain ⟨st, a, h⟩ := initial_parse_complete c
    ((procedure c hn).simulate v c.sampleCap le_rfl) le_rfl
  refine ⟨st, ?_⟩
  simp only [procedure_evaluate, answer, h]

theorem procedure_actualOutput_complete (c : Config) (hn : 2 ≤ n)
    (ω : SampleSpace n) :
    ∃ st, parse c c.fuel (initial n) 0
      ((procedure c hn).simulate (GaussianBlocks.rewardBlock 0 c.sampleCap ω)
        c.sampleCap le_rfl) = .inr (st, (procedure c hn).actualOutput ω) :=
  procedure_evaluate_complete c hn (GaussianBlocks.rewardBlock 0 c.sampleCap ω)

end GapEntropy.UniversalAttempt
