import GapEntropy.UniversalAttemptTrace
import GapEntropy.ProgramSimulation

/-!
# Universal-attempt execution on actual successive reward blocks

This module connects the observed-history parser with genuine bounded call
simulations. Each completed call is evaluated on its next block of reward
rows, after which the continuation receives the suffix. The stored numerical
reference is passed unchanged between calls at the same scale.
-/
noncomputable section
open MeasureTheory
open scoped Classical
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram
variable {n : ℕ}
attribute [local irreducible] Config.fuel

/-- Uniform output type for entry and later calls. Later calls simply carry the
previous numerical reference alongside their newly retained set. -/
def callProcedure (c : Config) (a : Metadata n) (ha : 2 ≤ a.active.card) (z : ℝ) :
    BoundedProcedure n (ℝ × Finset (Fin n)) where
  budget := (a.call c).samples
  request _ _ := request c a ha
  measurable_request t _ := measurable_request c a ha t
  output := readout c a z
  measurable_output := (measurable_readout c a _).comp (measurable_const.prodMk measurable_id)

def execute (c : Config) : ℕ → Metadata n → ℝ → Values n → State n × Option (Fin n)
  | 0, a, z, _ => ((a, z), none)
  | fuel + 1, a, z, x =>
    if ha : a.Allowed c then
      let r := (callProcedure c a ha.1 z).evaluate (firstBlock (a.call c).samples x)
      if r.2.card = 1 then ((a.advance c r.2, r.1), singletonAnswer r.2)
      else execute c fuel (a.advance c r.2) (retainedReference a r.1 r.2)
        (shiftValues (a.call c).samples x)
    else ((a, z), none)

def parsedRequest (hn : 2 ≤ n) : Parsed n → Fin n :=
  Sum.elim id (fun _ => ⟨0, by omega⟩)

def ValidHistory (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    (hn : 2 ≤ n) (x : Values n) {t : ℕ} (h : History n t) : Prop :=
  ∀ s (hs : s < t),
    (h ⟨s, hs⟩).1 = parsedRequest hn (parse c fuel a z (historyPrefix s hs.le h)) ∧
    (h ⟨s, hs⟩).2 = x s (h ⟨s, hs⟩).1

theorem parse_congr_history (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    {t T : ℕ} (hT : t = T) (h : History n t) (h' : History n T)
    (heq : ∀ i : Fin t, h i = h' ⟨i, by have := i.isLt; omega⟩) :
    parse c fuel a z h = parse c fuel a z h' := by
  subst T
  exact congrArg (parse c fuel a z) (funext heq)

theorem parse_suffix_prefix (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    {t : ℕ} (h : History n t) (m : ℕ) (hm : m ≤ t) (s : ℕ) (hs : s ≤ t - m) :
    parse c fuel a z (historySuffix m (by omega) (historyPrefix (m + s) (by omega) h)) =
      parse c fuel a z (historyPrefix s hs (historySuffix m hm h)) := by
  apply parse_congr_history c fuel a z (by omega)
  intro i
  rfl

theorem valid_first_call (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    (ha : a.Allowed c) (hn : 2 ≤ n) (x : Values n) {t : ℕ} (h : History n t)
    (hv : ValidHistory c (fuel + 1) a z hn x h) (hm : (a.call c).samples ≤ t) :
    (callProcedure c a ha.1 z).simulate (firstBlock (a.call c).samples x)
      (a.call c).samples le_rfl = historyPrefix (a.call c).samples hm h := by
  apply BoundedProcedure.simulate_eq_of_decisions
  intro s hs
  have hs' : s < t := hs.trans_le hm
  have hh := hv s hs'
  have hnot : ¬ (a.call c).samples ≤ s := by omega
  have hreq : parsedRequest hn (parse c (fuel + 1) a z (historyPrefix s hs'.le h)) =
      request c a ha.1 (historyPrefix s hs'.le h) := by
    simp only [parse, dif_pos ha, dif_neg hnot, parsedRequest, Sum.elim_inl, id_eq]
  exact ⟨(hh.1.trans hreq).symm, hh.2⟩

theorem first_call_readout (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    (ha : a.Allowed c) (hn : 2 ≤ n) (x : Values n) {t : ℕ} (h : History n t)
    (hv : ValidHistory c (fuel + 1) a z hn x h) (hm : (a.call c).samples ≤ t) :
    readout c a z (historyPrefix (a.call c).samples hm h) =
      (callProcedure c a ha.1 z).evaluate (firstBlock (a.call c).samples x) := by
  exact (congrArg (readout c a z) (valid_first_call c fuel a z ha hn x h hv hm)).symm

theorem valid_call_suffix (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    (ha : a.Allowed c) (hn : 2 ≤ n) (x : Values n) {t : ℕ} (h : History n t)
    (hv : ValidHistory c (fuel + 1) a z hn x h) (hm : (a.call c).samples ≤ t)
    (hsingle : (readout c a z (historyPrefix (a.call c).samples hm h)).2.card ≠ 1) :
    let r := readout c a z (historyPrefix (a.call c).samples hm h)
    ValidHistory c fuel (a.advance c r.2) (retainedReference a r.1 r.2) hn
      (shiftValues (a.call c).samples x) (historySuffix (a.call c).samples hm h) := by
  dsimp only
  let m := (a.call c).samples
  intro s hs
  have hglobal : m + s < t := by omega
  have hh := hv (m + s) hglobal
  have hp : parse c (fuel + 1) a z (historyPrefix (m + s) hglobal.le h) =
      parse c fuel (a.advance c (readout c a z (historyPrefix m hm h)).2)
        (retainedReference a (readout c a z (historyPrefix m hm h)).1
          (readout c a z (historyPrefix m hm h)).2)
        (historyPrefix s hs.le (historySuffix m hm h)) := by
    simp only [parse, dif_pos ha]
    rw [dif_pos (show m ≤ m + s by omega), historyPrefix_prefix, if_neg hsingle,
      parse_suffix_prefix]
  rw [hp] at hh
  exact hh

/-- The full reserved sample cap is sufficient for recursive block execution,
including erroneous paths and immediate reservation aborts. -/
theorem parse_eq_execute_of_valid (c : Config) (fuel : ℕ) (a : Metadata n) (z : ℝ)
    (hn : 2 ≤ n) (x : Values n) {t : ℕ} (h : History n t)
    (hv : ValidHistory c fuel a z hn x h) (ht : c.sampleCap ≤ a.samples + t) :
    parse c fuel a z h = .inr (execute c fuel a z x) := by
  induction fuel generalizing a z t x with
  | zero => rfl
  | succ fuel ih =>
    by_cases ha : a.Allowed c
    · have hm : (a.call c).samples ≤ t := by have := ha.2.2; omega
      have hread := first_call_readout c fuel a z ha hn x h hv hm
      let r := readout c a z (historyPrefix (a.call c).samples hm h)
      by_cases hr : r.2.card = 1
      · simp only [parse, execute, dif_pos ha, dif_pos hm, ← hread, r, if_pos hr]
      · have hv' := valid_call_suffix c fuel a z ha hn x h hv hm hr
        have ht' : c.sampleCap ≤ (a.advance c r.2).samples + (t - (a.call c).samples) := by
          change c.sampleCap ≤ (a.samples + (a.call c).samples) + (t - (a.call c).samples)
          omega
        have he := ih (a.advance c r.2) (retainedReference a r.1 r.2)
          (shiftValues (a.call c).samples x) (historySuffix (a.call c).samples hm h) hv' ht'
        simpa only [parse, execute, dif_pos ha, dif_pos hm, ← hread, r, if_neg hr] using he
    · simp only [parse, execute, dif_neg ha]

theorem nextRequest_eq_parsedRequest (c : Config) (hn : 2 ≤ n)
    {t : ℕ} (h : History n t) :
    nextRequest c hn h = parsedRequest hn (parse c c.fuel (initial n) 0 h) := by
  cases hp : parse c c.fuel (initial n) 0 h <;> simp [nextRequest, parsedRequest, hp]

theorem valid_simulate (c : Config) (hn : 2 ≤ n) (v : (procedure c hn).Tape)
    (T : ℕ) (hT : T ≤ c.sampleCap) :
    ValidHistory c c.fuel (initial n) 0 hn (extendBlock c.sampleCap v)
      ((procedure c hn).simulate v T hT) := by
  intro s hs
  have hd := (procedure c hn).simulate_decision v T hT s hs
  refine ⟨hd.1.symm.trans (nextRequest_eq_parsedRequest c hn _), ?_⟩
  exact hd.2.trans (by
    simp only [FiniteCallProgram.extendBlock, dif_pos (hs.trans_le hT)]
    rfl)

theorem evaluate_eq_execute (c : Config) (hn : 2 ≤ n) (v : (procedure c hn).Tape) :
    (procedure c hn).evaluate v =
      (execute c c.fuel (initial n) 0 (extendBlock c.sampleCap v)).2 := by
  have hp := parse_eq_execute_of_valid c c.fuel (initial n) 0 hn
    (extendBlock c.sampleCap v) ((procedure c hn).simulate v c.sampleCap le_rfl)
    (valid_simulate c hn v c.sampleCap le_rfl)
    (by change c.sampleCap ≤ 0 + c.sampleCap; omega)
  change answer c ((procedure c hn).simulate v c.sampleCap le_rfl) = _
  simp only [answer, hp]

/-- Exact execution identity on the genuine infinite reward rows. Thus every
local call is the actual entry/later sampler on its next fresh block. -/
theorem actualOutput_eq_execute (c : Config) (hn : 2 ≤ n) (ω : SampleSpace n) :
    (procedure c hn).actualOutput ω = (execute c c.fuel (initial n) 0 ω.2).2 := by
  let v := GaussianBlocks.rewardBlock 0 c.sampleCap ω
  have hv : ValidHistory c c.fuel (initial n) 0 hn ω.2
      ((procedure c hn).simulate v c.sampleCap le_rfl) := by
    intro s hs
    have hd := (procedure c hn).simulate_decision v c.sampleCap le_rfl s hs
    refine ⟨hd.1.symm.trans (nextRequest_eq_parsedRequest c hn _), ?_⟩
    simpa only [v, GaussianBlocks.rewardBlock, Nat.zero_add] using hd.2
  have hp := parse_eq_execute_of_valid c c.fuel (initial n) 0 hn ω.2 _ hv
    (by change c.sampleCap ≤ 0 + c.sampleCap; omega)
  change answer c ((procedure c hn).simulate v c.sampleCap le_rfl) = _
  simp only [answer, hp]

end GapEntropy.UniversalAttempt
