import GapEntropy.ProgramExecution
import GapEntropy.AttemptProcedure
import GapEntropy.ProcedureSimulation

/-!
# Actual parser histories agree with sequential elimination execution

The simulation theorem is proved for histories whose requests and rewards match
the actual parser. A completed first call is exactly its bounded procedure's
simulation; slicing off that call yields a valid history for the continuation.
This establishes the padded attempt procedure's actual output identity.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace GapEntropy.FiniteCallProgram

variable {n : ℕ} {α : Type*}

def parseRequest (hn : 2 ≤ n) : Parsed n α → Fin n :=
  Sum.elim id (fun _ => ⟨0, by omega⟩)

@[simp] theorem parseRequest_addCost (hn : 2 ≤ n) (m : ℕ) (p : Parsed n α) :
    parseRequest hn (addCost m p) = parseRequest hn p := by
  cases p <;> rfl

def ValidHistory (p : Program n α) (hn : 2 ≤ n) (x : Values n)
    {t : ℕ} (h : History n t) : Prop :=
  ∀ s (hs : s < t),
    (h ⟨s, hs⟩).1 = parseRequest hn (parse p (historyPrefix s hs.le h)) ∧
    (h ⟨s, hs⟩).2 = x s (h ⟨s, hs⟩).1

theorem historyPrefix_prefix {t : ℕ} (h : History n t) (T : ℕ) (hT : T ≤ t)
    (s : ℕ) (hs : s ≤ T) :
    historyPrefix s hs (historyPrefix T hT h) = historyPrefix s (hs.trans hT) h := rfl

theorem parse_congr_history (p : Program n α) {t T : ℕ} (hT : t = T)
    (h : History n t) (h' : History n T)
    (heq : ∀ i : Fin t, h i = h' ⟨i, by have := i.isLt; omega⟩) : parse p h = parse p h' := by
  subst T
  exact congrArg (parse p) (funext heq)

theorem parse_suffix_prefix (p : Program n α) {t : ℕ} (h : History n t)
    (m : ℕ) (hm : m ≤ t) (s : ℕ) (hs : s ≤ t - m) :
    parse p (historySuffix m (by omega)
      (historyPrefix (m + s) (by omega) h)) =
      parse p (historyPrefix s hs (historySuffix m hm h)) := by
  apply parse_congr_history p (by omega)
  intro i
  rfl

theorem valid_first_call {key : TargetAttempt.CallKey} {S : Finset (Fin n)} (hS : S.Nonempty)
    {d δ : ℝ} {next : Finset (Fin n) → Program n α} (hn : 2 ≤ n) (x : Values n)
    {t : ℕ} (h : History n t)
    (hv : ValidHistory (.call key S hS d δ next) hn x h)
    (hm : EliminationPolicy.budget S.card d δ ≤ t) :
    (EliminationPolicy.rawProcedure S hS d δ hn).simulate
      (firstBlock (EliminationPolicy.budget S.card d δ) x)
      (EliminationPolicy.budget S.card d δ) le_rfl =
      historyPrefix (EliminationPolicy.budget S.card d δ) hm h := by
  apply BoundedProcedure.simulate_eq_of_decisions
  intro s hs
  have hs' : s < t := hs.trans_le hm
  have hh := hv s hs'
  have hnot : ¬ EliminationPolicy.budget S.card d δ ≤ s := by omega
  have hreq : parseRequest hn (parse (.call key S hS d δ next) (historyPrefix s hs'.le h)) =
      EliminationPolicy.requestedFromHistory S hS d δ s (historyPrefix s hs'.le h) := by
    simp only [parse, dif_neg hnot, parseRequest, Sum.elim_inl, id_eq]
  exact ⟨(hh.1.trans hreq).symm, hh.2⟩

theorem first_call_readout {key : TargetAttempt.CallKey} {S : Finset (Fin n)} (hS : S.Nonempty)
    {d δ : ℝ} {next : Finset (Fin n) → Program n α} (hn : 2 ≤ n) (x : Values n)
    {t : ℕ} (h : History n t)
    (hv : ValidHistory (.call key S hS d δ next) hn x h)
    (hm : EliminationPolicy.budget S.card d δ ≤ t) :
    EliminationPolicy.rawOutputFromHistory S hS d δ
      (historyPrefix (EliminationPolicy.budget S.card d δ) hm h) =
    EliminationPolicy.rawOutputFromBlock S hS d δ hn
      (firstBlock (EliminationPolicy.budget S.card d δ) x) := by
  have hs := valid_first_call hS hn x h hv hm
  have he := congrArg (EliminationPolicy.rawOutputFromHistory S hS d δ) hs
  have hp := congrFun (EliminationPolicy.rawProcedure_evaluate_eq S hS d δ hn)
    (firstBlock (EliminationPolicy.budget S.card d δ) x)
  exact he.symm.trans hp

theorem valid_call_suffix {key : TargetAttempt.CallKey} {S : Finset (Fin n)} (hS : S.Nonempty)
    {d δ : ℝ} {next : Finset (Fin n) → Program n α} (hn : 2 ≤ n) (x : Values n)
    {t : ℕ} (h : History n t)
    (hv : ValidHistory (.call key S hS d δ next) hn x h)
    (hm : EliminationPolicy.budget S.card d δ ≤ t) :
    ValidHistory (next (EliminationPolicy.rawOutputFromHistory S hS d δ
      (historyPrefix (EliminationPolicy.budget S.card d δ) hm h))) hn
      (shiftValues (EliminationPolicy.budget S.card d δ) x)
      (historySuffix (EliminationPolicy.budget S.card d δ) hm h) := by
  let m := EliminationPolicy.budget S.card d δ
  intro s hs
  have hglobal : m + s < t := by omega
  have hh := hv (m + s) hglobal
  have hp : parse (.call key S hS d δ next) (historyPrefix (m + s) hglobal.le h) =
      addCost m (parse (next (EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h)))
        (historyPrefix s hs.le (historySuffix m hm h))) := by
    change (if hms : m ≤ m + s then addCost m (parse
      (next (EliminationPolicy.rawOutputFromHistory S hS d δ
        (historyPrefix m hms (historyPrefix (m + s) hglobal.le h))))
      (historySuffix m hms (historyPrefix (m + s) hglobal.le h))) else _) = _
    rw [dif_pos (by omega), historyPrefix_prefix, parse_suffix_prefix]
  rw [hp, parseRequest_addCost] at hh
  exact hh

theorem parse_eq_execute_of_valid (p : Program n α) (hn : 2 ≤ n) (x : Values n)
    {t : ℕ} (h : History n t) (hv : ValidHistory p hn x h) (ht : capacity p ≤ t) :
    parse p h = Sum.inr (execute p hn x) := by
  induction p generalizing t x with
  | pure a => rfl
  | call key S hS d δ next ih =>
      let m := EliminationPolicy.budget S.card d δ
      have hm : m ≤ t := (Nat.le_add_right _ _).trans ht
      let R := EliminationPolicy.rawOutputFromBlock S hS d δ hn (firstBlock m x)
      have hread : EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h) = R :=
        first_call_readout hS hn x h hv hm
      have htail := valid_call_suffix hS hn x h hv hm
      rw [hread] at htail
      have hcap : capacity (next R) ≤ t - m := by
        have hle := Finset.le_sup (f := fun U => capacity (next U)) (Finset.mem_univ R)
        change m + Finset.univ.sup (fun U => capacity (next U)) ≤ t at ht
        omega
      have he := ih R (shiftValues m x) (historySuffix m hm h) htail hcap
      change (if hm : m ≤ t then addCost m (parse
        (next (EliminationPolicy.rawOutputFromHistory S hS d δ (historyPrefix m hm h)))
        (historySuffix m hm h)) else _) = _
      rw [dif_pos hm, hread, he]
      rfl

/-- The bounded sampler's recorded history satisfies the actual parser whenever
its requests are the parser's requests, including harmless padding after completion. -/
theorem valid_simulate {β : Type*} [MeasurableSpace β]
    (R : BoundedProcedure n β) (p : Program n α) (hn : 2 ≤ n)
    (v : R.Tape) (T : ℕ) (hT : T ≤ R.budget)
    (hreq : ∀ s (hs : s < T) (h : History n s),
      R.request s (hs.trans_le hT) h = parseRequest hn (parse p h)) :
    ValidHistory p hn (extendBlock R.budget v) (R.simulate v T hT) := by
  intro s hs
  have hd := R.simulate_decision v T hT s hs
  refine ⟨hd.1.symm.trans (hreq s hs _), ?_⟩
  simpa only [extendBlock, dif_pos (hs.trans_le hT)] using hd.2

/-- Exact consumed cost and result of a completed bounded program simulation. -/
theorem parse_simulate_eq_execute {β : Type*} [MeasurableSpace β]
    (R : BoundedProcedure n β) (p : Program n α) (hn : 2 ≤ n)
    (v : R.Tape) (T : ℕ) (hT : T ≤ R.budget) (hcap : capacity p ≤ T)
    (hreq : ∀ s (hs : s < T) (h : History n s),
      R.request s (hs.trans_le hT) h = parseRequest hn (parse p h)) :
    parse p (R.simulate v T hT) = .inr (execute p hn (extendBlock R.budget v)) :=
  parse_eq_execute_of_valid p hn _ _ (valid_simulate R p hn v T hT hreq) hcap

end GapEntropy.FiniteCallProgram

namespace GapEntropy.AttemptProcedure
open FiniteCallProgram
variable {n : ℕ}

theorem nextRequest_eq_parseRequest (I : Instance n) (ε : ℝ) (t : ℕ) (h : History n t) :
    nextRequest I ε t h = parseRequest I.two_le (parse (TargetProgram.program I ε) h) := by
  cases hp : parse (TargetProgram.program I ε) h <;> simp [nextRequest, parseRequest, hp]

/-- The actual fixed-cap sampler executes all calls in order; the terminal parser
also records their exact unpadded consumed cost. -/
theorem parse_simulate_eq_execute (I : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) (v : (procedure I ε).Tape) :
    parse (TargetProgram.program I ε)
      ((procedure I ε).simulate v (cap I ε) le_rfl) =
    .inr (execute (TargetProgram.program I ε) I.two_le (extendBlock (cap I ε) v)) := by
  apply FiniteCallProgram.parse_simulate_eq_execute (procedure I ε)
    (TargetProgram.program I ε) I.two_le v (cap I ε) le_rfl (capacity_le_cap I hε hε10)
  intro s hs h
  exact nextRequest_eq_parseRequest I ε s h

/-- Actual padded attempt readout equals recursive execution on its finite reward tape. -/
theorem evaluate_eq_execute (I : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) (v : (procedure I ε).Tape) :
    (procedure I ε).evaluate v =
      (execute (TargetProgram.program I ε) I.two_le (extendBlock (cap I ε) v)).2 := by
  change readout I ε ((procedure I ε).simulate v (cap I ε) le_rfl) = _
  unfold readout
  rw [parse_simulate_eq_execute I hε hε10 v]

/-- The real policy's terminal readout uses precisely the sequential execution's
reward rows. All equality is pathwise and precedes probability calculations. -/
theorem actualOutput_eq_execute (I : Instance n) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) (ω : SampleSpace n) :
    (procedure I ε).actualOutput ω =
      (execute (TargetProgram.program I ε) I.two_le ω.2).2 := by
  rw [BoundedProcedure.actualOutput, evaluate_eq_execute I hε hε10]
  have he := execute_eq_extendBlock (TargetProgram.program I ε) I.two_le
    (cap I ε) (capacity_le_cap I hε hε10) ω.2
  have hb : GaussianBlocks.rewardBlock 0 (cap I ε) ω = firstBlock (cap I ε) ω.2 := by
    funext j
    simp only [GaussianBlocks.rewardBlock, firstBlock, Nat.zero_add]
  change (execute (TargetProgram.program I ε) I.two_le
    (extendBlock (cap I ε) (GaussianBlocks.rewardBlock 0 (cap I ε) ω))).2 = _
  rw [hb]
  exact (congrArg Prod.snd he).symm

end GapEntropy.AttemptProcedure
