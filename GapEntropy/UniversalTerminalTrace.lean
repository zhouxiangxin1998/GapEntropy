import GapEntropy.UniversalFavorablePath
import GapEntropy.TerminalCollapse

/-! Every actual universal return supplies an actual padded deletion trajectory. -/
noncomputable section
open scoped BigOperators Classical
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram UniversalCall
variable {n : ℕ}

def metadataOfStage : Stage n → Metadata n
  | .inl ((a, _), _) => a
  | .inr (a, _) => a

def referenceOfStage : Stage n → ℝ
  | .inl ((_, z), _) => z
  | .inr (_, z) => z

theorem stage_terminal_persists (c : Config) (x : Values n) {t u : ℕ} (htu : t ≤ u)
    {result : State n × Option (Fin n)} (ht : stage c x t = .inl result) :
    stage c x u = .inl result := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le htu
  clear htu
  induction d with
  | zero => simpa using ht
  | succ d ih =>
      rw [show t + (d + 1) = (t + d) + 1 by omega, stage, ih]
      rfl

theorem metadata_scale_step (c : Config) (x : Values n) (st : Stage n) :
    (metadataOfStage st).scale ≤ (metadataOfStage (stageStep c x st)).scale := by
  cases st with
  | inl result => rfl
  | inr state =>
      rcases state with ⟨a, z⟩
      simp only [stageStep]
      split_ifs <;> simp only [metadataOfStage, Metadata.advance, Metadata.scale]
      all_goals first | omega | (split_ifs <;> omega)

theorem metadata_scale_mono (c : Config) (x : Values n) :
    Monotone (fun t => (metadataOfStage (stage c x t)).scale) :=
  monotone_nat_of_le_succ (fun _t => metadata_scale_step c x _)

/-- First termination, recovered from the true deterministic controller execution. -/
theorem exists_first_return_stage (c : Config) (x : Values n) (out : Fin n)
    (hout : (execute c c.fuel (initial n) 0 x).2 = some out) :
    ∃ T ≤ c.fuel, ∃ st : State n,
      stage c x T = .inl (st, some out) ∧
        ∀ t < T, ∃ a z, stage c x t = .inr (a, z) := by
  have hex : ∃ t, ∃ result, stage c x t = .inl result :=
    ⟨c.fuel, _, stage_fuel_eq_execute c x⟩
  let T := Nat.find hex
  obtain ⟨result, hresult⟩ := Nat.find_spec hex
  have hT : T ≤ c.fuel := Nat.find_min' hex ⟨_, stage_fuel_eq_execute c x⟩
  have hlast := stage_terminal_persists c x hT hresult
  rw [stage_fuel_eq_execute] at hlast
  have he := Sum.inl.inj hlast
  have hr : result.2 = some out := by rw [← he]; exact hout
  refine ⟨T, hT, result.1, ?_, ?_⟩
  · simpa only [← hr, Prod.mk.eta] using hresult
  · intro t ht
    cases hs : stage c x t with
    | inl result => exact False.elim ((Nat.find_min hex ht) ⟨result, hs⟩)
    | inr st => exact ⟨st.1, st.2, rfl⟩

/-- A stage preceding a true return cannot have rejected its reservation:
that would create an absorbing abort result. -/
theorem allowed_before_return (c : Config) (x : Values n) {T t : ℕ} (ht : t < T)
    {st : State n} {out : Fin n} (hreturn : stage c x T = .inl (st, some out))
    {a : Metadata n} {z : ℝ} (hstate : stage c x t = .inr (a, z)) : a.Allowed c := by
  by_contra hnot
  have hnext : stage c x (t + 1) = .inl ((a, z), none) := by
    simp only [stage, hstate, stageStep, dif_neg hnot]
  have hlast := stage_terminal_persists c x (Nat.succ_le_of_lt ht) hnext
  rw [hreturn] at hlast
  have he := congrArg Prod.snd (Sum.inl.inj hlast)
  contradiction

/-- The real local simulation history of the accepted call. -/
def callObservedHistory (c : Config) (x : Values n) (a : Metadata n) (ha : a.Allowed c) (z : ℝ) :
    History n (a.call c).samples :=
  (callProcedure c a ha.1 z).simulate
    (firstBlock (a.call c).samples (shiftValues a.samples x)) (a.call c).samples le_rfl

def callObservedEstimates (c : Config) (x : Values n) (a : Metadata n)
    (ha : a.Allowed c) (z : ℝ) : Fin n → ℝ :=
  estimateFromHistory a.active
    (if a.entry then activeStart a.active.card a.tolerance (a.alpha c) (a.beta c) else 0)
    (EliminationTape.activeSamples a.tolerance (a.alpha c)) (callObservedHistory c x a ha z)

theorem callResult_eq_padded (c : Config) (x : Values n) (a : Metadata n)
    (ha : a.Allowed c) (z : ℝ) :
    (callResult c x a ha z).2 = Elimination.padded a.active
      (callObservedEstimates c x a ha z) (callResult c x a ha z).1 a.tolerance := by
  change (readout c a z (callObservedHistory c x a ha z)).2 = _
  change _ = Elimination.padded a.active (callObservedEstimates c x a ha z)
    (readout c a z (callObservedHistory c x a ha z)).1 a.tolerance
  unfold readout callObservedEstimates
  cases a.entry <;> simp only [Bool.false_eq_true, ↓reduceIte,
    entryReadout, laterReadout]

def observedEstimates (c : Config) (x : Values n) (t : ℕ) : Fin n → ℝ :=
  match stage c x t with
  | .inl _ => fun _ => 0
  | .inr (a, z) => if ha : a.Allowed c then callObservedEstimates c x a ha z else fun _ => 0

def observedReference (c : Config) (x : Values n) (t : ℕ) : ℝ :=
  match stage c x t with
  | .inl _ => 0
  | .inr (a, z) => if ha : a.Allowed c then (callResult c x a ha z).1 else z

theorem metadata_active_step (c : Config) (x : Values n) (a : Metadata n)
    (ha : a.Allowed c) (z : ℝ) :
    (metadataOfStage (stageStep c x (.inr (a, z)))).active =
      (callResult c x a ha z).2 := by
  simp only [stageStep, dif_pos ha]
  split_ifs <;> rfl

/-- No statistical assumptions enter the actual padded trajectory construction. -/
def terminalTrajectory (c : Config) (x : Values n) (T : ℕ)
    (haccepted : ∀ t < T, ∃ a z, stage c x t = .inr (a, z) ∧ a.Allowed c) :
    Elimination.PaddedTrajectory n T where
  active t := (metadataOfStage (stage c x t)).active
  tolerance t := (metadataOfStage (stage c x t)).tolerance
  estimates := observedEstimates c x
  reference := observedReference c x
  initial := rfl
  tolerance_pos t _ := by unfold Metadata.tolerance; positivity
  tolerance_antitone t u htu _ := by
    simp only [Metadata.tolerance, zpow_neg, zpow_natCast]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr
      (pow_le_pow_right₀ (by norm_num) (metadata_scale_mono c x htu))
  step t ht := by
    obtain ⟨a, z, hs, ha⟩ := haccepted t ht
    rw [stage, hs, metadata_active_step c x a ha z]
    simpa only [observedEstimates, observedReference, hs, dif_pos ha, metadataOfStage]
      using callResult_eq_padded c x a ha z

theorem singletonAnswer_some_imp {R : Finset (Fin n)} {out : Fin n}
    (h : singletonAnswer R = some out) : R = {out} := by
  by_cases hc : R.card = 1
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    have he : a = out := by simpa [singletonAnswer] using h
    rw [he]
  · simp [singletonAnswer, hc] at h

/-- The actual return value is precisely the surviving singleton label. -/
theorem stage_return_singleton (c : Config) (x : Values n) (t : ℕ)
    (st : State n) (out : Fin n) (hs : stage c x t = .inl (st, some out)) :
    st.1.active = {out} := by
  induction t generalizing st with
  | zero => simp only [stage] at hs; contradiction
  | succ t ih =>
      cases hp : stage c x t with
      | inl result =>
          have he : result = (st, some out) := Sum.inl.inj (by
            simpa only [stage, hp, stageStep] using hs)
          exact ih st (by simpa only [he] using hp)
      | inr state =>
          rcases state with ⟨a, z⟩
          simp only [stage, hp, stageStep] at hs
          split_ifs at hs with ha hc
          · have hresult := Sum.inl.inj hs
            have hout := singletonAnswer_some_imp (congrArg Prod.snd hresult)
            have hmeta := congrArg (fun r : State n × Option (Fin n) => r.1.1) hresult
            rw [← hmeta]
            exact hout
          · have he := congrArg Prod.snd (Sum.inl.inj hs)
            contradiction

/-- The first actual return gives a finite accepted-call trajectory and its true
terminal singleton. Its calls may contain arbitrary statistical errors. -/
theorem exists_terminalTrajectory_of_return (c : Config) (x : Values n) (out : Fin n)
    (hout : (execute c c.fuel (initial n) 0 x).2 = some out) :
    ∃ T ≤ c.fuel,
      ∃ haccepted : ∀ t < T, ∃ a z, stage c x t = .inr (a, z) ∧ a.Allowed c,
        (terminalTrajectory c x T haccepted).active T = {out} := by
  obtain ⟨T, hT, st, hs, hbefore⟩ := exists_first_return_stage c x out hout
  have haccepted : ∀ t < T, ∃ a z, stage c x t = .inr (a, z) ∧ a.Allowed c := by
    intro t ht
    obtain ⟨a, z, hstate⟩ := hbefore t ht
    exact ⟨a, z, hstate, allowed_before_return c x ht hs hstate⟩
  refine ⟨T, hT, haccepted, ?_⟩
  change (metadataOfStage (stage c x T)).active = _
  rw [hs]
  exact stage_return_singleton c x T st out hs

end GapEntropy.UniversalAttempt
