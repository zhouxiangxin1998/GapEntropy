import GapEntropy.AdaptiveGaussianCalls
import GapEntropy.UniversalStageFiltration
import GapEntropy.UniversalStageBudget
import GapEntropy.EverFlags
import GapEntropy.BernoulliFlagTails
import GapEntropy.Problem

/-! Actual chronological universal-call severe flags, conditional product law, and common hazard. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Classical NNReal
namespace GapEntropy.UniversalSevereProcess
open UniversalAttempt UniversalCall EliminationTape
variable {n : ℕ}

abbrev Accepted (c : Config) (n : ℕ) := {a : Metadata n // a.Allowed c}

instance (c : Config) : MeasurableSpace (Option (Accepted c n)) := ⊤
instance (c : Config) : MeasurableSingletonClass (Option (Accepted c n)) := ⟨fun _ => trivial⟩

def choiceFromStage (c : Config) : Stage n → Option (Accepted c n)
  | .inl _ => none
  | .inr (a, _) => if ha : a.Allowed c then some ⟨a, ha⟩ else none

def choice (c : Config) (r : ℕ) (ω : SampleSpace n) : Option (Accepted c n) :=
  choiceFromStage c (stage c ω.2 r)

theorem measurable_choiceFromStage (c : Config) : Measurable (choiceFromStage c (n := n)) := by
  have hl : Measurable (fun _ : State n × Option (Fin n) => (none : Option (Accepted c n))) := measurable_const
  have hr : Measurable (fun p : State n =>
      if ha : p.1.Allowed c then some (⟨p.1, ha⟩ : Accepted c n) else none) :=
    (measurable_of_countable (fun a : Metadata n =>
      if ha : a.Allowed c then some (⟨a, ha⟩ : Accepted c n) else none)).comp measurable_fst
  exact hl.sumElim hr

theorem choice_adapted (c : Config) (r : ℕ) :
    Measurable[callPast c r] (choice c (n := n) r) :=
  (measurable_choiceFromStage c).comp (stage_adapted c r)

def activeOffset (c : Config) (a : Metadata n) : ℕ :=
  if a.entry then activeStart a.active.card a.tolerance (a.alpha c) (a.beta c) else 0

def activeBoundary (c : Config) (a : Metadata n) : ℕ := a.samples + activeOffset c a

theorem tolerance_pos (a : Metadata n) : 0 < a.tolerance := by
  unfold Metadata.tolerance
  positivity

theorem alpha_pos (c : Config) (hδ : 0 < c.confidence) (a : Accepted c n) : 0 < a.val.alpha c := by
  have hw : 0 < a.val.baseCall.work := by
    have := Reservation.two_le_call_work a.val.baseCall a.property.1
    omega
  unfold Metadata.alpha Reservation.callConfidence Config.errorBudget
  apply mul_pos
  · exact div_pos (mul_pos (by positivity) (by exact_mod_cast hw)) (by unfold Config.workCap; positivity)
  · unfold Reservation.smallFactor
    split_ifs <;> positivity

theorem alpha_le_errorBudget (c : Config) (hδ : 0 ≤ c.confidence) (a : Accepted c n) :
    a.val.alpha c ≤ c.errorBudget := by
  have hw : a.val.baseCall.work ≤ c.workCap := by
    have := a.property.2.1
    change a.val.work + a.val.baseCall.work ≤ c.workCap at this
    omega
  have hM : (0 : ℝ) < c.workCap := by unfold Config.workCap; positivity
  have hγ : 0 ≤ c.errorBudget := by unfold Config.errorBudget; positivity
  apply (Reservation.callConfidence_le_work_fraction hγ _ _ _).trans
  apply (div_le_iff₀ hM).mpr
  have hwR : (a.val.baseCall.work : ℝ) ≤ c.workCap := by exact_mod_cast hw
  nlinarith

def gaussianSchedule (c : Config) (hδ : ValidConfidence c.confidence) :
    AdaptiveGaussianCalls.Schedule (Accepted c n) n where
  active a := a.val.active
  start a := activeBoundary c a.val
  samples a := activeSamples a.val.tolerance (a.val.alpha c)
  tolerance a := a.val.tolerance
  active_nonempty a := Finset.card_pos.mp (by have := a.property.1; omega)
  samples_pos a := activeSamples_pos (tolerance_pos a.val) (alpha_pos c hδ.1 a)
    ((alpha_le_errorBudget c hδ.1.le a).trans (by
      unfold Config.errorBudget
      linarith [hδ.2]))

theorem boundary_of_choice_some (c : Config) (r : ℕ) (a : Accepted c n)
    (ω : SampleSpace n) (ha : choice c r ω = some a) :
    boundary (stage c ω.2 r) = a.val.samples := by
  unfold choice choiceFromStage at ha
  cases hs : stage c ω.2 r with
  | inl result => simp only [hs] at ha; contradiction
  | inr st =>
    rcases st with ⟨b, z⟩
    rw [hs] at ha
    dsimp only at ha
    split_ifs at ha with hb
    · have he := Option.some.inj ha
      have hba : b = a.val := congrArg Subtype.val he
      simp only [boundary, hba]

theorem schedule_past (c : Config) (hδ : ValidConfidence c.confidence) (r : ℕ) :
    (gaussianSchedule c hδ (n := n)).OptionalPastAtChoice (callPast c r) (choice c r) := by
  intro R hR a
  exact past_event_choice_prefix c r (choice c r) (choice_adapted c r) (some a)
    a.val.samples (activeBoundary c a.val) (by unfold activeBoundary; omega)
    (fun ω h => boundary_of_choice_some c r a ω h) R hR

/-- Actual fresh severe indicators for the next executed call; terminal and rejected stages
produce the zero vector. The mean is used solely for the analysis predicate. -/
def fresh (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ)
    (r : ℕ) : SampleSpace n → Fin n → Bool :=
  (gaussianSchedule c hδ).optionalFlags mean (choice c r)

def parameters (c : Config) (hδ : ValidConfidence c.confidence) (r : ℕ)
    (ω : SampleSpace n) : Fin n → unitInterval :=
  (gaussianSchedule c hδ).optionalParameters (choice c r ω)

/-- The actual universal controller satisfies the complete conditional Bernoulli law.
This theorem has only the controller configuration and confidence-domain assumption. -/
theorem conditional_joint_law (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (r : ℕ) :
    HasConditionalBernoulliLaw (sampleLawOfMeans mean) (callPast c r)
      (fresh c hδ mean r) (parameters c hδ r) :=
  (gaussianSchedule c hδ).optional_hasConditionalBernoulliLaw mean
    ((callFiltration c).le r) (choice_adapted c r) (schedule_past c hδ r)

theorem active_block_end (c : Config) (a : Metadata n) :
    activeBoundary c a + a.active.card * activeSamples a.tolerance (a.alpha c) =
      a.samples + (a.call c).samples := by
  unfold activeBoundary activeOffset Metadata.call
  split_ifs <;> simp [entryBudget, laterBudget, Nat.add_assoc]

theorem end_boundary_of_choice_some (c : Config) (r : ℕ) (a : Accepted c n)
    (ω : SampleSpace n) (ha : choice c r ω = some a) :
    boundary (stage c ω.2 (r + 1)) = a.val.samples + (a.val.call c).samples := by
  rw [stage, boundary_stageStep]
  unfold choice choiceFromStage at ha
  cases hs : stage c ω.2 r with
  | inl result => simp only [hs] at ha; contradiction
  | inr st =>
    rcases st with ⟨b, z⟩
    rw [hs] at ha
    dsimp only at ha
    split_ifs at ha with hb
    have hba : b = a.val := congrArg Subtype.val (Option.some.inj ha)
    simp only [nextBoundary, hba, if_pos a.property]

theorem fresh_measurable (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (r : ℕ) : Measurable (fresh c hδ mean (n := n) r) :=
  (gaussianSchedule c hδ).measurable_optionalFlags mean
    ((choice_adapted c r).mono ((callFiltration c).le r) le_rfl)

/-- The fresh vector uses only rows strictly before the following actual call boundary. -/
theorem fresh_reconstruct (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (r : ℕ) (ω : SampleSpace n) :
    fresh c hδ mean r ω =
      fresh c hδ mean r ((stoppedData c (r + 1) ω).1, (stoppedData c (r + 1) ω).2.2) := by
  have hc : choice c r ((stoppedData c (r + 1) ω).1, (stoppedData c (r + 1) ω).2.2) =
      choice c r ω := by
    unfold choice
    rw [← stage_eq_from_later_stoppedData c r (r + 1) (by omega) ω]
  unfold fresh AdaptiveGaussianCalls.Schedule.optionalFlags
  rw [hc]
  cases ha : choice c r ω with
  | none => rfl
  | some a =>
    change AdaptiveGaussianCalls.scheduledSevere _ _ _ _ _ ω =
      AdaptiveGaussianCalls.scheduledSevere _ _ _ _ _ _
    funext i
    unfold AdaptiveGaussianCalls.scheduledSevere
    congr 2
    funext j
    unfold MedianPolicy.fixedObservation
    congr 1
    have ht := active_index_lt a.val.active
      (Finset.card_pos.mp (show 0 < a.val.active.card by have := a.property.1; omega))
      (activeBoundary c a.val) (activeSamples a.val.tolerance (a.val.alpha c)) i j
    have hend := end_boundary_of_choice_some c r a ω ha
    rw [active_block_end] at ht
    exact congrArg (fun v => v i) (maskedRows_eq (boundary (stage c ω.2 (r + 1))) ω.2
      (activeBoundary c a.val + MedianPolicy.armRank a.val.active i *
        activeSamples a.val.tolerance (a.val.alpha c) + j) (by omega)).symm

/-- Fresh flags are measurable at the next actual stage of the chronological filtration. -/
theorem fresh_adapted (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (r : ℕ) :
    Measurable[callPast c (r + 1)] (fresh c hδ mean (n := n) r) := by
  have hm : Measurable (fun p : StoppedData n => fresh c hδ mean r (p.1, p.2.2)) :=
    (fresh_measurable c hδ mean r).comp (measurable_fst.prodMk measurable_snd.snd)
  have heq : fresh c hδ mean (n := n) r =
      (fun p : StoppedData n => fresh c hδ mean r (p.1, p.2.2)) ∘ stoppedData c (r + 1) :=
    funext (fresh_reconstruct c hδ mean r)
  rw [heq]
  exact hm.comp (comap_measurable (stoppedData c (r + 1)))

def eta (c : Config) : ℝ := c.errorBudget / 128

def rho (c : Config) (r : ℕ) (ω : SampleSpace n) : ℝ :=
  confidenceCharge c (stage c ω.2 r) / 128

theorem rho_nonneg (c : Config) (hδ : 0 ≤ c.confidence) (r : ℕ) (ω : SampleSpace n) :
    0 ≤ rho c r ω := div_nonneg (confidenceCharge_nonneg c hδ _) (by norm_num)

theorem rho_le_eta (c : Config) (hδ : 0 ≤ c.confidence) (r : ℕ) (ω : SampleSpace n) :
    rho c r ω ≤ eta c := div_le_div_of_nonneg_right (stage_confidence_le c hδ ω.2 r) (by norm_num)

theorem eta_nonneg (c : Config) (hδ : 0 ≤ c.confidence) : 0 ≤ eta c := by
  unfold eta Config.errorBudget
  positivity

theorem eta_le_half (c : Config) (hδ : ValidConfidence c.confidence) : eta c ≤ 1 / 2 := by
  unfold eta Config.errorBudget
  linarith [hδ.2]

theorem sum_rho_le_eta (c : Config) (hδ : 0 ≤ c.confidence) (R : ℕ) (ω : SampleSpace n) :
    (∑ r ∈ Finset.range R, rho c r ω) ≤ eta c := by
  unfold rho eta
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (stage_confidence_sum_le c hδ ω.2 R) (by norm_num)

/-- A simple common hazard increment dominates a Bernoulli parameter bounded by r≤1/2. -/
theorem le_hazard_double {p : unitInterval} {r : ℝ} (hr0 : 0 ≤ r) (hrhalf : r ≤ 1 / 2)
    (hp : (p : ℝ) ≤ r) : p ≤ hazardProbability (⟨2 * r, by positivity⟩ : ℝ≥0) := by
  change (p : ℝ) ≤ 1 - Real.exp (-(2 * r))
  have hexp := Real.add_one_le_exp (2 * r)
  have hmul := mul_le_mul_of_nonneg_left hexp (show 0 ≤ 1 - r by linarith)
  have hinv : Real.exp (-(2 * r)) ≤ 1 - r := by
    rw [Real.exp_neg, ← one_div]
    apply (div_le_iff₀ (Real.exp_pos (2 * r))).mpr
    nlinarith
  linarith

def hazardBudget (c : Config) (hδ : ValidConfidence c.confidence) : ℝ≥0 :=
  ⟨2 * eta c ^ (25 : ℕ), by have := eta_nonneg c hδ.1.le; positivity⟩

def increment (c : Config) (hδ : ValidConfidence c.confidence) (r : ℕ) (ω : SampleSpace n) : ℝ≥0 :=
  ⟨2 * rho c r ω ^ (25 : ℕ), by have := rho_nonneg c hδ.1.le r ω; positivity⟩

def remaining (c : Config) (hδ : ValidConfidence c.confidence) (r : ℕ) (ω : SampleSpace n) : ℝ≥0 :=
  hazardBudget c hδ - ∑ t ∈ Finset.range r, increment c hδ t ω

/-- The manuscript's common hazard cap is derived from the actual controller's confidence
reservations on every path, including erroneous and aborted paths. -/
theorem sum_increment_le (c : Config) (hδ : ValidConfidence c.confidence) (R : ℕ) (ω : SampleSpace n) :
    (∑ r ∈ Finset.range R, increment c hδ r ω) ≤ hazardBudget c hδ := by
  have hη0 := eta_nonneg c hδ.1.le
  have hpoint (r : ℕ) : 2 * rho c r ω ^ (25 : ℕ) ≤ 2 * eta c ^ (24 : ℕ) * rho c r ω := by
    have hp := pow_le_pow_left₀ (rho_nonneg c hδ.1.le r ω) (rho_le_eta c hδ.1.le r ω) 24
    have h := mul_le_mul_of_nonneg_right hp (rho_nonneg c hδ.1.le r ω)
    rw [show (25 : ℕ) = 24 + 1 by omega, pow_succ]
    nlinarith
  have hreal : (∑ r ∈ Finset.range R, 2 * rho c r ω ^ (25 : ℕ)) ≤ 2 * eta c ^ (25 : ℕ) := by
    calc
      (∑ r ∈ Finset.range R, 2 * rho c r ω ^ (25 : ℕ)) ≤
          ∑ r ∈ Finset.range R, 2 * eta c ^ (24 : ℕ) * rho c r ω :=
        Finset.sum_le_sum fun r _ => hpoint r
      _ = 2 * eta c ^ (24 : ℕ) * ∑ r ∈ Finset.range R, rho c r ω := (Finset.mul_sum ..).symm
      _ ≤ 2 * eta c ^ (25 : ℕ) := by
        have h := mul_le_mul_of_nonneg_left (sum_rho_le_eta c hδ.1.le R ω)
          (show 0 ≤ 2 * eta c ^ (24 : ℕ) by positivity)
        simpa only [pow_succ, mul_assoc] using h
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_sum]
  exact hreal

theorem parameters_le_rho_pow (c : Config) (hδ : ValidConfidence c.confidence)
    (r : ℕ) (ω : SampleSpace n) (i : Fin n) :
    (parameters c hδ r ω i : ℝ) ≤ rho c r ω ^ (25 : ℕ) := by
  have hρ0 := rho_nonneg c hδ.1.le r ω
  unfold parameters AdaptiveGaussianCalls.Schedule.optionalParameters
  cases ha : choice c r ω with
  | none => exact pow_nonneg hρ0 _
  | some a =>
    have hρeq : rho c r ω = a.val.alpha c / 128 := by
      unfold rho choice choiceFromStage at *
      cases hs : stage c ω.2 r with
      | inl result => simp only [hs] at ha; contradiction
      | inr st =>
        rcases st with ⟨b, z⟩
        rw [hs] at ha
        dsimp only at ha
        split_ifs at ha with hb
        have hba : b = a.val := congrArg Subtype.val (Option.some.inj ha)
        simp only [confidenceCharge, hba, if_pos a.property]
    rw [hρeq]
    exact AdaptiveGaussianCalls.severeProbability_le (tolerance_pos a.val)
      (by have := alpha_pos c hδ.1 a; positivity)
      (by simpa only [gaussianSchedule, one_div, inv_div, one_mul, activeSamples] using
        (Nat.le_ceil (512 * (a.val.tolerance ^ 2)⁻¹ * Real.log (128 / a.val.alpha c))))
      ((gaussianSchedule c hδ).samples_pos a)

theorem parameters_le_increment (c : Config) (hδ : ValidConfidence c.confidence)
    (r : ℕ) (ω : SampleSpace n) (i : Fin n) :
    parameters c hδ r ω i ≤ hazardProbability (increment c hδ r ω) := by
  have hρ0 := rho_nonneg c hδ.1.le r ω
  have hρhalf := (rho_le_eta c hδ.1.le r ω).trans (eta_le_half c hδ)
  have hrhalf : rho c r ω ^ (25 : ℕ) ≤ 1 / 2 := by
    have hp := pow_le_pow_of_le_one hρ0 (show rho c r ω ≤ 1 by linarith) (show 1 ≤ 25 by omega)
    norm_num only [pow_one] at hp
    exact hp.trans hρhalf
  exact le_hazard_double (pow_nonneg hρ0 _) hrhalf (parameters_le_rho_pow c hδ r ω i)

def active (c : Config) (r : ℕ) (ω : SampleSpace n) : Finset (Fin n) :=
  match choice c r ω with
  | none => ∅
  | some a => a.val.active

def flags (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ) :
    ℕ → SampleSpace n → Finset (Fin n)
  | 0, _ => ∅
  | r + 1, ω => flags c hδ mean r ω ∪ (freshFlagSet (fresh c hδ mean r ω) ∩ active c r ω)

theorem active_adapted (c : Config) (r : ℕ) : Measurable[callPast c r] (active c (n := n) r) :=
  (measurable_of_countable (fun k : Option (Accepted c n) =>
    (match k with | none => ∅ | some a => a.val.active : Finset (Fin n)))).comp (choice_adapted c r)

theorem flags_adapted (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ) (r : ℕ) :
    Measurable[callPast c r] (flags c hδ mean (n := n) r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
    have hU : Measurable (fun p : Finset (Fin n) × (Finset (Fin n) × Finset (Fin n)) =>
        p.1 ∪ (p.2.1 ∩ p.2.2)) := measurable_of_finite _
    exact hU.comp ((ih.mono ((callPast_mono c) (Nat.le_succ r)) le_rfl).prodMk
      (((measurable_of_finite freshFlagSet).comp (fresh_adapted c hδ mean r)).prodMk
        ((active_adapted c r).mono ((callPast_mono c) (Nat.le_succ r)) le_rfl)))

theorem increment_adapted (c : Config) (hδ : ValidConfidence c.confidence) (r : ℕ) :
    Measurable[callPast c r] (increment c hδ (n := n) r) :=
  (((confidenceCharge_adapted c r).div_const 128).pow_const 25 |>.const_mul 2).subtype_mk

theorem remaining_adapted (c : Config) (hδ : ValidConfidence c.confidence) (r : ℕ) :
    Measurable[callPast c r] (remaining c hδ (n := n) r) := by
  apply measurable_const.sub
  apply Finset.measurable_sum
  intro t ht
  exact (increment_adapted c hδ t).mono ((callPast_mono c) (by
    exact (Finset.mem_range.mp ht).le)) le_rfl

/-- The full predictable Bernoulli process is constructed from actual controller states,
actual Gaussian observations, and actual confidence reservations. -/
def process (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ) :
    PredictableBernoulliProcess (ι := Fin n) (sampleLawOfMeans mean) (callFiltration c) where
  flags := flags c hδ mean
  active := active c
  remaining := remaining c hδ
  increment := increment c hδ
  parameters := parameters c hδ
  fresh := fresh c hδ mean
  measurable_flags := flags_adapted c hδ mean
  measurable_active := active_adapted c
  measurable_remaining := remaining_adapted c hδ
  measurable_increment := increment_adapted c hδ
  measurable_parameters r i :=
    (measurable_of_countable (fun k : Option (Accepted c n) =>
      (gaussianSchedule c hδ).optionalParameters k i)).comp (choice_adapted c r)
  measurable_fresh := fresh_adapted c hδ mean
  increment_le r ω := by
    apply (le_tsub_iff_left (sum_increment_le c hδ r ω)).mpr
    simpa only [Finset.sum_range_succ] using sum_increment_le c hδ (r + 1) ω
  parameters_le := parameters_le_increment c hδ
  remaining_succ r ω := by
    simp only [remaining, Finset.sum_range_succ, tsub_add_eq_tsub_tsub]
  flags_succ _ _ := rfl
  conditional_law := conditional_joint_law c hδ mean

@[simp] theorem process_flags_zero (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (ω : SampleSpace n) : (process c hδ mean).flags 0 ω = ∅ := rfl

@[simp] theorem process_remaining_zero (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (ω : SampleSpace n) :
    (process c hδ mean).remaining 0 ω = hazardBudget c hδ := by
  simp only [process, remaining, Finset.range_zero, Finset.sum_empty, tsub_zero]

/-- E.1's infinite ever-flag joint stochastic domination for the actual universal attempt.
Only the original means, controller configuration, and valid confidence remain as inputs. -/
theorem probability_everFlags_increasing_event_le (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (S : Set (Finset (Fin n)))
    (hS : ∀ F G, F ⊆ G → F ∈ S → G ∈ S) :
    sampleLawOfMeans mean {ω | (process c hδ mean).everFlags ω ∈ S} ≤
      bernoulliFlagLaw (fun _ : Fin n => hazardProbability (hazardBudget c hδ))
        {x | freshFlagSet x ∈ S} := by
  exact (process c hδ mean).probability_everFlags_increasing_event_le (hazardBudget c hδ)
    (fun ω => process_flags_zero c hδ mean ω) (fun ω => process_remaining_zero c hδ mean ω) S hS

theorem mem_flags_iff (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ)
    (r : ℕ) (ω : SampleSpace n) (i : Fin n) :
    i ∈ flags c hδ mean r ω ↔ ∃ t < r, i ∈ active c t ω ∧ fresh c hδ mean t ω i = true := by
  induction r with
  | zero => simp [flags]
  | succ r ih =>
    simp only [flags, Finset.mem_union, Finset.mem_inter, mem_freshFlagSet, ih]
    constructor
    · rintro (⟨t, ht, hi, hf⟩ | ⟨hf, hi⟩)
      · exact ⟨t, Nat.lt_succ_of_lt ht, hi, hf⟩
      · exact ⟨r, Nat.lt_succ_self r, hi, hf⟩
    · rintro ⟨t, ht, hi, hf⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with hlt | rfl
      · exact Or.inl ⟨t, hlt, hi, hf⟩
      · exact Or.inr ⟨hf, hi⟩

/-- The process ever-flags are exactly actual active-arm severe errors on some executed call. -/
theorem mem_everFlags_iff (c : Config) (hδ : ValidConfidence c.confidence) (mean : Fin n → ℝ)
    (ω : SampleSpace n) (i : Fin n) :
    i ∈ (process c hδ mean).everFlags ω ↔
      ∃ t, i ∈ active c t ω ∧ fresh c hδ mean t ω i = true := by
  change i ∈ everFlagSet (fun r => flags c hδ mean r ω) ↔ _
  rw [mem_everFlagSet]
  simp only [mem_flags_iff]
  constructor
  · rintro ⟨r, t, ht, hi, hf⟩
    exact ⟨t, hi, hf⟩
  · rintro ⟨t, hi, hf⟩
    exact ⟨t + 1, t, Nat.lt_succ_self t, hi, hf⟩

def comparisonProbability (c : Config) : ℝ := 2 * eta c ^ (25 : ℕ)

theorem comparisonProbability_pos (c : Config) (hδ : ValidConfidence c.confidence) :
    0 < comparisonProbability c := by
  have hη : 0 < eta c := by unfold eta Config.errorBudget; exact div_pos (div_pos hδ.1 (by norm_num)) (by norm_num)
  unfold comparisonProbability
  positivity

theorem comparisonProbability_lt_half (c : Config) (hδ : ValidConfidence c.confidence) :
    comparisonProbability c < 1 / 2 := by
  have hη0 := eta_nonneg c hδ.1.le
  have hηhalf := eta_le_half c hδ
  have hp := pow_le_pow_of_le_one hη0 (show eta c ≤ 1 by linarith) (show 1 ≤ 25 by omega)
  norm_num only [pow_one] at hp
  unfold comparisonProbability
  have hηsmall : eta c < 1 / 4 := by unfold eta Config.errorBudget; linarith [hδ.2]
  linarith

/-- E.7 for the actual universal attempt's complete trajectory. -/
theorem probability_core_flags_le (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (B : Finset (Fin n)) (hB : B.Nonempty) :
    sampleLawOfMeans mean {ω | max 1 (B.card - 1) ≤ (B ∩ (process c hδ mean).everFlags ω).card} ≤
      ENNReal.ofReal ((B.card : ℝ) * comparisonProbability c ^ max 1 (B.card - 1)) :=
  (process c hδ mean).probability_everFlags_core_le (hazardBudget c hδ)
    (fun ω => process_flags_zero c hδ mean ω) (fun ω => process_remaining_zero c hδ mean ω)
    B hB (comparisonProbability c) le_rfl

/-- E.10/E.11's joint core and outside-weight bound for actual universal-call ever-flags. -/
theorem probability_core_weighted_flags_le (c : Config) (hδ : ValidConfidence c.confidence)
    (mean : Fin n → ℝ) (B outside : Finset (Fin n)) (hB : B.Nonempty) (hdisjoint : Disjoint B outside)
    (a : Fin n → ℝ) (ha0 : ∀ i ∈ outside, 0 ≤ a i) (M : ℝ) (hM : 0 < M)
    (haM : ∀ i ∈ outside, a i ≤ 32 * M) :
    sampleLawOfMeans mean {ω | max 1 (B.card - 1) ≤ (B ∩ (process c hδ mean).everFlags ω).card ∧
      (∑ i ∈ outside, a i) / 2 ≤ ∑ i ∈ outside ∩ (process c hδ mean).everFlags ω, a i} ≤
      ENNReal.ofReal ((B.card : ℝ) * comparisonProbability c ^ max 1 (B.card - 1) *
        Real.exp (-((∑ i ∈ outside, a i) / (64 * M)) * Real.log (1 / (2 * comparisonProbability c)) +
          (∑ i ∈ outside, a i) / (64 * M))) :=
  (process c hδ mean).probability_everFlags_core_weighted_le (hazardBudget c hδ)
    (fun ω => process_flags_zero c hδ mean ω) (fun ω => process_remaining_zero c hδ mean ω)
    B outside hB hdisjoint a ha0 M hM haM (comparisonProbability c)
    (comparisonProbability_pos c hδ) (comparisonProbability_lt_half c hδ) le_rfl

end GapEntropy.UniversalSevereProcess
