import GapEntropy.UniversalSevereProcess
import GapEntropy.UniversalErrorBudget

/-! The stronger confidence and severe-tail budget for actual small active sets. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace GapEntropy.UniversalSevereProcess
open UniversalAttempt FiniteCallProgram
variable {n : ℕ}

def smallRho (c : Config) (r : ℕ) (ω : SampleSpace n) : ℝ :=
  if (active c r ω).card ≤ 7 then rho c r ω else 0

def smallEta (c : Config) : ℝ := eta c / (c.attempt + 1 : ℝ) ^ 2

theorem smallRho_nonneg (c : Config) (hδ : 0 ≤ c.confidence) (r : ℕ) (ω : SampleSpace n) :
    0 ≤ smallRho c r ω := by
  unfold smallRho
  split_ifs
  · exact rho_nonneg c hδ r ω
  · exact le_rfl

theorem smallEta_nonneg (c : Config) (hδ : 0 ≤ c.confidence) : 0 ≤ smallEta c :=
  div_nonneg (eta_nonneg c hδ) (sq_nonneg _)

theorem smallRho_le_work (c : Config) (hδ : 0 ≤ c.confidence) (r : ℕ) (ω : SampleSpace n) :
    smallRho c r ω ≤ eta c * (workCharge c (stage c ω.2 r) : ℝ) /
      (c.workCap : ℝ) / (c.attempt + 1 : ℝ) ^ 2 := by
  unfold smallRho rho active choice choiceFromStage
  cases hs : stage c ω.2 r with
  | inl result => simp [confidenceCharge, workCharge]
  | inr state =>
      rcases state with ⟨a, z⟩
      by_cases ha : a.Allowed c
      · simp only [dif_pos ha, confidenceCharge, workCharge, if_pos ha]
        by_cases hsmall : a.active.card ≤ 7
        · rw [if_pos hsmall]
          unfold Metadata.alpha Reservation.callConfidence eta
          rw [Reservation.smallFactor, if_pos ⟨ha.1, hsmall⟩]
          simp only [Metadata.baseCall, Metadata.call, Reservation.Call.work, Nat.cast_add, Nat.cast_one]
          simp only [div_eq_mul_inv]
          ring_nf
          exact le_rfl
        · rw [if_neg hsmall]
          have hη := eta_nonneg c hδ
          positivity
      · simp [ha, confidenceCharge, workCharge]

theorem sum_smallRho_le (c : Config) (hδ : 0 ≤ c.confidence) (R : ℕ) (ω : SampleSpace n) :
    (∑ r ∈ Finset.range R, smallRho c r ω) ≤ smallEta c := by
  have hη := eta_nonneg c hδ
  have hM : (0 : ℝ) < c.workCap := by unfold Config.workCap; positivity
  calc
    _ ≤ ∑ r ∈ Finset.range R, eta c * (workCharge c (stage c ω.2 r) : ℝ) /
        (c.workCap : ℝ) / (c.attempt + 1 : ℝ) ^ 2 :=
      Finset.sum_le_sum (fun r _ => smallRho_le_work c hδ r ω)
    _ = (eta c * ((∑ r ∈ Finset.range R, workCharge c (stage c ω.2 r) : ℕ) : ℝ) /
        (c.workCap : ℝ)) / (c.attempt + 1 : ℝ) ^ 2 := by
      rw [Nat.cast_sum, Finset.mul_sum, Finset.sum_div, Finset.sum_div]
    _ ≤ smallEta c := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg _)
      apply (div_le_iff₀ hM).mpr
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast stage_work_sum_le c ω.2 R) hη

theorem smallRho_le_smallEta (c : Config) (hδ : 0 ≤ c.confidence) (r : ℕ) (ω : SampleSpace n) :
    smallRho c r ω ≤ smallEta c := by
  apply (Finset.single_le_sum (fun s _ => smallRho_nonneg c hδ s ω)
    (Finset.mem_range.mpr (Nat.lt_succ_self r))).trans
  exact sum_smallRho_le c hδ (r + 1) ω

theorem sum_smallRho_pow_le (c : Config) (hδ : 0 ≤ c.confidence) (R : ℕ) (ω : SampleSpace n) :
    (∑ r ∈ Finset.range R, smallRho c r ω ^ 25) ≤ smallEta c ^ 25 := by
  have hpoint (r : ℕ) : smallRho c r ω ^ 25 ≤ smallEta c ^ 24 * smallRho c r ω := by
    have hp := pow_le_pow_left₀ (smallRho_nonneg c hδ r ω) (smallRho_le_smallEta c hδ r ω) 24
    simpa only [show (25 : ℕ) = 24 + 1 from rfl, pow_succ] using
      mul_le_mul_of_nonneg_right hp (smallRho_nonneg c hδ r ω)
  calc
    _ ≤ ∑ r ∈ Finset.range R, smallEta c ^ 24 * smallRho c r ω := Finset.sum_le_sum (fun r _ => hpoint r)
    _ = smallEta c ^ 24 * ∑ r ∈ Finset.range R, smallRho c r ω := (Finset.mul_sum ..).symm
    _ ≤ smallEta c ^ 25 := by
      simpa only [show (25 : ℕ) = 24 + 1 from rfl, pow_succ] using
        mul_le_mul_of_nonneg_left (sum_smallRho_le c hδ R ω) (pow_nonneg (smallEta_nonneg c hδ) 24)

theorem smallEta_pow_eq (c : Config) :
    smallEta c ^ 25 = eta c ^ 25 * UniversalErrorBudget.indexWeight 50 c.attempt := by
  unfold smallEta UniversalErrorBudget.indexWeight
  rw [div_pow, ← pow_mul]
  norm_num
  ring

theorem smallRho_adapted (c : Config) (r : ℕ) : Measurable[callPast c r] (smallRho (n := n) c r) := by
  apply Measurable.ite
  · exact (active_adapted c r) (MeasurableSet.of_discrete : MeasurableSet {S : Finset (Fin n) | S.card ≤ 7})
  · exact (confidenceCharge_adapted c r).div_const 128
  · exact measurable_const

theorem integrable_smallRho_pow (c : Config) (hδ : 0 ≤ c.confidence) (mean : Fin n → ℝ) (r : ℕ) :
    Integrable (fun ω => smallRho c r ω ^ 25) (sampleLawOfMeans mean) := by
  apply (integrable_const (smallEta c ^ 25)).mono'
    (((smallRho_adapted c r).mono ((callFiltration c).le r) le_rfl).pow_const 25).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (smallRho_nonneg c hδ r ω) 25)]
    exact pow_le_pow_left₀ (smallRho_nonneg c hδ r ω) (smallRho_le_smallEta c hδ r ω) 25

end GapEntropy.UniversalSevereProcess
