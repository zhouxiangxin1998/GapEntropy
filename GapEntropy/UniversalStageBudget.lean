import GapEntropy.UniversalStageFiltration

/-! Exact work telescoping and confidence budgets for the actual chronological
call process, including paths with statistical errors and terminal padding. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram
variable {n : ℕ}

def usedWork : Stage n → ℕ
  | .inl ((a, _), _) => a.work
  | .inr (a, _) => a.work

def workCharge (c : Config) : Stage n → ℕ
  | .inl _ => 0
  | .inr (a, _) => if a.Allowed c then (a.call c).work else 0

def confidenceCharge (c : Config) : Stage n → ℝ
  | .inl _ => 0
  | .inr (a, _) => if a.Allowed c then a.alpha c else 0

theorem measurable_workCharge (c : Config) : Measurable (workCharge (n := n) c) := by
  apply measurable_fun_sum
  · exact measurable_const
  · exact measurable_from_prod_countable_right (fun _ => measurable_const)

theorem measurable_confidenceCharge (c : Config) : Measurable (confidenceCharge (n := n) c) := by
  apply measurable_fun_sum
  · exact measurable_const
  · exact measurable_from_prod_countable_right (fun _ => measurable_const)

theorem confidenceCharge_adapted (c : Config) (r : ℕ) :
    Measurable[callPast c r] (fun ω : SampleSpace n => confidenceCharge c (stage c ω.2 r)) :=
  (measurable_confidenceCharge c).comp (stage_adapted c r)

theorem usedWork_stageStep (c : Config) (x : Values n) (st : Stage n) :
    usedWork (stageStep c x st) = usedWork st + workCharge c st := by
  cases st with
  | inl result => rcases result with ⟨⟨a, z⟩, ans⟩; exact (Nat.add_zero _).symm
  | inr state =>
    rcases state with ⟨a, z⟩
    simp only [stageStep, usedWork, workCharge]
    split_ifs <;> rfl

theorem usedWork_stageStep_le (c : Config) (x : Values n) (st : Stage n)
    (h : usedWork st ≤ c.workCap) : usedWork (stageStep c x st) ≤ c.workCap := by
  rw [usedWork_stageStep]
  cases st with
  | inl result => simpa only [workCharge, Nat.add_zero] using h
  | inr state =>
    rcases state with ⟨a, z⟩
    by_cases ha : a.Allowed c
    · simpa only [usedWork, workCharge, if_pos ha] using ha.2.1
    · simpa only [workCharge, if_neg ha, Nat.add_zero] using h

theorem stage_usedWork_le (c : Config) (x : Values n) (r : ℕ) :
    usedWork (stage c x r) ≤ c.workCap := by
  induction r with
  | zero => exact Nat.zero_le _
  | succ r ih => exact usedWork_stageStep_le c x _ ih

/-- The work counter is precisely the sum of actual accepted calls before r. -/
theorem stage_usedWork_eq_sum (c : Config) (x : Values n) (r : ℕ) :
    usedWork (stage c x r) = ∑ i ∈ Finset.range r, workCharge c (stage c x i) := by
  induction r with
  | zero => simp [stage, initial, usedWork, Metadata.work]
  | succ r ih => rw [stage, usedWork_stageStep, ih, Finset.sum_range_succ]

theorem stage_work_sum_le (c : Config) (x : Values n) (r : ℕ) :
    (∑ i ∈ Finset.range r, workCharge c (stage c x i)) ≤ c.workCap := by
  rw [← stage_usedWork_eq_sum]
  exact stage_usedWork_le c x r

theorem confidenceCharge_nonneg (c : Config) (hδ : 0 ≤ c.confidence) (st : Stage n) :
    0 ≤ confidenceCharge c st := by
  cases st with
  | inl result => exact le_rfl
  | inr state =>
    rcases state with ⟨a, z⟩
    simp only [confidenceCharge]
    split_ifs
    · exact Reservation.callConfidence_nonneg (div_nonneg hδ (by norm_num)) _ _ _
    · exact le_rfl

theorem confidenceCharge_le_work (c : Config) (hδ : 0 ≤ c.confidence) (st : Stage n) :
    confidenceCharge c st ≤ c.errorBudget * (workCharge c st : ℝ) / (c.workCap : ℝ) := by
  cases st with
  | inl result => simp [confidenceCharge, workCharge]
  | inr state =>
    rcases state with ⟨a, z⟩
    by_cases ha : a.Allowed c
    · simp only [confidenceCharge, workCharge, if_pos ha, ← call_confidence c a]
      exact Reservation.callConfidence_le_work_fraction (div_nonneg hδ (by norm_num)) _ _ _
    · simp only [confidenceCharge, workCharge, if_neg ha, Nat.cast_zero, mul_zero, zero_div, le_refl]

/-- Every actual chronological prefix, including all abort/error paths, obeys
D.8's confidence budget. These are the same alpha values used by its samplers. -/
theorem stage_confidence_sum_le (c : Config) (hδ : 0 ≤ c.confidence) (x : Values n) (r : ℕ) :
    (∑ i ∈ Finset.range r, confidenceCharge c (stage c x i)) ≤ c.errorBudget := by
  have hγ : 0 ≤ c.errorBudget := div_nonneg hδ (by norm_num)
  have hM : (0 : ℝ) < c.workCap := by unfold Config.workCap; positivity
  calc
    (∑ i ∈ Finset.range r, confidenceCharge c (stage c x i)) ≤
        ∑ i ∈ Finset.range r, c.errorBudget * (workCharge c (stage c x i) : ℝ) / (c.workCap : ℝ) :=
      Finset.sum_le_sum (fun i _ => confidenceCharge_le_work c hδ _)
    _ = c.errorBudget * ((∑ i ∈ Finset.range r, workCharge c (stage c x i) : ℕ) : ℝ) /
        (c.workCap : ℝ) := by rw [← Finset.sum_div, ← Finset.mul_sum, Nat.cast_sum]
    _ ≤ c.errorBudget := by
      apply (div_le_iff₀ hM).mpr
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast stage_work_sum_le c x r) hγ

theorem stage_confidence_le (c : Config) (hδ : 0 ≤ c.confidence) (x : Values n) (r : ℕ) :
    confidenceCharge c (stage c x r) ≤ c.errorBudget := by
  have hs := stage_confidence_sum_le c hδ x (r + 1)
  exact (Finset.single_le_sum (fun i _ => confidenceCharge_nonneg c hδ (stage c x i))
    (Finset.mem_range.mpr (Nat.lt_succ_self r))).trans hs

end GapEntropy.UniversalAttempt
