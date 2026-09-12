import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-!
# Exact reservation counters for universal attempts

Section D.2 reserves both base work and the complete deterministic sample budget
before observing the call's data. These are the actual two-counter transitions,
including abort, and their pathwise consequences. Statistical success is never
needed to bound a reserved trajectory. Reference/PAC sample budgets enter as the
call's fixed sample charge, as required by the reservation order.
-/

open scoped BigOperators

namespace GapEntropy.Reservation

structure Call where
  arms : ℕ
  scale : ℕ
  samples : ℕ
  deriving DecidableEq

def Call.work (c : Call) : ℕ := c.arms * 4 ^ c.scale

structure Counters where
  work : ℕ
  samples : ℕ
  deriving DecidableEq

def zero : Counters := ⟨0, 0⟩

def charge (s : Counters) (c : Call) : Counters :=
  ⟨s.work + c.work, s.samples + c.samples⟩

/-- The two reservations happen before any observation of the call. -/
def reserve (M Q : ℕ) (s : Counters) (c : Call) : Option Counters :=
  if s.work + c.work ≤ M ∧ s.samples + c.samples ≤ Q then some (charge s c) else none

def reserveAll (M Q : ℕ) : Counters → List Call → Option Counters
  | s, [] => some s
  | s, c :: cs => (reserve M Q s c).bind (fun s' => reserveAll M Q s' cs)

theorem reserve_eq_some_iff (M Q : ℕ) (s s' : Counters) (c : Call) :
    reserve M Q s c = some s' ↔
      s.work + c.work ≤ M ∧ s.samples + c.samples ≤ Q ∧ s' = charge s c := by
  unfold reserve
  split_ifs <;> simp_all [eq_comm]

theorem reserve_eq_none_iff (M Q : ℕ) (s : Counters) (c : Call) :
    reserve M Q s c = none ↔ M < s.work + c.work ∨ Q < s.samples + c.samples := by
  unfold reserve
  split_ifs <;> simp_all; omega

theorem reserveAll_totals (M Q : ℕ) (cs : List Call) (s s' : Counters)
    (h : reserveAll M Q s cs = some s') :
    s'.work = s.work + (cs.map Call.work).sum ∧
      s'.samples = s.samples + (cs.map Call.samples).sum := by
  induction cs generalizing s with
  | nil => simp [reserveAll] at h; subst s'; simp
  | cons c cs ih =>
      change (reserve M Q s c).bind (fun st => reserveAll M Q st cs) = some s' at h
      cases hr : reserve M Q s c with
      | none => simp [hr] at h
      | some st =>
          have hrest : reserveAll M Q st cs = some s' := by simpa [hr] using h
          obtain ⟨_, _, rfl⟩ := (reserve_eq_some_iff M Q s st c).1 hr
          obtain ⟨hw, ht⟩ := ih (charge s c) hrest
          simp only [charge] at hw ht
          simp only [List.map_cons, List.sum_cons]
          exact ⟨by omega, by omega⟩

theorem reserveAll_within_budget (M Q : ℕ) (cs : List Call) (s s' : Counters)
    (hsw : s.work ≤ M) (hst : s.samples ≤ Q) (h : reserveAll M Q s cs = some s') :
    s'.work ≤ M ∧ s'.samples ≤ Q := by
  induction cs generalizing s with
  | nil => simp [reserveAll] at h; subst s'; exact ⟨hsw, hst⟩
  | cons c cs ih =>
      change (reserve M Q s c).bind (fun st => reserveAll M Q st cs) = some s' at h
      cases hr : reserve M Q s c with
      | none => simp [hr] at h
      | some st =>
          have hrest : reserveAll M Q st cs = some s' := by simpa [hr] using h
          obtain ⟨hw, ht, rfl⟩ := (reserve_eq_some_iff M Q s st c).1 hr
          exact ih (charge s c) hw ht hrest

/-- Every accepted trajectory, including one with statistical errors, obeys both
caps. The sample charge includes the full reference and PAC cost at scale entry. -/
theorem reserved_path_budgets (M Q : ℕ) (cs : List Call) (s' : Counters)
    (h : reserveAll M Q zero cs = some s') :
    (cs.map Call.work).sum ≤ M ∧ (cs.map Call.samples).sum ≤ Q := by
  obtain ⟨hw, ht⟩ := reserveAll_within_budget M Q cs zero s' (Nat.zero_le _) (Nat.zero_le _) h
  obtain ⟨heq₁, heq₂⟩ := reserveAll_totals M Q cs zero s' h
  rw [heq₁] at hw
  rw [heq₂] at ht
  simpa only [zero, Nat.zero_add] using And.intro hw ht

theorem two_le_call_work (c : Call) (hc : 2 ≤ c.arms) : 2 ≤ c.work := by
  have hp : 1 ≤ 4 ^ c.scale := Nat.one_le_pow _ _ (by omega)
  unfold Call.work
  nlinarith

theorem twice_length_le_work (cs : List Call) (hc : ∀ c ∈ cs, 2 ≤ c.arms) :
    2 * cs.length ≤ (cs.map Call.work).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
      have hcw := two_le_call_work c (hc c (by simp))
      have hcs := ih (fun d hd => hc d (by simp [hd]))
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- Positive base work gives a deterministic bound on the number of accepted
calls, strengthening the separate scale and halving termination argument. -/
theorem accepted_call_count_le (M Q : ℕ) (cs : List Call) (s' : Counters)
    (h : reserveAll M Q zero cs = some s') (hc : ∀ c ∈ cs, 2 ≤ c.arms) :
    cs.length ≤ M / 2 := by
  have hlen := (twice_length_le_work cs hc).trans (reserved_path_budgets M Q cs s' h).1
  omega

noncomputable def smallFactor (j s : ℕ) : ℝ :=
  if 2 ≤ s ∧ s ≤ 7 then (((j + 1 : ℕ) : ℝ) ^ 2)⁻¹ else 1

theorem smallFactor_nonneg (j s : ℕ) : 0 ≤ smallFactor j s := by
  unfold smallFactor
  split_ifs <;> positivity

theorem smallFactor_le_one (j s : ℕ) : smallFactor j s ≤ 1 := by
  unfold smallFactor
  split_ifs
  · have hj : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
    exact inv_le_one_of_one_le₀ (by nlinarith)
  · exact le_rfl

noncomputable def callConfidence (γ : ℝ) (M j : ℕ) (c : Call) : ℝ :=
  γ * (c.work : ℝ) / (M : ℝ) * smallFactor j c.arms

theorem callConfidence_nonneg {γ : ℝ} (hγ : 0 ≤ γ) (M j : ℕ) (c : Call) :
    0 ≤ callConfidence γ M j c := by
  exact mul_nonneg (div_nonneg (mul_nonneg hγ (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (smallFactor_nonneg j c.arms)

theorem callConfidence_le_work_fraction {γ : ℝ} (hγ : 0 ≤ γ) (M j : ℕ) (c : Call) :
    callConfidence γ M j c ≤ γ * (c.work : ℝ) / (M : ℝ) := by
  exact mul_le_of_le_one_right
    (div_nonneg (mul_nonneg hγ (Nat.cast_nonneg _)) (Nat.cast_nonneg _))
    (smallFactor_le_one j c.arms)

/-- Equation D.8's confidence sum follows from the same actual reservations,
including the small-set correction and all erroneous sample paths. -/
theorem reserved_confidence_sum_le {γ : ℝ} (hγ : 0 ≤ γ) (M Q j : ℕ) (hM : 0 < M)
    (cs : List Call) (s' : Counters) (h : reserveAll M Q zero cs = some s') :
    (cs.map (callConfidence γ M j)).sum ≤ γ := by
  have hwork := (reserved_path_budgets M Q cs s' h).1
  have hsum : (cs.map (callConfidence γ M j)).sum ≤
      γ * ((cs.map Call.work).sum : ℝ) / (M : ℝ) := by
    clear h hwork
    induction cs with
    | nil => simp
    | cons c cs ih =>
        have hc := callConfidence_le_work_fraction hγ M j c
        simp only [List.map_cons, List.sum_cons, Nat.cast_add, mul_add, add_div]
        exact add_le_add hc ih
  apply hsum.trans
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  apply (div_le_iff₀ hMR).2
  have hwR : (((cs.map Call.work).sum : ℕ) : ℝ) ≤ M := by exact_mod_cast hwork
  nlinarith

end GapEntropy.Reservation
