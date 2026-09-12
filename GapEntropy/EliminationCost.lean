import GapEntropy.EliminationTape

/-!
# The declared sample cost of the A.3 elimination call

The declared cost of an A.3 call on `s` arms is the median-elimination declared cost at
parameters `(d/8, α/16)`, plus the reference samples, plus `s` blocks of active-arm samples.
Every trajectory consumes exactly this declared cost. The reference and active sample counts are
each at most `513 · d⁻² · log(128/α)`, and the total declared cost is at most
`6500000 · s · d⁻² · log(128/α)`, with the explicit universal constant `6500000`.
-/

noncomputable section
open scoped BigOperators

namespace GapEntropy.EliminationTape
open GapEntropy.MedianElimination

def declaredCost (s : ℕ) (d α : ℝ) : ℕ :=
  GapEntropy.MedianElimination.declaredCost s (d / 8) (α / 16) +
    referenceSamples d α + s * activeSamples d α

def trajectoryCost {n : ℕ} {d α : ℝ} (S : Finset (Fin n)) (ω : Tape n d α) : ℕ :=
  GapEntropy.MedianElimination.trajectoryCost S
    (fun r => empiricalVectors GapEntropy.MedianTape.observation r ω.1) (d / 8) (α / 16) +
    referenceSamples d α + S.card * activeSamples d α

theorem trajectoryCost_eq_declaredCost {n : ℕ} {d α : ℝ}
    (S : Finset (Fin n)) (ω : Tape n d α) : trajectoryCost S ω = declaredCost S.card d α := by
  simp only [trajectoryCost, declaredCost, GapEntropy.MedianElimination.trajectoryCost_eq_declaredCost]

theorem one_le_elimination_log {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    1 ≤ Real.log (128 / α) := by
  have h := one_le_budget_log (show 0 < α / 16 by positivity) (show α / 16 ≤ 1 by linarith)
  have heq : (8 / (α / 16) : ℝ) = 128 / α := by ring
  rw [heq] at h
  exact h

theorem referenceSamples_le {d α : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    (referenceSamples d α : ℝ) ≤ 513 * (d ^ 2)⁻¹ * Real.log (128 / α) := by
  have hlog := one_le_elimination_log hα hα1
  have hdinv : 1 ≤ (d ^ 2)⁻¹ := (one_le_inv₀ (sq_pos_of_pos hd)).mpr (by nlinarith)
  have hlo : 0 < Real.log (32 / α) := Real.log_pos ((lt_div_iff₀ hα).mpr (by linarith))
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ 512 * (d ^ 2)⁻¹ * Real.log (32 / α) by positivity)).le
  have hlogs : Real.log (32 / α) ≤ Real.log (128 / α) := by
    apply Real.log_le_log (div_pos (by norm_num) hα)
    exact div_le_div_of_nonneg_right (by norm_num) hα.le
  have hp := mul_le_mul_of_nonneg_left hlogs (show 0 ≤ 512 * (d ^ 2)⁻¹ by positivity)
  change (referenceSamples d α : ℝ) ≤ _ at hceil
  have ha := mul_le_mul hdinv hlog (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (d ^ 2)⁻¹)
  nlinarith

theorem activeSamples_le {d α : ℝ} (hd : 0 < d) (hd1 : d ≤ 1)
    (hα : 0 < α) (hα1 : α ≤ 1) :
    (activeSamples d α : ℝ) ≤ 513 * (d ^ 2)⁻¹ * Real.log (128 / α) := by
  have hlog := one_le_elimination_log hα hα1
  have hdinv : 1 ≤ (d ^ 2)⁻¹ := (one_le_inv₀ (sq_pos_of_pos hd)).mpr (by nlinarith)
  have hceil := (Nat.ceil_lt_add_one
    (show 0 ≤ 512 * (d ^ 2)⁻¹ * Real.log (128 / α) by positivity)).le
  change (activeSamples d α : ℝ) ≤ _ at hceil
  have ha := mul_le_mul hdinv hlog (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ (d ^ 2)⁻¹)
  nlinarith

/-- A.3's deterministic total sample bound, with explicit universal constant 6500000. -/
theorem declaredCost_le {s : ℕ} (hs : 0 < s) {d α : ℝ}
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    (declaredCost s d α : ℝ) ≤ 6500000 * (s : ℝ) * (d ^ 2)⁻¹ * Real.log (128 / α) := by
  have hp := GapEntropy.MedianElimination.declaredCost_le hs
    (show 0 < d / 8 by positivity) (show d / 8 ≤ 1 by linarith)
    (show 0 < α / 16 by positivity) (show α / 16 ≤ 1 by linarith)
  have heq : 100000 * (s : ℝ) * ((d / 8) ^ 2)⁻¹ * Real.log (8 / (α / 16)) =
      6400000 * (s : ℝ) * (d ^ 2)⁻¹ * Real.log (128 / α) := by
    have hh : (8 / (α / 16) : ℝ) = 128 / α := by ring
    have hinv : ((d / 8) ^ 2)⁻¹ = 64 * (d ^ 2)⁻¹ := by
      rw [div_pow, inv_div]
      norm_num [div_eq_mul_inv]
    rw [hh, hinv]
    ring
  rw [heq] at hp
  have hr := referenceSamples_le hd hd1 hα hα1
  have ha := mul_le_mul_of_nonneg_left (activeSamples_le hd hd1 hα hα1)
    (show (0 : ℝ) ≤ s by positivity)
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hlog := one_le_elimination_log hα hα1
  have hr' := mul_le_mul_of_nonneg_right hsR
    (show 0 ≤ 513 * (d ^ 2)⁻¹ * Real.log (128 / α) by positivity)
  have hscale : 0 ≤ (s : ℝ) * (d ^ 2)⁻¹ * Real.log (128 / α) := by positivity
  simp only [declaredCost, Nat.cast_add, Nat.cast_mul]
  nlinarith

end GapEntropy.EliminationTape
