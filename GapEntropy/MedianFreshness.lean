import GapEntropy.MedianElimination
import Mathlib.Probability.Independence.Basic

/-!
# Freshness of the median-elimination round vectors

The active set after `r` rounds depends only on the round vectors strictly before round `r`, and
it is a measurable function of those vectors through the finite reconstruction
`historyReconstruct`. When the round vectors are independent, the active set entering round `r`
is therefore independent of the vector observed in round `r`. Freshness is proved from the
independence of the round vectors, not assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace GapEntropy.MedianElimination

theorem activeSets_congr_before {n : ℕ} (S : Finset (Fin n))
    {x y : ℕ → Fin n → ℝ} {r : ℕ} (h : ∀ k < r, x k = y k) :
    activeSets S x r = activeSets S y r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [activeSets, activeSets, ih (fun k hk => h k (Nat.lt_succ_of_lt hk)),
      h r (Nat.lt_succ_self r)]

def historyReconstruct {n : ℕ} (r : ℕ) (history : (Finset.range r) → (Fin n → ℝ))
    (k : ℕ) : Fin n → ℝ := if hk : k < r then history ⟨k, Finset.mem_range.mpr hk⟩ else 0

theorem activeSets_history {n : ℕ} (S : Finset (Fin n)) (x : ℕ → Fin n → ℝ) (r : ℕ) :
    activeSets S (historyReconstruct r (fun k => x k)) r = activeSets S x r := by
  apply activeSets_congr_before
  intro k hk
  simp [historyReconstruct, hk]

theorem activeSets_history_measurable {n : ℕ} (S : Finset (Fin n)) (r : ℕ) :
    Measurable (fun h : (Finset.range r) → (Fin n → ℝ) =>
      activeSets S (historyReconstruct r h) r) := by
  apply activeSets_measurable
  intro k i
  by_cases hk : k < r
  · simpa only [historyReconstruct, dif_pos hk, Function.comp_def] using
      (measurable_pi_apply i).comp
        (measurable_pi_apply (⟨k, Finset.mem_range.mpr hk⟩ : Finset.range r))
  · simp only [historyReconstruct, dif_neg hk, Pi.zero_apply]
    exact measurable_const

/-- Freshness is proved from independent round vectors: the actual adaptive arm set
is a measurable function of the strictly earlier vectors. -/
theorem activeSets_indep_current {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {P : Measure Ω} {X : ℕ → Ω → (Fin n → ℝ)}
    (hX : ∀ r, Measurable (X r)) (hind : iIndepFun X P) (S : Finset (Fin n)) (r : ℕ) :
    IndepFun (fun ω => activeSets S (fun k => X k ω) r) (X r) P := by
  classical
  have hdis : Disjoint (Finset.range r) {r} := by simp
  have h := hind.indepFun_finset (Finset.range r) {r} hdis hX
  have hc := h.comp (activeSets_history_measurable S r)
    (measurable_pi_apply (⟨r, Finset.mem_singleton_self r⟩ : ({r} : Finset ℕ)))
  change IndepFun (fun ω => activeSets S (historyReconstruct r (fun k => X k ω)) r)
    (X r) P at hc
  have heq : (fun ω => activeSets S (historyReconstruct r (fun k => X k ω)) r) =
      (fun ω => activeSets S (fun k => X k ω) r) := by
    funext ω
    exact activeSets_history S (fun k => X k ω) r
  rw [heq] at hc
  exact hc

end GapEntropy.MedianElimination
