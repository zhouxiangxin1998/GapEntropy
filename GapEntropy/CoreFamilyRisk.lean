import GapEntropy.CoreRiskSeries
import GapEntropy.TerminalCore

/-!
# Summing the fixed terminal-core family

E.19's infinite series apply to the actual nested family, including repeated gap
values. The probability theorem explicitly retains the per-core estimate as a
premise: its application to the universal policy requires the three cap regimes.
-/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory

namespace GapEntropy
namespace Instance
variable {n : ℕ} (I : Instance n)

theorem terminalCoreFamily_nonempty_mem {B : Finset (Fin n)}
    (hB : B ∈ I.terminalCoreFamily) : B.Nonempty := by
  obtain ⟨d, hd, rfl⟩ := (I.mem_terminalCoreFamily B).mp hB
  exact I.terminalCore_nonempty hd

theorem terminalCoreFamily_index_injective :
    Set.InjOn (fun B : Finset (Fin n) => B.card - 1)
      (I.terminalCoreFamily : Set (Finset (Fin n))) := by
  intro B hB C hC h
  change B.card - 1 = C.card - 1 at h
  apply I.terminalCoreFamily_card_injective hB hC
  have hBpos := (I.terminalCoreFamily_nonempty_mem hB).card_pos
  have hCpos := (I.terminalCoreFamily_nonempty_mem hC).card_pos
  omega

/-- A fixed core of each positive cardinality occurs at most once. -/
theorem sum_terminalCoreFamily_le_tsum {f : ℕ → ℝ}
    (hf : ∀ k, 0 ≤ f k) (hs : Summable f) :
    (∑ B ∈ I.terminalCoreFamily, f (B.card - 1)) ≤ ∑' k, f k := by
  classical
  rw [← Finset.sum_image I.terminalCoreFamily_index_injective]
  exact hs.sum_le_tsum _ (fun k _ => hf k)

theorem sum_terminalCoreRisk_le {p : ℝ} (hp : 0 ≤ p) (hp16 : p ≤ 1 / 16) :
    (∑ B ∈ I.terminalCoreFamily, coreRisk p (B.card - 1)) ≤ 4 * p :=
  (I.sum_terminalCoreFamily_le_tsum (coreRisk_nonneg hp)
    (coreRisk_summable hp (by linarith))).trans (sum_coreRisk_le hp hp16)

theorem sum_sqrt_terminalCoreRisk_le {p : ℝ} (hp : 0 ≤ p) (hp16 : p ≤ 1 / 16) :
    (∑ B ∈ I.terminalCoreFamily, Real.sqrt (coreRisk p (B.card - 1))) ≤
      5 * Real.sqrt p :=
  (I.sum_terminalCoreFamily_le_tsum (fun _ => Real.sqrt_nonneg _)
    (sqrt_coreRisk_summable hp hp16)).trans (sum_sqrt_coreRisk_le hp hp16)

/-- The summed E.19 error charge, with the source's exact coefficients. -/
theorem sum_terminalCoreRisk_charge_le {p η : ℝ} (hp : 0 ≤ p) (hp16 : p ≤ 1 / 16) :
    (∑ B ∈ I.terminalCoreFamily,
      (10 * coreRisk p (B.card - 1) + 3 * η ^ 2 * Real.sqrt (coreRisk p (B.card - 1)))) ≤
      40 * p + 15 * η ^ 2 * Real.sqrt p := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h₁ := mul_le_mul_of_nonneg_left (I.sum_terminalCoreRisk_le hp hp16)
    (show (0 : ℝ) ≤ 10 by norm_num)
  have h₂ := mul_le_mul_of_nonneg_left (I.sum_sqrt_terminalCoreRisk_le hp hp16)
    (show 0 ≤ 3 * η ^ 2 by positivity)
  nlinarith

/-- Union bound over fixed cores; no conditioning on a randomly chosen core. -/
theorem measure_terminalCoreFamily_union_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Finset (Fin n) → Set Ω) {p η : ℝ}
    (hp : 0 ≤ p) (hp16 : p ≤ 1 / 16)
    (hE : ∀ B ∈ I.terminalCoreFamily,
      μ (E B) ≤ ENNReal.ofReal
        (10 * coreRisk p (B.card - 1) + 3 * η ^ 2 * Real.sqrt (coreRisk p (B.card - 1)))) :
    μ (⋃ B ∈ I.terminalCoreFamily, E B) ≤ ENNReal.ofReal
      (40 * p + 15 * η ^ 2 * Real.sqrt p) := by
  classical
  apply (measure_biUnion_finset_le _ _).trans
  apply (Finset.sum_le_sum hE).trans
  rw [← ENNReal.ofReal_sum_of_nonneg (fun B _ =>
    add_nonneg (mul_nonneg (by norm_num) (coreRisk_nonneg hp _))
      (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))]
  exact ENNReal.ofReal_le_ofReal (I.sum_terminalCoreRisk_charge_le hp hp16)

end Instance
end GapEntropy
