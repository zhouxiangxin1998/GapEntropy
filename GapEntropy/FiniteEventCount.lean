import GapEntropy.PACRound

/-!
# A Markov bound on the number of occurring events

If each of finitely many events has probability at most `η`, then the probability that at least
a fraction `1/q` of them occur is at most `q · η`. The proof applies Markov's inequality to the
indicator sum `eventCount` of `PACRound`; no independence among the events is needed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace GapEntropy.PACRound

/-- Markov's inequality for a fraction `1/q` of a finite family of events.
No independence among events is needed. -/
theorem measure_fraction_events_le {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {S : Finset ι} (hS : S.Nonempty)
    {E : ι → Set Ω} (hE : ∀ i ∈ S, MeasurableSet (E i))
    {η : ℝ} (hprob : ∀ i ∈ S, P.real (E i) ≤ η) {q : ℕ} (hq : 0 < q) :
    P.real {ω | S.card ≤ q * (occurringEvents S E ω).card} ≤ q * η := by
  classical
  have hint_i (i : ι) (hi : i ∈ S) :
      Integrable ((E i).indicator (fun _ : Ω => (1 : ℝ))) P :=
    (integrable_const 1).indicator (hE i hi)
  have hint : Integrable (eventCount S E) P := integrable_finsetSum S hint_i
  have hnonneg : 0 ≤ᵐ[P] eventCount S E := ae_of_all P fun ω => by
    rw [eventCount_eq_card]
    positivity
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hmarkov := mul_meas_ge_le_integral_of_nonneg hnonneg hint ((S.card : ℝ) / q)
  have hintegral : ∫ ω, eventCount S E ω ∂P = ∑ i ∈ S, P.real (E i) := by
    change (∫ ω, ∑ i ∈ S, (E i).indicator (fun _ => (1 : ℝ)) ω ∂P) = _
    rw [integral_finsetSum S hint_i]
    apply Finset.sum_congr rfl
    intro i hi
    simpa only [smul_eq_mul, mul_one] using
      integral_indicator_const (μ := P) (1 : ℝ) (hE i hi)
  rw [hintegral] at hmarkov
  have hbound : ∑ i ∈ S, P.real (E i) ≤ (S.card : ℝ) * η := by
    simpa using Finset.sum_le_sum hprob
  have hevent : {ω | (S.card : ℝ) / q ≤ eventCount S E ω} =
      {ω | S.card ≤ q * (occurringEvents S E ω).card} := by
    ext ω
    rw [Set.mem_ofPred_eq, eventCount_eq_card, div_le_iff₀ hqR]
    change ((S.card : ℝ) ≤ (↑(occurringEvents S E ω).card : ℝ) * q) ↔
      S.card ≤ q * (occurringEvents S E ω).card
    rw [mul_comm]
    exact_mod_cast Iff.rfl
  rw [hevent] at hmarkov
  have hscaled := mul_le_mul_of_nonneg_right hmarkov hqR.le
  have hid : ((S.card : ℝ) / q) *
      P.real {ω | S.card ≤ q * (occurringEvents S E ω).card} * q =
      (S.card : ℝ) * P.real {ω | S.card ≤ q * (occurringEvents S E ω).card} := by
    field_simp
  rw [hid] at hscaled
  have hbound' := mul_le_mul_of_nonneg_right hbound hqR.le
  have hs : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  nlinarith

end GapEntropy.PACRound
