import GapEntropy.MarkedTranscript
import GapEntropy.PermutationCounts

/-!
# Marked information charged to the original full sampling cost

Finite transcripts are charged to full unconditional per-arm expectations on
the original instance and its permutations. Converting to real costs requires
an explicit proof that the original permutation average is finite.
-/

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy

theorem permutationTruncatedArmSamples_le_full (A : Algorithm) {n : ℕ} (I : Instance n)
    (T : ℕ) (i : Fin n) :
    (A n).permutationTruncatedArmSamples I.two_le I.mean T i ≤ permutationArmSamples A I i := by
  unfold Policy.permutationTruncatedArmSamples permutationArmSamples
  simp only [Fintype.card_perm, Fintype.card_fin, div_eq_mul_inv]
  apply mul_le_mul' _ le_rfl
  apply Finset.sum_le_sum
  intro π _
  exact lintegral_mono ((A n).truncatedArmSamples_le_armSamples (I.permute π).two_le T (π i))

theorem klDiv_markedTranscriptLaw_le_full_source_counts (A : Algorithm) {n : ℕ}
    (I : Instance n) (mean' : Fin n → ℝ) (T : ℕ) (d : Fin n) :
    InformationTheory.klDiv ((A n).markedTranscriptLaw I.two_le I.mean T d)
      ((A n).markedTranscriptLaw I.two_le mean' T d) ≤
      ∑ i : Fin n, ENNReal.ofReal ((I.mean i - mean' i) ^ 2 / 2) *
        permutationArmSamples A I i := by
  apply ((A n).klDiv_markedTranscriptLaw_le_source_counts I.two_le I.mean mean' T d).trans
  apply Finset.sum_le_sum
  intro i _
  exact mul_le_mul' le_rfl (permutationTruncatedArmSamples_le_full A I T i)

theorem gaussian_cost_eq_normalizedArmCost (A : Algorithm) {n : ℕ} (I : Instance n)
    (h : permutationAverage A I ≠ ⊤) (i : Fin n) :
    ENNReal.ofReal (I.gap i ^ 2 / 2) * permutationArmSamples A I i =
      ENNReal.ofReal (normalizedArmCost A I h i / 2) := by
  rw [← ENNReal.ofReal_toReal (permutationArmSamples_ne_top A I h i),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ I.gap i ^ 2 / 2)]
  congr 1
  unfold normalizedArmCost
  ring

/-- Raising the marked source arm to the best mean costs exactly its own
normalized source sample count in the information upper bound. -/
theorem klDiv_markedTranscriptLaw_raised_le (A : Algorithm) {n : ℕ} (I : Instance n)
    (h : permutationAverage A I ≠ ⊤) (T : ℕ) (d : Fin n) :
    InformationTheory.klDiv ((A n).markedTranscriptLaw I.two_le I.mean T d)
      ((A n).markedTranscriptLaw I.two_le (Coupling.raisedMean I.mean I.best d) T d) ≤
      ENNReal.ofReal (normalizedArmCost A I h d / 2) := by
  apply (klDiv_markedTranscriptLaw_le_full_source_counts A I
    (Coupling.raisedMean I.mean I.best d) T d).trans_eq
  rw [Finset.sum_eq_single d]
  · rw [← gaussian_cost_eq_normalizedArmCost A I h d]
    congr 2
    simp only [Coupling.raisedMean, Function.update_self, Instance.gap]
    ring
  · intro i _ hid
    simp [Coupling.raisedMean, hid]
  · simp

/-- The two-coordinate comparison is charged solely to the two original arms,
and never to a perturbed instance's expected sample count. -/
theorem klDiv_markedTranscriptLaw_twoCoordinate_le_full (A : Algorithm) {n : ℕ}
    (I : Instance n) (T : ℕ) (a d : Fin n) (had : a ≠ d) :
    InformationTheory.klDiv ((A n).markedTranscriptLaw I.two_le I.mean T d)
      ((A n).markedTranscriptLaw I.two_le (Coupling.raisedMean I.mean I.best a) T a) ≤
      ENNReal.ofReal (I.gap d ^ 2 / 2) * permutationArmSamples A I d +
        ENNReal.ofReal ((I.gap d - I.gap a) ^ 2 / 2) * permutationArmSamples A I a := by
  apply ((A n).klDiv_markedTranscriptLaw_twoCoordinate_le_gaps I T a d had).trans
  exact add_le_add
    (mul_le_mul' le_rfl (permutationTruncatedArmSamples_le_full A I T d))
    (mul_le_mul' le_rfl (permutationTruncatedArmSamples_le_full A I T a))

/-- B.8 in real normalized-cost notation. The pivot has at least the designated
gap. The case where the designated arm is itself the pivot is included. -/
theorem klDiv_markedTranscriptLaw_le_normalized_pair (A : Algorithm) {n : ℕ}
    (I : Instance n) (h : permutationAverage A I ≠ ⊤) (T : ℕ) (a d : Fin n)
    (hgap : I.gap d ≤ I.gap a) :
    InformationTheory.klDiv ((A n).markedTranscriptLaw I.two_le I.mean T d)
      ((A n).markedTranscriptLaw I.two_le (Coupling.raisedMean I.mean I.best a) T a) ≤
      ENNReal.ofReal ((normalizedArmCost A I h d + normalizedArmCost A I h a) / 2) := by
  by_cases had : a = d
  · subst a
    apply (klDiv_markedTranscriptLaw_raised_le A I h T d).trans
    apply ENNReal.ofReal_le_ofReal
    linarith [normalizedArmCost_nonneg A I h d]
  have hsq : (I.gap d - I.gap a) ^ 2 / 2 ≤ I.gap a ^ 2 / 2 := by
    have hd := I.gap_nonneg d
    have ha := I.gap_nonneg a
    nlinarith [mul_nonneg hd (sub_nonneg.2 hgap)]
  calc
    _ ≤ ENNReal.ofReal (I.gap d ^ 2 / 2) * permutationArmSamples A I d +
        ENNReal.ofReal ((I.gap d - I.gap a) ^ 2 / 2) * permutationArmSamples A I a :=
      klDiv_markedTranscriptLaw_twoCoordinate_le_full A I T a d had
    _ ≤ ENNReal.ofReal (I.gap d ^ 2 / 2) * permutationArmSamples A I d +
        ENNReal.ofReal (I.gap a ^ 2 / 2) * permutationArmSamples A I a :=
      add_le_add le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal hsq) le_rfl)
    _ = _ := by
      rw [gaussian_cost_eq_normalizedArmCost A I h d,
        gaussian_cost_eq_normalizedArmCost A I h a, ← ENNReal.ofReal_add (by
          exact div_nonneg (normalizedArmCost_nonneg A I h d) (by norm_num)) (by
          exact div_nonneg (normalizedArmCost_nonneg A I h a) (by norm_num))]
      congr 1
      ring

end GapEntropy
