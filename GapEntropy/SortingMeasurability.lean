import GapEntropy.Elimination
import GapEntropy.PACRound
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of the actual finite-arm elimination operations

Empirical ranking factors through the finite Boolean comparison matrix.
Every function out of this finite discrete space is measurable. This proves
measurability of the actual `mergeSort`/`take` implementation, including ties.
Active sets, references, tolerances and empirical means may all be measurable
functions of the same history; no independence assumption is used here.
-/

noncomputable section
open MeasureTheory

namespace GapEntropy.SortingMeasurability

variable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}

def comparisonMatrix (x : Fin n → ℝ) (i j : Fin n) : Bool := decide (x j ≤ x i)

theorem comparisonMatrix_measurable {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => comparisonMatrix (fun i => X i ω)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  apply measurable_to_bool
  change MeasurableSet {ω | decide (X j ω ≤ X i ω) = true}
  simpa only [decide_eq_true_eq] using measurableSet_le (hX j) (hX i)

/-- The ranking is measurable for any sigma-algebra placed on its list-valued output. -/
theorem ranking_measurable [MeasurableSpace (List (Fin n))]
    {S : Ω → Finset (Fin n)} {X : Fin n → Ω → ℝ}
    (hS : Measurable S) (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => GapEntropy.Elimination.ranking (S ω) (fun i => X i ω)) := by
  let F : Finset (Fin n) × (Fin n → Fin n → Bool) → List (Fin n) :=
    fun b => b.1.toList.mergeSort b.2
  have hF : Measurable F := measurable_of_finite F
  exact hF.comp (hS.prodMk (comparisonMatrix_measurable hX))

theorem upperHalf_measurable {S : Ω → Finset (Fin n)} {X : Fin n → Ω → ℝ}
    (hS : Measurable S) (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => GapEntropy.Elimination.upperHalf (S ω) (fun i => X i ω)) := by
  let F : Finset (Fin n) × (Fin n → Fin n → Bool) → Finset (Fin n) :=
    fun b => ((b.1.toList.mergeSort b.2).take ((b.1.card + 1) / 2)).toFinset
  have hF : Measurable F := measurable_of_finite F
  exact hF.comp (hS.prodMk (comparisonMatrix_measurable hX))

theorem raw_measurable {S : Ω → Finset (Fin n)} {X : Fin n → Ω → ℝ}
    {z d : Ω → ℝ} (hS : Measurable S) (hX : ∀ i, Measurable (X i))
    (hz : Measurable z) (hd : Measurable d) :
    Measurable (fun ω => GapEntropy.Elimination.raw (S ω) (fun i => X i ω) (z ω) (d ω)) := by
  let flags : Ω → Fin n → Bool := fun ω i => decide (z ω - d ω / 2 ≤ X i ω)
  have hflags : Measurable flags := by
    apply measurable_pi_lambda
    intro i
    apply measurable_to_bool
    change MeasurableSet {ω | decide (z ω - d ω / 2 ≤ X i ω) = true}
    simpa only [decide_eq_true_eq, Pi.sub_apply] using
      measurableSet_le (hz.sub (hd.div_const 2)) (hX i)
  let F : Finset (Fin n) × (Fin n → Bool) → Finset (Fin n) :=
    fun b => b.1.filter (fun i => b.2 i)
  have hF : Measurable F := measurable_of_finite F
  simpa [F, flags, Function.comp_def, GapEntropy.Elimination.raw] using hF.comp (hS.prodMk hflags)

theorem padded_measurable {S : Ω → Finset (Fin n)} {X : Fin n → Ω → ℝ}
    {z d : Ω → ℝ} (hS : Measurable S) (hX : ∀ i, Measurable (X i))
    (hz : Measurable z) (hd : Measurable d) :
    Measurable (fun ω => GapEntropy.Elimination.padded (S ω) (fun i => X i ω) (z ω) (d ω)) := by
  have hUnion : Measurable (fun p : Finset (Fin n) × Finset (Fin n) => p.1 ∪ p.2) :=
    measurable_of_finite _
  exact hUnion.comp ((raw_measurable hS hX hz hd).prodMk (upperHalf_measurable hS hX))

/-- The PACRound bad event is measurable, discharging its earlier finite-arm sorting obligation. -/
theorem measurableSet_failureEvent (S : Finset (Fin n)) (μ : Fin n → ℝ)
    {X : Fin n → Ω → ℝ} (hX : ∀ i, Measurable (X i)) (a : Fin n) (ε : ℝ) :
    MeasurableSet (GapEntropy.PACRound.failureEvent S μ X a ε) := by
  let F : Finset (Fin n) → Prop := fun R => ¬ ∃ b ∈ R, μ a - 2 * ε ≤ μ b
  have hF : Measurable F := measurable_of_finite F
  exact measurableSet_setOfPred.mpr (hF.comp (upperHalf_measurable measurable_const hX))

end GapEntropy.SortingMeasurability
