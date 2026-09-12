import GapEntropy.Instance
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# The exact finite relabeling in the two-coordinate coupling

For the latent variable in B.3 we use uniformly labeled *arm identities*.
This automatically handles repeated means: choose an identity `d` pinned to the
designated label, and an identity `a` for the other changed coordinate. Composing
the labeling with `swap a d` is a bijection to labelings with `a` pinned. The
mutated mean vector becomes precisely the vector with arm `a` raised to the best.

This proves equality of the common comparison mixture for any experiment law.
The KL/count inequality for these mixtures is a further probabilistic step.
-/

open MeasureTheory
open scoped BigOperators ENNReal Classical

namespace GapEntropy.Coupling

variable {n : ℕ}

abbrev PinnedPerm (d label : Fin n) := {π : Equiv.Perm (Fin n) // π d = label}

def pinnedSwap (a d label : Fin n) : PinnedPerm d label ≃ PinnedPerm a label where
  toFun π := ⟨(Equiv.swap a d).trans π.val, by simp [Equiv.trans_apply, π.property]⟩
  invFun π := ⟨(Equiv.swap a d).trans π.val, by simp [Equiv.trans_apply, π.property]⟩
  left_inv π := by
    apply Subtype.ext
    ext i
    simp [Equiv.trans_apply]
  right_inv π := by
    apply Subtype.ext
    ext i
    simp [Equiv.trans_apply]

theorem pinned_card_eq (a d label : Fin n) :
    Fintype.card (PinnedPerm d label) = Fintype.card (PinnedPerm a label) :=
  Fintype.card_congr (pinnedSwap a d label)

theorem pinned_nonempty (d label : Fin n) : Nonempty (PinnedPerm d label) :=
  ⟨⟨Equiv.swap d label, by simp⟩⟩

def relabelMean (mean : Fin n → ℝ) (π : Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun i => mean (π.symm i)

def raisedMean (mean : Fin n → ℝ) (best a : Fin n) : Fin n → ℝ :=
  Function.update mean a (mean best)

def twoCoordinateMean (mean : Fin n → ℝ) (best a d : Fin n) : Fin n → ℝ :=
  Function.update (Function.update mean d (mean best)) a (mean d)

theorem twoCoordinate_eq_raised_swap (mean : Fin n → ℝ) (best a d : Fin n)
    (had : a ≠ d) :
    twoCoordinateMean mean best a d = raisedMean mean best a ∘ Equiv.swap a d := by
  funext i
  by_cases hia : i = a
  · subst i
    simp [twoCoordinateMean, raisedMean, had.symm]
  · by_cases hid : i = d
    · subst i
      simp [twoCoordinateMean, raisedMean, had.symm]
    · simp [twoCoordinateMean, raisedMean, hia, hid,
        Equiv.swap_apply_of_ne_of_ne hia hid]

/-- Equality of labeled vectors, stronger than equality of their multisets. -/
theorem relabel_twoCoordinate (mean : Fin n → ℝ) (best a d : Fin n)
    (had : a ≠ d) (π : Equiv.Perm (Fin n)) :
    relabelMean (twoCoordinateMean mean best a d) π =
      relabelMean (raisedMean mean best a) ((Equiv.swap a d).trans π) := by
  rw [twoCoordinate_eq_raised_swap mean best a d had]
  ext i
  simp [relabelMean, Equiv.trans_apply]

/-- Uniform average over labelings pinning one specified identity to a label. -/
noncomputable def pinnedAverage {β : Type*} [AddCommMonoid β] [Module ℝ≥0∞ β]
    (F : (Fin n → ℝ) → β) (mean : Fin n → ℝ) (d label : Fin n) : β :=
  (Fintype.card (PinnedPerm d label) : ℝ≥0∞)⁻¹ •
    ∑ π : PinnedPerm d label, F (relabelMean mean π.val)

/-- The common comparison law is independent of which source arm `d` was pinned.
`F` can be the true finite-transcript law; repeated gaps require no special case. -/
theorem pinned_twoCoordinate_average {β : Type*} [AddCommMonoid β] [Module ℝ≥0∞ β]
    (F : (Fin n → ℝ) → β) (mean : Fin n → ℝ) (best a d label : Fin n)
    (had : a ≠ d) :
    pinnedAverage F (twoCoordinateMean mean best a d) d label =
      pinnedAverage F (raisedMean mean best a) a label := by
  unfold pinnedAverage
  rw [pinned_card_eq a d label]
  congr 1
  apply Fintype.sum_equiv (pinnedSwap a d label)
  intro π
  exact congrArg F (relabel_twoCoordinate mean best a d had π.val)

/-- Bijection on all labelings used when the designated label is retained as an
extra observable in the comparison experiment. -/
def swapLabelings (a d : Fin n) : Equiv.Perm (Fin n) ≃ Equiv.Perm (Fin n) where
  toFun π := (Equiv.swap a d).trans π
  invFun π := (Equiv.swap a d).trans π
  left_inv π := by ext i; simp [Equiv.trans_apply]
  right_inv π := by ext i; simp [Equiv.trans_apply]

noncomputable def markedAverage {β : Type*} [AddCommMonoid β] [Module ℝ≥0∞ β]
    (F : (Fin n → ℝ) → Fin n → β) (mean : Fin n → ℝ) (d : Fin n) : β :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ •
    ∑ π : Equiv.Perm (Fin n), F (relabelMean mean π) (π d)

/-- Full-permutation version of B.3. The mark is for the mathematical observer,
not extra information given to the sampling policy. This permits analyzing the
original algorithm's permutation average without constructing a symmetrized policy. -/
theorem marked_twoCoordinate_average {β : Type*} [AddCommMonoid β] [Module ℝ≥0∞ β]
    (F : (Fin n → ℝ) → Fin n → β) (mean : Fin n → ℝ) (best a d : Fin n)
    (had : a ≠ d) :
    markedAverage F (twoCoordinateMean mean best a d) d =
      markedAverage F (raisedMean mean best a) a := by
  unfold markedAverage
  congr 1
  apply Fintype.sum_equiv (swapLabelings a d)
  intro π
  change F _ (π d) = F _ (((Equiv.swap a d).trans π) a)
  rw [relabel_twoCoordinate mean best a d had]
  simp [Equiv.trans_apply, swapLabelings]

theorem twoCoordinate_unchanged (mean : Fin n → ℝ) (best a d i : Fin n)
    (hia : i ≠ a) (hid : i ≠ d) :
    twoCoordinateMean mean best a d i = mean i := by
  simp [twoCoordinateMean, hia, hid]

theorem twoCoordinate_at_designated (mean : Fin n → ℝ) (best a d : Fin n)
    (had : a ≠ d) : twoCoordinateMean mean best a d d = mean best := by
  simp [twoCoordinateMean, had.symm]

theorem twoCoordinate_at_pivot (mean : Fin n → ℝ) (best a d : Fin n) :
    twoCoordinateMean mean best a d a = mean d := by
  simp [twoCoordinateMean]

end GapEntropy.Coupling
