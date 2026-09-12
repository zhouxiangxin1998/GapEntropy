import GapEntropy.UniversalCall

/-! # Deterministic universal readout facts for arbitrary parser histories -/
noncomputable section
open scoped Classical
namespace GapEntropy.UniversalCall
variable {n t : ℕ}

theorem entryReadout_subset (S : Finset (Fin n)) (d α β : ℝ) (h : History n t) :
    (entryReadout S d α β h).2 ⊆ S := Elimination.padded_subset _ _ _ _

theorem laterReadout_subset (S : Finset (Fin n)) (d α z : ℝ) (h : History n t) :
    laterReadout S d α z h ⊆ S := Elimination.padded_subset _ _ _ _

theorem entryReadout_card_ge_half (S : Finset (Fin n)) (d α β : ℝ) (h : History n t) :
    (S.card + 1) / 2 ≤ (entryReadout S d α β h).2.card :=
  Elimination.padded_card_ge_half _ _ _ _

theorem laterReadout_card_ge_half (S : Finset (Fin n)) (d α z : ℝ) (h : History n t) :
    (S.card + 1) / 2 ≤ (laterReadout S d α z h).card :=
  Elimination.padded_card_ge_half _ _ _ _

theorem entryReadout_nonempty (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α β : ℝ) (h : History n t) : (entryReadout S d α β h).2.Nonempty := by
  apply Finset.card_pos.mp
  have hh := entryReadout_card_ge_half S d α β h
  have hp := hS.card_pos
  omega

theorem laterReadout_nonempty (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α z : ℝ) (h : History n t) : (laterReadout S d α z h).Nonempty := by
  apply Finset.card_pos.mp
  have hh := laterReadout_card_ge_half S d α z h
  have hp := hS.card_pos
  omega

/-- Padding precedes the singleton test: a nontrivial input can produce a
singleton only when its input cardinality was exactly two. -/
theorem entryReadout_card_eq_two_of_singleton (S : Finset (Fin n))
    (d α β : ℝ) (h : History n t) (hs : 2 ≤ S.card)
    (hR : (entryReadout S d α β h).2.card = 1) : S.card = 2 := by
  have hh := entryReadout_card_ge_half S d α β h
  omega

theorem laterReadout_card_eq_two_of_singleton (S : Finset (Fin n))
    (d α z : ℝ) (h : History n t) (hs : 2 ≤ S.card)
    (hR : (laterReadout S d α z h).card = 1) : S.card = 2 := by
  have hh := laterReadout_card_ge_half S d α z h
  omega

end GapEntropy.UniversalCall
