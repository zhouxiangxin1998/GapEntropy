import GapEntropy.TerminalCore
import GapEntropy.BatchCollapse

/-! The actual wrong terminal singleton forces an eligible batch collapse (E.6). -/
noncomputable section
namespace GapEntropy.Elimination.PaddedTrajectory

variable {n T : ℕ} (P : Elimination.PaddedTrajectory n T)

/-- A severe flag on an executed call whose active size is below eight. -/
def SmallSevere (I : Instance n) : Prop :=
  ∃ t < T, (P.active t).card < 8 ∧ (P.severeAt I t).Nonempty

/-- Eligibility and collapse refer to the actual padded update, with the original fixed core. -/
def EligibleCollapse (I : Instance n) (B : Finset (Fin n)) (t : ℕ) : Prop :=
  t < T ∧ 8 ≤ (P.active t).card ∧ (P.active t ∩ B).Nonempty ∧
    (∀ i ∈ B, I.gap i ≤ P.tolerance t / 8) ∧
    BatchCollapse.collapse (P.active t) B (P.estimates t) (P.reference t) (P.tolerance t)

/-- An elementary finite crossing; monotonicity is not needed for this combinatorial fact. -/
theorem exists_count_crossing (f : ℕ → ℕ) (hstart : 2 ≤ f 0) (hend : f T ≤ 1) :
    ∃ t < T, 2 ≤ f t ∧ f (t + 1) ≤ 1 := by
  induction T with
  | zero => omega
  | succ T ih =>
    by_cases hT : f T ≤ 1
    · obtain ⟨t, ht, hbefore, hafter⟩ := ih hT
      exact ⟨t, Nat.lt_succ_of_lt ht, hbefore, hafter⟩
    · exact ⟨T, Nat.lt_succ_self T, by omega, hend⟩

/-- A strict decrease in retained core cardinality removes an actual core member. -/
theorem removed_core_nonempty_of_card_lt (B : Finset (Fin n)) {t : ℕ}
    (hdrop : (P.active (t + 1) ∩ B).card < (P.active t ∩ B).card) :
    (P.removedAt t ∩ B).Nonempty := by
  by_contra hnone
  have hsub : P.active t ∩ B ⊆ P.active (t + 1) ∩ B := by
    intro i hi
    obtain ⟨hactive, hB⟩ := Finset.mem_inter.mp hi
    by_cases hnext : i ∈ P.active (t + 1)
    · exact Finset.mem_inter.mpr ⟨hnext, hB⟩
    · exact False.elim (hnone ⟨i, Finset.mem_inter.mpr
        ⟨(P.mem_removedAt t i).mpr ⟨hactive, hnext⟩, hB⟩⟩)
  have := Finset.card_le_card hsub
  omega

/-- Pure trajectory combinatorics: a wrong terminal singleton creates a collapse of any fixed
core containing the original best, and that call removes a core member. -/
theorem wrong_singleton_exists_collapse (I : Instance n) (B : Finset (Fin n))
    (hbest : I.best ∈ B) {out : Fin n}
    (hfinal : P.active T = {out}) (hwrong : out ≠ I.best) :
    ∃ t < T, (P.active t ∩ B).Nonempty ∧
      BatchCollapse.collapse (P.active t) B (P.estimates t) (P.reference t) (P.tolerance t) ∧
      (P.removedAt t ∩ B).Nonempty := by
  have hBpos : 0 < B.card := Finset.card_pos.mpr ⟨I.best, hbest⟩
  by_cases hB : 2 ≤ B.card
  · have hstart : 2 ≤ (P.active 0 ∩ B).card := by simpa [P.initial] using hB
    have hend : (P.active T ∩ B).card ≤ 1 := by
      rw [hfinal]
      exact (Finset.card_le_card Finset.inter_subset_left).trans_eq (Finset.card_singleton _)
    obtain ⟨t, ht, hbefore, hafter⟩ := exists_count_crossing
      (fun t => (P.active t ∩ B).card) hstart hend
    refine ⟨t, ht, Finset.card_pos.mp (by omega), ?_,
      P.removed_core_nonempty_of_card_lt B (by omega)⟩
    exact Or.inr ⟨hbefore, by rwa [← P.step t ht]⟩
  · have hBcard : B.card = 1 := by omega
    have hBeq : B = {I.best} := by
      exact Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hbest)
        (by simp [hBcard]) |>.symm
    have hbestnot : I.best ∉ P.active T := by simp [hfinal, Ne.symm hwrong]
    obtain ⟨t, ht, hremoved⟩ := P.exists_removedAt le_rfl hbestnot
    obtain ⟨hactive, hnext⟩ := (P.mem_removedAt t I.best).mp hremoved
    refine ⟨t, ht, ⟨I.best, Finset.mem_inter.mpr ⟨hactive, hbest⟩⟩, ?_,
      ⟨I.best, Finset.mem_inter.mpr ⟨hremoved, hbest⟩⟩⟩
    apply Or.inl
    constructor
    · simp [hBeq, hactive]
    · rw [← P.step t ht]
      simp [hBeq, hnext]

/-- Outside the two excluded deterministic failure predicates, an erroneous output has an
eligible collapse of its actual terminal core. No existence or probability bound is assumed. -/
theorem wrong_singleton_exists_eligible_collapse (I : Instance n)
    (hvalid : P.UpperValid I) (hsmall : ¬P.SmallSevere I)
    {out : Fin n} (hfinal : P.active T = {out}) (hwrong : out ≠ I.best) :
    ∃ t, P.EligibleCollapse I (P.core I) t := by
  have hbest := P.best_mem_core I (P.pos_of_terminal_singleton I hfinal)
  obtain ⟨t, ht, hnonempty, hcollapse, i, hi⟩ :=
    P.wrong_singleton_exists_collapse I (P.core I) hbest hfinal hwrong
  obtain ⟨hremoved, hi⟩ := Finset.mem_inter.mp hi
  have hflag := P.removed_core_mem_severeAt I hvalid ht hi hremoved
  have hs : 8 ≤ (P.active t).card := by
    by_contra hs
    exact hsmall ⟨t, ht, by omega, i, hflag⟩
  exact ⟨t, ht, hs, hnonempty, fun i hi => P.core_gap_le_call I ht hi, hcollapse⟩

/-- Fixed-core form for taking a union over the deterministic instance core family. -/
theorem wrong_singleton_fixed_core_exists_eligible_collapse (I : Instance n)
    (hvalid : P.UpperValid I) (hsmall : ¬P.SmallSevere I)
    (B : Finset (Fin n)) (hcore : P.core I = B)
    {out : Fin n} (hfinal : P.active T = {out}) (hwrong : out ≠ I.best) :
    ∃ t, P.EligibleCollapse I B t := by
  simpa only [hcore] using P.wrong_singleton_exists_eligible_collapse I hvalid hsmall hfinal hwrong

/-- The h=0 case of E.6 is impossible for the actual erroneous terminal trajectory. -/
theorem not_wrong_singleton_of_outsideHardness_zero (I : Instance n)
    (hvalid : P.UpperValid I) (hsmall : ¬P.SmallSevere I)
    {out : Fin n} (hfinal : P.active T = {out})
    (hh : BatchCollapse.outsideHardness I (P.core I) = 0) : out = I.best := by
  by_contra hwrong
  obtain ⟨t, ht, hs, _, _, hc⟩ :=
    P.wrong_singleton_exists_eligible_collapse I hvalid hsmall hfinal hwrong
  exact BatchCollapse.collapse_impossible_of_outsideHardness_zero I (P.active t) (P.core I)
    (P.best_mem_core I (P.pos_of_terminal_singleton I hfinal)) hs hh
    (P.estimates t) (P.reference t) (P.tolerance t) hc

end GapEntropy.Elimination.PaddedTrajectory
