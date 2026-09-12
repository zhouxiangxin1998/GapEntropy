import GapEntropy.Instance
import GapEntropy.Elimination
import GapEntropy.EverFlags

/-! Fixed terminal cores and their actual severe-flag requirements along padded trajectories. -/
noncomputable section
open scoped BigOperators
namespace GapEntropy

namespace Instance
variable {n : ℕ} (I : Instance n)

/-- Fixed core at a strict gap threshold; the terminal call of tolerance `d` uses threshold `d/8`. -/
def terminalCore (threshold : ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun i => I.gap i < threshold

@[simp] theorem mem_terminalCore (threshold : ℝ) (i : Fin n) :
    i ∈ I.terminalCore threshold ↔ I.gap i < threshold := by
  simp [terminalCore]

theorem terminalCore_mono {d e : ℝ} (h : d ≤ e) : I.terminalCore d ⊆ I.terminalCore e := by
  intro i hi
  exact (I.mem_terminalCore e i).mpr ((I.mem_terminalCore d i).mp hi |>.trans_le h)

theorem best_mem_terminalCore {d : ℝ} (hd : 0 < d) : I.best ∈ I.terminalCore d := by
  simpa using hd

theorem terminalCore_nonempty {d : ℝ} (hd : 0 < d) : (I.terminalCore d).Nonempty :=
  ⟨I.best, I.best_mem_terminalCore hd⟩

/-- Two fixed cores are always nested, including repeated gap values. -/
theorem terminalCore_nested (d e : ℝ) :
    I.terminalCore d ⊆ I.terminalCore e ∨ I.terminalCore e ⊆ I.terminalCore d := by
  rcases le_total d e with h | h
  · exact Or.inl (I.terminalCore_mono h)
  · exact Or.inr (I.terminalCore_mono h)

/-- Equal cardinalities of nested cores imply the same core. -/
theorem terminalCore_eq_of_card_eq (d e : ℝ)
    (h : (I.terminalCore d).card = (I.terminalCore e).card) :
    I.terminalCore d = I.terminalCore e := by
  rcases I.terminalCore_nested d e with hde | hed
  · exact Finset.eq_of_subset_of_card_le hde h.ge
  · exact (Finset.eq_of_subset_of_card_le hed h.le).symm

/-- The finite collection of distinct positive-threshold cores. This includes all dyadic
terminal cores and automatically discards repeated sets. -/
def terminalCoreFamily : Finset (Finset (Fin n)) := by
  classical
  exact Finset.univ.filter fun B => ∃ d : ℝ, 0 < d ∧ I.terminalCore d = B

@[simp] theorem mem_terminalCoreFamily (B : Finset (Fin n)) :
    B ∈ I.terminalCoreFamily ↔ ∃ d : ℝ, 0 < d ∧ I.terminalCore d = B := by
  classical
  simp [terminalCoreFamily]

theorem terminalCoreFamily_card_injective :
    Set.InjOn Finset.card (I.terminalCoreFamily : Set (Finset (Fin n))) := by
  intro B hB C hC hcard
  obtain ⟨d, _, rfl⟩ := (I.mem_terminalCoreFamily B).mp hB
  obtain ⟨e, _, rfl⟩ := (I.mem_terminalCoreFamily C).mp hC
  exact I.terminalCore_eq_of_card_eq d e hcard

/-- There are at most `n` distinct cores, since there is at most one of each positive size. -/
theorem terminalCoreFamily_card_le : I.terminalCoreFamily.card ≤ n := by
  classical
  rw [← Finset.card_image_of_injOn I.terminalCoreFamily_card_injective]
  calc
    (I.terminalCoreFamily.image Finset.card).card ≤ (Finset.Icc 1 n).card := by
      apply Finset.card_le_card
      intro k hk
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hk
      obtain ⟨d, hd, rfl⟩ := (I.mem_terminalCoreFamily B).mp hB
      exact Finset.mem_Icc.mpr ⟨(I.terminalCore_nonempty hd).card_pos,
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)⟩
    _ = n := by simp

end Instance

namespace Elimination

/-- A finite path of the actual padded elimination procedure. Every listed update is executed;
no reference validity, flag-count conclusion, or terminal outcome is part of this structure. -/
structure PaddedTrajectory (n T : ℕ) where
  active : ℕ → Finset (Fin n)
  tolerance : ℕ → ℝ
  estimates : ℕ → Fin n → ℝ
  reference : ℕ → ℝ
  initial : active 0 = Finset.univ
  tolerance_pos : ∀ t, t < T → 0 < tolerance t
  tolerance_antitone : ∀ t u, t ≤ u → u < T → tolerance u ≤ tolerance t
  step : ∀ t, t < T → active (t + 1) =
    padded (active t) (estimates t) (reference t) (tolerance t)

namespace PaddedTrajectory
variable {n T : ℕ} (P : PaddedTrajectory n T)

/-- An arm's unique actual deletion call. -/
def removedAt (t : ℕ) : Finset (Fin n) := P.active t \ P.active (t + 1)

/-- Actual centered severe downward errors, only on active labels. -/
def severeAt (I : Instance n) (t : ℕ) : Finset (Fin n) :=
  (P.active t).filter fun i => P.estimates t i - I.mean i < -5 * P.tolerance t / 16

/-- All severe flags in the finite trajectory. -/
def everSevere (I : Instance n) : Finset (Fin n) :=
  (Finset.range T).biUnion (P.severeAt I)

/-- The tolerance of the last executed call. Results using it require `0<T`. -/
def finalTolerance : ℝ := P.tolerance (T - 1)

/-- The fixed core determined by the last tolerance. -/
def core (I : Instance n) : Finset (Fin n) := I.terminalCore (P.finalTolerance / 8)

/-- Upper validity is only used for a deterministic removal implication. -/
def UpperValid (I : Instance n) : Prop :=
  ∀ t, t < T → P.reference t ≤ I.mean I.best + P.tolerance t / 16

@[simp] theorem mem_removedAt (t : ℕ) (i : Fin n) :
    i ∈ P.removedAt t ↔ i ∈ P.active t ∧ i ∉ P.active (t + 1) := by
  simp [removedAt]

@[simp] theorem mem_severeAt (I : Instance n) (t : ℕ) (i : Fin n) :
    i ∈ P.severeAt I t ↔
      i ∈ P.active t ∧ P.estimates t i - I.mean i < -5 * P.tolerance t / 16 := by
  simp [severeAt]

@[simp] theorem mem_everSevere (I : Instance n) (i : Fin n) :
    i ∈ P.everSevere I ↔ ∃ t < T, i ∈ P.severeAt I t := by
  simp [everSevere]

/-- The retained active sets shrink on every executed call. -/
theorem active_succ_subset (t : ℕ) (ht : t < T) : P.active (t + 1) ⊆ P.active t := by
  rw [P.step t ht]
  exact padded_subset _ _ _ _

/-- Monotonicity is asserted only between states in the finite executed trajectory. -/
theorem active_antitone {t u : ℕ} (htu : t ≤ u) (hu : u ≤ T) : P.active u ⊆ P.active t := by
  induction u with
  | zero =>
    have ht : t = 0 := by omega
    subst t
    exact Finset.Subset.rfl
  | succ u ih =>
    rcases Nat.eq_or_lt_of_le htu with h | h
    · subst t; exact Finset.Subset.rfl
    · exact (P.active_succ_subset u (by omega)).trans (ih (by omega) (by omega))

/-- Every label absent from an executed state was removed at an earlier executed call. -/
theorem exists_removedAt {u : ℕ} (hu : u ≤ T) {i : Fin n}
    (hi : i ∉ P.active u) : ∃ t < u, i ∈ P.removedAt t := by
  induction u with
  | zero => simp [P.initial] at hi
  | succ u ih =>
    by_cases hiu : i ∈ P.active u
    · exact ⟨u, Nat.lt_succ_self u, (P.mem_removedAt u i).mpr ⟨hiu, hi⟩⟩
    · obtain ⟨t, ht, hit⟩ := ih (by omega) hiu
      exact ⟨t, ht.trans (Nat.lt_succ_self u), hit⟩

/-- A removed arm never re-enters the active set before the terminal state. -/
theorem removedAt_not_mem_final {t : ℕ} (ht : t < T) {i : Fin n}
    (hi : i ∈ P.removedAt t) : i ∉ P.active T := by
  intro hfinal
  exact (P.mem_removedAt t i).mp hi |>.2
    (P.active_antitone (Nat.succ_le_of_lt ht) le_rfl hfinal)

theorem removedAt_disjoint_of_lt {s t : ℕ} (hst : s < t) (ht : t < T) :
    Disjoint (P.removedAt s) (P.removedAt t) := by
  apply Finset.disjoint_left.mpr
  intro i his hit
  exact (P.mem_removedAt s i).mp his |>.2
    (P.active_antitone (Nat.succ_le_of_lt hst) ht.le ((P.mem_removedAt t i).mp hit).1)

/-- Deletion sets of different executed calls are disjoint. -/
theorem removedAt_pairwiseDisjoint : (↑(Finset.range T) : Set ℕ).PairwiseDisjoint P.removedAt := by
  intro s hs t ht hne
  simp only [Finset.mem_coe, Finset.mem_range] at hs ht
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact P.removedAt_disjoint_of_lt hst ht
  · exact (P.removedAt_disjoint_of_lt hts hs).symm

/-- An arm has only one removal call in an executed trajectory. -/
theorem removedAt_unique {s t : ℕ} (hs : s < T) (ht : t < T) {i : Fin n}
    (his : i ∈ P.removedAt s) (hit : i ∈ P.removedAt t) : s = t := by
  rcases lt_trichotomy s t with hst | hst | hts
  · exact False.elim ((Finset.disjoint_left.mp (P.removedAt_disjoint_of_lt hst ht)) his hit)
  · exact hst
  · exact False.elim ((Finset.disjoint_left.mp (P.removedAt_disjoint_of_lt hts hs)) hit his)

/-- Actual deletion sets partition precisely the labels absent at the end. -/
theorem biUnion_removedAt :
    (Finset.range T).biUnion P.removedAt = Finset.univ \ P.active T := by
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_sdiff,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, hi⟩
    exact P.removedAt_not_mem_final ht hi
  · exact P.exists_removedAt le_rfl

/-- A terminal core is near enough at every earlier executed tolerance. -/
theorem core_gap_le_call (I : Instance n) {t : ℕ} (ht : t < T) {i : Fin n}
    (hi : i ∈ P.core I) : I.gap i ≤ P.tolerance t / 8 := by
  have hgap : I.gap i < P.finalTolerance / 8 := (I.mem_terminalCore _ _).mp hi
  have htol : P.finalTolerance ≤ P.tolerance t :=
    P.tolerance_antitone t (T - 1) (by omega) (by omega)
  linarith

/-- A removed terminal-core arm has the actual severe Gaussian-error predicate.
This uses the padded retained-set definition, not a stipulated flag-count bound. -/
theorem removed_core_mem_severeAt (I : Instance n) (hvalid : P.UpperValid I)
    {t : ℕ} (ht : t < T) {i : Fin n} (hcore : i ∈ P.core I)
    (hremoved : i ∈ P.removedAt t) : i ∈ P.severeAt I t := by
  obtain ⟨hi, hnot⟩ := (P.mem_removedAt t i).mp hremoved
  apply (P.mem_severeAt I t i).mpr
  refine ⟨hi, padded_removed_near_severe hi (hvalid t ht) (P.core_gap_le_call I ht hcore) ?_⟩
  rwa [← P.step t ht]

/-- Every removed terminal-core arm belongs to the derived ever-severe set. -/
theorem core_sdiff_final_subset_everSevere (I : Instance n) (hvalid : P.UpperValid I) :
    P.core I \ P.active T ⊆ P.everSevere I := by
  intro i hi
  obtain ⟨hcore, hnot⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨t, ht, hremoved⟩ := P.exists_removedAt le_rfl hnot
  exact (P.mem_everSevere I i).mpr
    ⟨t, ht, P.removed_core_mem_severeAt I hvalid ht hcore hremoved⟩

/-- On a nontrivial instance, reaching a singleton requires at least one executed update. -/
theorem pos_of_terminal_singleton (I : Instance n) {out : Fin n}
    (hfinal : P.active T = {out}) : 0 < T := by
  by_contra! hT
  have hzero : T = 0 := Nat.eq_zero_of_le_zero hT
  have hinitial : P.active T = Finset.univ := by simpa [hzero] using P.initial
  have hc := congrArg Finset.card (hinitial.symm.trans hfinal)
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_singleton] at hc
  have hn := I.two_le
  omega

theorem best_mem_core (I : Instance n) (hT : 0 < T) : I.best ∈ P.core I := by
  exact I.best_mem_terminalCore (div_pos (P.tolerance_pos (T - 1) (by omega)) (by norm_num))

/-- Any incorrect singleton output entails a severe flag of the original best arm. -/
theorem wrong_singleton_best_mem_everSevere (I : Instance n) (hvalid : P.UpperValid I)
    {out : Fin n} (hfinal : P.active T = {out}) (hwrong : out ≠ I.best) :
    I.best ∈ P.everSevere I := by
  apply P.core_sdiff_final_subset_everSevere I hvalid
  exact Finset.mem_sdiff.mpr ⟨P.best_mem_core I (P.pos_of_terminal_singleton I hfinal),
    by simp [hfinal, Ne.symm hwrong]⟩

/-- The complete deterministic terminal-core implication in E.7: an incorrect singleton has a
best-arm severe flag and at least max(1,|core|-1) distinct severely flagged core arms. -/
theorem wrong_singleton_core_flags (I : Instance n) (hvalid : P.UpperValid I)
    {out : Fin n} (hfinal : P.active T = {out}) (hwrong : out ≠ I.best) :
    I.best ∈ P.everSevere I ∧
      max 1 ((P.core I).card - 1) ≤ (P.core I ∩ P.everSevere I).card := by
  have hbest := P.wrong_singleton_best_mem_everSevere I hvalid hfinal hwrong
  have hbestcore := P.best_mem_core I (P.pos_of_terminal_singleton I hfinal)
  have hone : 1 ≤ (P.core I ∩ P.everSevere I).card :=
    Finset.card_pos.mpr ⟨I.best, Finset.mem_inter.mpr ⟨hbestcore, hbest⟩⟩
  have hcover : P.core I ⊆ (P.core I ∩ P.everSevere I) ∪ P.active T := by
    intro i hi
    by_cases hfinali : i ∈ P.active T
    · exact Finset.mem_union_right _ hfinali
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hi,
        P.core_sdiff_final_subset_everSevere I hvalid (Finset.mem_sdiff.mpr ⟨hi, hfinali⟩)⟩)
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  rw [hfinal, Finset.card_singleton] at hc
  exact ⟨hbest, max_le hone (by omega)⟩

/-- The path's positive terminal threshold belongs to the fixed instance core family. -/
theorem core_mem_terminalCoreFamily (I : Instance n) (hT : 0 < T) :
    P.core I ∈ I.terminalCoreFamily := by
  apply (I.mem_terminalCoreFamily _).mpr
  exact ⟨P.finalTolerance / 8,
    div_pos (P.tolerance_pos (T - 1) (by omega)) (by norm_num), rfl⟩

/-- The form used for probability bounds: first fix a core `B`, then restrict to paths whose
terminal core equals it. This is a deterministic implication, not conditioning on core selection. -/
theorem wrong_singleton_fixed_core_flags (I : Instance n) (hvalid : P.UpperValid I)
    (B : Finset (Fin n)) (hcore : P.core I = B)
    {out : Fin n} (hfinal : P.active T = {out}) (hwrong : out ≠ I.best) :
    I.best ∈ P.everSevere I ∧ max 1 (B.card - 1) ≤ (B ∩ P.everSevere I).card := by
  simpa only [hcore] using P.wrong_singleton_core_flags I hvalid hfinal hwrong

end PaddedTrajectory
end Elimination
end GapEntropy
