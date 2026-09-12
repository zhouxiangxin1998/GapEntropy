import GapEntropy.TerminalCore

/-!
# Outside-arm work accounting for Appendix E.4

Every nonpremature deletion is charged to its actual unique removal call.
The final executed call supplies the deterministic outside-weight maximum. Thus
an incorrect terminal path with small work cap forces both the core-flag count
and a large outside flagged weight, without conditioning on a selected core.
-/

noncomputable section
open scoped BigOperators Classical

namespace GapEntropy.Elimination.PaddedTrajectory

variable {n T : ℕ} (P : PaddedTrajectory n T)

def callWork (t : ℕ) : ℝ := (P.active t).card * (P.tolerance t ^ 2)⁻¹

def baseWork : ℝ := ∑ t ∈ Finset.range T, P.callWork t

def outside (I : Instance n) : Finset (Fin n) := Finset.univ \ P.core I

def outsideHardness (I : Instance n) : ℝ := ∑ i ∈ P.outside I, I.weight i

def nonprematureAt (I : Instance n) (t : ℕ) : Finset (Fin n) :=
  (P.removedAt t).filter fun i => P.tolerance t ≤ 8 * I.gap i

def nonpremature (I : Instance n) : Finset (Fin n) :=
  (Finset.range T).biUnion (P.nonprematureAt I)

theorem callWork_nonneg (t : ℕ) : 0 ≤ P.callWork t := by unfold callWork; positivity

theorem baseWork_nonneg : 0 ≤ P.baseWork :=
  Finset.sum_nonneg (fun t _ => P.callWork_nonneg t)

theorem callWork_le_baseWork {t : ℕ} (ht : t < T) : P.callWork t ≤ P.baseWork :=
  Finset.single_le_sum (fun u _ => P.callWork_nonneg u) (Finset.mem_range.mpr ht)

private theorem inverse_gap_weight_le {d g : ℝ} (hd : 0 < d) (hg : d ≤ 8 * g) :
    (g ^ 2)⁻¹ ≤ 64 * (d ^ 2)⁻¹ := by
  have hgpos : 0 < g := by linarith
  have he : ((d / 8) ^ 2)⁻¹ = 64 * (d ^ 2)⁻¹ := by
    field_simp
    ring
  rw [← he]
  apply (inv_le_inv₀ (sq_pos_of_pos hgpos) (sq_pos_of_pos (by positivity))).mpr
  have h : d / 8 ≤ g := by linarith
  nlinarith

theorem nonprematureAt_subset_removed (I : Instance n) (t : ℕ) :
    P.nonprematureAt I t ⊆ P.removedAt t := Finset.filter_subset _ _

theorem nonprematureAt_subset_active (I : Instance n) (t : ℕ) :
    P.nonprematureAt I t ⊆ P.active t :=
  (P.nonprematureAt_subset_removed I t).trans Finset.sdiff_subset

theorem nonprematureAt_weight_le (I : Instance n) {t : ℕ} (ht : t < T)
    {i : Fin n} (hi : i ∈ P.nonprematureAt I t) :
    I.weight i ≤ 64 * (P.tolerance t ^ 2)⁻¹ :=
  inverse_gap_weight_le (P.tolerance_pos t ht) (Finset.mem_filter.mp hi).2

/-- Each nonpremature deletion costs at most 64 times that arm's current work. -/
theorem nonprematureAt_sum_le (I : Instance n) {t : ℕ} (ht : t < T) :
    (∑ i ∈ P.nonprematureAt I t, I.weight i) ≤ 64 * P.callWork t := by
  calc
    (∑ i ∈ P.nonprematureAt I t, I.weight i) ≤
        ∑ _i ∈ P.nonprematureAt I t, 64 * (P.tolerance t ^ 2)⁻¹ :=
      Finset.sum_le_sum (fun _ hi => P.nonprematureAt_weight_le I ht hi)
    _ ≤ ∑ _i ∈ P.active t, 64 * (P.tolerance t ^ 2)⁻¹ :=
      Finset.sum_le_sum_of_subset_of_nonneg (P.nonprematureAt_subset_active I t)
        (fun _ _ _ => by positivity)
    _ = 64 * P.callWork t := by simp [callWork]; ring

/-- The actual deletion sets are disjoint, so no removed arm is charged twice. -/
theorem nonpremature_sum_le (I : Instance n) :
    (∑ i ∈ P.nonpremature I, I.weight i) ≤ 64 * P.baseWork := by
  have hd : (↑(Finset.range T) : Set ℕ).PairwiseDisjoint (P.nonprematureAt I) := by
    intro s hs t ht hst
    exact (P.removedAt_pairwiseDisjoint hs ht hst).mono
      (P.nonprematureAt_subset_removed I s) (P.nonprematureAt_subset_removed I t)
  rw [nonpremature, Finset.sum_biUnion hd, baseWork, Finset.mul_sum]
  exact Finset.sum_le_sum (fun t ht => P.nonprematureAt_sum_le I (Finset.mem_range.mp ht))

/-- A premature removed arm has the actual centered severe-error predicate. -/
theorem removed_mem_nonpremature_or_severe (I : Instance n) (hvalid : P.UpperValid I)
    {t : ℕ} (ht : t < T) {i : Fin n} (hi : i ∈ P.removedAt t) :
    i ∈ P.nonprematureAt I t ∨ i ∈ P.severeAt I t := by
  by_cases h : P.tolerance t ≤ 8 * I.gap i
  · exact Or.inl (Finset.mem_filter.mpr ⟨hi, h⟩)
  · right
    obtain ⟨hia, hir⟩ := (P.mem_removedAt t i).mp hi
    apply (P.mem_severeAt I t i).mpr
    refine ⟨hia, padded_removed_near_severe hia (hvalid t ht) (by change I.gap i ≤ P.tolerance t / 8; linarith) ?_⟩
    rwa [← P.step t ht]

/-- Deleted labels are either nonpremature charges or severely flagged labels. -/
theorem outside_cover (I : Instance n) (hvalid : P.UpperValid I) :
    P.outside I ⊆ ((P.outside I ∩ P.everSevere I) ∪ P.nonpremature I) ∪
      (P.active T ∩ P.outside I) := by
  intro i hi
  by_cases hfin : i ∈ P.active T
  · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hfin, hi⟩)
  · obtain ⟨t, ht, hr⟩ := P.exists_removedAt le_rfl hfin
    rcases P.removed_mem_nonpremature_or_severe I hvalid ht hr with hn | hs
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨t, Finset.mem_range.mpr ht, hn⟩))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_inter.mpr ⟨hi, (P.mem_everSevere I i).mpr ⟨t, ht, hs⟩⟩))

private theorem weightSum_union_le (I : Instance n) (S U : Finset (Fin n)) :
    (∑ i ∈ S ∪ U, I.weight i) ≤ (∑ i ∈ S, I.weight i) + ∑ i ∈ U, I.weight i := by
  have h := Finset.sum_union_inter (s₁ := S) (s₂ := U) (f := I.weight)
  have hn : 0 ≤ ∑ i ∈ S ∩ U, I.weight i := Finset.sum_nonneg (fun i _ => I.weight_nonneg i)
  linarith

/-- E.8: the final executed call bounds every fixed outside weight. Requiring its
input size to be at least two is the actual algorithm's singleton stopping guard. -/
theorem outside_weight_le_work (I : Instance n) (hT : 0 < T)
    (hlast : 2 ≤ (P.active (T - 1)).card) {i : Fin n} (hi : i ∈ P.outside I) :
    I.weight i ≤ 32 * P.baseWork := by
  have hgap : P.finalTolerance / 8 ≤ I.gap i := by
    have hn := (Finset.mem_sdiff.mp hi).2
    exact le_of_not_gt (fun h => hn ((I.mem_terminalCore _ i).mpr h))
  change P.tolerance (T - 1) / 8 ≤ I.gap i at hgap
  have ht : T - 1 < T := by omega
  have hw := inverse_gap_weight_le (P.tolerance_pos (T - 1) ht) (by linarith :
    P.tolerance (T - 1) ≤ 8 * I.gap i)
  have hc : 2 * (P.tolerance (T - 1) ^ 2)⁻¹ ≤ P.callWork (T - 1) := by
    apply mul_le_mul_of_nonneg_right (by exact_mod_cast hlast) (by positivity)
  have hb := P.callWork_le_baseWork ht
  change I.weight i ≤ 32 * P.baseWork
  change I.weight i ≤ 64 * (P.tolerance (T - 1) ^ 2)⁻¹ at hw
  linarith

theorem final_outside_weight_le_work (I : Instance n) {out : Fin n}
    (hfinal : P.active T = {out}) (hlast : 2 ≤ (P.active (T - 1)).card) :
    (∑ i ∈ P.active T ∩ P.outside I, I.weight i) ≤ 32 * P.baseWork := by
  by_cases ho : out ∈ P.outside I
  · have he : P.active T ∩ P.outside I = {out} := by
      rw [hfinal]
      exact Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr ho)
    rw [he, Finset.sum_singleton]
    exact P.outside_weight_le_work I (P.pos_of_terminal_singleton I hfinal) hlast ho
  · have he : P.active T ∩ P.outside I = ∅ := by
      ext i
      constructor
      · intro hi
        obtain ⟨h₁, h₂⟩ := Finset.mem_inter.mp hi
        have hie : i = out := by simpa only [hfinal, Finset.mem_singleton] using h₁
        exact (ho (hie ▸ h₂)).elim
      · simp
    rw [he, Finset.sum_empty]
    exact mul_nonneg (by norm_num) P.baseWork_nonneg

/-- E.4's full deterministic accounting, on the actual padded path. -/
theorem outside_flagged_weight_lower (I : Instance n) (hvalid : P.UpperValid I)
    {out : Fin n} (hfinal : P.active T = {out})
    (hlast : 2 ≤ (P.active (T - 1)).card) :
    P.outsideHardness I - 96 * P.baseWork ≤
      ∑ i ∈ P.outside I ∩ P.everSevere I, I.weight i := by
  have hcover := Finset.sum_le_sum_of_subset_of_nonneg (P.outside_cover I hvalid)
    (fun i _ _ => I.weight_nonneg i)
  have hU := weightSum_union_le I ((P.outside I ∩ P.everSevere I) ∪ P.nonpremature I)
    (P.active T ∩ P.outside I)
  have hV := weightSum_union_le I (P.outside I ∩ P.everSevere I) (P.nonpremature I)
  have hnon := P.nonpremature_sum_le I
  have hfin := P.final_outside_weight_le_work I hfinal hlast
  unfold outsideHardness
  linarith

/-- On a fixed small cap, the same path has the joint core-count and outside-weight
requirements used in E.11. This theorem does not assert independence of flags. -/
theorem small_cap_joint_flags (I : Instance n) (hvalid : P.UpperValid I)
    {out : Fin n} (hfinal : P.active T = {out}) (hwrong : out ≠ I.best)
    (hlast : 2 ≤ (P.active (T - 1)).card) {M : ℝ}
    (hwork : P.baseWork ≤ M) (hsmall : M ≤ P.outsideHardness I / 192) :
    max 1 ((P.core I).card - 1) ≤ (P.core I ∩ P.everSevere I).card ∧
      P.outsideHardness I / 2 ≤ ∑ i ∈ P.outside I ∩ P.everSevere I, I.weight i ∧
      ∀ i ∈ P.outside I, I.weight i ≤ 32 * M := by
  refine ⟨(P.wrong_singleton_core_flags I hvalid hfinal hwrong).2, ?_, ?_⟩
  · have h := P.outside_flagged_weight_lower I hvalid hfinal hlast
    linarith
  · intro i hi
    exact (P.outside_weight_le_work I (P.pos_of_terminal_singleton I hfinal) hlast hi).trans
      (mul_le_mul_of_nonneg_left hwork (by norm_num))

end GapEntropy.Elimination.PaddedTrajectory
