import GapEntropy.MedianTape
import GapEntropy.HistoryConsistency
import GapEntropy.ReturnedCounts

/-!
# Deterministic schedule and history reconstruction for median elimination

Round boundaries depend only on the initial cardinality and public budgets.
The current active set is reconstructed from completed earlier blocks. Every
arm in a block is sampled consecutively, in increasing label order.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.MedianPolicy
open MedianElimination

def blockSize (s : ℕ) (ε β : ℝ) (r : ℕ) : ℕ :=
  if 2 ≤ cardinalSchedule s r then cardinalSchedule s r * roundSamples ε β r else 0

def start (s : ℕ) (ε β : ℝ) : ℕ → ℕ
  | 0 => 0
  | r + 1 => start s ε β r + blockSize s ε β r

theorem start_eq_sum (s : ℕ) (ε β : ℝ) (r : ℕ) :
    start s ε β r = ∑ q ∈ Finset.range r, blockSize s ε β q := by
  induction r with
  | zero => simp [start]
  | succ r ih => simp only [start, Finset.sum_range_succ, ih]

@[simp] theorem start_terminal (s : ℕ) (ε β : ℝ) :
    start s ε β s = declaredCost s ε β := by
  simp only [start_eq_sum, declaredCost, blockSize]

theorem start_mono (s : ℕ) (ε β : ℝ) : Monotone (start s ε β) :=
  monotone_nat_of_le_succ (fun r => by simp only [start]; omega)

def armRank {n : ℕ} (U : Finset (Fin n)) (i : Fin n) : ℕ :=
  if hi : i ∈ U then ((U.orderIsoOfFin rfl).symm ⟨i, hi⟩ : ℕ) else 0

def armAt {n : ℕ} (fallback : Fin n) (U : Finset (Fin n)) (k : ℕ) : Fin n :=
  if hk : k < U.card then U.orderEmbOfFin rfl ⟨k, hk⟩ else fallback

theorem armRank_lt {n : ℕ} {U : Finset (Fin n)} (hU : U.Nonempty) (i : Fin n) :
    armRank U i < U.card := by
  unfold armRank
  split_ifs with hi
  · exact Fin.isLt _
  · exact hU.card_pos

theorem armAt_mem {n : ℕ} (fallback : Fin n) {U : Finset (Fin n)} {k : ℕ}
    (hk : k < U.card) : armAt fallback U k ∈ U := by
  simp only [armAt, dif_pos hk]
  exact Finset.orderEmbOfFin_mem _ _ _

theorem armAt_armRank {n : ℕ} (fallback : Fin n) {U : Finset (Fin n)}
    {i : Fin n} (hi : i ∈ U) : armAt fallback U (armRank U i) = i := by
  have hk := armRank_lt (show U.Nonempty from ⟨i, hi⟩) i
  rw [armAt, dif_pos hk]
  simp only [armRank, dif_pos hi]
  exact congrArg Subtype.val ((U.orderIsoOfFin rfl).apply_symm_apply ⟨i, hi⟩)

theorem armRank_armAt {n : ℕ} (fallback : Fin n) {U : Finset (Fin n)}
    {k : ℕ} (hk : k < U.card) : armRank U (armAt fallback U k) = k := by
  have hi := armAt_mem fallback hk
  rw [armRank, dif_pos hi]
  simp only [armAt, dif_pos hk]
  exact congrArg Fin.val ((U.orderIsoOfFin rfl).symm_apply_apply ⟨k, hk⟩)

/-- The unused coordinates use rank zero. This does not affect sorting on the
active set, and all reconstruction reads stay within the current block. -/
def blockMean {n : ℕ} (s : ℕ) (ε β : ℝ) (r : ℕ) (U : Finset (Fin n))
    (y : ℕ → ℝ) (i : Fin n) : ℝ :=
  (∑ j : Fin (roundSamples ε β r),
    y (start s ε β r + armRank U i * roundSamples ε β r + j)) /
      (roundSamples ε β r : ℝ)

def reconstruct {n : ℕ} (S : Finset (Fin n)) (ε β : ℝ) (y : ℕ → ℝ) :
    ℕ → Finset (Fin n)
  | 0 => S
  | r + 1 => nextActive (reconstruct S ε β y r)
      (blockMean S.card ε β r (reconstruct S ε β y r) y)

theorem reconstruct_card {n : ℕ} (S : Finset (Fin n)) (ε β : ℝ) (y : ℕ → ℝ) (r : ℕ) :
    (reconstruct S ε β y r).card = cardinalSchedule S.card r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [reconstruct, nextActive_card, ih]; rfl

theorem reconstruct_nonempty {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty)
    (ε β : ℝ) (y : ℕ → ℝ) (r : ℕ) : (reconstruct S ε β y r).Nonempty := by
  apply Finset.card_pos.mp
  rw [reconstruct_card]
  exact cardinalSchedule_pos hS.card_pos r

theorem reconstruct_subset {n : ℕ} (S : Finset (Fin n)) (ε β : ℝ) (y : ℕ → ℝ) (r : ℕ) :
    reconstruct S ε β y r ⊆ S := by
  induction r with
  | zero => exact Finset.Subset.refl _
  | succ r ih => exact (nextActive_subset _ _).trans ih

theorem reconstruct_terminal_card {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty)
    (ε β : ℝ) (y : ℕ → ℝ) : (reconstruct S ε β y S.card).card = 1 := by
  rw [reconstruct_card]
  exact cardinalSchedule_one hS.card_pos

theorem blockMean_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (s : ℕ) (ε β : ℝ) (r : ℕ) {U : Ω → Finset (Fin n)} {Y : ℕ → Ω → ℝ}
    (hU : Measurable U) (hY : ∀ t, Measurable (Y t)) (i : Fin n) :
    Measurable (fun ω => blockMean s ε β r (U ω) (fun t => Y t ω) i) := by
  unfold blockMean
  apply Measurable.div_const
  apply Finset.measurable_fun_sum
  intro j _
  have hk : Measurable (fun ω => start s ε β r + armRank (U ω) i * roundSamples ε β r + j) :=
    (measurable_of_finite (fun V : Finset (Fin n) =>
      start s ε β r + armRank V i * roundSamples ε β r + j)).comp hU
  exact (measurable_from_prod_countable_left (f := fun p : Ω × ℕ => Y p.2 p.1) hY).comp
    (measurable_id.prodMk hk)

theorem reconstruct_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (S : Finset (Fin n)) (ε β : ℝ) {Y : ℕ → Ω → ℝ}
    (hY : ∀ t, Measurable (Y t)) (r : ℕ) :
    Measurable (fun ω => reconstruct S ε β (fun t => Y t ω) r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih =>
      exact nextActive_measurable ih (fun i => blockMean_measurable S.card ε β r ih hY i)

theorem block_index_lt {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty)
    (ε β : ℝ) (y : ℕ → ℝ) (r : ℕ) (hr : 2 ≤ cardinalSchedule S.card r)
    (i : Fin n) (j : Fin (roundSamples ε β r)) :
    start S.card ε β r + armRank (reconstruct S ε β y r) i * roundSamples ε β r + j <
      start S.card ε β (r + 1) := by
  have hi := armRank_lt (reconstruct_nonempty hS ε β y r) i
  rw [reconstruct_card] at hi
  have hmul := Nat.mul_le_mul_right (roundSamples ε β r) hi
  simp only [start, blockSize, if_pos hr]
  have hj := j.isLt
  nlinarith

/-- Reconstructing round `r` consults only samples before its fixed start time. -/
theorem reconstruct_congr_before {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty)
    (ε β : ℝ) (r : ℕ) {y z : ℕ → ℝ}
    (hyz : ∀ t < start S.card ε β r, y t = z t) :
    reconstruct S ε β y r = reconstruct S ε β z r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      have hprev : reconstruct S ε β y r = reconstruct S ε β z r :=
        ih (fun t ht => hyz t (ht.trans_le (start_mono S.card ε β (Nat.le_succ r))))
      by_cases hr : 2 ≤ cardinalSchedule S.card r
      · rw [reconstruct, reconstruct, ← hprev]
        congr 1
        funext i
        unfold blockMean
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        exact hyz _ (block_index_lt hS ε β y r hr i j)
      · have hcy : ¬ 2 ≤ (reconstruct S ε β y r).card := by rwa [reconstruct_card]
        have hcz : ¬ 2 ≤ (reconstruct S ε β z r).card := by rwa [reconstruct_card]
        simpa only [reconstruct, nextActive, if_neg hcy, if_neg hcz] using hprev

def estimates {n : ℕ} (S : Finset (Fin n)) (ε β : ℝ) (y : ℕ → ℝ)
    (r : ℕ) : Fin n → ℝ := blockMean S.card ε β r (reconstruct S ε β y r) y

theorem reconstruct_eq_activeSets {n : ℕ} (S : Finset (Fin n)) (ε β : ℝ)
    (y : ℕ → ℝ) (r : ℕ) : reconstruct S ε β y r = activeSets S (estimates S ε β y) r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [reconstruct, activeSets, estimates, ih]

end GapEntropy.MedianPolicy
