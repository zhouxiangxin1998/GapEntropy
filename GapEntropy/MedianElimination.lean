import GapEntropy.SortingMeasurability
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Median elimination: exact schedules and measurable finite recursion

The procedure uses the manuscript's schedules and the actual empirical upper half.
It is unrolled for the initial arm count; after reaching at most one arm, later
steps are identities and reserve no observations. This gives a finite measurable
implementation with the same observations and output as stopping immediately.

The multi-round probabilistic guarantee and deterministic sample bound are proved
in `MedianGaussian` and `MedianCost`. `MedianTape` supplies a canonical Gaussian
product measure. The deterministic good-round composition below is only one step
in that complete statistical theorem, not an assumed probabilistic guarantee.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace GapEntropy.MedianElimination

def roundEpsilon (ε : ℝ) (r : ℕ) : ℝ := ε / 8 * (3 / 4 : ℝ) ^ r
def roundBeta (β : ℝ) (r : ℕ) : ℝ := β * (1 / 2 : ℝ) ^ (r + 1)
def roundBudget (ε β : ℝ) (r : ℕ) : ℝ :=
  8 * (roundEpsilon ε r ^ 2)⁻¹ * Real.log (8 / roundBeta β r)
def roundSamples (ε β : ℝ) (r : ℕ) : ℕ := ⌈roundBudget ε β r⌉₊

theorem roundEpsilon_pos {ε : ℝ} (hε : 0 < ε) (r : ℕ) : 0 < roundEpsilon ε r := by
  unfold roundEpsilon
  positivity

theorem roundBeta_pos {β : ℝ} (hβ : 0 < β) (r : ℕ) : 0 < roundBeta β r := by
  unfold roundBeta
  positivity

theorem roundBeta_le {β : ℝ} (hβ : 0 ≤ β) (r : ℕ) : roundBeta β r ≤ β := by
  have hp : (1 / 2 : ℝ) ^ (r + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold roundBeta
  nlinarith

theorem roundBudget_pos {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (r : ℕ) :
    0 < roundBudget ε β r := by
  have he := roundEpsilon_pos hε r
  have hb := roundBeta_pos hβ r
  have hb1 := (roundBeta_le hβ.le r).trans hβ1
  have hlog : 0 < Real.log (8 / roundBeta β r) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hb).mpr (by linarith)
  unfold roundBudget
  positivity

theorem roundSamples_pos {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (r : ℕ) :
    0 < roundSamples ε β r :=
  Nat.one_le_ceil_iff.mpr (roundBudget_pos hε hβ hβ1 r)

theorem roundSamples_budget (ε β : ℝ) (r : ℕ) :
    roundBudget ε β r ≤ (roundSamples ε β r : ℝ) := Nat.le_ceil _

theorem roundSamples_lt_budget_add_one {ε β : ℝ}
    (hε : 0 < ε) (hβ : 0 < β) (hβ1 : β ≤ 1) (r : ℕ) :
    (roundSamples ε β r : ℝ) < roundBudget ε β r + 1 :=
  Nat.ceil_lt_add_one (roundBudget_pos hε hβ hβ1 r).le

theorem cumulative_accuracy {ε : ℝ} (hε : 0 ≤ ε) (R : ℕ) :
    2 * (∑ r ∈ Finset.range R, roundEpsilon ε r) ≤ ε := by
  have hg := geom_sum_mul_neg (3 / 4 : ℝ) R
  have hp : 0 ≤ (3 / 4 : ℝ) ^ R := by positivity
  have hs : (∑ r ∈ Finset.range R, (3 / 4 : ℝ) ^ r) ≤ 4 := by linarith
  simp only [roundEpsilon, ← Finset.mul_sum]
  nlinarith

theorem cumulative_confidence {β : ℝ} (hβ : 0 ≤ β) (R : ℕ) :
    (∑ r ∈ Finset.range R, roundBeta β r) ≤ β := by
  have hg := geom_sum_mul_neg (1 / 2 : ℝ) R
  have hp : 0 ≤ (1 / 2 : ℝ) ^ R := by positivity
  have hs : (∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r) ≤ 2 := by linarith
  have heq : (∑ r ∈ Finset.range R, roundBeta β r) =
      (β / 2) * ∑ r ∈ Finset.range R, (1 / 2 : ℝ) ^ r := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp [roundBeta, pow_succ]
    ring
  rw [heq]
  nlinarith

def cardinalSchedule (s : ℕ) : ℕ → ℕ
  | 0 => s
  | r + 1 => (cardinalSchedule s r + 1) / 2

theorem cardinalSchedule_exact {s : ℕ} (hs : 0 < s) (r : ℕ) :
    cardinalSchedule s r = (s - 1) / 2 ^ r + 1 := by
  induction r with
  | zero => simp [cardinalSchedule]; omega
  | succ r ih =>
    rw [cardinalSchedule, ih]
    calc
      ((s - 1) / 2 ^ r + 1 + 1) / 2 = ((s - 1) / 2 ^ r) / 2 + 1 := by omega
      _ = (s - 1) / 2 ^ (r + 1) + 1 := by rw [Nat.div_div_eq_div_mul, pow_succ]

theorem cardinalSchedule_pos {s : ℕ} (hs : 0 < s) (r : ℕ) : 0 < cardinalSchedule s r := by
  rw [cardinalSchedule_exact hs]
  exact Nat.succ_pos _

theorem cardinalSchedule_one {s : ℕ} (hs : 0 < s) : cardinalSchedule s s = 1 := by
  rw [cardinalSchedule_exact hs, Nat.div_eq_of_lt, zero_add]
  exact (Nat.sub_le s 1).trans_lt s.lt_two_pow_self

/-- Before termination, the retained-size bound used in the A.2 work sum. -/
theorem cardinalSchedule_work_bound {s r : ℕ} (hs : 0 < s)
    (hr : 2 ≤ cardinalSchedule s r) : 2 ^ r * cardinalSchedule s r ≤ 2 * s := by
  have hc := cardinalSchedule_exact hs r
  have hfloor := Nat.div_mul_le_self (s - 1) (2 ^ r)
  have hp : 0 < 2 ^ r := by positivity
  have hq : 1 ≤ (s - 1) / 2 ^ r := by omega
  have hpow : 2 ^ r ≤ s - 1 := by nlinarith
  calc
    2 ^ r * cardinalSchedule s r = ((s - 1) / 2 ^ r) * 2 ^ r + 2 ^ r := by rw [hc]; ring
    _ ≤ (s - 1) + (s - 1) := Nat.add_le_add hfloor hpow
    _ ≤ 2 * s := by omega

variable {n : ℕ}

def nextActive (S : Finset (Fin n)) (x : Fin n → ℝ) : Finset (Fin n) :=
  if 2 ≤ S.card then GapEntropy.Elimination.upperHalf S x else S

def activeSets (S : Finset (Fin n)) (estimates : ℕ → Fin n → ℝ) : ℕ → Finset (Fin n)
  | 0 => S
  | r + 1 => nextActive (activeSets S estimates r) (estimates r)

theorem nextActive_subset (S : Finset (Fin n)) (x : Fin n → ℝ) : nextActive S x ⊆ S := by
  unfold nextActive
  split_ifs
  · exact GapEntropy.Elimination.upperHalf_subset S x
  · exact Finset.Subset.refl _

theorem nextActive_card (S : Finset (Fin n)) (x : Fin n → ℝ) :
    (nextActive S x).card = (S.card + 1) / 2 := by
  unfold nextActive
  split_ifs with h
  · exact GapEntropy.Elimination.upperHalf_card S x
  · omega

theorem activeSets_card (S : Finset (Fin n)) (estimates : ℕ → Fin n → ℝ) (r : ℕ) :
    (activeSets S estimates r).card = cardinalSchedule S.card r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [activeSets, nextActive_card, ih]; rfl

theorem activeSets_subset (S : Finset (Fin n)) (estimates : ℕ → Fin n → ℝ) (r : ℕ) :
    activeSets S estimates r ⊆ S := by
  induction r with
  | zero => exact Finset.Subset.refl _
  | succ r ih => exact (nextActive_subset _ _).trans ih

theorem activeSets_nonempty {S : Finset (Fin n)} (hS : S.Nonempty)
    (estimates : ℕ → Fin n → ℝ) (r : ℕ) : (activeSets S estimates r).Nonempty := by
  apply Finset.card_pos.mp
  rw [activeSets_card]
  exact cardinalSchedule_pos hS.card_pos r

theorem activeSets_terminal_card {S : Finset (Fin n)} (hS : S.Nonempty)
    (estimates : ℕ → Fin n → ℝ) : (activeSets S estimates S.card).card = 1 := by
  rw [activeSets_card]
  exact cardinalSchedule_one hS.card_pos

def selectedArm (fallback : Fin n) (S : Finset (Fin n)) : Fin n :=
  if hS : S.Nonempty then S.min' hS else fallback

theorem selectedArm_mem (fallback : Fin n) {S : Finset (Fin n)} (hS : S.Nonempty) :
    selectedArm fallback S ∈ S := by
  simp only [selectedArm, dif_pos hS]
  exact Finset.min'_mem _ _

/-- Actual finite median elimination, returning the unique terminal arm. -/
def medianEliminate (S : Finset (Fin n)) (hS : S.Nonempty)
    (estimates : ℕ → Fin n → ℝ) : Fin n :=
  selectedArm (S.min' hS) (activeSets S estimates S.card)

theorem medianEliminate_mem_terminal {S : Finset (Fin n)} (hS : S.Nonempty)
    (estimates : ℕ → Fin n → ℝ) :
    medianEliminate S hS estimates ∈ activeSets S estimates S.card :=
  selectedArm_mem _ (activeSets_nonempty hS estimates _)

/-- Reserved sample cost, expressed only in the initial size and public accuracy budgets. -/
def declaredCost (s : ℕ) (ε β : ℝ) : ℕ :=
  ∑ r ∈ Finset.range s,
    if 2 ≤ cardinalSchedule s r then cardinalSchedule s r * roundSamples ε β r else 0

def trajectoryCost (S : Finset (Fin n)) (estimates : ℕ → Fin n → ℝ) (ε β : ℝ) : ℕ :=
  ∑ r ∈ Finset.range S.card,
    if 2 ≤ (activeSets S estimates r).card then
      (activeSets S estimates r).card * roundSamples ε β r else 0

theorem trajectoryCost_eq_declaredCost (S : Finset (Fin n)) (estimates : ℕ → Fin n → ℝ)
    (ε β : ℝ) : trajectoryCost S estimates ε β = declaredCost S.card ε β := by
  simp only [trajectoryCost, declaredCost, activeSets_card]

/-- A deterministic good-round condition; its probability is a separate theorem obligation. -/
def GoodRound (S : Finset (Fin n)) (μ : Fin n → ℝ) (estimates : ℕ → Fin n → ℝ)
    (ε : ℝ) (r : ℕ) : Prop :=
  ∀ i ∈ activeSets S estimates r, ∃ b ∈ activeSets S estimates (r + 1),
    μ i - 2 * roundEpsilon ε r ≤ μ b

theorem accumulated_loss {S : Finset (Fin n)} {μ : Fin n → ℝ}
    {estimates : ℕ → Fin n → ℝ} {ε : ℝ} {R : ℕ}
    (hgood : ∀ r < R, GoodRound S μ estimates ε r) :
    ∀ i ∈ S, ∃ b ∈ activeSets S estimates R,
      μ i - 2 * (∑ r ∈ Finset.range R, roundEpsilon ε r) ≤ μ b := by
  induction R with
  | zero =>
    intro i hi
    exact ⟨i, hi, by simp⟩
  | succ R ih =>
    intro i hi
    obtain ⟨b, hb, hloss⟩ := ih (fun r hr => hgood r (Nat.lt_succ_of_lt hr)) i hi
    obtain ⟨c, hc, hstep⟩ := hgood R (Nat.lt_succ_self R) b hb
    refine ⟨c, hc, ?_⟩
    rw [Finset.sum_range_succ]
    linarith

/-- On good rounds the actual returned arm is `ε`-optimal in the original active set.
This deterministic composition is not an assumption about the random sampling law. -/
theorem medianEliminate_pac_of_goodRounds {S : Finset (Fin n)} (hS : S.Nonempty)
    {μ : Fin n → ℝ} {estimates : ℕ → Fin n → ℝ} {ε : ℝ} (hε : 0 ≤ ε)
    (hgood : ∀ r < S.card, GoodRound S μ estimates ε r) :
    ∀ i ∈ S, μ i - ε ≤ μ (medianEliminate S hS estimates) := by
  intro i hi
  obtain ⟨b, hb, hloss⟩ := accumulated_loss hgood i hi
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp (activeSets_terminal_card hS estimates)
  have hout := medianEliminate_mem_terminal hS estimates
  simp only [hc, Finset.mem_singleton] at hb hout
  rw [hout]
  rw [hb] at hloss
  linarith [cumulative_accuracy hε S.card]

section Measurability
variable {Ω : Type*} [MeasurableSpace Ω]

theorem nextActive_measurable {S : Ω → Finset (Fin n)} {X : Fin n → Ω → ℝ}
    (hS : Measurable S) (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => nextActive (S ω) (fun i => X i ω)) := by
  have hF : Measurable (fun p : Finset (Fin n) × Finset (Fin n) =>
      if 2 ≤ p.1.card then p.2 else p.1) := measurable_of_finite _
  exact hF.comp (hS.prodMk (GapEntropy.SortingMeasurability.upperHalf_measurable hS hX))

theorem activeSets_measurable (S : Finset (Fin n)) {X : ℕ → Fin n → Ω → ℝ}
    (hX : ∀ r i, Measurable (X r i)) (r : ℕ) :
    Measurable (fun ω => activeSets S (fun r i => X r i ω) r) := by
  induction r with
  | zero => exact measurable_const
  | succ r ih => exact nextActive_measurable ih (hX r)

theorem medianEliminate_measurable (S : Finset (Fin n)) (hS : S.Nonempty)
    {X : ℕ → Fin n → Ω → ℝ} (hX : ∀ r i, Measurable (X r i)) :
    Measurable (fun ω => medianEliminate S hS (fun r i => X r i ω)) :=
  (measurable_of_finite (selectedArm (S.min' hS))).comp (activeSets_measurable S hX S.card)

end Measurability
end GapEntropy.MedianElimination
