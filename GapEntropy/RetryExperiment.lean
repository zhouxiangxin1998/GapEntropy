import GapEntropy.RetryBounds
import Mathlib.Probability.ProductMeasure

/-!
# Independent attempts with actual reach events

Attempts may use different measurable spaces. Their fresh tape is the actual
infinite product of their probability laws. A reached attempt either aborts or
returns a label; the first returned label stops the stream. The reach product,
incorrect-return bound, and unconditional sample-cap integral are proved for this
experiment, rather than postulated as conditional independence assumptions.
Embedding this experiment into `Policy` remains a separate obligation.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.RetryExperiment

variable {Ω : ℕ → Type*} [∀ t, MeasurableSpace (Ω t)]
variable {α : Type*} [MeasurableSpace (Option α)] [MeasurableSingletonClass (Option α)]
variable (P : ∀ t, Measure (Ω t)) [∀ t, IsProbabilityMeasure (P t)]
variable (answer : ∀ t, Ω t → Option α) (hanswer : ∀ t, Measurable (answer t))

abbrev Tape (Ω : ℕ → Type*) := ∀ t, Ω t

def law : Measure (Tape Ω) := Measure.infinitePi P

instance : IsProbabilityMeasure (law P) := by unfold law; infer_instance

def reach (t : ℕ) : Set (Tape Ω) := {ω | ∀ u < t, answer u (ω u) = none}

def returned (a : α) : Set (Tape Ω) :=
  {ω | ∃ t, ω ∈ reach answer t ∧ answer t (ω t) = some a}

def incorrect (a : α) : Set (Tape Ω) :=
  {ω | ∃ t, ω ∈ reach answer t ∧ answer t (ω t) ≠ none ∧ answer t (ω t) ≠ some a}

def terminates : Set (Tape Ω) := {ω | ∃ t, answer t (ω t) ≠ none}

include hanswer in
theorem measurableSet_reach (t : ℕ) : MeasurableSet (reach answer t) := by
  exact (Measurable.forall fun u => Measurable.forall fun _hu =>
    ((hanswer u).comp (measurable_pi_apply u)).eq_const none).setOf

include hanswer in
theorem measurableSet_returned (a : α) : MeasurableSet (returned answer a) := by
  simp only [returned, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion fun t => (measurableSet_reach answer hanswer t).inter
    (((hanswer t).comp (measurable_pi_apply t)).eq_const (some a)).setOf

include hanswer in
theorem measurableSet_incorrect (a : α) : MeasurableSet (incorrect answer a) := by
  simp only [incorrect, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iUnion fun t => (measurableSet_reach answer hanswer t).inter
    (((((hanswer t).comp (measurable_pi_apply t)).eq_const none).not).setOf.inter
      ((((hanswer t).comp (measurable_pi_apply t)).eq_const (some a)).not).setOf)

include hanswer in
include hanswer in
theorem measurableSet_terminates : MeasurableSet (terminates answer) := by
  exact (Measurable.exists fun t =>
    (((hanswer t).comp (measurable_pi_apply t)).eq_const none).not).setOf

omit [∀ t, MeasurableSpace (Ω t)] [MeasurableSpace (Option α)]
  [MeasurableSingletonClass (Option α)] in
@[simp] theorem reach_zero : reach answer 0 = Set.univ := by ext ω; simp [reach]

omit [∀ t, MeasurableSpace (Ω t)] [MeasurableSpace (Option α)]
  [MeasurableSingletonClass (Option α)] in
theorem reach_succ (t : ℕ) :
    reach answer (t + 1) = reach answer t ∩ {ω | answer t (ω t) = none} := by
  ext ω
  simp only [reach, Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · exact fun h => ⟨fun u hu => h u (by omega), h t (by omega)⟩
  · intro h u hu
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu) with hu | rfl
    · exact h.1 u hu
    · exact h.2

omit [∀ t, MeasurableSpace (Ω t)] [MeasurableSpace (Option α)]
  [MeasurableSingletonClass (Option α)] in
theorem reach_antitone : Antitone (reach answer) := by
  intro s t hst ω hω u hu
  exact hω u (hu.trans_le hst)

include hanswer in
/-- Independence is supplied by the explicitly constructed product measure. -/
theorem measure_reach (t : ℕ) :
    law P (reach answer t) = ∏ u ∈ Finset.range t, P u {x | answer u x = none} := by
  have he : reach answer t = Set.pi (Finset.range t) (fun u => {x | answer u x = none}) := by
    ext ω
    simp [reach, Set.mem_pi]
  rw [he, law, Measure.infinitePi_pi P]
  exact fun u _ => (hanswer u).eq_const none |>.setOf

include hanswer in
theorem measure_reach_succ (t : ℕ) :
    law P (reach answer (t + 1)) =
      law P (reach answer t) * P t {x | answer t x = none} := by
  rw [measure_reach P answer hanswer, measure_reach P answer hanswer, Finset.prod_range_succ]

include hanswer in
theorem measure_reach_le_pow {r : ℝ≥0∞}
    (habort : ∀ t, P t {x | answer t x = none} ≤ r) (t : ℕ) :
    law P (reach answer t) ≤ r ^ t := by
  apply geometric_reach_bound (law P) (reach answer) r
  intro u
  rw [measure_reach_succ P answer hanswer]
  exact (mul_le_mul' le_rfl (habort u)).trans_eq (mul_comm _ _)

omit [∀ t, MeasurableSpace (Ω t)] [MeasurableSpace (Option α)]
  [MeasurableSingletonClass (Option α)] in
theorem first_answer {ω : Tape Ω} (hω : ω ∈ terminates answer) :
    ∃ t a, ω ∈ reach answer t ∧ answer t (ω t) = some a := by
  let t := Nat.find hω
  have ht : answer t (ω t) ≠ none := Nat.find_spec hω
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp ht
  refine ⟨t, a, ?_, ha⟩
  intro u hu
  exact not_not.mp (Nat.find_min hω hu)

omit [∀ t, MeasurableSpace (Ω t)] [MeasurableSpace (Option α)]
  [MeasurableSingletonClass (Option α)] in
theorem return_unique {a b : α} {ω : Tape Ω}
    (ha : ω ∈ returned answer a) (hb : ω ∈ returned answer b) : a = b := by
  obtain ⟨s, hs, ha⟩ := ha
  obtain ⟨t, ht, hb⟩ := hb
  rcases lt_trichotomy s t with hst | rfl | hts
  · have he := ht s hst
    simp [ha] at he
  · exact Option.some.inj (ha.symm.trans hb)
  · have he := hs t hts
    simp [hb] at he

omit [∀ t, MeasurableSpace (Ω t)] [MeasurableSpace (Option α)]
  [MeasurableSingletonClass (Option α)] in
theorem terminates_eq_returned_union_incorrect (a : α) :
    terminates answer = returned answer a ∪ incorrect answer a := by
  ext ω
  constructor
  · intro hω
    obtain ⟨t, b, ht, hb⟩ := first_answer answer hω
    by_cases hba : b = a
    · exact Or.inl ⟨t, ht, hba ▸ hb⟩
    · exact Or.inr ⟨t, ht, by simp [hb], by simpa [hb] using hba⟩
  · rintro (⟨t, ht, ha⟩ | ⟨t, ht, hn, ha⟩)
    · exact ⟨t, by simp [ha]⟩
    · exact ⟨t, hn⟩

omit [∀ t, MeasurableSpace (Ω t)] [MeasurableSpace (Option α)]
  [MeasurableSingletonClass (Option α)] in
theorem incorrect_subset_union (a : α) :
    incorrect answer a ⊆ ⋃ t, {ω | answer t (ω t) ≠ none ∧ answer t (ω t) ≠ some a} := by
  rintro ω ⟨t, ht, hnone, ha⟩
  exact Set.mem_iUnion.mpr ⟨t, hnone, ha⟩

include hanswer in
/-- This union bound includes every incorrect return, even on atypical histories. -/
theorem measure_incorrect_le (a : α) (ε : ℕ → ℝ≥0∞)
    (hbad : ∀ t, P t {x | answer t x ≠ none ∧ answer t x ≠ some a} ≤ ε t) :
    law P (incorrect answer a) ≤ ∑' t, ε t := by
  apply (measure_mono (incorrect_subset_union answer a)).trans
  apply (measure_iUnion_le _).trans
  apply ENNReal.tsum_le_tsum
  intro t
  have hm := measurePreserving_eval_infinitePi P t
  have hset : MeasurableSet {x | answer t x ≠ none ∧ answer t x ≠ some a} :=
    ((hanswer t).eq_const none).not.and ((hanswer t).eq_const (some a)).not |>.setOf
  change Measure.infinitePi P ((fun ω => ω t) ⁻¹' {x | answer t x ≠ none ∧ answer t x ≠ some a}) ≤ ε t
  rw [hm.measure_preimage hset.nullMeasurableSet]
  exact hbad t


include hanswer in
/-- A uniform abort probability below one forces the actual infinite stream to
answer almost surely. This is independent of any sample-cost integrability. -/
theorem almostSurely_terminates {r : ℝ≥0∞} (hr : r < 1)
    (habort : ∀ t, P t {x | answer t x = none} ≤ r) :
    ∀ᵐ ω ∂law P, ω ∈ terminates answer := by
  rw [ae_iff]
  apply le_antisymm _ zero_le
  have hb : ∀ t, law P {ω | ω ∉ terminates answer} ≤ r ^ t := by
    intro t
    apply (measure_mono ?_).trans (measure_reach_le_pow P answer hanswer habort t)
    intro ω hω u hu
    by_contra hne
    exact hω ⟨u, hne⟩
  exact le_of_tendsto_of_tendsto tendsto_const_nhds
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr) (Filter.Eventually.of_forall hb)

include hanswer in
theorem measure_terminates_eq_one {r : ℝ≥0∞} (hr : r < 1)
    (habort : ∀ t, P t {x | answer t x = none} ≤ r) :
    law P (terminates answer) = 1 := by
  have h := (ae_iff_measure_eq (measurableSet_terminates answer hanswer).nullMeasurableSet).mp
    (almostSurely_terminates P answer hanswer hr habort)
  simpa only [measure_univ, terminates] using h

include hanswer in
/-- Source C.3's exact stream error budget, summed over all fresh attempts. -/
theorem measure_incorrect_le_retryConfidence (a : α) {δ : ℝ} (hδ : 0 < δ)
    (hbad : ∀ t, P t {x | answer t x ≠ none ∧ answer t x ≠ some a} ≤
      ENNReal.ofReal (retryConfidence δ t)) :
    law P (incorrect answer a) ≤ ENNReal.ofReal (δ / 2) := by
  apply (measure_incorrect_le P answer hanswer a _ hbad).trans_eq
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun t => (retryConfidence_pos hδ t).le)
    (hasSum_retryConfidence δ).summable, sum_retryConfidence]

/-- Every attempted cost is charged on its reach event, including aborts and errors. -/
def chargedCost (cost : ∀ t, Ω t → ℝ≥0∞) (t : ℕ) (ω : Tape Ω) : ℝ≥0∞ :=
  (reach answer t).indicator (fun ω => cost t (ω t)) ω

include hanswer in
theorem measurable_chargedCost (cost : ∀ t, Ω t → ℝ≥0∞)
    (hcost : ∀ t, Measurable (cost t)) (t : ℕ) : Measurable (chargedCost answer cost t) :=
  ((hcost t).comp (measurable_pi_apply t)).indicator (measurableSet_reach answer hanswer t)

include hanswer in
theorem expected_cost_le_caps (cost : ∀ t, Ω t → ℝ≥0∞)
    (hcost : ∀ t, Measurable (cost t)) (cap : ℕ → ℝ≥0∞)
    (hcap : ∀ t x, cost t x ≤ cap t) :
    (∫⁻ ω, ∑' t, chargedCost answer cost t ω ∂law P) ≤
      ∑' t, cap t * ∏ u ∈ Finset.range t, P u {x | answer u x = none} := by
  simpa only [measure_reach P answer hanswer] using
    expected_attempt_cost_le (law P) (reach answer) (measurableSet_reach answer hanswer)
      (chargedCost answer cost) (measurable_chargedCost answer hanswer cost hcost) cap
      (fun t ω hω => Set.indicator_of_notMem hω _)
      (fun t ω hω => by simpa only [chargedCost, Set.indicator_of_mem hω] using hcap t (ω t))

include hanswer in
theorem expected_cost_le_geometric (cost : ∀ t, Ω t → ℝ≥0∞)
    (hcost : ∀ t, Measurable (cost t)) {C A B : ℝ}
    (hC : 0 ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hcap : ∀ t x, cost t x ≤ ENNReal.ofReal (C * (A + (t + 2) * B)))
    (habort : ∀ t, P t {x | answer t x = none} ≤ 1 / 2) :
    (∫⁻ ω, ∑' t, chargedCost answer cost t ω ∂law P) ≤
      ENNReal.ofReal (C * (2 * A + 6 * B)) := by
  apply expected_retry_cost_le (law P) (reach answer) (measurableSet_reach answer hanswer)
    (chargedCost answer cost) (measurable_chargedCost answer hanswer cost hcost) hC hA hB
    (fun t ω hω => Set.indicator_of_notMem hω _)
    (fun t ω hω => by simpa only [chargedCost, Set.indicator_of_mem hω] using hcap t (ω t))
  intro t
  convert measure_reach_le_pow P answer hanswer habort t using 1
  rw [ENNReal.ofReal_pow (by positivity)]
  congr 1
  simp

end GapEntropy.RetryExperiment
