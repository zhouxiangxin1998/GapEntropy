import GapEntropy.Model
import GapEntropy.BinaryTesting

/-!
# Absorbing return events

Returned labels persist, so a finite return different from a specified label is
disjoint from ever returning that label. The increasing finite-horizon events
recover the full event, without an almost-sure termination assumption.
-/

open MeasureTheory
open scoped ENNReal Classical

namespace GapEntropy.Policy

variable {n : ℕ} (A : Policy n)

@[simp] theorem returnedAt_eq_some_iff (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n)
    (i : Fin n) : A.returnedAt hn t ω = some i ↔ A.run hn ω t = Sum.inl i := by
  unfold returnedAt
  cases A.run hn ω t <;> simp

theorem run_return_persists (hn : 2 ≤ n) {s t : ℕ} (hst : s ≤ t)
    (ω : SampleSpace n) (i : Fin n) (hs : A.run hn ω s = Sum.inl i) :
    A.run hn ω t = Sum.inl i := by
  induction t, hst using Nat.le_induction with
  | base => exact hs
  | succ t _ ih => simp [run, step, ih]

theorem returnedAt_persists (hn : 2 ≤ n) {s t : ℕ} (hst : s ≤ t)
    (ω : SampleSpace n) (i : Fin n) (hs : A.returnedAt hn s ω = some i) :
    A.returnedAt hn t ω = some i :=
  (A.returnedAt_eq_some_iff hn t ω i).2
    (A.run_return_persists hn hst ω i ((A.returnedAt_eq_some_iff hn s ω i).1 hs))

theorem returnedAt_unique (hn : 2 ≤ n) {s t : ℕ} (ω : SampleSpace n) {i j : Fin n}
    (hi : A.returnedAt hn s ω = some i) (hj : A.returnedAt hn t ω = some j) : i = j := by
  rcases le_total s t with h | h
  · exact Option.some.inj ((A.returnedAt_persists hn h ω i hi).symm.trans hj)
  · exact Option.some.inj (hi.symm.trans (A.returnedAt_persists hn h ω j hj))

def returnedNotAt (hn : 2 ≤ n) (tag : Fin n) (t : ℕ) : Set (SampleSpace n) :=
  {ω | ∃ i, i ≠ tag ∧ A.returnedAt hn t ω = some i}

def returnedNotEvent (hn : 2 ≤ n) (tag : Fin n) : Set (SampleSpace n) :=
  {ω | ∃ t, ω ∈ A.returnedNotAt hn tag t}

theorem measurableSet_returnedNotAt (hn : 2 ≤ n) (tag : Fin n) (t : ℕ) :
    MeasurableSet (A.returnedNotAt hn tag t) := by
  exact (Measurable.exists fun i =>
    measurable_const.and ((A.measurable_returnedAt hn t).eq_const (some i))).setOf

theorem measurableSet_returnedNotEvent (hn : 2 ≤ n) (tag : Fin n) :
    MeasurableSet (A.returnedNotEvent hn tag) := by
  have h := MeasurableSet.iUnion (A.measurableSet_returnedNotAt hn tag)
  convert h using 1
  ext ω
  simp [returnedNotEvent]

theorem returnedNotAt_mono (hn : 2 ≤ n) (tag : Fin n) :
    Monotone (A.returnedNotAt hn tag) := by
  intro s t hst ω hω
  obtain ⟨i, hi, hret⟩ := hω
  exact ⟨i, hi, A.returnedAt_persists hn hst ω i hret⟩

theorem returnedNotEvent_eq_iUnion (hn : 2 ≤ n) (tag : Fin n) :
    A.returnedNotEvent hn tag = ⋃ t, A.returnedNotAt hn tag t := by
  ext ω
  simp [returnedNotEvent]

theorem measure_returnedNotEvent_eq_iSup (hn : 2 ≤ n) (tag : Fin n)
    (μ : Measure (SampleSpace n)) :
    μ (A.returnedNotEvent hn tag) = ⨆ t, μ (A.returnedNotAt hn tag t) := by
  rw [A.returnedNotEvent_eq_iUnion]
  exact (A.returnedNotAt_mono hn tag).measure_iUnion

theorem measure_returnedNotEvent_le_of_finite (hn : 2 ≤ n) (tag : Fin n)
    (μ : Measure (SampleSpace n)) (q : ℝ≥0∞)
    (h : ∀ t, μ (A.returnedNotAt hn tag t) ≤ q) : μ (A.returnedNotEvent hn tag) ≤ q := by
  rw [A.measure_returnedNotEvent_eq_iSup]
  exact iSup_le h

theorem returnedNotEvent_subset_success_compl (I : Instance n) :
    A.returnedNotEvent I.two_le I.best ⊆ (A.successEvent I)ᶜ := by
  rintro ω ⟨t, i, hi, hret⟩ ⟨s, hs⟩
  exact hi (A.returnedAt_unique I.two_le ω hret hs)

theorem returnedNotEvent_real_le_of_correct (I : Instance n) {δ : ℝ}
    (hδ : δ ≤ 1) (hcorrect : ENNReal.ofReal (1 - δ) ≤ A.successProb I) :
    (sampleLaw I).real (A.returnedNotEvent I.two_le I.best) ≤ δ := by
  have hc : 1 - δ ≤ (sampleLaw I).real (A.successEvent I) := by
    have h := ENNReal.toReal_mono (measure_ne_top _ _) hcorrect
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.2 hδ), successProb, measureReal_def] using h
  have hm := measureReal_mono (μ := sampleLaw I) (A.returnedNotEvent_subset_success_compl I)
  rw [probReal_compl_eq_one_sub (A.measurableSet_successEvent I)] at hm
  linarith

theorem returnedNotEvent_measure_le_of_correct (I : Instance n) {δ : ℝ}
    (hδ : δ ≤ 1) (hcorrect : ENNReal.ofReal (1 - δ) ≤ A.successProb I) :
    sampleLaw I (A.returnedNotEvent I.two_le I.best) ≤ ENNReal.ofReal δ := by
  rw [← ENNReal.ofReal_toReal (measure_ne_top (sampleLaw I) _)]
  exact ENNReal.ofReal_le_ofReal (A.returnedNotEvent_real_le_of_correct I hδ hcorrect)

theorem returnedNotAt_measure_le_of_correct (I : Instance n) {δ : ℝ}
    (hδ : δ ≤ 1) (hcorrect : ENNReal.ofReal (1 - δ) ≤ A.successProb I) (t : ℕ) :
      sampleLaw I (A.returnedNotAt I.two_le I.best t) ≤ ENNReal.ofReal δ := by
  have hs : A.returnedNotAt I.two_le I.best t ⊆ A.returnedNotEvent I.two_le I.best :=
    fun _ h => ⟨t, h⟩
  exact (measure_mono hs).trans (A.returnedNotEvent_measure_le_of_correct I hδ hcorrect)

end GapEntropy.Policy
