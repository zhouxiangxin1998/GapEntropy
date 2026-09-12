import GapEntropy.ReturnedCounts
import GapEntropy.Freshness
import GapEntropy.HistoryConsistency

/-!
# The actual alternating policy and its private sample tapes

At even global steps the first policy receives the even-indexed observations;
at odd steps the second policy receives the odd-indexed observations. Their seed
coordinates are split in the same way. This construction sees only the global
observed history, and each extracted private tape has the original Gaussian law.

The run-simulation, correctness and expected-cost comparison theorems are further
obligations; defining this policy and preserving tape laws alone do not establish
the globalization theorem in C.3.
-/

open MeasureTheory ProbabilityTheory

namespace GapEntropy.Interleave

def seedPart (e : Fin 2) (z : Seed) : Seed := fun k => z (2 * k + e)

def samplePart {n : ℕ} (e : Fin 2) (ω : SampleSpace n) : SampleSpace n :=
  (seedPart e ω.1, fun k => ω.2 (2 * k + e))

theorem measurable_seedPart (e : Fin 2) : Measurable (seedPart e) := by
  exact measurable_pi_lambda _ (fun k => measurable_pi_apply _)

theorem measurable_samplePart {n : ℕ} (e : Fin 2) : Measurable (samplePart (n := n) e) := by
  exact ((measurable_seedPart e).comp measurable_fst).prodMk
    (measurable_pi_lambda _ (fun k => (measurable_pi_apply _).comp measurable_snd))

theorem measurePreserving_seedPart (e : Fin 2) : MeasurePreserving (seedPart e) seedLaw seedLaw := by
  refine ⟨measurable_seedPart e, ?_⟩
  exact Measure.map_infinitePi_infinitePi_of_inj (fun i j h => by omega)

theorem measurePreserving_samplePart {n : ℕ} (mean : Fin n → ℝ) (e : Fin 2) :
    MeasurePreserving (samplePart e) (sampleLawOfMeans mean) (sampleLawOfMeans mean) := by
  have hr : MeasurePreserving (fun r : ℕ → Fin n → ℝ => fun k => r (2 * k + e))
      (rewardLaw mean) (rewardLaw mean) :=
    ⟨measurable_pi_lambda _ (fun k => measurable_pi_apply _),
      Measure.map_infinitePi_infinitePi_of_inj (fun i j h => by omega)⟩
  exact (measurePreserving_seedPart e).prod hr

def evenHistory {n t : ℕ} (h : History n t) : History n ((t + 1) / 2) :=
  fun j => h ⟨2 * j, by have := j.isLt; omega⟩

def oddHistory {n t : ℕ} (h : History n t) : History n (t / 2) :=
  fun j => h ⟨2 * j + 1, by have := j.isLt; omega⟩

theorem measurable_evenHistory (n t : ℕ) : Measurable (evenHistory (n := n) (t := t)) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

theorem measurable_oddHistory (n t : ℕ) : Measurable (oddHistory (n := n) (t := t)) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

/-- One requested sample from each stream alternately. A return by the stream
whose turn is next returns from the combined policy immediately. -/
def policy {n : ℕ} (A B : Policy n) : Policy n where
  choose hn t p :=
    if t % 2 = 0 then A.choose hn ((t + 1) / 2) (seedPart 0 p.1, evenHistory p.2)
    else B.choose hn (t / 2) (seedPart 1 p.1, oddHistory p.2)
  measurable_choose hn t := by
    by_cases ht : t % 2 = 0
    · simp only [if_pos ht]
      exact (A.measurable_choose hn _).comp
        (((measurable_seedPart 0).comp measurable_fst).prodMk
          ((measurable_evenHistory n t).comp measurable_snd))
    · simp only [if_neg ht]
      exact (B.measurable_choose hn _).comp
        (((measurable_seedPart 1).comp measurable_fst).prodMk
          ((measurable_oddHistory n t).comp measurable_snd))

@[simp] theorem policy_choose_even {n : ℕ} (A B : Policy n) (hn : 2 ≤ n)
    (t : ℕ) (p : Seed × History n (2 * t)) :
    (policy A B).choose hn (2 * t) p =
      A.choose hn ((2 * t + 1) / 2) (seedPart 0 p.1, evenHistory p.2) := by
  simp [policy]

@[simp] theorem policy_choose_odd {n : ℕ} (A B : Policy n) (hn : 2 ≤ n)
    (t : ℕ) (p : Seed × History n (2 * t + 1)) :
    (policy A B).choose hn (2 * t + 1) p =
      B.choose hn ((2 * t + 1) / 2) (seedPart 1 p.1, oddHistory p.2) := by
  simp [policy]

theorem consistent_evenHistory {n : ℕ} (A B : Policy n) (hn : 2 ≤ n)
    (ω : SampleSpace n) (t : ℕ) (h : History n t)
    (hc : (policy A B).historyConsistent hn ω t h) :
    A.historyConsistent hn (samplePart 0 ω) ((t + 1) / 2) (evenHistory h) := by
  apply A.historyConsistent_of_decisions
  intro s hs
  have hst : 2 * s < t := by omega
  have hd := (policy A B).historyConsistent_decision hn ω h hc (2 * s) hst
  have hdiv : (2 * s + 1) / 2 = s := by omega
  simp only [policy, Nat.mul_mod, Nat.mod_self, zero_mul, Nat.zero_mod, if_true] at hd
  have heq := A.choose_congr_history hn hdiv (seedPart 0 ω.1)
    (evenHistory (Policy.historyPrefix h (2 * s) hst.le))
    (Policy.historyPrefix (evenHistory h) s hs.le) (fun i => rfl)
  exact ⟨heq.symm.trans hd.1, hd.2⟩

theorem consistent_oddHistory {n : ℕ} (A B : Policy n) (hn : 2 ≤ n)
    (ω : SampleSpace n) (t : ℕ) (h : History n t)
    (hc : (policy A B).historyConsistent hn ω t h) :
    B.historyConsistent hn (samplePart 1 ω) (t / 2) (oddHistory h) := by
  apply B.historyConsistent_of_decisions
  intro s hs
  have hst : 2 * s + 1 < t := by omega
  have hd := (policy A B).historyConsistent_decision hn ω h hc (2 * s + 1) hst
  have hdiv : (2 * s + 1) / 2 = s := by omega
  have hmod : (2 * s + 1) % 2 ≠ 0 := by omega
  simp only [policy, if_neg hmod] at hd
  have heq := B.choose_congr_history hn hdiv (seedPart 1 ω.1)
    (oddHistory (Policy.historyPrefix h (2 * s + 1) hst.le))
    (Policy.historyPrefix (oddHistory h) s hs.le) (fun i => rfl)
  exact ⟨heq.symm.trans hd.1, hd.2⟩

/-- While the combined policy is active, its two extracted histories are the
actual runs of the component policies on their private Gaussian tapes. -/
theorem active_component_runs {n : ℕ} (A B : Policy n) (hn : 2 ≤ n)
    (ω : SampleSpace n) (t : ℕ) (h : History n t)
    (hr : (policy A B).run hn ω t = Sum.inr h) :
    A.run hn (samplePart 0 ω) ((t + 1) / 2) = Sum.inr (evenHistory h) ∧
      B.run hn (samplePart 1 ω) (t / 2) = Sum.inr (oddHistory h) := by
  have hc := ((policy A B).run_eq_active_iff_historyConsistent hn ω t h).1 hr
  exact ⟨(A.run_eq_active_iff_historyConsistent hn _ _ _).2
      (consistent_evenHistory A B hn ω t h hc),
    (B.run_eq_active_iff_historyConsistent hn _ _ _).2
      (consistent_oddHistory A B hn ω t h hc)⟩

end GapEntropy.Interleave
