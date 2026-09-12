import GapEntropy.BoundedProcedure
import GapEntropy.BlockSchedule

/-!
# An actual stream of deterministic-budget attempts

Each attempt reads only its own observations and returns `none` (abort) or a label.
The stream detects the preceding attempt's answer at the next block boundary;
otherwise it immediately requests the next attempt's sample. Internal readout and
restart computation cost no observations. Positive budgets ensure that the
infinite stream always has a next sample position.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace GapEntropy.FixedCapRetry

variable {n : ℕ} (R : ℕ → BoundedProcedure n (Option (Fin n)))
  (hpos : ∀ j, 0 < (R j).budget)

def schedule : BlockSchedule := ⟨fun j => (R j).budget, hpos⟩

def segment {t : ℕ} (h : History n t) (a m : ℕ) (ham : a + m ≤ t) : History n m :=
  fun i => h ⟨a + i, by have := i.isLt; omega⟩

theorem measurable_segment (t a m : ℕ) (ham : a + m ≤ t) :
    Measurable (fun h : History n t => segment h a m ham) :=
  measurable_pi_lambda _ (fun _i => measurable_pi_apply _)

def currentIndex (t : ℕ) : ℕ := (schedule R hpos).index t

def offset (t : ℕ) : ℕ := t - (schedule R hpos).start (currentIndex R hpos t)

theorem start_add_offset (t : ℕ) :
    (schedule R hpos).start (currentIndex R hpos t) + offset R hpos t = t :=
  Nat.add_sub_of_le ((schedule R hpos).start_index_le t)

theorem offset_lt_budget (t : ℕ) : offset R hpos t < (R (currentIndex R hpos t)).budget :=
  (schedule R hpos).offset_lt_size t

def currentHistory {t : ℕ} (h : History n t) : History n (offset R hpos t) :=
  segment h ((schedule R hpos).start (currentIndex R hpos t)) (offset R hpos t)
    (le_of_eq (start_add_offset R hpos t))

def currentRequest (t : ℕ) (h : History n t) : Fin n :=
  (R (currentIndex R hpos t)).request (offset R hpos t) (offset_lt_budget R hpos t)
    (currentHistory R hpos h)

theorem measurable_currentRequest (t : ℕ) : Measurable (currentRequest R hpos t) :=
  ((R (currentIndex R hpos t)).measurable_request _ _).comp
    (measurable_segment _ _ _ _)

theorem previous_end_le (t : ℕ) (hj : 0 < currentIndex R hpos t) :
    (schedule R hpos).start (currentIndex R hpos t - 1) +
      (R (currentIndex R hpos t - 1)).budget ≤ t := by
  have he : currentIndex R hpos t - 1 + 1 = currentIndex R hpos t := by omega
  have h := (schedule R hpos).start_index_le t
  change (schedule R hpos).start (currentIndex R hpos t) ≤ t at h
  rw [← he, (schedule R hpos).start_succ] at h
  exact h

def previousOutput (t : ℕ) (hj : 0 < currentIndex R hpos t) (h : History n t) :
    Option (Fin n) :=
  (R (currentIndex R hpos t - 1)).output
    (segment h ((schedule R hpos).start (currentIndex R hpos t - 1))
      (R (currentIndex R hpos t - 1)).budget (previous_end_le R hpos t hj))

def pendingOutput (t : ℕ) (h : History n t) : Option (Fin n) :=
  if hj : 0 < currentIndex R hpos t then previousOutput R hpos t hj h else none

theorem measurable_previousOutput (t : ℕ) (hj : 0 < currentIndex R hpos t) :
    Measurable (previousOutput R hpos t hj) :=
  (R (currentIndex R hpos t - 1)).measurable_output.comp (measurable_segment _ _ _ _)

theorem measurable_pendingOutput (t : ℕ) : Measurable (pendingOutput R hpos t) := by
  change Measurable (fun h : History n t =>
    if hj : 0 < currentIndex R hpos t then previousOutput R hpos t hj h else none)
  by_cases hj : 0 < currentIndex R hpos t
  · simpa only [dif_pos hj] using measurable_previousOutput R hpos t hj
  · simp only [dif_neg hj]
    exact measurable_const

/-- No completion-marker label from a subroutine is used as the stream's answer. -/
def policy : Policy n where
  choose _ t p := (pendingOutput R hpos t p.2).elim
    (.inl (currentRequest R hpos t p.2)) Sum.inr
  measurable_choose _ t := by
    have hf : Measurable (fun p : History n t × Option (Fin n) =>
        p.2.elim (.inl (currentRequest R hpos t p.1)) (Sum.inr : Fin n → Decision n)) := by
      apply measurable_from_prod_countable_left
      intro a
      cases a with
      | none => exact measurable_inl.comp (measurable_currentRequest R hpos t)
      | some i => exact measurable_const
    exact hf.comp (measurable_snd.prodMk
      ((measurable_pendingOutput R hpos t).comp measurable_snd))

theorem choose_sample_imp (hn : 2 ≤ n) (t : ℕ) (z : Seed) (h : History n t) (i : Fin n)
    (hc : (policy R hpos).choose hn t (z, h) = Sum.inl i) :
    pendingOutput R hpos t h = none ∧ currentRequest R hpos t h = i := by
  change (pendingOutput R hpos t h).elim (.inl (currentRequest R hpos t h)) Sum.inr = _ at hc
  cases hp : pendingOutput R hpos t h with
  | none => exact ⟨rfl, by simpa only [hp, Option.elim_none, Sum.inl.injEq] using hc⟩
  | some a => simp only [hp, Option.elim_some, reduceCtorEq] at hc

theorem choose_return_imp (hn : 2 ≤ n) (t : ℕ) (z : Seed) (h : History n t) (i : Fin n)
    (hc : (policy R hpos).choose hn t (z, h) = Sum.inr i) :
    pendingOutput R hpos t h = some i := by
  change (pendingOutput R hpos t h).elim (.inl (currentRequest R hpos t h)) Sum.inr = _ at hc
  cases hp : pendingOutput R hpos t h with
  | none => simp only [hp, Option.elim_none, reduceCtorEq] at hc
  | some a => simpa only [hp, Option.elim_some, Sum.inr.injEq, Option.some.injEq] using hc

/-- The complete private reward table for every attempt, including those never reached. -/
def blocks (ω : SampleSpace n) : ∀ j, (R j).Tape := (schedule R hpos).blocks ω

def answer (j : ℕ) (ω : SampleSpace n) : Option (Fin n) := (R j).evaluate (blocks R hpos ω j)

theorem measurable_answer (j : ℕ) : Measurable (answer R hpos j) :=
  (R j).measurable_evaluate.comp
    ((measurable_pi_apply j).comp ((schedule R hpos).measurable_blocks n))

end GapEntropy.FixedCapRetry
