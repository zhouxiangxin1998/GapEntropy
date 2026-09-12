import GapEntropy.UniversalTerminalTrace
import GapEntropy.UniversalCallEquivalence
import GapEntropy.UniversalCallTrace

/-! The terminal trajectory's observed estimates are the actual scheduled reward means. -/
noncomputable section
open scoped Classical
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram UniversalCall
variable {n : ℕ}

def shiftedSample (m : ℕ) (ω : SampleSpace n) : SampleSpace n := (ω.1, shiftValues m ω.2)

theorem rewardBlock_shiftedSample (m b : ℕ) (ω : SampleSpace n) :
    GaussianBlocks.rewardBlock 0 b (shiftedSample m ω) = firstBlock b (shiftValues m ω.2) := by
  funext j
  simp only [GaussianBlocks.rewardBlock, shiftedSample, firstBlock, Nat.zero_add]

theorem scheduleEstimate_shiftedSample (S : Finset (Fin n)) (m start b : ℕ)
    (ω : SampleSpace n) (i : Fin n) :
    scheduleEstimate S start b (shiftedSample m ω) i = scheduleEstimate S (m + start) b ω i := by
  unfold scheduleEstimate Gaussian.sampleMean MedianPolicy.fixedObservation shiftedSample shiftValues
  simp only [Nat.add_assoc]

/-- Current-call offset, including all PAC and reference observations at entry. -/
def observedActiveOffset (c : Config) (a : Metadata n) : ℕ :=
  if a.entry then activeStart a.active.card a.tolerance (a.alpha c) (a.beta c) else 0

theorem callObservedEstimates_eq_schedule (c : Config) (ω : SampleSpace n)
    (a : Metadata n) (ha : a.Allowed c) (z : ℝ) (i : Fin n) (hi : i ∈ a.active) :
    callObservedEstimates c ω.2 a ha z i =
      scheduleEstimate a.active (a.samples + observedActiveOffset c a)
        (EliminationTape.activeSamples a.tolerance (a.alpha c)) ω i := by
  let ω' := shiftedSample a.samples ω
  have hblock := rewardBlock_shiftedSample a.samples (a.call c).samples ω
  have hS : a.active.Nonempty := Finset.card_pos.mp (by have := ha.1; omega)
  have hlocal : callObservedEstimates c ω.2 a ha z i =
      scheduleEstimate a.active (observedActiveOffset c a)
        (EliminationTape.activeSamples a.tolerance (a.alpha c)) ω' i := by
    unfold callObservedEstimates callObservedHistory
    rw [← hblock]
    rcases a with ⟨S, k, entry, w, q⟩
    cases entry with
    | false =>
        change estimateFromHistory S 0 _
          ((carryReference (laterProcedure S hS _ _ z) z).simulate _ _ le_rfl) i = _
        let R := laterProcedure S hS (Metadata.tolerance (S, k, false, w, q))
          (Metadata.alpha c (S, k, false, w, q)) z
        have he := carryReference_simulate R z (GaussianBlocks.rewardBlock 0 R.budget ω')
          R.budget le_rfl
        exact (congrArg (fun H => estimateFromHistory S 0
          (EliminationTape.activeSamples (Metadata.tolerance (S, k, false, w, q))
            (Metadata.alpha c (S, k, false, w, q))) H i) he).trans
          (laterEstimate_eq_schedule S hS _ _ z ω' i hi)
    | true =>
        exact entryEstimate_eq_schedule S hS _ _ _ ω' i hi
  exact hlocal.trans (scheduleEstimate_shiftedSample a.active a.samples
    (observedActiveOffset c a) _ ω i)

end GapEntropy.UniversalAttempt
