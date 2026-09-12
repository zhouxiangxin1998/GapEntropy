import GapEntropy.EliminationProcedure

/-!
# Actual bounded calls for the universal algorithm

A scale-entry call selects a PAC reference, independently estimates its mean
with the separate confidence parameter β, and samples the active arms. Later
calls reuse the numerical reference z and sample only active arms.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators Classical
namespace GapEntropy.UniversalCall
open EliminationTape
variable {n : ℕ}

def referenceBudget (d β : ℝ) : ℕ := ⌈512 * (d ^ 2)⁻¹ * Real.log (2 / β)⌉₊
abbrev medianBudget := EliminationPolicy.medianBudget

def activeStart (s : ℕ) (d α β : ℝ) : ℕ := medianBudget s d α + referenceBudget d β

def laterBudget (s : ℕ) (d α : ℝ) : ℕ := s * activeSamples d α

def entryBudget (s : ℕ) (d α β : ℝ) : ℕ := activeStart s d α β + laterBudget s d α

/-- The separate reference error allocation in (D.6). -/
def referenceError (δ : ℝ) (j k : ℕ) : ℝ :=
  δ / (64 * ((j : ℝ) + 1) ^ 2 * ((k : ℝ) + 1) ^ 2)

theorem referenceBudget_pos {d β : ℝ} (hd : 0 < d) (hβ : 0 < β) (hβ1 : β ≤ 1) :
    0 < referenceBudget d β := by
  apply Nat.one_le_ceil_iff.mpr
  have hl : 0 < Real.log (2 / β) := Real.log_pos ((lt_div_iff₀ hβ).mpr (by linarith))
  positivity

theorem medianBudget_le_entryBudget (s : ℕ) (d α β : ℝ) :
    medianBudget s d α ≤ entryBudget s d α β := by unfold entryBudget activeStart; omega

abbrev referenceFromHistory := @EliminationPolicy.referenceFromHistory

def entryRequest (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (t : ℕ) (h : History n t) : Fin n :=
  if ht : t < medianBudget S.card d α then
    MedianPolicy.requestedFromHistory S hS (d / 8) (α / 16) t ht h
  else if t < activeStart S.card d α β then referenceFromHistory S hS d α h
  else MedianPolicy.armAt (S.min' hS) S
    ((t - activeStart S.card d α β) / activeSamples d α)

def laterRequest (S : Finset (Fin n)) (hS : S.Nonempty) (d α : ℝ)
    (t : ℕ) (_h : History n t) : Fin n :=
  MedianPolicy.armAt (S.min' hS) S (t / activeSamples d α)

theorem measurable_entryRequest (S : Finset (Fin n)) (hS : S.Nonempty)
    (d α β : ℝ) (t : ℕ) : Measurable (entryRequest S hS d α β t) := by
  unfold entryRequest
  split_ifs with ht ht'
  · exact MedianPolicy.measurable_requestedFromHistory S hS _ _ t ht
  · exact EliminationPolicy.measurable_referenceFromHistory S hS d α
  · exact measurable_const

def estimateFromHistory {t : ℕ} (S : Finset (Fin n)) (start m : ℕ)
    (h : History n t) (i : Fin n) : ℝ :=
  (∑ j : Fin m, MedianPolicy.historyValues h (start + MedianPolicy.armRank S i * m + j)) / (m : ℝ)

def referenceEstimateFromHistory {t : ℕ} (S : Finset (Fin n)) (d α β : ℝ)
    (h : History n t) : ℝ :=
  (∑ j : Fin (referenceBudget d β),
    MedianPolicy.historyValues h (medianBudget S.card d α + j)) / (referenceBudget d β : ℝ)

theorem measurable_estimateFromHistory {t : ℕ} (S : Finset (Fin n)) (start m : ℕ)
    (i : Fin n) : Measurable (fun h : History n t => estimateFromHistory S start m h i) := by
  unfold estimateFromHistory
  exact (Finset.measurable_fun_sum _ (fun j _ => MedianPolicy.measurable_historyValues _)).div_const _

theorem measurable_referenceEstimateFromHistory {t : ℕ} (S : Finset (Fin n)) (d α β : ℝ) :
    Measurable (referenceEstimateFromHistory (t := t) S d α β) := by
  unfold referenceEstimateFromHistory
  exact (Finset.measurable_fun_sum _ (fun j _ => MedianPolicy.measurable_historyValues _)).div_const _

def laterReadout {t : ℕ} (S : Finset (Fin n)) (d α z : ℝ) (h : History n t) : Finset (Fin n) :=
  Elimination.padded S (estimateFromHistory S 0 (activeSamples d α) h) z d

def entryReadout {t : ℕ} (S : Finset (Fin n)) (d α β : ℝ) (h : History n t) :
    ℝ × Finset (Fin n) :=
  let z := referenceEstimateFromHistory S d α β h
  (z, Elimination.padded S
    (estimateFromHistory S (activeStart S.card d α β) (activeSamples d α) h) z d)

/-- Joint measurability includes the retained real-valued reference parameter. -/
theorem measurable_laterReadout {t : ℕ} (S : Finset (Fin n)) (d α : ℝ) :
    Measurable (fun p : ℝ × History n t => laterReadout S d α p.1 p.2) :=
  SortingMeasurability.padded_measurable measurable_const
    (fun i => (measurable_estimateFromHistory S 0 (activeSamples d α) i).comp measurable_snd)
    measurable_fst measurable_const

theorem measurable_entryReadout {t : ℕ} (S : Finset (Fin n)) (d α β : ℝ) :
    Measurable (entryReadout (t := t) S d α β) :=
  (measurable_referenceEstimateFromHistory S d α β).prodMk
    (SortingMeasurability.padded_measurable measurable_const
      (measurable_estimateFromHistory S (activeStart S.card d α β) (activeSamples d α))
      (measurable_referenceEstimateFromHistory S d α β) measurable_const)

def entryProcedure (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ) :
    BoundedProcedure n (ℝ × Finset (Fin n)) where
  budget := entryBudget S.card d α β
  request t _ := entryRequest S hS d α β t
  measurable_request t _ := measurable_entryRequest S hS d α β t
  output := entryReadout S d α β
  measurable_output := measurable_entryReadout S d α β

def laterProcedure (S : Finset (Fin n)) (hS : S.Nonempty) (d α z : ℝ) :
    BoundedProcedure n (Finset (Fin n)) where
  budget := laterBudget S.card d α
  request t _ := laterRequest S hS d α t
  measurable_request _ _ := measurable_const
  output := laterReadout S d α z
  measurable_output := SortingMeasurability.padded_measurable measurable_const
    (measurable_estimateFromHistory S 0 (activeSamples d α)) measurable_const measurable_const

def completedHistory {γ : Type*} [MeasurableSpace γ] (R : BoundedProcedure n γ)
    (ω : SampleSpace n) : History n R.budget :=
  R.simulate (GaussianBlocks.rewardBlock 0 R.budget ω) R.budget le_rfl

theorem measurable_completedHistory {γ : Type*} [MeasurableSpace γ] (R : BoundedProcedure n γ) :
    Measurable (completedHistory R) :=
  (R.measurable_simulate R.budget le_rfl).comp (GaussianBlocks.measurable_rewardBlock 0 R.budget)

theorem entry_samples (S : Finset (Fin n)) (hS : S.Nonempty) (d α β : ℝ)
    (hn : 2 ≤ n) (ω : SampleSpace n) :
    (entryProcedure S hS d α β).samplingPolicy.sampleCount hn ω = entryBudget S.card d α β :=
  (entryProcedure S hS d α β).sampleCount_eq_budget hn ω

theorem later_samples (S : Finset (Fin n)) (hS : S.Nonempty) (d α z : ℝ)
    (hn : 2 ≤ n) (ω : SampleSpace n) :
    (laterProcedure S hS d α z).samplingPolicy.sampleCount hn ω = laterBudget S.card d α :=
  (laterProcedure S hS d α z).sampleCount_eq_budget hn ω

end GapEntropy.UniversalCall
