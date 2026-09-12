import GapEntropy.MedianTape
import GapEntropy.GaussianNoise
import GapEntropy.EliminationProbability

/-!
# Actual A.3 threshold and padded procedures on an independent Gaussian tape

The probability space is the product of a PAC tape, fresh reference noises, and
fresh active-arm noises. The reference observations are `μ(reference) + noise`;
the active observations are `μ(i) + noise`. This is a complete statistical
subroutine. An interactive `Policy` implementation remains a separate obligation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MeasureTheory.Measure

namespace GapEntropy.EliminationTape
open GapEntropy.MedianElimination GapEntropy.EliminationProbability

def referenceSamples (d α : ℝ) : ℕ := ⌈512 * (d ^ 2)⁻¹ * Real.log (32 / α)⌉₊
def activeSamples (d α : ℝ) : ℕ := ⌈512 * (d ^ 2)⁻¹ * Real.log (128 / α)⌉₊

theorem referenceSamples_pos {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) :
    0 < referenceSamples d α := by
  apply Nat.one_le_ceil_iff.mpr
  have hl : 0 < Real.log (32 / α) := Real.log_pos ((lt_div_iff₀ hα).mpr (by linarith))
  positivity

theorem activeSamples_pos {d α : ℝ} (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) :
    0 < activeSamples d α := by
  apply Nat.one_le_ceil_iff.mpr
  have hl : 0 < Real.log (128 / α) := Real.log_pos ((lt_div_iff₀ hα).mpr (by linarith))
  positivity

abbrev Tape (n : ℕ) (d α : ℝ) :=
  GapEntropy.MedianTape.Tape n (d / 8) (α / 16) ×
    ((Fin (referenceSamples d α) → ℝ) × (Fin n → Fin (activeSamples d α) → ℝ))

def activeLaw (n : ℕ) (d α : ℝ) : Measure (Fin n → Fin (activeSamples d α) → ℝ) :=
  infinitePi (fun _ => GapEntropy.GaussianNoise.law (activeSamples d α))

instance (n : ℕ) (d α : ℝ) : IsProbabilityMeasure (activeLaw n d α) := by
  unfold activeLaw
  infer_instance

def law {n : ℕ} (μ : Fin n → ℝ) (d α : ℝ) : Measure (Tape n d α) :=
  (GapEntropy.MedianTape.law μ (d / 8) (α / 16)).prod
    ((GapEntropy.GaussianNoise.law (referenceSamples d α)).prod (activeLaw n d α))

instance {n : ℕ} (μ : Fin n → ℝ) (d α : ℝ) : IsProbabilityMeasure (law μ d α) := by
  unfold law
  infer_instance

variable {n : ℕ} {d α : ℝ}

theorem pac_preserving (μ : Fin n → ℝ) : MeasurePreserving Prod.fst
    (law μ d α) (GapEntropy.MedianTape.law μ (d / 8) (α / 16)) := measurePreserving_fst

theorem referenceNoise_preserving (μ : Fin n → ℝ) :
    MeasurePreserving (fun ω : Tape n d α => ω.2.1)
      (law μ d α) (GapEntropy.GaussianNoise.law (referenceSamples d α)) :=
  measurePreserving_fst.comp measurePreserving_snd

theorem activeNoise_preserving (μ : Fin n → ℝ) (i : Fin n) :
    MeasurePreserving (fun ω : Tape n d α => ω.2.2 i)
      (law μ d α) (GapEntropy.GaussianNoise.law (activeSamples d α)) :=
  (measurePreserving_eval_infinitePi
    (fun _ : Fin n => GapEntropy.GaussianNoise.law (activeSamples d α)) i).comp
      (measurePreserving_snd.comp measurePreserving_snd)

/-- The PAC experiment and both fresh noise blocks are independent by construction. -/
theorem pac_independent_fresh (μ : Fin n → ℝ) :
    IndepFun (Prod.fst : Tape n d α → _) Prod.snd (law μ d α) :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

def referenceArm (S : Finset (Fin n)) (hS : S.Nonempty) (ω : Tape n d α) : Fin n :=
  GapEntropy.MedianTape.output S hS ω.1

def referenceEstimate (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    (ω : Tape n d α) : ℝ :=
  μ (referenceArm S hS ω) + GapEntropy.GaussianNoise.mean ω.2.1

def activeEstimate (μ : Fin n → ℝ) (i : Fin n) (ω : Tape n d α) : ℝ :=
  μ i + GapEntropy.GaussianNoise.mean (ω.2.2 i)

def rawOutput (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    (ω : Tape n d α) : Finset (Fin n) :=
  GapEntropy.Elimination.raw S (fun i => activeEstimate μ i ω) (referenceEstimate μ S hS ω) d

def paddedOutput (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    (ω : Tape n d α) : Finset (Fin n) :=
  GapEntropy.Elimination.padded S (fun i => activeEstimate μ i ω) (referenceEstimate μ S hS ω) d

theorem referenceArm_measurable (S : Finset (Fin n)) (hS : S.Nonempty) :
    Measurable (referenceArm (d := d) (α := α) S hS) := by
  have h := medianEliminate_measurable S hS
    (fun r i => (measurable_pi_apply i).comp
      (empiricalVectors_measurable
        (GapEntropy.MedianTape.observation_measurable (ε := d / 8) (β := α / 16)) r))
  exact h.comp measurable_fst

theorem referenceArm_mem (S : Finset (Fin n)) (hS : S.Nonempty) (ω : Tape n d α) :
    referenceArm S hS ω ∈ S :=
  activeSets_subset S _ _ (medianEliminate_mem_terminal hS _)

theorem referenceEstimate_measurable (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    Measurable (referenceEstimate (d := d) (α := α) μ S hS) :=
  ((measurable_of_finite μ).comp (referenceArm_measurable S hS)).add
    ((GapEntropy.GaussianNoise.mean_measurable _).comp (measurable_fst.comp measurable_snd))

theorem activeEstimate_measurable (μ : Fin n → ℝ) (i : Fin n) :
    Measurable (activeEstimate (d := d) (α := α) μ i) :=
  measurable_const.add ((GapEntropy.GaussianNoise.mean_measurable _).comp
    ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))

theorem rawOutput_measurable (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    Measurable (rawOutput (d := d) (α := α) μ S hS) :=
  GapEntropy.SortingMeasurability.raw_measurable measurable_const
    (activeEstimate_measurable μ) (referenceEstimate_measurable μ S hS) measurable_const

theorem paddedOutput_measurable (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty) :
    Measurable (paddedOutput (d := d) (α := α) μ S hS) :=
  GapEntropy.SortingMeasurability.padded_measurable measurable_const
    (activeEstimate_measurable μ) (referenceEstimate_measurable μ S hS) measurable_const

theorem active_deviation_le (μ : Fin n → ℝ) (i : Fin n)
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) :
    (law μ d α).real (deviation μ d (activeEstimate μ) i) ≤ α / 64 := by
  have h := GapEntropy.GaussianNoise.mean_tail_of_budget (activeSamples_pos hd hα hα1)
    (activeNoise_preserving (d := d) (α := α) μ i) hd hα (by norm_num : (0 : ℝ) < 128)
    (show 512 * (d ^ 2)⁻¹ * Real.log (128 / α) ≤ (activeSamples d α : ℝ) from Nat.le_ceil _)
  simpa only [deviation, activeEstimate, add_sub_cancel_left, show (2 * α / 128 : ℝ) = α / 64 by ring]
    using h

theorem reference_noise_deviation_le (μ : Fin n → ℝ)
    (hd : 0 < d) (hα : 0 < α) (hα1 : α ≤ 1) :
    (law μ d α).real {ω : Tape n d α | d / 16 ≤ |GapEntropy.GaussianNoise.mean ω.2.1|} ≤ α / 16 := by
  have h := GapEntropy.GaussianNoise.mean_tail_of_budget (referenceSamples_pos hd hα hα1)
    (referenceNoise_preserving (d := d) (α := α) μ) hd hα (by norm_num : (0 : ℝ) < 32)
    (show 512 * (d ^ 2)⁻¹ * Real.log (32 / α) ≤ (referenceSamples d α : ℝ) from Nat.le_ceil _)
  convert h using 1
  ring

theorem pac_failure_le (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    (law μ d α).real {ω : Tape n d α | ¬ ∀ i ∈ S,
      μ i - d / 8 ≤ μ (referenceArm S hS ω)} ≤ α / 16 := by
  have h := GapEntropy.MedianTape.medianElimination_A2 μ hS
    (show 0 < d / 8 by positivity) (show d / 8 ≤ 1 by linarith)
    (show 0 < α / 16 by positivity) (show α / 16 ≤ 1 by linarith)
  let G : Set (GapEntropy.MedianTape.Tape n (d / 8) (α / 16)) :=
    {ω | ∀ i ∈ S, μ i - d / 8 ≤ μ (GapEntropy.MedianTape.output S hS ω)}
  have hm : MeasurableSet G := h.1 (Set.toFinite {a : Fin n | ∀ i ∈ S, μ i - d / 8 ≤ μ a}).measurableSet
  have he := (pac_preserving (d := d) (α := α) μ).measureReal_preimage hm.compl.nullMeasurableSet
  have hc := measureReal_compl (μ := GapEntropy.MedianTape.law μ (d / 8) (α / 16)) hm
  rw [probReal_univ] at hc
  change (law μ d α).real {ω : Tape n d α | ¬ ∀ i ∈ S,
    μ i - d / 8 ≤ μ (referenceArm S hS ω)} = _ at he
  have hs := h.2.2.1
  change 1 - α / 16 ≤ (GapEntropy.MedianTape.law μ (d / 8) (α / 16)).real G at hs
  linarith

theorem reference_bad_le (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, μ i ≤ μ best)
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    (law μ d α).real (referenceBad (μ best) d (referenceEstimate μ S hS)) ≤ α / 8 := by
  let B : Set (Tape n d α) := {ω | ¬ ∀ i ∈ S, μ i - d / 8 ≤ μ (referenceArm S hS ω)}
  let E : Set (Tape n d α) := {ω | d / 16 ≤ |GapEntropy.GaussianNoise.mean ω.2.1|}
  have hsub : referenceBad (μ best) d (referenceEstimate μ S hS) ⊆ B ∪ E := by
    intro ω hω
    by_contra! h
    simp only [Set.mem_union, not_or] at h
    have hp : ∀ i ∈ S, μ i - d / 8 ≤ μ (referenceArm S hS ω) := not_not.mp h.1
    have hn : |GapEntropy.GaussianNoise.mean ω.2.1| < d / 16 := lt_of_not_ge h.2
    have hu := hmax _ (referenceArm_mem S hS ω)
    have hl := hp best hbest
    have hab := abs_lt.mp hn
    apply hω
    dsimp [referenceEstimate]
    constructor <;> linarith
  have hu := (measureReal_mono hsub (measure_ne_top (law μ d α) _)).trans (measureReal_union_le _ _)
  have hp := pac_failure_le μ S hS hd hd1 hα hα1
  have hn := reference_noise_deviation_le μ hd hα hα1
  change (law μ d α).real B ≤ α / 16 at hp
  change (law μ d α).real E ≤ α / 16 at hn
  linarith

/-- A.3(1) for the actual raw procedure on the explicitly constructed Gaussian tape. -/
theorem raw_best_failure (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, μ i ≤ μ best)
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    (law μ d α).real {ω | best ∉ rawOutput μ S hS ω} ≤ α :=
  raw_best_failure_le hbest hd.le hα.le (reference_bad_le μ S hS hbest hmax hd hd1 hα hα1)
    (active_deviation_le μ best hd hα hα1)

theorem padded_best_failure (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, μ i ≤ μ best)
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1) :
    (law μ d α).real {ω | best ∉ paddedOutput μ S hS ω} ≤ α := by
  apply le_trans (measureReal_mono (s₂ := {ω | best ∉ rawOutput μ S hS ω}) ?_
    (measure_ne_top (law μ d α) _)) (raw_best_failure μ S hS hbest hmax hd hd1 hα hα1)
  intro ω hω hb
  exact hω (GapEntropy.Elimination.raw_subset_padded _ _ _ _ hb)

/-- A.3(2): raw best retention and rounded-half size, without a conditional-success premise. -/
theorem raw_large_failure (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, μ i ≤ μ best)
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    {N : ℕ} (hnear : (GapEntropy.Elimination.near S μ (μ best) d).card ≤ N)
    (hs : 4 * N < S.card) :
    (law μ d α).real {ω | best ∉ rawOutput μ S hS ω ∨
      (S.card + 1) / 2 < (rawOutput μ S hS ω).card} ≤ α :=
  raw_large_failure_le hbest hd.le hα.le (activeEstimate_measurable μ)
    (reference_bad_le μ S hS hbest hmax hd hd1 hα hα1)
    (fun i _ => active_deviation_le μ i hd hα hα1) hnear hs

/-- A.3(2), actual padded output: the set both retains the best and has exactly the rounded-half size. -/
theorem padded_large_failure (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, μ i ≤ μ best)
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    {N : ℕ} (hnear : (GapEntropy.Elimination.near S μ (μ best) d).card ≤ N)
    (hs : 4 * N < S.card) :
    (law μ d α).real {ω | best ∉ paddedOutput μ S hS ω ∨
      (paddedOutput μ S hS ω).card ≠ (S.card + 1) / 2} ≤ α :=
  padded_large_failure_le hbest hd.le hα.le (activeEstimate_measurable μ)
    (reference_bad_le μ S hS hbest hmax hd hd1 hα hα1)
    (fun i _ => active_deviation_le μ i hd hα hα1) hnear hs

/-- A.3(3): separated sets of size at most four return the exact best singleton in the raw procedure. -/
theorem raw_small_failure (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, μ i ≤ μ best)
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : S.card ≤ 4) (hgaps : ∀ i ∈ S, i ≠ best → d ≤ μ best - μ i) :
    (law μ d α).real {ω | rawOutput μ S hS ω ≠ {best}} ≤ α :=
  raw_small_failure_le hbest hd.le hα.le (reference_bad_le μ S hS hbest hmax hd hd1 hα hα1)
    (fun i _ => active_deviation_le μ i hd hα hα1) hs hgaps

/-- On the raw-singleton good event, padding retains the best and halves a small set. -/
theorem padded_small_failure (μ : Fin n → ℝ) (S : Finset (Fin n)) (hS : S.Nonempty)
    {best : Fin n} (hbest : best ∈ S) (hmax : ∀ i ∈ S, μ i ≤ μ best)
    (hd : 0 < d) (hd1 : d ≤ 1) (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : S.card ≤ 4) (hgaps : ∀ i ∈ S, i ≠ best → d ≤ μ best - μ i) :
    (law μ d α).real {ω | best ∉ paddedOutput μ S hS ω ∨
      (paddedOutput μ S hS ω).card ≠ (S.card + 1) / 2} ≤ α := by
  apply le_trans (measureReal_mono (s₂ := {ω | rawOutput μ S hS ω ≠ {best}}) ?_
    (measure_ne_top (law μ d α) _)) (raw_small_failure μ S hS hbest hmax hd hd1 hα hα1 hs hgaps)
  intro ω hω heq
  have hb : best ∈ rawOutput μ S hS ω := by simp [heq]
  have hcard : (rawOutput μ S hS ω).card = 1 := by simp [heq]
  rcases hω with hnot | hsize
  · exact hnot (GapEntropy.Elimination.raw_subset_padded _ _ _ _ hb)
  · apply hsize
    apply GapEntropy.Elimination.padded_halves_of_raw_small
    change (rawOutput μ S hS ω).card ≤ (S.card + 1) / 2
    have hpos := hS.card_pos
    omega

theorem two_small_halves {s : ℕ} (hs : 0 < s) (hs4 : s ≤ 4) :
    ((s + 1) / 2 + 1) / 2 = 1 := by omega

end GapEntropy.EliminationTape
