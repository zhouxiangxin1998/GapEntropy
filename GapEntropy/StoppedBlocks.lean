import GapEntropy.GaussianBlocks

/-!
# Fresh Gaussian blocks after a finite stopping time

A start event at time `t` must depend only on the seed and reward rows before `t`.
We prove its exact factorization against the next fixed-length block and then sum
over disjoint start events. Thus an adaptive call boundary does not require an
assumed fresh-noise oracle. The boundary may be unbounded but must be finite on
paths where the call is reached.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal BigOperators Classical

namespace GapEntropy.GaussianBlocks

variable {n : ℕ}

def blockLaw (mean : Fin n → ℝ) (m : ℕ) : Measure (Fin m → Fin n → ℝ) :=
  Measure.infinitePi (fun _ => Measure.pi (fun i => gaussianReal (mean i) 1))

instance (mean : Fin n → ℝ) (m : ℕ) : IsProbabilityMeasure (blockLaw mean m) := by
  unfold blockLaw
  infer_instance

theorem measurePreserving_rewardBlock (mean : Fin n → ℝ) (t m : ℕ) :
    MeasurePreserving (rewardBlock t m) (sampleLawOfMeans mean) (blockLaw mean m) := by
  have h : MeasurePreserving (fun r : ℕ → Fin n → ℝ => fun j : Fin m => r (t + j))
      (rewardLaw mean) (blockLaw mean m) := by
    refine ⟨by fun_prop, ?_⟩
    exact Measure.map_infinitePi_infinitePi_of_inj (fun i j hij =>
      Fin.ext (Nat.add_left_cancel hij))
  exact h.comp (measurePreserving_snd (μ := seedLaw) (ν := rewardLaw mean))

theorem measure_prefix_event_block (mean : Fin n → ℝ) (t m : ℕ)
    (E : Set (SeedPrefix n t)) (hE : MeasurableSet E)
    (B : Set (Fin m → Fin n → ℝ)) (hB : MeasurableSet B) :
    sampleLawOfMeans mean {ω | seedPrefix t ω ∈ E ∧ rewardBlock t m ω ∈ B} =
      sampleLawOfMeans mean ((seedPrefix t) ⁻¹' E) * blockLaw mean m B := by
  have h := (indepFun_seedPrefix_rewardBlock mean t m).measure_inter_preimage_eq_mul E B hE hB
  have hm := (measurePreserving_rewardBlock mean t m).measure_preimage hB.nullMeasurableSet
  rw [hm] at h
  exact h

/-- No path contributes two separate starts to this identity. The start events
can include an arbitrary measurable past restriction, e.g. reaching a call with
specified parameters and state. -/
theorem measure_disjoint_starts_block (mean : Fin n → ℝ) (m : ℕ)
    (E : ∀ t, Set (SeedPrefix n t)) (hE : ∀ t, MeasurableSet (E t))
    (hdis : Pairwise (Disjoint on (fun t => (seedPrefix t) ⁻¹' E t)))
    (B : Set (Fin m → Fin n → ℝ)) (hB : MeasurableSet B) :
    sampleLawOfMeans mean (⋃ t, {ω | seedPrefix t ω ∈ E t ∧ rewardBlock t m ω ∈ B}) =
      sampleLawOfMeans mean (⋃ t, (seedPrefix t) ⁻¹' E t) * blockLaw mean m B := by
  have hD : Pairwise (Disjoint on
      (fun t => {ω | seedPrefix t ω ∈ E t ∧ rewardBlock t m ω ∈ B})) := by
    intro s t hst
    exact (hdis hst).mono (fun _ h => h.1) (fun _ h => h.1)
  have hmeas (t : ℕ) : MeasurableSet {ω | seedPrefix t ω ∈ E t ∧ rewardBlock t m ω ∈ B} :=
    ((measurable_prefix t) (hE t)).inter ((measurable_rewardBlock t m) hB)
  rw [measure_iUnion hD hmeas, measure_iUnion hdis (fun t => measurable_prefix t (hE t))]
  simp_rw [measure_prefix_event_block mean _ m _ (hE _) B hB]
  exact ENNReal.tsum_mul_right

/-- The next `m` reward rows, beginning at a finite adaptive boundary. -/
def stoppedBlock (τ : SampleSpace n → ℕ) (m : ℕ) (ω : SampleSpace n) : Fin m → Fin n → ℝ :=
  rewardBlock (τ ω) m ω

theorem measurable_stoppedBlock {τ : SampleSpace n → ℕ} (hτ : Measurable τ) (m : ℕ) :
    Measurable (stoppedBlock τ m) := by
  have hf : Measurable (fun p : ℕ × SampleSpace n => rewardBlock p.1 m p.2) := by
    apply measurable_from_prod_countable_right
    intro t
    exact measurable_rewardBlock t m
  exact hf.comp (hτ.prodMk measurable_id)

/-- Any event known at the adaptive boundary factors exactly from the following
Gaussian block. The past-event representation explicitly rules out selection
using the block's future data. -/
theorem measure_event_stoppedBlock (mean : Fin n → ℝ) (τ : SampleSpace n → ℕ) (m : ℕ)
    (R : Set (SampleSpace n))
    (hpast : ∀ t, ∃ E : Set (SeedPrefix n t), MeasurableSet E ∧
      {ω | τ ω = t ∧ ω ∈ R} = (seedPrefix t) ⁻¹' E)
    (B : Set (Fin m → Fin n → ℝ)) (hB : MeasurableSet B) :
    sampleLawOfMeans mean {ω | ω ∈ R ∧ stoppedBlock τ m ω ∈ B} =
      sampleLawOfMeans mean R * blockLaw mean m B := by
  choose E hE he using hpast
  have hd : Pairwise (Disjoint on (fun t => (seedPrefix t) ⁻¹' E t)) := by
    intro s t hst
    change Disjoint ((seedPrefix s) ⁻¹' E s) ((seedPrefix t) ⁻¹' E t)
    rw [← he s, ← he t]
    apply Set.disjoint_left.mpr
    intro ω hs ht
    exact hst (hs.1.symm.trans ht.1)
  have hu : (⋃ t, (seedPrefix t) ⁻¹' E t) = R := by
    simp_rw [← he]
    ext ω
    simp
  have hv : (⋃ t, {ω | seedPrefix t ω ∈ E t ∧ rewardBlock t m ω ∈ B}) =
      {ω | ω ∈ R ∧ stoppedBlock τ m ω ∈ B} := by
    ext ω
    constructor
    · intro hω
      obtain ⟨t, ht, hB⟩ := Set.mem_iUnion.mp hω
      have ht' : τ ω = t ∧ ω ∈ R := by
        change ω ∈ (seedPrefix t) ⁻¹' E t at ht
        rwa [← he t] at ht
      exact ⟨ht'.2, by simpa only [stoppedBlock, ht'.1] using hB⟩
    · rintro ⟨hR, hB⟩
      apply Set.mem_iUnion.mpr
      refine ⟨τ ω, ?_, hB⟩
      change ω ∈ (seedPrefix (τ ω)) ⁻¹' E (τ ω)
      rw [← he]
      exact ⟨rfl, hR⟩
  rw [← hv, measure_disjoint_starts_block mean m E hE hd B hB, hu]

/-- Finite stopping-time shifts preserve the entire joint law of a following
finite reward block, not just its coordinate marginals. -/
theorem measurePreserving_stoppedBlock (mean : Fin n → ℝ) (τ : SampleSpace n → ℕ)
    (hτ : Measurable τ)
    (hpast : ∀ t, ∃ E : Set (SeedPrefix n t), MeasurableSet E ∧
      {ω | τ ω = t} = (seedPrefix t) ⁻¹' E) (m : ℕ) :
    MeasurePreserving (stoppedBlock τ m) (sampleLawOfMeans mean) (blockLaw mean m) := by
  refine ⟨measurable_stoppedBlock hτ m, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_stoppedBlock hτ m) hB]
  have h := measure_event_stoppedBlock mean τ m Set.univ
    (fun t => by simpa only [Set.mem_univ, and_true] using hpast t) B hB
  simpa only [Set.mem_univ, true_and, measure_univ, one_mul, Set.preimage] using h

end GapEntropy.GaussianBlocks
