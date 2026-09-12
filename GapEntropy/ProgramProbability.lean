import GapEntropy.ProgramGood
import GapEntropy.FiniteAdaptivity

/-!
# Failure probability of a finite call program under the Gaussian sample law

A finite choice based on the first `m` reward rows may select a tail event depending on the
following rows; by independence of disjoint reward blocks the uniform bound for fixed choices is
preserved (`adaptive_tail_event_le`). `LocallyValid` requires that each call's fixed A.3 block
experiment violate the good-call predicate with probability at most its declared confidence; it
is preserved by `bind`.

The main theorem bounds the probability of a bad sequential execution by the program's `risk`.
All local assumptions concern fixed Gaussian A.3 block experiments; the independence of the
adaptive continuation is proved, not assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Classical

namespace GapEntropy.FiniteCallProgram
open TargetAttempt GaussianBlocks
variable {n : ℕ} {α : Type*}

/-- A finite choice based on the first `m` actual reward rows can select a tail
event depending on the following `M` rows. Its uniform probability bound is
preserved, by product-law independence of the two disjoint blocks. -/
theorem adaptive_tail_event_le (mean : Fin n → ℝ) (m M : ℕ)
    (choose : (Fin m → Fin n → ℝ) → Finset (Fin n)) (hc : Measurable choose)
    (bad : Finset (Fin n) → Set (Values n)) (hbad : ∀ R, MeasurableSet (bad R))
    (hdep : ∀ R x y, (∀ j < M, x j = y j) → (x ∈ bad R ↔ y ∈ bad R))
    {b : ℝ} (hb : ∀ R, (sampleLawOfMeans mean).real {ω | ω.2 ∈ bad R} ≤ b) :
    (sampleLawOfMeans mean).real
      {ω | shiftValues m ω.2 ∈ bad (choose (rewardBlock 0 m ω))} ≤ b := by
  let P := sampleLawOfMeans mean
  let B : Finset (Fin n) → Set (Fin M → Fin n → ℝ) := fun R => extendBlock M ⁻¹' bad R
  have hB (R) : MeasurableSet (B R) := (extendBlock_measurable M) (hbad R)
  let Z : SampleSpace n → Finset (Fin n) := fun ω => choose (rewardBlock 0 m ω)
  have hZ : Measurable Z := hc.comp (measurable_rewardBlock 0 m)
  have hind : IndepFun Z (rewardBlock m M) P := by
    have h := (indepFun_seedPrefix_rewardBlock mean m M).comp (hc.comp measurable_snd) measurable_id
    change IndepFun (fun ω : SampleSpace n => choose (seedPrefix m ω).2) (rewardBlock m M) P at h
    have he : (fun ω : SampleSpace n => choose (seedPrefix m ω).2) = Z := by
      funext ω
      apply congrArg choose
      funext j
      simp only [seedPrefix, rewardBlock, zero_add]
    rwa [he] at h
  have heq (R) : rewardBlock 0 M ⁻¹' B R = {ω : SampleSpace n | ω.2 ∈ bad R} := by
    ext ω
    exact (hdep R _ _ (fun j hj => by simp [extendBlock, hj, rewardBlock])).symm
  have hlocal (R) : P.real (rewardBlock m M ⁻¹' B R) ≤ b := by
    rw [(measurePreserving_rewardBlock mean m M).measureReal_preimage (hB R).nullMeasurableSet]
    have h0 := (measurePreserving_rewardBlock mean 0 M).measureReal_preimage (hB R).nullMeasurableSet
    rw [heq R] at h0
    rw [← h0]
    exact hb R
  have h := FiniteAdaptivity.measure_adaptive_event_le hZ hind hB hlocal
  have he : {ω : SampleSpace n | rewardBlock m M ω ∈ B (Z ω)} =
      {ω | shiftValues m ω.2 ∈ bad (choose (rewardBlock 0 m ω))} := by
    ext ω
    exact (hdep (Z ω) _ _ (fun j hj => by simp [extendBlock, hj, rewardBlock, shiftValues])).symm
  rwa [he] at h

def LocallyValid (mean : Fin n → ℝ) (hn : 2 ≤ n) (G : Good n) : Program n α → Prop
  | .pure _ => True
  | .call key S hS d δ next =>
      (blockLaw mean (EliminationPolicy.budget S.card d δ)).real
        {v | ¬ G key S (EliminationPolicy.rawOutputFromBlock S hS d δ hn v)} ≤ δ ∧
      ∀ R, LocallyValid mean hn G (next R)

theorem locallyValid_bind (mean : Fin n → ℝ) (hn : 2 ≤ n) (G : Good n)
    {β : Type*} (p : Program n α) (f : α → Program n β)
    (hp : LocallyValid mean hn G p) (hf : ∀ a, LocallyValid mean hn G (f a)) :
    LocallyValid mean hn G (bind p f) := by
  induction p with
  | pure a => exact hf a
  | call key S hS d δ next ih => exact ⟨hp.1, fun R => ih R (hp.2 R)⟩

/-- All local probability assumptions concern fixed actual Gaussian A.3 block
experiments. Adaptive continuation independence is proved, not assumed. -/
theorem executionGood_failure_le (mean : Fin n → ℝ) (hn : 2 ≤ n) (G : Good n)
    (p : Program n α) (hp : LocallyValid mean hn G p) :
    (sampleLawOfMeans mean).real {ω | ¬ executionGood G p hn ω.2} ≤ risk p := by
  induction p with
  | pure a => simp [executionGood, risk]
  | call key S hS d δ next ih =>
    let m := EliminationPolicy.budget S.card d δ
    let M := Finset.univ.sup (fun R => capacity (next R))
    let b := Finset.univ.sup' Finset.univ_nonempty (fun R => risk (next R))
    let choose := EliminationPolicy.rawOutputFromBlock S hS d δ hn
    have hc : Measurable choose := EliminationPolicy.measurable_rawOutputFromBlock S hS d δ hn
    let Z : SampleSpace n → Finset (Fin n) := fun ω => choose (rewardBlock 0 m ω)
    have hfirst : (sampleLawOfMeans mean).real {ω | ¬ G key S (Z ω)} ≤ δ := by
      have hB : MeasurableSet {v | ¬ G key S (choose v)} :=
        hc (Set.toFinite {R | ¬ G key S R}).measurableSet
      have h := (measurePreserving_rewardBlock mean 0 m).measureReal_preimage hB.nullMeasurableSet
      exact h.le.trans hp.1
    have htail : (sampleLawOfMeans mean).real
        {ω | ¬ executionGood G (next (Z ω)) hn (shiftValues m ω.2)} ≤ b := by
      apply adaptive_tail_event_le mean m M choose hc
        (fun R => {x | ¬ executionGood G (next R) hn x})
        (fun R => (executionGood_measurable G (next R) hn).compl)
      · intro R x y hxy
        exact not_congr (executionGood_congr_prefix G (next R) hn x y (fun j hj =>
          hxy j (hj.trans_le (Finset.le_sup (f := fun T => capacity (next T)) (Finset.mem_univ R)))))
      · intro R
        exact (ih R (hp.2 R)).trans (Finset.le_sup' (fun R => risk (next R)) (Finset.mem_univ R))
    have hsub : {ω : SampleSpace n | ¬ executionGood G (.call key S hS d δ next) hn ω.2} ⊆
        {ω | ¬ G key S (Z ω)} ∪
          {ω | ¬ executionGood G (next (Z ω)) hn (shiftValues m ω.2)} := by
      intro ω hω
      have heq : firstBlock m ω.2 = rewardBlock 0 m ω := by funext j; simp [firstBlock, rewardBlock]
      change ¬ (G key S (choose (firstBlock m ω.2)) ∧
        executionGood G (next (choose (firstBlock m ω.2))) hn (shiftValues m ω.2)) at hω
      rw [heq] at hω
      exact not_and_or.mp hω
    exact (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add hfirst htail))

end GapEntropy.FiniteCallProgram
