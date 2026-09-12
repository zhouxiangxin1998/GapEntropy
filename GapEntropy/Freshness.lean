import GapEntropy.Model
import Mathlib.Probability.Independence.InfinitePi

/-!
# Fresh rewards for the operational Gaussian model

The actual operational history factors through the seed and the reward rows strictly before
the current time. Independence of disjoint finite blocks of the product reward law then makes
the current reward row fresh with respect to that history.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GapEntropy

abbrev RewardPrefix (n t : ℕ) := Fin t → Fin n → ℝ
abbrev SeedPrefix (n t : ℕ) := Seed × RewardPrefix n t

def seedPrefix {n : ℕ} (t : ℕ) (ω : SampleSpace n) : SeedPrefix n t :=
  (ω.1, fun s => ω.2 s)

/-- Complete a finite reward prefix with zeros; these future coordinates
are only a device for the factorization and are never observed before `t`. -/
def extendPrefix {n : ℕ} (t : ℕ) (p : SeedPrefix n t) : SampleSpace n :=
  (p.1, fun s => if h : s < t then p.2 ⟨s, h⟩ else fun _ => 0)

theorem measurable_prefix {n : ℕ} (t : ℕ) : Measurable (seedPrefix (n := n) t) := by
  exact measurable_fst.prodMk (measurable_pi_lambda _ fun s =>
    (measurable_pi_apply (s : ℕ)).comp measurable_snd)

theorem measurable_extendPrefix {n : ℕ} (t : ℕ) :
    Measurable (extendPrefix (n := n) t) := by
  apply Measurable.prodMk measurable_fst
  apply measurable_pi_lambda
  intro s
  by_cases h : s < t
  · simpa only [extendPrefix, dif_pos h, Function.comp_def] using
      (measurable_pi_apply (⟨s, h⟩ : Fin t)).comp
        (measurable_snd : Measurable (fun p : SeedPrefix n t => p.2))
  · simpa only [extendPrefix, dif_neg h] using
      (measurable_const : Measurable (fun _ : SeedPrefix n t => (fun _ : Fin n => (0 : ℝ))))

private theorem indepFun_of_joint_measurePreserving {Ω α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} {ν : Measure α} {ρ : Measure β}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {f : Ω → α} {g : Ω → β}
    (h : MeasurePreserving (fun ω => (f ω, g ω)) μ (ν.prod ρ)) : IndepFun f g μ := by
  have hf : Measurable f := measurable_fst.comp h.measurable
  have hg : Measurable g := measurable_snd.comp h.measurable
  apply (indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable).2
  have hfm : μ.map f = ν := (measurePreserving_fst.comp h).map_eq
  have hgm : μ.map g = ρ := (measurePreserving_snd.comp h).map_eq
  rw [hfm, hgm]
  exact h.map_eq

/-- Adding an independent coordinate preserves the independence of the two
original coordinates, jointly with that added coordinate on the left. -/
private theorem indepFun_pair_left_prod {Ω Ω' α β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω' → α} {g : Ω' → β} (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g ν) :
    IndepFun (fun ω : Ω × Ω' => (ω.1, f ω.2)) (fun ω => g ω.2) (μ.prod ν) := by
  let : IsProbabilityMeasure (ν.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  let : IsProbabilityMeasure (ν.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  have hj : MeasurePreserving (fun x => (f x, g x)) ν ((ν.map f).prod (ν.map g)) :=
    ⟨hf.prodMk hg, hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable⟩
  have hp := (MeasurePreserving.id μ).prod hj
  have ha := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ (ν.map f) (ν.map g))
  exact indepFun_of_joint_measurePreserving (ha.comp hp)

theorem indepFun_rewardPrefix_row {n : ℕ} (mean : Fin n → ℝ) (t : ℕ) :
    IndepFun (fun r : ℕ → Fin n → ℝ => fun s : Fin t => r s)
      (fun r => r t) (rewardLaw mean) := by
  have hi : iIndepFun (fun s (r : ℕ → Fin n → ℝ) => r s) (rewardLaw mean) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hd : Disjoint (Finset.range t) ({t} : Finset ℕ) := by simp
  have hb := hi.indepFun_finset (Finset.range t) {t} hd
    (fun s => measurable_pi_apply s)
  have hl : Measurable (fun x : (s : Finset.range t) → (Fin n → ℝ) =>
      fun s : Fin t => x ⟨s, Finset.mem_range.mpr s.isLt⟩) :=
    measurable_pi_lambda _ (fun s => measurable_pi_apply _)
  have hr : Measurable (fun x : (s : ({t} : Finset ℕ)) → (Fin n → ℝ) =>
      x ⟨t, Finset.mem_singleton_self t⟩) := measurable_pi_apply _
  exact hb.comp hl hr

theorem indepFun_seedPrefix_row {n : ℕ} (mean : Fin n → ℝ) (t : ℕ) :
    IndepFun (seedPrefix (n := n) t) (fun ω : SampleSpace n => ω.2 t)
      (sampleLawOfMeans mean) := by
  exact indepFun_pair_left_prod
    (measurable_pi_lambda _ (fun s : Fin t => measurable_pi_apply (s : ℕ)))
    (measurable_pi_apply t) (indepFun_rewardPrefix_row mean t)

namespace Policy

variable {n : ℕ} (A : Policy n)

/-- Equal seeds and equal reward rows before `t` give exactly equal states. -/
theorem run_congr_prefix (hn : 2 ≤ n) (t : ℕ) {ω ω' : SampleSpace n}
    (hseed : ω.1 = ω'.1) :
    (∀ s, s < t → ω.2 s = ω'.2 s) → A.run hn ω t = A.run hn ω' t := by
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro hrows
      have hr := ih (fun s hs => hrows s (Nat.lt_succ_of_lt hs))
      simp only [run_succ, hr, step, hseed, hrows t (Nat.lt_succ_self t)]

def runFromPrefix (hn : 2 ≤ n) (t : ℕ) (p : SeedPrefix n t) : RunState n t :=
  A.run hn (extendPrefix t p) t

theorem measurable_runFromPrefix (hn : 2 ≤ n) (t : ℕ) :
    Measurable (A.runFromPrefix hn t) :=
  (A.measurable_run hn t).comp (measurable_extendPrefix t)

theorem run_eq_runFromPrefix (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) :
    A.run hn ω t = A.runFromPrefix hn t (seedPrefix t ω) := by
  unfold runFromPrefix
  apply A.run_congr_prefix hn t (ω := ω) (ω' := extendPrefix t (seedPrefix t ω)) rfl
  intro s hs
  simp [seedPrefix, extendPrefix, hs]

def requestedArmFromPrefix (hn : 2 ≤ n) (t : ℕ) (p : SeedPrefix n t) : Option (Fin n) :=
  A.requestedArm hn t (extendPrefix t p)

theorem measurable_requestedArmFromPrefix (hn : 2 ≤ n) (t : ℕ) :
    Measurable (A.requestedArmFromPrefix hn t) :=
  (A.measurable_requestedArm hn t).comp (measurable_extendPrefix t)

theorem requestedArm_eq_fromPrefix (hn : 2 ≤ n) (t : ℕ) (ω : SampleSpace n) :
    A.requestedArm hn t ω = A.requestedArmFromPrefix hn t (seedPrefix t ω) := by
  unfold requestedArmFromPrefix requestedArm
  rw [A.run_eq_runFromPrefix hn t ω]
  rfl

/-- The fresh row is independent of the complete seed and the actual
adaptive execution state at the start of the current decision. -/
theorem indepFun_seed_run_row (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    IndepFun (fun ω : SampleSpace n => (ω.1, A.run hn ω t)) (fun ω => ω.2 t)
      (sampleLawOfMeans mean) := by
  have h := (indepFun_seedPrefix_row mean t).comp
    (measurable_fst.prodMk (A.measurable_runFromPrefix hn t)) measurable_id
  convert h using 1
  · funext ω
    exact congrArg (Prod.mk ω.1) (A.run_eq_runFromPrefix hn t ω)
  · rfl

theorem indepFun_requestedArm_row (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) :
    IndepFun (A.requestedArm hn t) (fun ω : SampleSpace n => ω.2 t)
      (sampleLawOfMeans mean) := by
  have h := (indepFun_seedPrefix_row mean t).comp
    (A.measurable_requestedArmFromPrefix hn t) measurable_id
  convert h using 1
  · funext ω
    exact A.requestedArm_eq_fromPrefix hn t ω
  · rfl

theorem indepFun_seed_run_reward (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) (i : Fin n) :
    IndepFun (fun ω : SampleSpace n => (ω.1, A.run hn ω t)) (fun ω => ω.2 t i)
      (sampleLawOfMeans mean) :=
  (A.indepFun_seed_run_row hn mean t).comp measurable_id (measurable_pi_apply i)

/-- An eventwise conditional-Gaussian identity. It applies to every measurable
event in the seed and past reward rows, intersected with the actual decision
to sample arm `i`. No positive-probability conditioning assumption is needed. -/
theorem measure_request_reward (hn : 2 ≤ n) (mean : Fin n → ℝ) (t : ℕ) (i : Fin n)
    {B : Set (SeedPrefix n t)} (hB : MeasurableSet B) {S : Set ℝ} (hS : MeasurableSet S) :
    sampleLawOfMeans mean {ω | seedPrefix t ω ∈ B ∧
      A.requestedArm hn t ω = some i ∧ ω.2 t i ∈ S} =
    sampleLawOfMeans mean {ω | seedPrefix t ω ∈ B ∧ A.requestedArm hn t ω = some i} *
      gaussianReal (mean i) 1 S := by
  let E : Set (SeedPrefix n t) := B ∩ {p | A.requestedArmFromPrefix hn t p = some i}
  have hE : MeasurableSet E := hB.inter
    ((A.measurable_requestedArmFromPrefix hn t).eq_const (some i)).setOf
  have hi := (indepFun_seedPrefix_row mean t).comp measurable_id (measurable_pi_apply i)
  have heq := hi.measure_inter_preimage_eq_mul E S hE hS
  have hm : sampleLawOfMeans mean ((fun ω : SampleSpace n => ω.2 t i) ⁻¹' S) =
      gaussianReal (mean i) 1 S := by
    rw [← Measure.map_apply (by fun_prop) hS, sampleLawOfMeans_map_reward]
  change sampleLawOfMeans mean
      ((seedPrefix t) ⁻¹' E ∩ (fun ω : SampleSpace n => ω.2 t i) ⁻¹' S) =
      sampleLawOfMeans mean ((seedPrefix t) ⁻¹' E) * _ at heq
  dsimp only [Function.comp_def] at heq
  rw [hm] at heq
  have hpre : (seedPrefix t) ⁻¹' E =
      {ω | seedPrefix t ω ∈ B ∧ A.requestedArm hn t ω = some i} := by
    ext ω
    simp only [E, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
      ← A.requestedArm_eq_fromPrefix]
  rw [hpre] at heq
  have hinter :
      {ω | seedPrefix t ω ∈ B ∧ A.requestedArm hn t ω = some i} ∩
        (fun ω : SampleSpace n => ω.2 t i) ⁻¹' S =
      {ω | seedPrefix t ω ∈ B ∧ A.requestedArm hn t ω = some i ∧ ω.2 t i ∈ S} := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, and_assoc]
  rw [hinter] at heq
  exact heq

end Policy
end GapEntropy
