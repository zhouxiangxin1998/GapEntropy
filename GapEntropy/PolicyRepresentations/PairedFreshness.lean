import GapEntropy.Freshness
import Mathlib.MeasureTheory.Constructions.UnitInterval

/-!
# Freshness of paired uniform and Gaussian coordinates

The law `freshnessLaw mean` is the product of an independent sequence of uniform variables on
the unit interval with the Gaussian reward table. At each time `t`, the pair of prefixes before
`t` is independent of the fresh pair consisting of the uniform coordinate and the reward row at
`t`, and that fresh pair has the product of uniform volume and the Gaussian row law. These facts
supply the fresh uniform coordinate used by the kernel-policy implementation in `KernelPolicy`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory GapEntropy
open scoped ENNReal

namespace GapEntropy.PolicyRepresentations

abbrev FreshUniformSeed := ℕ → unitInterval

def freshnessUniformLaw : Measure FreshUniformSeed :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure unitInterval))

instance : IsProbabilityMeasure freshnessUniformLaw := by
  unfold freshnessUniformLaw
  infer_instance

def freshnessLaw {n : ℕ} (mean : Fin n → ℝ) :=
  freshnessUniformLaw.prod (rewardLaw mean)

instance {n : ℕ} (mean : Fin n → ℝ) : IsProbabilityMeasure (freshnessLaw mean) := by
  unfold freshnessLaw
  infer_instance

def pairedPrefix {n : ℕ} (t : ℕ)
    (ω : FreshUniformSeed × (ℕ → Fin n → ℝ)) :=
  ((fun s : Fin t => ω.1 s), (fun s : Fin t => ω.2 s))

def freshPair {n : ℕ} (t : ℕ)
    (ω : FreshUniformSeed × (ℕ → Fin n → ℝ)) := (ω.1 t, ω.2 t)

@[fun_prop] theorem measurable_pairedPrefix {n : ℕ} (t : ℕ) :
    Measurable (pairedPrefix (n := n) t) := by unfold pairedPrefix; fun_prop

@[fun_prop] theorem measurable_freshPair {n : ℕ} (t : ℕ) :
    Measurable (freshPair (n := n) t) := by unfold freshPair; fun_prop

private theorem measurePreserving_pairShuffle
    {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ]
    (a : Measure α) (b : Measure β) (c : Measure γ) (d : Measure δ)
    [IsProbabilityMeasure a] [IsProbabilityMeasure b]
    [IsProbabilityMeasure c] [IsProbabilityMeasure d] :
    MeasurePreserving (fun p : (α × β) × (γ × δ) =>
      ((p.1.1, p.2.1), (p.1.2, p.2.2)))
      ((a.prod b).prod (c.prod d)) ((a.prod c).prod (b.prod d)) := by
  have h1 := measurePreserving_prodAssoc a b (c.prod d)
  have h2 := (MeasurePreserving.id a).prod
    ((measurePreserving_prodAssoc b c d).symm MeasurableEquiv.prodAssoc)
  have h3 := (MeasurePreserving.id a).prod
    ((Measure.measurePreserving_swap (μ := b) (ν := c)).prod (MeasurePreserving.id d))
  have h4 := (MeasurePreserving.id a).prod (measurePreserving_prodAssoc c b d)
  have h5 := (measurePreserving_prodAssoc a c (b.prod d)).symm
    MeasurableEquiv.prodAssoc
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

private theorem indepFun_uniformPrefix_current (t : ℕ) :
    IndepFun (fun u : FreshUniformSeed => fun s : Fin t => u s)
      (fun u => u t) freshnessUniformLaw := by
  have hi : iIndepFun (fun s (u : FreshUniformSeed) => u s) freshnessUniformLaw :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hb := hi.indepFun_finset (Finset.range t) {t} (by simp)
    (fun s => measurable_pi_apply s)
  exact hb.comp
    (measurable_pi_lambda _ (fun s : Fin t =>
      measurable_pi_apply (⟨s, Finset.mem_range.mpr s.isLt⟩ : Finset.range t)))
    (measurable_pi_apply (⟨t, Finset.mem_singleton_self t⟩ : ({t} : Finset ℕ)))

theorem measurePreserving_freshPair {n : ℕ} (mean : Fin n → ℝ) (t : ℕ) :
    MeasurePreserving (freshPair (n := n) t) (freshnessLaw mean)
      ((volume : Measure unitInterval).prod (Measure.pi (fun i => gaussianReal (mean i) 1))) :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ => (volume : Measure unitInterval)) t).prod
    (measurePreserving_eval_infinitePi _ t)

theorem indepFun_pairedPrefix_freshPair {n : ℕ} (mean : Fin n → ℝ) (t : ℕ) :
    IndepFun (pairedPrefix (n := n) t) (freshPair (n := n) t) (freshnessLaw mean) := by
  let pU := fun u : FreshUniformSeed => fun s : Fin t => u s
  let pR := fun r : ℕ → Fin n → ℝ => fun s : Fin t => r s
  let vU := freshnessUniformLaw.map pU
  let vR := (rewardLaw mean).map pR
  let gR := Measure.pi (fun i => gaussianReal (mean i) 1)
  have hpU : Measurable pU := by fun_prop
  have hpR : Measurable pR := by fun_prop
  let : IsProbabilityMeasure vU := Measure.isProbabilityMeasure_map hpU.aemeasurable
  let : IsProbabilityMeasure vR := Measure.isProbabilityMeasure_map hpR.aemeasurable
  have hU : MeasurePreserving (fun u : FreshUniformSeed => (pU u, u t))
      freshnessUniformLaw (vU.prod (volume : Measure unitInterval)) := by
    refine ⟨by fun_prop, ?_⟩
    rw [(indepFun_uniformPrefix_current t).map_prod_eq_prod_map_map hpU.aemeasurable
      (measurable_pi_apply t).aemeasurable]
    exact congrArg (vU.prod) (measurePreserving_eval_infinitePi
      (fun _ : ℕ => (volume : Measure unitInterval)) t).map_eq
  have hR : MeasurePreserving (fun r : ℕ → Fin n → ℝ => (pR r, r t))
      (rewardLaw mean) (vR.prod gR) := by
    refine ⟨by fun_prop, ?_⟩
    rw [(indepFun_rewardPrefix_row mean t).map_prod_eq_prod_map_map hpR.aemeasurable
      (measurable_pi_apply t).aemeasurable]
    exact congrArg (vR.prod) (measurePreserving_eval_infinitePi
      (fun _ : ℕ => Measure.pi (fun i => gaussianReal (mean i) 1)) t).map_eq
  have hj : MeasurePreserving
      (fun ω => (pairedPrefix (n := n) t ω, freshPair (n := n) t ω))
      (freshnessLaw mean) ((vU.prod vR).prod ((volume : Measure unitInterval).prod gR)) :=
    (measurePreserving_pairShuffle vU volume vR gR).comp (hU.prod hR)
  have hleft : (freshnessLaw mean).map (pairedPrefix (n := n) t) = vU.prod vR :=
    (measurePreserving_fst.comp hj).map_eq
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_pairedPrefix t).aemeasurable (measurable_freshPair t).aemeasurable).2
  rw [hleft, (measurePreserving_freshPair mean t).map_eq]
  exact hj.map_eq

theorem measurePreserving_pairedPrefix_freshPair {n : ℕ} (mean : Fin n → ℝ) (t : ℕ) :
    MeasurePreserving
      (fun ω => (pairedPrefix (n := n) t ω, freshPair (n := n) t ω))
      (freshnessLaw mean)
      (((freshnessLaw mean).map (pairedPrefix (n := n) t)).prod
        ((volume : Measure unitInterval).prod (Measure.pi (fun i => gaussianReal (mean i) 1)))) := by
  refine ⟨by fun_prop, ?_⟩
  rw [(indepFun_pairedPrefix_freshPair mean t).map_prod_eq_prod_map_map
    (measurable_pairedPrefix t).aemeasurable (measurable_freshPair t).aemeasurable,
    (measurePreserving_freshPair mean t).map_eq]

end GapEntropy.PolicyRepresentations
