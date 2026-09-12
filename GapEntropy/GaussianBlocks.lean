import GapEntropy.Freshness
import GapEntropy.Gaussian

/-!
# Fresh finite Gaussian blocks in the actual sampling model

The seed and all rows before a deterministic boundary are independent of the
following finite block. This is proved from the model's product measure.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace GapEntropy.GaussianBlocks

def rewardBlock {n : ℕ} (t m : ℕ) (ω : SampleSpace n) : Fin m → Fin n → ℝ :=
  fun j => ω.2 (t + j)

theorem measurable_rewardBlock {n : ℕ} (t m : ℕ) :
    Measurable (rewardBlock (n := n) t m) := by
  unfold rewardBlock
  fun_prop

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

theorem indepFun_seedPrefix_rewardBlock {n : ℕ} (mean : Fin n → ℝ) (t m : ℕ) :
    IndepFun (seedPrefix (n := n) t) (rewardBlock t m) (sampleLawOfMeans mean) := by
  have hi : iIndepFun (fun s (x : ℕ → Fin n → ℝ) => x s) (rewardLaw mean) :=
    iIndepFun_infinitePi (fun _ => measurable_id)
  have hd : Disjoint (Finset.range t) (Finset.Ico t (t + m)) := by
    apply Finset.disjoint_left.mpr
    intro s hs ht
    have hs' := Finset.mem_range.mp hs
    have ht' := (Finset.mem_Ico.mp ht).1
    omega
  have hb := hi.indepFun_finset (Finset.range t) (Finset.Ico t (t + m)) hd
    (fun s => measurable_pi_apply s)
  have hl : Measurable (fun x : (s : Finset.range t) → (Fin n → ℝ) =>
      fun s : Fin t => x ⟨s, Finset.mem_range.mpr s.isLt⟩) :=
    measurable_pi_lambda _ (fun s => measurable_pi_apply _)
  have hr : Measurable (fun x : (s : Finset.Ico t (t + m)) → (Fin n → ℝ) =>
      fun j : Fin m => x ⟨t + j, Finset.mem_Ico.mpr ⟨by omega, by have := j.isLt; omega⟩⟩) :=
    measurable_pi_lambda _ (fun j => measurable_pi_apply _)
  exact indepFun_pair_left_prod
    (measurable_pi_lambda _ (fun s : Fin t => measurable_pi_apply (s : ℕ)))
    (measurable_pi_lambda _ (fun j : Fin m => measurable_pi_apply (t + j))) (hb.comp hl hr)

theorem rows_independent {n : ℕ} (mean : Fin n → ℝ) :
    iIndepFun (fun t (ω : SampleSpace n) => ω.2 t) (sampleLawOfMeans mean) := by
  have hlaw (t : ℕ) : HasLaw (fun ω : SampleSpace n => ω.2 t)
      (Measure.pi (fun i => gaussianReal (mean i) 1)) (sampleLawOfMeans mean) := by
    have hp := (measurePreserving_eval_infinitePi
      (fun _ : ℕ => Measure.pi (fun i => gaussianReal (mean i) 1)) t).comp
        (measurePreserving_snd (μ := seedLaw) (ν := rewardLaw mean))
    exact ⟨hp.measurable.aemeasurable, hp.map_eq⟩
  apply (iIndepFun_iff_hasLaw_Pi_infinitePi hlaw (by fun_prop)).mpr
  exact ⟨measurable_snd.aemeasurable, measurePreserving_snd.map_eq⟩

theorem observations_independent {n m : ℕ} (mean : Fin n → ℝ) (i : Fin n) (t : ℕ) :
    iIndepFun (fun j : Fin m => fun ω : SampleSpace n => ω.2 (t + j) i)
      (sampleLawOfMeans mean) := by
  have hinj : Function.Injective (fun j : Fin m => t + (j : ℕ)) := by
    intro j k h
    exact Fin.ext (Nat.add_left_cancel h)
  exact ((rows_independent mean).precomp hinj).comp
    (fun _ row => row i) (fun _ => measurable_pi_apply i)

end GapEntropy.GaussianBlocks
