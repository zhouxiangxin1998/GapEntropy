import GapEntropy.PredictableBernoulli

/-! Identification of finite conditional laws by a countable past partition. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace GapEntropy

/-- Exact event factorization on each past-measurable partition cell identifies the complete
conditional law. Applications below prove the factorization from the actual Gaussian table. -/
theorem conditionalLaw_of_countable_partition
    {Ω κ α : Type*} [mΩ : MeasurableSpace Ω]
    [Countable κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]
    [MeasurableSpace α] [MeasurableSingletonClass α] [DecidableEq α]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    (choice : Ω → κ) (hchoice : Measurable[m] choice) (X : Ω → α) (hX : Measurable[mΩ] X)
    (laws : κ → Measure α) [∀ k, IsProbabilityMeasure (laws k)]
    (hfactor : ∀ R, MeasurableSet[m] R → ∀ k x,
      μ.real ({ω | ω ∈ R ∧ choice ω = k} ∩ {ω | X ω = x}) =
        μ.real {ω | ω ∈ R ∧ choice ω = k} * (laws k).real {x}) :
    ∀ x, μ[fun ω => if X ω = x then (1 : ℝ) else 0 | m] =ᵐ[μ]
      fun ω => (laws (choice ω)).real {x} := by
  classical
  have hchoice' : Measurable[mΩ] choice := hchoice.mono hm le_rfl
  intro x
  let f : Ω → ℝ := {ω | X ω = x}.indicator (fun _ => 1)
  let q : κ → ℝ := fun k => (laws k).real {x}
  let g : Ω → ℝ := fun ω => q (choice ω)
  have hq0 (k : κ) : 0 ≤ q k := measureReal_nonneg
  have hq1 (k : κ) : q k ≤ 1 := measureReal_le_one
  have hgm : Measurable[m] g := (measurable_of_countable q).comp hchoice
  have hgint : Integrable g μ := (integrable_const (1 : ℝ)).mono'
    (hgm.mono hm le_rfl).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 (choice ω))]
      exact hq1 (choice ω))
  have hfmeas : MeasurableSet[mΩ] {ω | X ω = x} := hX (measurableSet_singleton x)
  have hfint : Integrable f μ := (integrable_const (1 : ℝ)).indicator hfmeas
  have hce : g =ᵐ[μ] μ[f | m] := by
    apply ae_eq_condExp_of_forall_setIntegral_eq hm hfint
      (fun _ _ _ => hgint.integrableOn) _ hgm.aestronglyMeasurable
    intro R hR _
    let part : κ → Set Ω := fun k => {ω | ω ∈ R ∧ choice ω = k}
    have hpart (k : κ) : MeasurableSet[mΩ] (part k) :=
      (hm _ hR).inter (hchoice' (measurableSet_singleton k))
    have hdis : Pairwise (Function.onFun Disjoint part) := by
      intro k l hkl
      apply Set.disjoint_left.mpr
      intro ω hk hl
      exact hkl (hk.2.symm.trans hl.2)
    have hunion : (⋃ k, part k) = R := by ext ω; simp [part]
    have hpartEq (k : κ) : (∫ ω in part k, g ω ∂μ) = ∫ ω in part k, f ω ∂μ := by
      calc
        (∫ ω in part k, g ω ∂μ) = ∫ _ω in part k, q k ∂μ :=
          setIntegral_congr_fun (hpart k) fun ω hω => by simp only [g, hω.2]
        _ = μ.real (part k) * q k := by rw [setIntegral_const, smul_eq_mul]
        _ = μ.real (part k ∩ {ω | X ω = x}) := (hfactor R hR k x).symm
        _ = ∫ ω in part k, f ω ∂μ := by
          dsimp only [f]
          rw [setIntegral_indicator hfmeas, setIntegral_const, smul_eq_mul, mul_one]
    rw [← hunion, integral_iUnion hpart hdis hgint.integrableOn,
      integral_iUnion hpart hdis hfint.integrableOn]
    exact tsum_congr hpartEq
  have hef : f = (fun ω => if X ω = x then (1 : ℝ) else 0) := by
    funext ω
    by_cases hx : X ω = x <;> simp [f, hx]
  rw [hef] at hce
  exact hce.symm

end GapEntropy
