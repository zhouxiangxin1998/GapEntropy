import Mathlib.Probability.Independence.Basic

/-!
# Independence of a fresh coordinate from finitely many earlier ones

On a product space with independent coordinates, a measurable function that depends only on the
coordinates in a finite set `s` is independent of any coordinate outside `s`. The dependence
hypothesis is pointwise agreement, and the proof factors the function through the measurable
`fill` map that reads the coordinates in `s` and takes a fixed base value elsewhere.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace GapEntropy.FiniteFreshness

def fill {ι : Type*} {X : ι → Type*} (base : ∀ i, X i) (s : Finset ι)
    (history : ∀ i : s, X i) (i : ι) : X i := by
  classical
  exact if hi : i ∈ s then history ⟨i, hi⟩ else base i

theorem fill_measurable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (base : ∀ i, X i) (s : Finset ι) : Measurable (fill base s) := by
  classical
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ s
  · simpa only [fill, dif_pos hi] using (measurable_pi_apply (⟨i, hi⟩ : s))
  · simpa only [fill, dif_neg hi] using (measurable_const : Measurable (fun _ : (∀ j : s, X j) => base i))

/-- A measurable function of finitely many previous independent coordinates is
independent of a fresh coordinate. Dependence is proved by pointwise agreement. -/
theorem indep_of_finite_dependence {ι : Type*} {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] {A : Type*} [MeasurableSpace A]
    {P : Measure (∀ i, X i)} (hind : iIndepFun (fun i (ω : ∀ i, X i) => ω i) P)
    (base : ∀ i, X i) {F : (∀ i, X i) → A} (hF : Measurable F)
    (s : Finset ι) (i : ι) (hi : i ∉ s)
    (hdep : ∀ ω ω', (∀ j ∈ s, ω j = ω' j) → F ω = F ω') :
    IndepFun F (fun ω => ω i) P := by
  classical
  have hdis : Disjoint s {i} := Finset.disjoint_singleton_right.mpr hi
  have h := hind.indepFun_finset s {i} hdis (fun j => measurable_pi_apply j)
  have hc := h.comp (hF.comp (fill_measurable base s))
    (measurable_pi_apply (⟨i, Finset.mem_singleton_self i⟩ : ({i} : Finset ι)))
  change IndepFun (fun ω => F (fill base s (fun j => ω j))) (fun ω => ω i) P at hc
  have heq : (fun ω => F (fill base s (fun j => ω j))) = F := by
    funext ω
    apply hdep
    intro j hj
    simp only [fill, dif_pos hj]
  rw [heq] at hc
  exact hc

end GapEntropy.FiniteFreshness
