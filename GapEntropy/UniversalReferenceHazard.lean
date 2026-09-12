import GapEntropy.UniversalReferenceFailure
import GapEntropy.UniversalPathCounting

/-! Pathwise reference confidence budgets for actual accepted entries. -/
noncomputable section
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace GapEntropy.UniversalAttempt
open FiniteCallProgram UniversalCall UniversalErrorBudget
variable {n : ℕ}

def referenceCharge (c : Config) : Stage n → ℝ
  | .inl _ => 0
  | .inr (a, _) => if a.Allowed c ∧ a.entry = true then a.beta c else 0

theorem measurable_referenceCharge (c : Config) : Measurable (referenceCharge (n := n) c) := by
  apply measurable_fun_sum
  · exact measurable_const
  · exact measurable_from_prod_countable_right (fun _ => measurable_const)

theorem referenceCharge_nonneg (c : Config) (hδ : 0 ≤ c.confidence) (st : Stage n) :
    0 ≤ referenceCharge c st := by
  cases st with
  | inl result => exact le_rfl
  | inr state =>
      rcases state with ⟨a, z⟩
      simp only [referenceCharge]
      split_ifs
      · exact referenceConfidence_nonneg hδ _ _
      · exact le_rfl

theorem stage_reference_sum_le (c : Config) (hδ : 0 ≤ c.confidence) (x : Values n) (T : ℕ) :
    (∑ r ∈ Finset.range T, referenceCharge c (stage c x r)) ≤ c.confidence / 16 := by
  let e := (pendingCalls c x T).filter (fun t => (metadataAt c x t).entry = true)
  let g := fun t => (c.attempt, (metadataAt c x t).scale)
  let f := fun jk : ℕ × ℕ => ENNReal.ofReal (referenceConfidence c.confidence jk.1 jk.2)
  have hsum : (∑ r ∈ Finset.range T, ENNReal.ofReal (referenceCharge c (stage c x r))) ≤
      ∑ r ∈ e, f (g r) := by
    rw [Finset.sum_filter]
    simp only [pendingCalls, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro r hr
    cases hs : stage c x r with
    | inl result => simp [referenceCharge]
    | inr state =>
        obtain ⟨a, z⟩ := state
        simp only [referenceCharge, metadataAt, hs]
        by_cases ha : a.Allowed c
        · by_cases he : a.entry = true
          · simp [ha, he, f, g, metadataAt, hs, Metadata.beta, referenceConfidence, referenceError]
          · simp [ha, he]
        · simp [ha]
  have hinj : Set.InjOn g (e : Set ℕ) := by
    intro s hs t ht he
    exact entry_scale_injOn c x T hs ht (congrArg Prod.snd he)
  have hh := hsum.trans_eq (Finset.sum_image hinj).symm
  have hbound := (hh.trans (ENNReal.sum_le_tsum (e.image g))).trans (tsum_referenceConfidence_le hδ)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ => referenceCharge_nonneg c hδ (stage c x r))] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hbound

end GapEntropy.UniversalAttempt
