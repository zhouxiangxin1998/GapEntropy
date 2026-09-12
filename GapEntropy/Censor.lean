import GapEntropy.SamplingCounts

/-!
# An actual policy capped at a designated arm

Before requesting observation number `B + 1` from `tag`, the censored policy
returns `tag`. All other policy decisions and observed rewards are unchanged.
The simulation and count statements below concern `Model.run` itself.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GapEntropy

def historyArmCount {n t : ℕ} (tag : Fin n) (h : History n t) : ℕ :=
  ∑ s : Fin t, if (h s).1 = tag then 1 else 0

theorem measurable_historyArmCount {n t : ℕ} (tag : Fin n) :
    Measurable (historyArmCount (t := t) tag) := by
  apply Finset.measurable_fun_sum
  intro s _
  exact Measurable.ite ((measurable_fst.comp (measurable_pi_apply s)).eq_const tag).setOf
    measurable_const measurable_const

@[simp] theorem historyArmCount_zero {n : ℕ} (tag : Fin n) (h : History n 0) :
    historyArmCount tag h = 0 := by simp [historyArmCount]

theorem historyArmCount_snoc {n t : ℕ} (tag : Fin n) (h : History n t) (o : Observation n) :
    historyArmCount tag (Fin.snoc h o) = historyArmCount tag h + if o.1 = tag then 1 else 0 := by
  unfold historyArmCount
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

namespace Policy

variable {n : ℕ} (A : Policy n)

def requestCountNat (hn : 2 ≤ n) (T : ℕ) (tag : Fin n) (ω : SampleSpace n) : ℕ :=
  ∑ t ∈ Finset.range T, if A.requestedArm hn t ω = some tag then 1 else 0

@[simp] theorem requestCountNat_zero (hn : 2 ≤ n) (tag : Fin n) (ω : SampleSpace n) :
    A.requestCountNat hn 0 tag ω = 0 := by simp [requestCountNat]

theorem requestCountNat_succ (hn : 2 ≤ n) (T : ℕ) (tag : Fin n) (ω : SampleSpace n) :
    A.requestCountNat hn (T + 1) tag ω = A.requestCountNat hn T tag ω +
      if A.requestedArm hn T ω = some tag then 1 else 0 := by
  unfold requestCountNat
  rw [Finset.sum_range_succ]

theorem requestCountNat_le_succ (hn : 2 ≤ n) (T : ℕ) (tag : Fin n) (ω : SampleSpace n) :
    A.requestCountNat hn T tag ω ≤ A.requestCountNat hn (T + 1) tag ω := by
  rw [A.requestCountNat_succ]
  exact Nat.le_add_right _ _

theorem cast_requestCountNat (hn : 2 ≤ n) (T : ℕ) (tag : Fin n) (ω : SampleSpace n) :
    (A.requestCountNat hn T tag ω : ℝ≥0∞) = A.truncatedArmSamples hn T tag ω := by
  simp [requestCountNat, truncatedArmSamples]

/-- Active histories contain precisely the observations already requested. -/
theorem historyArmCount_eq_requestCountNat (hn : 2 ≤ n) (ω : SampleSpace n) (T : ℕ)
    (tag : Fin n) (h : History n T) (hr : A.run hn ω T = .inr h) :
    historyArmCount tag h = A.requestCountNat hn T tag ω := by
  induction T with
  | zero => simp
  | succ T ih =>
      cases hp : A.run hn ω T with
      | inl j => simp [run_succ, step, hp] at hr
      | inr hist =>
          cases hd : A.choose hn T (ω.1, hist) with
          | inl j =>
              have hh : Fin.snoc hist (j, ω.2 T j) = h := by
                simpa [run_succ, step, hp, hd] using hr
              subst h
              rw [historyArmCount_snoc, A.requestCountNat_succ, ← ih hist hp]
              simp [requestedArm, hp, hd]
          | inr j => simp [run_succ, step, hp, hd] at hr

/-- A genuine policy transformation, without access to the unknown means. -/
def censor (tag : Fin n) (B : ℕ) : Policy n where
  choose hn t p := if A.choose hn t p = .inl tag ∧ B ≤ historyArmCount tag p.2
    then .inr tag else A.choose hn t p
  measurable_choose hn t := by
    apply Measurable.ite _ measurable_const (A.measurable_choose hn t)
    apply MeasurableSet.inter (((A.measurable_choose hn t).eq_const (.inl tag)).setOf)
    have hm : Measurable (fun p : Seed × History n t => historyArmCount tag p.2) :=
      (measurable_historyArmCount tag).comp measurable_snd
    exact (measurable_const.le' hm).setOf

theorem censor_run_eq_or_tag (hn : 2 ≤ n) (tag : Fin n) (B T : ℕ) (ω : SampleSpace n) :
    (A.censor tag B).run hn ω T = A.run hn ω T ∨
      (A.censor tag B).run hn ω T = .inl tag := by
  induction T with
  | zero => exact Or.inl rfl
  | succ T ih =>
      rcases ih with heq | htag
      · cases hp : A.run hn ω T with
        | inl j => exact Or.inl (by simp [run_succ, step, heq, hp])
        | inr h =>
            by_cases hc : A.choose hn T (ω.1, h) = .inl tag ∧ B ≤ historyArmCount tag h
            · apply Or.inr
              rw [run_succ, heq, hp]
              simp [step, censor, hc]
            · apply Or.inl
              rw [run_succ, run_succ, heq, hp]
              simp [step, censor, hc]
      · exact Or.inr (by simp [run_succ, step, htag])

theorem censor_return_ne_tag_imp_original (hn : 2 ≤ n) (tag j : Fin n) (B T : ℕ)
    (ω : SampleSpace n) (hj : j ≠ tag)
    (hr : (A.censor tag B).returnedAt hn T ω = some j) :
    A.returnedAt hn T ω = some j := by
  rcases A.censor_run_eq_or_tag hn tag B T ω with heq | htag
  · simpa only [returnedAt, heq] using hr
  · simp [returnedAt, htag, hj.symm] at hr

theorem censor_choose_tag_count_lt (hn : 2 ≤ n) (tag : Fin n) (B t : ℕ)
    (p : Seed × History n t) (hd : (A.censor tag B).choose hn t p = .inl tag) :
    historyArmCount tag p.2 < B := by
  change (if A.choose hn t p = .inl tag ∧ B ≤ historyArmCount tag p.2
    then .inr tag else A.choose hn t p) = .inl tag at hd
  split_ifs at hd with hc
  have hh : ¬ B ≤ historyArmCount tag p.2 := fun hge => hc ⟨hd, hge⟩
  omega

theorem censor_request_tag_count_lt (hn : 2 ≤ n) (tag : Fin n) (B t : ℕ)
    (ω : SampleSpace n) (hreq : (A.censor tag B).requestedArm hn t ω = some tag) :
    (A.censor tag B).requestCountNat hn t tag ω < B := by
  cases hr : (A.censor tag B).run hn ω t with
  | inl j => simp [requestedArm, hr] at hreq
  | inr h =>
      cases hd : (A.censor tag B).choose hn t (ω.1, h) with
      | inl j =>
          have hj : j = tag := by simpa [requestedArm, hr, hd] using hreq
          subst j
          rw [← (A.censor tag B).historyArmCount_eq_requestCountNat hn ω t tag h hr]
          exact A.censor_choose_tag_count_lt hn tag B t (ω.1, h) hd
      | inr j => simp [requestedArm, hr, hd] at hreq

theorem censor_requestCountNat_le (hn : 2 ≤ n) (tag : Fin n) (B T : ℕ)
    (ω : SampleSpace n) : (A.censor tag B).requestCountNat hn T tag ω ≤ B := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [requestCountNat_succ]
      by_cases hreq : (A.censor tag B).requestedArm hn T ω = some tag
      · rw [if_pos hreq]
        have hlt := A.censor_request_tag_count_lt hn tag B T ω hreq
        omega
      · simpa only [if_neg hreq, Nat.add_zero] using ih

/-- Any finite original execution whose designated count stays within the cap
is reproduced exactly on the same seed and reward table. -/
theorem censor_run_eq_of_count_le (hn : 2 ≤ n) (tag : Fin n) (B T : ℕ)
    (ω : SampleSpace n) (hcount : A.requestCountNat hn T tag ω ≤ B) :
    (A.censor tag B).run hn ω T = A.run hn ω T := by
  induction T with
  | zero => rfl
  | succ T ih =>
      have heq := ih ((A.requestCountNat_le_succ hn T tag ω).trans hcount)
      cases hp : A.run hn ω T with
      | inl j => simp [run_succ, step, heq, hp]
      | inr h =>
          have hc : ¬ (A.choose hn T (ω.1, h) = .inl tag ∧ B ≤ historyArmCount tag h) := by
            rintro ⟨hd, hb⟩
            rw [A.historyArmCount_eq_requestCountNat hn ω T tag h hp] at hb
            have hreq : A.requestedArm hn T ω = some tag := by simp [requestedArm, hp, hd]
            rw [A.requestCountNat_succ, if_pos hreq] at hcount
            omega
          rw [run_succ, run_succ, heq, hp]
          simp [step, censor, hc]

theorem armSamples_eq_iSup_truncatedArmSamples (hn : 2 ≤ n) (tag : Fin n)
    (ω : SampleSpace n) :
    A.armSamples hn tag ω = ⨆ T, A.truncatedArmSamples hn T tag ω :=
  ENNReal.tsum_eq_iSup_nat

theorem censor_truncatedArmSamples_le (hn : 2 ≤ n) (tag : Fin n) (B T : ℕ)
    (ω : SampleSpace n) : (A.censor tag B).truncatedArmSamples hn T tag ω ≤ B := by
  rw [← cast_requestCountNat]
  exact_mod_cast A.censor_requestCountNat_le hn tag B T ω

/-- The cap bounds the full designated-arm count on every sample path. -/
theorem censor_armSamples_le (hn : 2 ≤ n) (tag : Fin n) (B : ℕ)
    (ω : SampleSpace n) : (A.censor tag B).armSamples hn tag ω ≤ B := by
  rw [armSamples_eq_iSup_truncatedArmSamples]
  exact iSup_le (fun T => A.censor_truncatedArmSamples_le hn tag B T ω)

theorem censor_run_eq_of_armSamples_le (hn : 2 ≤ n) (tag : Fin n) (B T : ℕ)
    (ω : SampleSpace n) (hcount : A.armSamples hn tag ω ≤ B) :
    (A.censor tag B).run hn ω T = A.run hn ω T := by
  apply A.censor_run_eq_of_count_le
  have ht := (A.truncatedArmSamples_le_armSamples hn T tag ω).trans hcount
  rw [← A.cast_requestCountNat] at ht
  exact_mod_cast ht

theorem censor_returns_ne_tag_imp_original (hn : 2 ≤ n) (tag j : Fin n) (B : ℕ)
    (ω : SampleSpace n) (hj : j ≠ tag)
    (hr : ∃ T, (A.censor tag B).returnedAt hn T ω = some j) :
    ∃ T, A.returnedAt hn T ω = some j := by
  obtain ⟨T, hT⟩ := hr
  exact ⟨T, A.censor_return_ne_tag_imp_original hn tag j B T ω hj hT⟩

/-- Any finite return of the original policy is preserved when its total
designated-arm count lies within the cap. -/
theorem censor_preserves_returns_of_count_le (hn : 2 ≤ n) (tag j : Fin n) (B : ℕ)
    (ω : SampleSpace n) (hcount : A.armSamples hn tag ω ≤ B)
    (hr : ∃ T, A.returnedAt hn T ω = some j) :
    ∃ T, (A.censor tag B).returnedAt hn T ω = some j := by
  obtain ⟨T, hT⟩ := hr
  refine ⟨T, ?_⟩
  simpa only [returnedAt, A.censor_run_eq_of_armSamples_le hn tag B T ω hcount] using hT

theorem censor_choose_sample_imp_original (hn : 2 ≤ n) (tag i : Fin n) (B t : ℕ)
    (p : Seed × History n t) (hd : (A.censor tag B).choose hn t p = .inl i) :
    A.choose hn t p = .inl i := by
  change (if A.choose hn t p = .inl tag ∧ B ≤ historyArmCount tag p.2
    then .inr tag else A.choose hn t p) = .inl i at hd
  split_ifs at hd
  exact hd

/-- Every censored request is an actual request by the original policy at the
same global time, on the same seed and reward table. -/
theorem censor_request_imp_original (hn : 2 ≤ n) (tag i : Fin n) (B t : ℕ)
    (ω : SampleSpace n) (hreq : (A.censor tag B).requestedArm hn t ω = some i) :
    A.requestedArm hn t ω = some i := by
  rcases A.censor_run_eq_or_tag hn tag B t ω with heq | htag
  · cases hp : A.run hn ω t with
    | inl j => simp [requestedArm, heq, hp] at hreq
    | inr h =>
        cases hd : (A.censor tag B).choose hn t (ω.1, h) with
        | inl j =>
            have hj : j = i := by simpa [requestedArm, heq, hp, hd] using hreq
            subst j
            have ho := A.censor_choose_sample_imp_original hn tag i B t (ω.1, h) hd
            simp [requestedArm, hp, ho]
        | inr j => simp [requestedArm, heq, hp, hd] at hreq
  · simp [requestedArm, htag] at hreq

theorem censor_armSamples_le_original (hn : 2 ≤ n) (tag i : Fin n) (B : ℕ)
    (ω : SampleSpace n) : (A.censor tag B).armSamples hn i ω ≤ A.armSamples hn i ω := by
  apply ENNReal.tsum_le_tsum
  intro t
  by_cases hreq : (A.censor tag B).requestedArm hn t ω = some i
  · simp [hreq, A.censor_request_imp_original hn tag i B t ω hreq]
  · simp [hreq]

theorem lintegral_censor_armSamples_le_cap (hn : 2 ≤ n) (tag : Fin n) (B : ℕ)
    (μ : Measure (SampleSpace n)) [IsProbabilityMeasure μ] :
    ∫⁻ ω, (A.censor tag B).armSamples hn tag ω ∂μ ≤ B := by
  calc
    _ ≤ ∫⁻ _ω, (B : ℝ≥0∞) ∂μ := lintegral_mono (A.censor_armSamples_le hn tag B)
    _ = B := by simp

end Policy
end GapEntropy
