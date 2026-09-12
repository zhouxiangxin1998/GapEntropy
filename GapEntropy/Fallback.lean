import GapEntropy.Freshness
import GapEntropy.ReturnedCounts
import GapEntropy.Gaussian

/-!
# The operational cumulative-doubling Gaussian fallback

This is the policy in manuscript C.2. The potential schedule samples arm `t mod n`
at global sample time `t`; round `r` is tested after `n * 2^r` observations.
The policy reads only its observed history. On every still-active execution that
history is exactly the corresponding prefix of the original reward table.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Classical

namespace GapEntropy.Fallback

def roundSamples (r : ℕ) : ℕ := 2 ^ r

def roundTime (n r : ℕ) : ℕ := n * roundSamples r

def radius (n : ℕ) (δ : ℝ) (r : ℕ) : ℝ :=
  Real.sqrt ((2 / (roundSamples r : ℝ)) *
    Real.log (8 * (n : ℝ) * ((r : ℝ) + 1)^2 / δ))

def schedule {n : ℕ} (hn : 2 ≤ n) (t : ℕ) : Fin n :=
  ⟨t % n, Nat.mod_lt t (by omega)⟩

def roundAt (n t : ℕ) : Option ℕ :=
  if h : ∃ r, t = roundTime n r then some (Nat.find h) else none

theorem roundAt_spec {n t r : ℕ} (hr : roundAt n t = some r) : t = roundTime n r := by
  unfold roundAt at hr
  split_ifs at hr with h
  have he : Nat.find h = r := Option.some.inj hr
  exact he ▸ Nat.find_spec h

theorem roundTime_injective {n : ℕ} (hn : 2 ≤ n) : Function.Injective (roundTime n) := by
  intro r s hrs
  have hp : 2 ^ r = 2 ^ s := Nat.eq_of_mul_eq_mul_left (by omega) hrs
  exact Nat.pow_right_injective (by norm_num : 2 ≤ (2 : ℕ)) hp

@[simp] theorem roundAt_roundTime {n : ℕ} (hn : 2 ≤ n) (r : ℕ) :
    roundAt n (roundTime n r) = some r := by
  have hex : ∃ s, roundTime n r = roundTime n s := ⟨r, rfl⟩
  simp only [roundAt, dif_pos hex]
  congr 1
  exact ((roundTime_injective hn) (Nat.find_spec hex)).symm

def historyReward {n t : ℕ} (h : History n t) (s : ℕ) : ℝ :=
  if hs : s < t then (h ⟨s, hs⟩).2 else 0

theorem measurable_historyReward {n t : ℕ} (s : ℕ) :
    Measurable (fun h : History n t => historyReward h s) := by
  unfold historyReward
  split_ifs with hs
  · exact measurable_snd.comp (measurable_pi_apply (⟨s, hs⟩ : Fin t))
  · exact measurable_const

def historyMean {n t : ℕ} (r : ℕ) (h : History n t) (i : Fin n) : ℝ :=
  (∑ k : Fin (roundSamples r), historyReward h (n * k + i)) / (roundSamples r : ℝ)

theorem measurable_historyMean {n t : ℕ} (r : ℕ) (i : Fin n) :
    Measurable (fun h : History n t => historyMean r h i) := by
  unfold historyMean
  exact (Finset.measurable_fun_sum _ (fun k _ => measurable_historyReward _)).div_const _

def separated {n : ℕ} (x : Fin n → ℝ) (ρ : ℝ) (i : Fin n) : Prop :=
  ∀ j, j ≠ i → x j + ρ < x i - ρ

def flags {n : ℕ} (x : Fin n → ℝ) (ρ : ℝ) : Fin n → Bool :=
  fun i => decide (separated x ρ i)

def winner {n : ℕ} (b : Fin n → Bool) : Option (Fin n) :=
  if h : ∃ i, b i = true then some (Classical.choose h) else none

theorem winner_spec {n : ℕ} {b : Fin n → Bool} {i : Fin n} (hi : winner b = some i) :
    b i = true := by
  unfold winner at hi
  split_ifs at hi with h
  have he := Option.some.inj hi
  exact he ▸ Classical.choose_spec h

theorem winner_ne_none {n : ℕ} {b : Fin n → Bool} (h : ∃ i, b i = true) : winner b ≠ none := by
  simp [winner, h]

theorem measurable_flags_history {n t : ℕ} (r : ℕ) (ρ : ℝ) :
    Measurable (fun h : History n t => flags (historyMean r h) ρ) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_to_bool
  change MeasurableSet {h : History n t | decide (separated (historyMean r h) ρ i) = true}
  simp only [decide_eq_true_eq]
  apply (Measurable.forall fun j => measurable_const.imp ?_).setOf
  exact measurableSet_setOfPred.mp
    (measurableSet_lt ((measurable_historyMean r j).add_const ρ)
      ((measurable_historyMean r i).sub_const ρ))

def roundDecision {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (t r : ℕ) (h : History n t) : Decision n :=
  (winner (flags (historyMean r h) (radius n δ r))).elim (.inl (schedule hn t)) Sum.inr

theorem measurable_roundDecision {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (t r : ℕ) :
    Measurable (roundDecision hn δ t r) := by
  exact (measurable_of_finite (fun b : Fin n → Bool =>
    (winner b).elim (.inl (schedule hn t)) Sum.inr)).comp (measurable_flags_history r _)

/-- The fallback is an actual nonanticipating policy, with no instance input. -/
def policy (n : ℕ) (δ : ℝ) : Policy n where
  choose hn t p := (roundAt n t).elim (.inl (schedule hn t))
    (fun r => roundDecision hn δ t r p.2)
  measurable_choose hn t := by
    cases roundAt n t with
    | none => exact measurable_const
    | some r => exact (measurable_roundDecision hn δ t r).comp measurable_snd

theorem choose_sample_eq_schedule {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (t : ℕ)
    (p : Seed × History n t) (i : Fin n) (hi : (policy n δ).choose hn t p = .inl i) :
    i = schedule hn t := by
  cases hr : roundAt n t with
  | none => simpa [policy, hr] using hi.symm
  | some r =>
      cases hw : winner (flags (historyMean r p.2) (radius n δ r)) with
      | none => simpa [policy, hr, roundDecision, hw] using hi.symm
      | some j => simp [policy, hr, roundDecision, hw] at hi

theorem choose_return_spec {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (t : ℕ)
    (p : Seed × History n t) (i : Fin n) (hi : (policy n δ).choose hn t p = .inr i) :
    ∃ r, t = roundTime n r ∧ separated (historyMean r p.2) (radius n δ r) i := by
  cases hr : roundAt n t with
  | none => simp [policy, hr] at hi
  | some r =>
      refine ⟨r, roundAt_spec hr, ?_⟩
      cases hw : winner (flags (historyMean r p.2) (radius n δ r)) with
      | none => simp [policy, hr, roundDecision, hw] at hi
      | some j =>
          have hji : j = i := by simpa [policy, hr, roundDecision, hw] using hi
          subst j
          simpa [flags] using winner_spec hw

def canonicalHistory {n : ℕ} (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) : History n t :=
  fun s => (schedule hn s, ω.2 s (schedule hn s))

theorem canonicalHistory_snoc {n : ℕ} (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ) :
    Fin.snoc (canonicalHistory hn ω t) (schedule hn t, ω.2 t (schedule hn t)) =
      canonicalHistory hn ω (t + 1) := by
  funext s
  refine Fin.lastCases ?_ (fun j => ?_) s
  · simp [canonicalHistory]
  · simp [canonicalHistory]

/-- Every active execution has exactly the deterministic scheduled history. -/
theorem active_history_eq_canonical {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (ω : SampleSpace n)
    (t : ℕ) (h : History n t) (hr : (policy n δ).run hn ω t = .inr h) :
    h = canonicalHistory hn ω t := by
  induction t with
  | zero => exact Subsingleton.elim _ _
  | succ t ih =>
      cases hp : (policy n δ).run hn ω t with
      | inl i => simp [Policy.run_succ, Policy.step, hp] at hr
      | inr hist =>
          cases hd : (policy n δ).choose hn t (ω.1, hist) with
          | inl i =>
              have hi := choose_sample_eq_schedule hn δ t (ω.1, hist) i hd
              have hh : Fin.snoc hist (i, ω.2 t i) = h := by
                simpa [Policy.run_succ, Policy.step, hp, hd] using hr
              rw [← hh, hi, ih hist hp]
              exact canonicalHistory_snoc hn ω t
          | inr i => simp [Policy.run_succ, Policy.step, hp, hd] at hr

theorem schedule_arm_time {n : ℕ} (hn : 2 ≤ n) (k : ℕ) (i : Fin n) :
    schedule hn (n * k + i) = i := by
  apply Fin.ext
  simp [schedule, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

theorem arm_time_lt_roundTime {n : ℕ} (r : ℕ) (k : Fin (roundSamples r)) (i : Fin n) :
    n * (k : ℕ) + i < roundTime n r := by
  calc
    n * (k : ℕ) + i < n * (k : ℕ) + n := Nat.add_lt_add_left i.isLt _
    _ = n * ((k : ℕ) + 1) := by ring
    _ ≤ roundTime n r := Nat.mul_le_mul_left n k.isLt

/-- The potential cumulative empirical means use the original reward table. -/
def empiricalMean {n : ℕ} (r : ℕ) (i : Fin n) (ω : SampleSpace n) : ℝ :=
  (∑ k : Fin (roundSamples r), ω.2 (n * k + i) i) / (roundSamples r : ℝ)

theorem historyMean_canonical {n : ℕ} (hn : 2 ≤ n) (r : ℕ) (i : Fin n) (ω : SampleSpace n) :
    historyMean r (canonicalHistory hn ω (roundTime n r)) i = empiricalMean r i ω := by
  unfold historyMean empiricalMean
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  simp [historyReward, arm_time_lt_roundTime r k i, canonicalHistory, schedule_arm_time]

theorem active_round_empiricalMean {n : ℕ} (hn : 2 ≤ n) (δ : ℝ) (r : ℕ)
    (i : Fin n) (ω : SampleSpace n) (h : History n (roundTime n r))
    (hr : (policy n δ).run hn ω (roundTime n r) = .inr h) :
    historyMean r h i = empiricalMean r i ω := by
  rw [active_history_eq_canonical hn δ ω _ h hr]
  exact historyMean_canonical hn r i ω

theorem measurable_empiricalMean {n : ℕ} (r : ℕ) (i : Fin n) :
    Measurable (empiricalMean r i) := by
  unfold empiricalMean
  fun_prop

/-- Every actual finite return comes from a separated interval at a tested round. -/
theorem returned_implies_empirical_separation {n : ℕ} (hn : 2 ≤ n) (δ : ℝ)
    (ω : SampleSpace n) (T : ℕ) (i : Fin n)
    (hret : (policy n δ).returnedAt hn T ω = some i) :
    ∃ r, separated (fun j => empiricalMean r j ω) (radius n δ r) i := by
  induction T with
  | zero => simp [Policy.returnedAt, Policy.run_zero] at hret
  | succ T ih =>
      cases hp : (policy n δ).run hn ω T with
      | inl j =>
          have hji : j = i := by simpa [Policy.returnedAt, Policy.run_succ, Policy.step, hp] using hret
          subst j
          exact ih (by simp [Policy.returnedAt, hp])
      | inr h =>
          cases hd : (policy n δ).choose hn T (ω.1, h) with
          | inl j => simp [Policy.returnedAt, Policy.run_succ, Policy.step, hp, hd] at hret
          | inr j =>
              have hji : j = i := by simpa [Policy.returnedAt, Policy.run_succ, Policy.step, hp, hd] using hret
              subst j
              obtain ⟨r, hr, hsep⟩ := choose_return_spec hn δ T (ω.1, h) i hd
              subst T
              refine ⟨r, ?_⟩
              have he : historyMean r h = fun j => empiricalMean r j ω := by
                funext j
                exact active_round_empiricalMean hn δ r j ω h hp
              rwa [he] at hsep

theorem separated_eq_best_of_intervals {n : ℕ} (I : Instance n)
    (x : Fin n → ℝ) (ρ : ℝ) (i : Fin n)
    (hgood : ∀ j, |x j - I.mean j| ≤ ρ) (hsep : separated x ρ i) : i = I.best := by
  by_contra hi
  have hs := hsep I.best (Ne.symm hi)
  have hb := (abs_le.mp (hgood I.best)).1
  have hj := (abs_le.mp (hgood i)).2
  have hu := I.best_unique i hi
  linarith

/-- Correctness on the simultaneous confidence event; termination is separate. -/
theorem returned_eq_best_on_good_intervals {n : ℕ} (I : Instance n) (δ : ℝ)
    (ω : SampleSpace n)
    (hgood : ∀ r i, |empiricalMean r i ω - I.mean i| ≤ radius n δ r)
    (T : ℕ) (i : Fin n) (hret : (policy n δ).returnedAt I.two_le T ω = some i) : i = I.best := by
  obtain ⟨r, hr⟩ := returned_implies_empirical_separation I.two_le δ ω T i hret
  exact separated_eq_best_of_intervals I _ _ i (hgood r) hr

theorem returns_by_round_of_separated {n : ℕ} (hn : 2 ≤ n) (δ : ℝ)
    (ω : SampleSpace n) (r : ℕ)
    (hsep : ∃ i, separated (fun j => empiricalMean r j ω) (radius n δ r) i) :
    ∃ i, (policy n δ).returnedAt hn (roundTime n r + 1) ω = some i := by
  cases hp : (policy n δ).run hn ω (roundTime n r) with
  | inl i => exact ⟨i, by simp [Policy.returnedAt, Policy.run_succ, Policy.step, hp]⟩
  | inr h =>
      have he : historyMean r h = fun j => empiricalMean r j ω := by
        funext j
        exact active_round_empiricalMean hn δ r j ω h hp
      have hex : ∃ i, flags (historyMean r h) (radius n δ r) i = true := by
        simpa only [flags, decide_eq_true_eq, he] using hsep
      have hne := winner_ne_none hex
      cases hw : winner (flags (historyMean r h) (radius n δ r)) with
      | none => exact False.elim (hne hw)
      | some i =>
          refine ⟨i, ?_⟩
          rw [Policy.returnedAt, Policy.run_succ, hp]
          simp [Policy.step, policy, roundAt_roundTime hn, roundDecision, hw]

theorem separated_best_of_small_errors {n : ℕ} (I : Instance n)
    (x : Fin n → ℝ) {g ρ : ℝ} (hg : 0 < g)
    (hgap : ∀ j, j ≠ I.best → g ≤ I.gap j)
    (hρ : ρ ≤ g / 8) (herr : ∀ j, |x j - I.mean j| ≤ g / 8) :
    separated x ρ I.best := by
  intro j hj
  have hb := (abs_le.mp (herr I.best)).1
  have he := (abs_le.mp (herr j)).2
  have hd := hgap j hj
  unfold Instance.gap at hd
  linarith

/-- Failure to stop by a sufficiently accurate round forces a large empirical
error in the fixed potential samples of that same round. -/
theorem not_returned_by_round_imp_error {n : ℕ} (I : Instance n) (δ : ℝ)
    (ω : SampleSpace n) (r : ℕ) {g : ℝ} (hg : 0 < g)
    (hgap : ∀ j, j ≠ I.best → g ≤ I.gap j) (hρ : radius n δ r ≤ g / 8)
    (hnot : ¬ ∃ i, (policy n δ).returnedAt I.two_le (roundTime n r + 1) ω = some i) :
    ∃ i, g / 8 < |empiricalMean r i ω - I.mean i| := by
  by_contra! he
  apply hnot
  apply returns_by_round_of_separated
  exact ⟨I.best, separated_best_of_small_errors I _ hg hgap hρ he⟩

end GapEntropy.Fallback
