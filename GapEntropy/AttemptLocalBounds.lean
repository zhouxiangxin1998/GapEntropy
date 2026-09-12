import GapEntropy.AttemptExperiment
import GapEntropy.TargetNearCount

/-!
# Fixed-request A.3 failure bounds under the canonical call laws

`ValidKey` restricts loop keys to scales at most `I.lastBucket`. The declared call tolerances lie
in `(0, 1]` and, for `ε ≤ 1/10`, the call confidences lie in `(0, 1]`, as the A.3 tape theorems
require. `removalBad` is the event that the best arm is dropped from a fixed request containing
it; `targetBad` is the event that a loop call on a large set fails to halve while keeping the
best, or that a final call on at most four arms fails to return exactly the best.

Both events are measurable, and each has probability at most the declared call confidence under
the canonical call law `localLaw`. The target bound uses the near-count and final-gap bridge of
`TargetNearCount` on every relabeling `I.permute π` of the target instance.
-/

noncomputable section
open MeasureTheory

namespace GapEntropy.AttemptExperiment
open GapEntropy.TargetAttempt
variable {n : ℕ}

def ValidKey (I : Instance n) : CallKey → Prop
  | .loop k _ => k ≤ I.lastBucket
  | .final => True

theorem tolerance_pos (I : Instance n) (key : CallKey) : 0 < callTolerance I key := by
  cases key with
  | loop k _ => exact I.targetTolerance_pos k
  | final => exact I.targetTolerance_pos I.lastBucket

theorem tolerance_le_one (I : Instance n) (key : CallKey) : callTolerance I key ≤ 1 := by
  cases key with
  | loop k _ => exact I.targetTolerance_le_one k
  | final => exact I.targetTolerance_le_one I.lastBucket

theorem confidence_pos (I : Instance n) {ε : ℝ} (hε : 0 < ε) (key : CallKey) :
    0 < callConfidence I ε key := by
  cases key with
  | loop k r => exact I.callConfidence_pos hε k r
  | final => exact div_pos hε (by norm_num)

theorem confidence_le_one (I : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (key : CallKey) (hkey : ValidKey I key) : callConfidence I ε key ≤ 1 := by
  cases key with
  | loop k r => exact (I.callConfidence_le hε.le hkey r).trans (by linarith)
  | final => change ε / 2 ≤ 1; linarith

theorem rawPredicate_measurable (I J : Instance n) (ε : ℝ) (key : CallKey) (S : Finset (Fin n))
    (predicate : Finset (Fin n) → Prop) :
    MeasurableSet {ω : CallTape I ε key | predicate (rawResponse I J ε key S ω)} :=
  (rawResponse_measurable I J ε key S) (Set.toFinite {R | predicate R}).measurableSet

def removalBad (I J : Instance n) (ε : ℝ) (key : CallKey) :
    Option (Finset (Fin n)) → Set (CallTape I ε key)
  | none => ∅
  | some S => if J.best ∈ S then {ω | J.best ∉ rawResponse I J ε key S ω} else ∅

def targetBad (I J : Instance n) (ε : ℝ) :
    (key : CallKey) → Option (Finset (Fin n)) → Set (CallTape I ε key)
  | _, none => ∅
  | .loop k r, some S =>
      if J.best ∈ S ∧ 4 * I.targetCount k < S.card then
        {ω | J.best ∉ rawResponse I J ε (.loop k r) S ω ∨
          (S.card + 1) / 2 < (rawResponse I J ε (.loop k r) S ω).card}
      else ∅
  | .final, some S =>
      if J.best ∈ S ∧ S.card ≤ 4 then
        {ω | rawResponse I J ε .final S ω ≠ {J.best}}
      else ∅

theorem removalBad_measurable (I J : Instance n) (ε : ℝ) (key : CallKey)
    (state : Option (Finset (Fin n))) : MeasurableSet (removalBad I J ε key state) := by
  cases state with
  | none => exact MeasurableSet.empty
  | some S =>
    dsimp only [removalBad]
    split_ifs
    · exact rawPredicate_measurable I J ε key S (fun R => J.best ∉ R)
    · exact MeasurableSet.empty

theorem targetBad_measurable (I J : Instance n) (ε : ℝ) (key : CallKey)
    (state : Option (Finset (Fin n))) : MeasurableSet (targetBad I J ε key state) := by
  cases state with
  | none => cases key <;> exact MeasurableSet.empty
  | some S =>
    cases key with
    | loop k r =>
      dsimp only [targetBad]
      split_ifs
      · exact rawPredicate_measurable I J ε (.loop k r) S
          (fun R => J.best ∉ R ∨ (S.card + 1) / 2 < R.card)
      · exact MeasurableSet.empty
    | final =>
      dsimp only [targetBad]
      split_ifs
      · exact rawPredicate_measurable I J ε .final S (fun R => R ≠ {J.best})
      · exact MeasurableSet.empty

/-- A.3 best protection for each fixed possible request, under the actual canonical call law. -/
theorem removalBad_le (I J : Instance n) {ε : ℝ} (hε : 0 < ε) (hε10 : ε ≤ 1 / 10)
    (key : CallKey) (hkey : ValidKey I key) (state : Option (Finset (Fin n))) :
    (localLaw I J ε key).real (removalBad I J ε key state) ≤ callConfidence I ε key := by
  have hα := confidence_pos I hε key
  cases state with
  | none => simpa only [removalBad, measureReal_empty] using hα.le
  | some S =>
    by_cases hb : J.best ∈ S
    · have hS : S.Nonempty := ⟨J.best, hb⟩
      have h := GapEntropy.EliminationTape.raw_best_failure J.mean S hS hb
        (fun i _ => sub_nonneg.mp (J.gap_nonneg i)) (tolerance_pos I key) (tolerance_le_one I key)
        hα (confidence_le_one I hε hε10 key hkey)
      simpa only [removalBad, if_pos hb, rawResponse, dif_pos hS, localLaw] using h
    · simpa only [removalBad, if_neg hb, measureReal_empty] using hα.le

/-- On every target labeling, A.3's complete good-call guarantee is derived from the
actual near-count and final-gap bridge, under each canonical call measure. -/
theorem targetBad_le (I : Instance n) (π : Equiv.Perm (Fin n)) {ε : ℝ}
    (hε : 0 < ε) (hε10 : ε ≤ 1 / 10) (key : CallKey) (hkey : ValidKey I key)
    (state : Option (Finset (Fin n))) :
    (localLaw I (I.permute π) ε key).real (targetBad I (I.permute π) ε key state) ≤
      callConfidence I ε key := by
  let J := I.permute π
  change (localLaw I J ε key).real (targetBad I J ε key state) ≤ callConfidence I ε key
  have hα := confidence_pos I hε key
  cases state with
  | none => cases key <;> simpa only [targetBad, measureReal_empty] using hα.le
  | some S =>
    cases key with
    | loop k r =>
      by_cases hg : J.best ∈ S ∧ 4 * I.targetCount k < S.card
      · have hS : S.Nonempty := ⟨J.best, hg.1⟩
        have h := GapEntropy.EliminationTape.raw_large_failure J.mean S hS hg.1
          (fun i _ => sub_nonneg.mp (J.gap_nonneg i))
          (tolerance_pos I (.loop k r)) (tolerance_le_one I (.loop k r)) hα
          (confidence_le_one I hε hε10 (.loop k r) hkey)
          (I.permuted_near_card_le_targetCount π S k) hg.2
        simpa only [targetBad, if_pos hg, rawResponse, dif_pos hS, localLaw] using h
      · simpa only [targetBad, if_neg hg, measureReal_empty] using hα.le
    | final =>
      by_cases hg : J.best ∈ S ∧ S.card ≤ 4
      · have hS : S.Nonempty := ⟨J.best, hg.1⟩
        have h := GapEntropy.EliminationTape.raw_small_failure J.mean S hS hg.1
          (fun i _ => sub_nonneg.mp (J.gap_nonneg i))
          (tolerance_pos I .final) (tolerance_le_one I .final) hα
          (confidence_le_one I hε hε10 .final hkey) hg.2
          (fun i _ hi => I.permuted_last_targetTolerance_le_gap π hi)
        simpa only [targetBad, if_pos hg, rawResponse, dif_pos hS, localLaw] using h
      · simpa only [targetBad, if_neg hg, measureReal_empty] using hα.le

end GapEntropy.AttemptExperiment
