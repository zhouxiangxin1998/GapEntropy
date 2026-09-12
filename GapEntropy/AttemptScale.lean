import GapEntropy.Elimination
import Mathlib.Tactic

/-! Finite control for one C.1 scale. `none` is abort. Identity steps after the
size threshold is met make a fixed finite unrolling equivalent to the while loop.
The oracle supplies raw outputs; no statistical success premise is used here. -/

noncomputable section
namespace GapEntropy.AttemptScale
variable {n : ℕ}

abbrev Oracle (n : ℕ) := ℕ → Finset (Fin n) → Finset (Fin n)

def step (N : ℕ) (oracle : Oracle n) (r : ℕ) : Option (Finset (Fin n)) → Option (Finset (Fin n))
  | none => none
  | some S =>
      if 4 * N < S.card then
        let R := oracle r S
        if R.Nonempty ∧ R.card ≤ (S.card + 1) / 2 then some R else none
      else some S

def run (N : ℕ) (oracle : Oracle n) (S : Finset (Fin n)) : ℕ → Option (Finset (Fin n))
  | 0 => some S
  | r + 1 => step N oracle r (run N oracle S r)

def request (N : ℕ) (oracle : Oracle n) (S : Finset (Fin n)) (r : ℕ) : Option (Finset (Fin n)) :=
  match run N oracle S r with
  | none => none
  | some T => if 4 * N < T.card then some T else none

theorem step_some_cases {N r : ℕ} {oracle : Oracle n} {S T : Finset (Fin n)}
    (h : step N oracle r (some S) = some T) :
    (S.card ≤ 4 * N ∧ T = S) ∨
      (4 * N < S.card ∧ T = oracle r S ∧ T.Nonempty ∧ T.card ≤ (S.card + 1) / 2) := by
  dsimp only [step] at h
  split_ifs at h with hcall hacc
  · right
    have he : oracle r S = T := Option.some.inj h
    exact ⟨hcall, he.symm, he ▸ hacc.1, he ▸ hacc.2⟩
  · exact Or.inl ⟨le_of_not_gt hcall, (Option.some.inj h).symm⟩

theorem run_succ_some_previous {N r : ℕ} {oracle : Oracle n} {S T : Finset (Fin n)}
    (h : run N oracle S (r + 1) = some T) :
    ∃ U, run N oracle S r = some U ∧ step N oracle r (some U) = some T := by
  cases he : run N oracle S r with
  | none => simp [run, he, step] at h
  | some U => exact ⟨U, rfl, by simpa only [run, he] using h⟩

theorem run_nonempty {N r : ℕ} {oracle : Oracle n} {S T : Finset (Fin n)}
    (hS : S.Nonempty) (h : run N oracle S r = some T) : T.Nonempty := by
  induction r generalizing T with
  | zero => have he := Option.some.inj h; subst T; exact hS
  | succ r ih =>
    obtain ⟨U, hU, hstep⟩ := run_succ_some_previous h
    rcases step_some_cases hstep with ⟨_, rfl⟩ | ⟨_, _, hT, _⟩
    · exact ih hU
    · exact hT

theorem run_large_previous {N r : ℕ} {oracle : Oracle n} {S T : Finset (Fin n)}
    (h : run N oracle S (r + 1) = some T) (hlarge : 4 * N < T.card) :
    ∃ U, run N oracle S r = some U ∧ 4 * N < U.card ∧ T.card ≤ (U.card + 1) / 2 := by
  obtain ⟨U, hU, hstep⟩ := run_succ_some_previous h
  rcases step_some_cases hstep with ⟨hsmall, rfl⟩ | ⟨hbig, _, _, hhalf⟩
  · omega
  · exact ⟨U, hU, hbig, hhalf⟩

/-- If the threshold has still not been met, every preceding call strictly decreased size. -/
theorem large_card_add_round_le {N : ℕ} (hN : 0 < N) {oracle : Oracle n}
    {S T : Finset (Fin n)} {r : ℕ} (h : run N oracle S r = some T)
    (hlarge : 4 * N < T.card) : T.card + r ≤ S.card := by
  induction r generalizing T with
  | zero => have he := Option.some.inj h; subst T; omega
  | succ r ih =>
    obtain ⟨U, hU, hbig, hhalf⟩ := run_large_previous h hlarge
    have hprev := ih hU hbig
    omega

/-- Unrolling at most the input cardinality always completes the while loop or aborts. -/
theorem run_finished {N R : ℕ} (hN : 0 < N) {oracle : Oracle n} {S T : Finset (Fin n)}
    (hbudget : S.card ≤ R) (h : run N oracle S R = some T) : T.card ≤ 4 * N := by
  by_contra! hlarge
  have hh := large_card_add_round_le hN h hlarge
  omega

theorem run_card_le {N r : ℕ} (hN : 0 < N) {oracle : Oracle n} {S T : Finset (Fin n)}
    (h : run N oracle S r = some T) : T.card ≤ S.card := by
  induction r generalizing T with
  | zero => have he := Option.some.inj h; subst T; rfl
  | succ r ih =>
    obtain ⟨U, hU, hstep⟩ := run_succ_some_previous h
    have hprev := ih hU
    rcases step_some_cases hstep with ⟨_, rfl⟩ | ⟨hbig, _, _, hhalf⟩ <;> omega

/-- Every possible call input, including one whose output aborts, has geometric size. -/
theorem large_card_geometric {N : ℕ} (hN : 0 < N) {oracle : Oracle n}
    {S T : Finset (Fin n)} {r : ℕ} (h : run N oracle S r = some T)
    (hlarge : 4 * N < T.card) : (T.card : ℝ) ≤ (S.card : ℝ) * (3 / 4 : ℝ) ^ r := by
  induction r generalizing T with
  | zero => have he := Option.some.inj h; subst T; simp
  | succ r ih =>
    obtain ⟨U, hU, hbig, hhalf⟩ := run_large_previous h hlarge
    have hprev := ih hU hbig
    have hcontract := GapEntropy.Elimination.rounded_half_contracts (show 3 ≤ U.card by omega)
    have hnat : 4 * T.card ≤ 3 * U.card := by omega
    have hreal : 4 * (T.card : ℝ) ≤ 3 * (U.card : ℝ) := by exact_mod_cast hnat
    rw [pow_succ]
    nlinarith

theorem request_some_iff {N r : ℕ} {oracle : Oracle n} {S T : Finset (Fin n)} :
    request N oracle S r = some T ↔ run N oracle S r = some T ∧ 4 * N < T.card := by
  unfold request
  cases hstate : run N oracle S r with
  | none => simp
  | some U =>
    dsimp only
    by_cases hlarge : 4 * N < U.card
    · simp only [if_pos hlarge, Option.some.injEq]
      constructor
      · intro he; subst T; exact ⟨rfl, hlarge⟩
      · exact fun h => h.1
    · rw [if_neg hlarge]
      constructor
      · intro h; cases h
      · rintro ⟨he, hbig⟩
        cases he
        exact (hlarge hbig).elim

theorem request_geometric {N : ℕ} (hN : 0 < N) {oracle : Oracle n}
    {S T : Finset (Fin n)} {r : ℕ} (h : request N oracle S r = some T) :
    (T.card : ℝ) ≤ (S.card : ℝ) * (3 / 4 : ℝ) ^ r :=
  large_card_geometric hN (request_some_iff.mp h).1 (request_some_iff.mp h).2

theorem run_stable {N r : ℕ} {oracle : Oracle n} {S T : Finset (Fin n)}
    (h : run N oracle S r = some T) (hsmall : T.card ≤ 4 * N) (j : ℕ) :
    run N oracle S (r + j) = some T := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [Nat.add_succ, run, ih]
    simp [step, not_lt_of_ge hsmall]

theorem run_abort_stable {N r : ℕ} {oracle : Oracle n} {S : Finset (Fin n)}
    (h : run N oracle S r = none) (j : ℕ) : run N oracle S (r + j) = none := by
  induction j with
  | zero => simpa using h
  | succ j ih => rw [Nat.add_succ, run, ih]; rfl

/-- No hidden extra call follows the fixed finite unrolling. -/
theorem request_none_of_card_le {N r : ℕ} (hN : 0 < N) {oracle : Oracle n}
    {S : Finset (Fin n)} (hcard : S.card ≤ r) : request N oracle S r = none := by
  unfold request
  cases he : run N oracle S r with
  | none => rfl
  | some T =>
    have hs := run_finished hN hcard he
    simp [not_lt_of_ge hs]

theorem request_none_stable {N r : ℕ} {oracle : Oracle n} {S : Finset (Fin n)}
    (h : request N oracle S r = none) (j : ℕ) : request N oracle S (r + j) = none := by
  cases he : run N oracle S r with
  | none => simp only [request, run_abort_stable he j]
  | some T =>
    have hsmall : T.card ≤ 4 * N := by
      by_contra! hbig
      simp [request, he, hbig] at h
    simp only [request, run_stable he hsmall j, if_neg (not_lt_of_ge hsmall)]

/-- The loop index is the actual invocation ordinal: a later call implies all earlier calls. -/
theorem request_some_earlier {N r j : ℕ} {oracle : Oracle n} {S T : Finset (Fin n)}
    (h : request N oracle S r = some T) (hj : j < r) :
    ∃ U, request N oracle S j = some U := by
  cases he : request N oracle S j with
  | some U => exact ⟨U, rfl⟩
  | none =>
    have hh := request_none_stable he (r - j)
    rw [Nat.add_sub_of_le hj.le] at hh
    rw [h] at hh
    cases hh

end GapEntropy.AttemptScale
