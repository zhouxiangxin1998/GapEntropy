import GapEntropy.Model

/-!
# Characterizing finite active runs by their observed histories

The recursive predicate below is a deterministic, pathwise description of the
actual policy execution. It is useful for proving that extracted histories in
composed policies are exactly the component policies' histories.
-/

namespace GapEntropy.Policy

variable {n : ℕ} (A : Policy n)

theorem choose_congr_history (hn : 2 ≤ n) {s t : ℕ} (hst : s = t) (z : Seed)
    (h : History n s) (h' : History n t)
    (heq : ∀ i : Fin s, h i = h' ⟨i, by have := i.isLt; omega⟩) :
    A.choose hn s (z, h) = A.choose hn t (z, h') := by
  subst t
  have hh : h = h' := funext heq
  rw [hh]

def historyConsistent (hn : 2 ≤ n) (ω : SampleSpace n) :
    (t : ℕ) → History n t → Prop
  | 0, _ => True
  | t + 1, h => historyConsistent hn ω t (Fin.init h) ∧
      A.choose hn t (ω.1, Fin.init h) = Sum.inl (h (Fin.last t)).1 ∧
      (h (Fin.last t)).2 = ω.2 t (h (Fin.last t)).1

@[simp] theorem historyConsistent_snoc (hn : 2 ≤ n) (ω : SampleSpace n) (t : ℕ)
    (h : History n t) (i : Fin n) (x : ℝ) :
    A.historyConsistent hn ω (t + 1) (Fin.snoc h (i, x)) ↔
      A.historyConsistent hn ω t h ∧ A.choose hn t (ω.1, h) = Sum.inl i ∧ x = ω.2 t i := by
  simp [historyConsistent]

/-- A history describes an actual active run exactly when every recorded arm
was requested by the policy and every reward is the corresponding tape entry. -/
theorem run_eq_active_iff_historyConsistent (hn : 2 ≤ n) (ω : SampleSpace n)
    (t : ℕ) (h : History n t) :
    A.run hn ω t = Sum.inr h ↔ A.historyConsistent hn ω t h := by
  induction t with
  | zero =>
      have hh : h = Fin.elim0 := Subsingleton.elim _ _
      simp [run, historyConsistent, hh]
  | succ t ih =>
      rw [← Fin.snoc_init_self h, A.historyConsistent_snoc, ← ih]
      cases hr : A.run hn ω t with
      | inl j => simp [run_succ, step, hr]
      | inr h₀ =>
          cases hc : A.choose hn t (ω.1, h₀) with
          | inl j =>
              simp only [run_succ, step, hr, Sum.elim_inr, hc, Sum.elim_inl,
                Sum.inr.injEq, Fin.snoc_inj]
              constructor
              · rintro ⟨hh, hp⟩
                subst h₀
                have hi : j = (h (Fin.last t)).1 := congrArg Prod.fst hp
                have hx : ω.2 t j = (h (Fin.last t)).2 := congrArg Prod.snd hp
                exact ⟨rfl, by simpa only [hi] using hc, by simpa only [hi] using hx.symm⟩
              · rintro ⟨hh, hchoose, hx⟩
                subst h₀
                have hi : j = (h (Fin.last t)).1 := Sum.inl.inj (hc.symm.trans hchoose)
                exact ⟨rfl, Prod.ext hi (by simpa only [hi] using hx.symm)⟩
          | inr j =>
              simp only [run_succ, step, hr, Sum.elim_inr, hc]
              constructor
              · intro hbad
                cases hbad
              · rintro ⟨hh, hchoose, _⟩
                have hh' : h₀ = Fin.init h := Sum.inr.inj hh
                subst h₀
                rw [hc] at hchoose
                cases hchoose

def historyPrefix {t : ℕ} (h : History n t) (s : ℕ) (hs : s ≤ t) : History n s :=
  fun j => h ⟨j, lt_of_lt_of_le j.isLt hs⟩

@[simp] theorem historyPrefix_self {t : ℕ} (h : History n t) :
    historyPrefix h t le_rfl = h := rfl

theorem historyConsistent_prefix (hn : 2 ≤ n) (ω : SampleSpace n) {t : ℕ}
    (h : History n t) (hc : A.historyConsistent hn ω t h) (s : ℕ) (hs : s ≤ t) :
    A.historyConsistent hn ω s (historyPrefix h s hs) := by
  induction t generalizing s with
  | zero =>
      have hz : s = 0 := by omega
      subst s
      trivial
  | succ t ih =>
      by_cases hst : s ≤ t
      · exact ih (Fin.init h) hc.1 s hst
      · have he : s = t + 1 := by omega
        subst s
        exact hc

/-- Every decision and reward in a consistent history can be read at its own
prefix. This gives a convenient nonrecursive interface for stream composition. -/
theorem historyConsistent_decision (hn : 2 ≤ n) (ω : SampleSpace n) {t : ℕ}
    (h : History n t) (hc : A.historyConsistent hn ω t h) (s : ℕ) (hs : s < t) :
    A.choose hn s (ω.1, historyPrefix h s hs.le) = Sum.inl (h ⟨s, hs⟩).1 ∧
      (h ⟨s, hs⟩).2 = ω.2 s (h ⟨s, hs⟩).1 := by
  have hh := A.historyConsistent_prefix hn ω h hc (s + 1) (by omega)
  exact hh.2

theorem historyConsistent_of_decisions (hn : 2 ≤ n) (ω : SampleSpace n) {t : ℕ}
    (h : History n t)
    (hc : ∀ s (hs : s < t),
      A.choose hn s (ω.1, historyPrefix h s hs.le) = Sum.inl (h ⟨s, hs⟩).1 ∧
        (h ⟨s, hs⟩).2 = ω.2 s (h ⟨s, hs⟩).1) :
    A.historyConsistent hn ω t h := by
  induction t with
  | zero => trivial
  | succ t ih =>
      refine ⟨ih (Fin.init h) ?_, ?_⟩
      · intro s hs
        exact hc s (by omega)
      · exact hc t (by omega)

end GapEntropy.Policy
