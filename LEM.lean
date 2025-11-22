import Mathlib

def lem (p : Prop) : Prop := p ∨ ¬p
def dne (p : Prop) : Prop := ¬¬p → p
def pierce (p q : Prop) : Prop := ((p → q) → p) → p

example (P : Prop) : ¬¬P→P := by
  intro h
  cases em P
  · assumption
  · contradiction

-- excluded middle for p implies double negation elimination for p
theorem lem_imp_dne (p : Prop) : lem p → dne p := by
  intro h
  unfold lem at h
  exact Or.elim h (fun hp : p => show ¬¬p → p by
    intro hnnp
    exact hp
    ) (fun hnp : ¬p => show ¬¬p → p by
    intro hnnp
    exact False.elim (hnnp hnp)
  )

lemma not_p_or_q_imp_not_p (p q : Prop) : ¬ (p ∨ q) → ¬ p := by
  intro hnpq hp
  exact hnpq (Or.inl hp : p ∨ q)

-- double negation elimination implies lem
theorem dne_imp_lem (p : Prop) : dne (lem p) → lem p := by
  have hp : ¬¬(p ∨ ¬p) := by
    intro hnponp
    have hnp : ¬p := by
      exact (not_p_or_q_imp_not_p p ¬p) hnponp
    have hnnp : ¬¬p := by
      rw [or_comm] at hnponp
      exact (not_p_or_q_imp_not_p (¬p) p) hnponp
    exact hnnp hnp
  intro hdnelemp
  unfold dne at hdnelemp
  exact hdnelemp hp

theorem lem_imp_pierce (p q : Prop) : lem p → pierce p q := by
  intro hlem hpqp
  cases hlem  with
  | inl hp => exact hp
  | inr hnp =>
  have hpq : p → q := by
    intro hp
    exfalso
    exact hnp hp
  exact hpqp hpq

theorem pierce_imp_dne (p : Prop) : pierce p False → dne p := by
  intro hpierce hnnp
  have hh : ¬p → p := by
    intro hnp
    exfalso
    exact hnnp hnp
  exact hpierce hh

-- now they are all equivalent ∀p lem p ↔ ∀ p dne p ↔ ∀ p q pierce p q
