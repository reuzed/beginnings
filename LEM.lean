import Mathlib



example (P : Prop) : ¬¬P→P := by
  intro h
  cases em P
  · assumption
  · contradiction

theorem dne (p : Prop) : ¬¬p → p := by
  sorry

theorem not_distrib_and (p q : Prop) : ¬ (p ∨ q) ↔ (¬ p ∧ ¬ q) := by
  sorry

theorem lem (P : Prop) : P ∨ ¬P := by
  sorry
