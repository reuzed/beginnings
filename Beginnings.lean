import Mathlib

example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
  have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
  show ∃ l, m * n = l + l from ⟨_, hmn⟩

#check 2 + 2

#check 2 + 2 = 4

theorem easy : 2 + 2 = 4 :=
  rfl


-- def FermatLastTheorem :=
--   ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

theorem hard : FermatLastTheorem :=
  sorry

#check hard
