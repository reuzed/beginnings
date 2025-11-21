import Mathlib

def divides (x y : ℕ) : Prop :=
  ∃ m : ℕ, x * m = y

-- def is_prime_0 (x : ℕ) : Prop :=
--   ∄ y : ℕ, y ≠ 1 ∧ y ≠ x ∧ divides y x

def is_prime (x : ℕ) :=
  ∀ y : ℕ, (divides y x) → y = 1 ∨ y = x

def inf_primes :=
  ∀ n : ℕ, ∃m > n, is_prime m

theorem first_thm : inf_primes :=
  sorry

def fermat (n : ℕ) : ℕ :=
  1 + 2 ^ (2 ^ n)

lemma fermat_product : (∀ n : ℕ, (∏ i ∈ Finset.range n, fermat i = (fermat n) - 2)) := by
  -- induction n with d hd
  sorry

def coprime (x y : ℕ) : Prop :=
  true

lemma fermats_coprime : ∀ n m : ℕ, n ≠ m → coprime (fermat n) (fermat m) := by
  sorry

-- lemma
