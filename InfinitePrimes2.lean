-- proof of infinite primes with Fermat numbers

import MathLib

def fermat (n : ℕ) : ℕ := 2^(2^n) + 1

#check Finset.Iic_bot
#check ()
-- Nat.Iic_zero (namespace Nat)
lemma finset_0_singleton : Finset.Iic 0 = {0} := Finset.Iic_bot

lemma finset_0_singleton' : Finset.Iic 0 = {0} := by
  unfold Finset.Iic
  unfold LocallyFiniteOrderBot.finsetIic
  unfold LocallyFiniteOrder.toLocallyFiniteOrderBot
  dsimp only
  rw [Nat.bot_eq_zero]
  unfold Finset.Icc
  unfold LocallyFiniteOrder.finsetIcc
  unfold Nat.instLocallyFiniteOrder
  dsimp only
  simp only [zero_add, tsub_zero, List.range'_one, Multiset.coe_singleton]
  unfold singleton
  unfold Finset.instSingleton
  simp only [Finset.mk.injEq]
  unfold Multiset.instSingleton
  simp only [Multiset.cons_zero]

lemma finset_0_singleton'' : Finset.Iic 0 = {0} := by
  rfl

lemma finset_n_plus_one (k : ℕ) : Finset.Iio (k + 1) = Finset.Iio k ∪ {k} := by
  simp [Finset.ext_iff]
  cutsat

lemma prod_union (A B : Finset ℕ)(f : ℕ → ℕ)(hAB : A ∩ B = ∅) :
    ∏ i ∈ A ∪ B, f i = (∏ i ∈ A, f i) * ∏ i ∈ B, f i := by
  refine Finset.prod_union ?_
  exact Finset.disjoint_iff_inter_eq_empty.mpr hAB

-- F_0 F_1 ...F_k + 2 = F_(k+1)
lemma product_fermat (k : ℕ) : ∏ i < k, fermat i + 2 = fermat k := by
  induction k with
  | zero =>
    unfold fermat
    exact rfl
  | succ k ih =>
  rw [finset_n_plus_one]
  rw [prod_union]
  · simp
    apply Nat.add_left_cancel (n := (2*(fermat (k))))

    rw [←Nat.add_assoc, ←Nat.add_mul]
    rw [Nat.add_comm 2 _]
    rw [ih]
    unfold fermat
    ring
  · ext
    simp

lemma blah (m n p q : ℕ)(hmn : m ≠ n)() m ≠ n → p ∣ fermat n → q → ∣

lemma fermat_minfac_distinct (m n : ℕ) : m ≠ n → (fermat m).minFac ≠ (fermat n).minFac := by
  intro hmn

  wlog h : m > n
  · simp at h
    symm
    refine this _ _ ?_ ?_
    · symm
      assumption
    · cutsat
  · simp
    rw [←product_fermat m]
    intro hferm





theorem infinite_sequence_of_primes : ∃ f : ℕ → ℕ, f.Injective ∧ ∀ n : ℕ, Nat.Prime (f n) := by
  let f : ℕ → ℕ := fun n ↦ Nat.minFac (fermat n)
  use f
  refine And.symm ⟨?_, ?_⟩
  · intro n
    unfold f
    simp
    unfold fermat
    simp
  · unfold f
    unfold Function.Injective
    intro a1 a2
    simp
    contrapose
    exact fermat_minfac_distinct a1 a2
