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

lemma fermat_neq_1 (m : ℕ) : fermat m ≠ 1 := by
  unfold fermat
  simp

lemma n_in_finset_m (n m : ℕ) (hmn : m > n) : n ∈ Finset.Iio m := by
  simp [hmn]

lemma finset_m_eq_n_union_rest (n m : ℕ) (hmn : m > n)
    : Finset.Iio m = {n} ∪ (Finset.Iio n ∪ Finset.Ioo n m) := by
  ext a
  simp
  cutsat

lemma prod_finset_m_eq (n m : ℕ) (hmn : m > n)
    : ∏ i ∈ (Finset.Iio m), fermat i =
    fermat n * (∏ i ∈ (Finset.Iio n ∪ Finset.Ioo n m), fermat i) := by
  rw [finset_m_eq_n_union_rest n m hmn]
  rw [←Finset.prod_singleton fermat n]
  apply Finset.prod_union ?_
  simp

lemma f_n_dvd_prod_f_i (n m : ℕ) (hmn : m > n) : fermat n ∣ ∏ i < m, fermat i := by
  rw [prod_finset_m_eq n m hmn]
  simp


lemma unique_factor_2 (p : ℕ) (hpt : p ∣ 2) (hpp : Nat.Prime p) : p = 2 := by
  sorry

lemma distinct_fermat_gcd_1 (m n p : ℕ) (hmn : m > n)
    (hp : Nat.Prime p) (hpn : p ∣ fermat n) (hqm : p ∣ fermat m)
    : p = 2 := by
  have hpm : p ∣ ∏ i < m, fermat i := Nat.dvd_trans hpn (f_n_dvd_prod_f_i n m hmn)
  have hprod_le_fm : ∏ i < m, fermat i ≤ fermat m := by
    rw [←product_fermat m]
    simp
  have pd2_ish := (Iff.mp (Iff.symm (Nat.dvd_sub_iff_left hprod_le_fm hpm))) hqm

  simp [←product_fermat m] at pd2_ish

  exact unique_factor_2 p pd2_ish hp

lemma two_ndivd_fermat (m : ℕ) : ¬2 ∣ 2 ^ 2 ^ m + 1 := by
  sorry

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
    intro hferm
    have hlol : (fermat m).minFac ≠ 2 := by
      by_contra h2
      have h3 : _ :=Nat.minFac_dvd (fermat m)
      rw [h2] at h3
      unfold fermat at h3
      apply two_ndivd_fermat m
      assumption

    apply hlol
    apply distinct_fermat_gcd_1 m n (fermat m).minFac h
    · exact Nat.minFac_prime (fermat_neq_1 m)
    · rw [hferm]
      exact Nat.minFac_dvd (fermat n)
    · exact Nat.minFac_dvd (fermat m)

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
