import ErdosProblems.Erdos360.LevCompletion

/-!
# The numerical reversal pairing in Lev's Proposition 1

This module contains the sharp numerical consequence of Lev's prefix
increment.  It has no further additive-combinatorial input.
-/

namespace Erdos360

open scoped BigOperators

/-- The signed contribution of the `i`th summand after subtracting its
diameter from twice Lev's prefix-cardinality increment.  Indices are
one-based. -/
def levSignedGain (r i x : ℕ) : ℤ :=
  2 * ((min (x - 1) (i * r) + 1 : ℕ) : ℤ) - x

/-- Summing the signed gains separates the doubled prefix increments from
the sum of the diameters.  Keeping this identity explicit avoids asking the
linear arithmetic tactic to normalize a sum of subtractions. -/
lemma sum_levSignedGain_eq (r : ℕ) (I : Finset ℕ) (a : ℕ → ℕ) :
    (∑ i ∈ I, levSignedGain r i (a i)) =
      2 * ((∑ i ∈ I, (min (a i - 1) (i * r) + 1) : ℕ) : ℤ) -
        ((∑ i ∈ I, a i : ℕ) : ℤ) := by
  simp only [levSignedGain, Finset.sum_sub_distrib]
  push_cast
  rw [Finset.mul_sum]

/-- Reversal pairing: if the diameters `x ≤ y` occur at complementary
one-based indices `i+j=k+1`, then their signed gains total at least
`2(r+1)`.  The only global input is `L ≤ kr+1`. -/
lemma two_mul_add_two_le_levSignedGain_add_rev
    {r k L i j x y : ℕ}
    (hr : 1 ≤ r) (hi : 1 ≤ i) (hij : i + j = k + 1) (hijOrder : i ≤ j)
    (hx : r + 1 ≤ x) (hxy : x ≤ y) (hyL : y ≤ L)
    (hL : L ≤ k * r + 1) :
    (2 * (r + 1 : ℕ) : ℤ) ≤
      levSignedGain r i x + levSignedGain r j y := by
  have hiMul : r ≤ i * r := by
    calc
      r = 1 * r := by simp
      _ ≤ i * r := Nat.mul_le_mul_right r hi
  have hijMul : i * r ≤ j * r := Nat.mul_le_mul_right r hijOrder
  have hsumMul : i * r + j * r = k * r + r := by
    calc
      i * r + j * r = (i + j) * r := (Nat.add_mul i j r).symm
      _ = (k + 1) * r := by rw [hij]
      _ = k * r + r := by rw [Nat.add_mul, one_mul]
  have hkToJ : k * r + r ≤ j * r + j * r := by
    rw [← hsumMul]
    exact Nat.add_le_add_right hijMul _
  by_cases hxi : x - 1 ≤ i * r
  · rw [levSignedGain, min_eq_left hxi]
    by_cases hyj : y - 1 ≤ j * r
    · rw [levSignedGain, min_eq_left hyj]
      push_cast
      omega
    · have hjy : j * r ≤ y - 1 := Nat.le_of_lt (Nat.lt_of_not_ge hyj)
      rw [levSignedGain, min_eq_right hjy]
      push_cast
      omega
  · have hix : i * r ≤ x - 1 := Nat.le_of_lt (Nat.lt_of_not_ge hxi)
    rw [levSignedGain, min_eq_right hix]
    by_cases hyj : y - 1 ≤ j * r
    · rw [levSignedGain, min_eq_left hyj]
      push_cast
      omega
    · have hjy : j * r ≤ y - 1 := Nat.le_of_lt (Nat.lt_of_not_ge hyj)
      rw [levSignedGain, min_eq_right hjy]
      push_cast
      omega

/-- The complementary-index involution preserves the sum over `1,…,k`. -/
lemma sum_levSignedGain_rev (r k : ℕ) (a : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc 1 k, levSignedGain r (k + 1 - i) (a (k + 1 - i)) =
      ∑ i ∈ Finset.Icc 1 k, levSignedGain r i (a i) := by
  classical
  apply Finset.sum_bij (fun i _ ↦ k + 1 - i)
  · intro i hi
    rw [Finset.mem_Icc] at hi ⊢
    omega
  · intro i₁ hi₁ i₂ hi₂ heq
    rw [Finset.mem_Icc] at hi₁ hi₂
    omega
  · intro j hj
    rw [Finset.mem_Icc] at hj
    refine ⟨k + 1 - j, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      omega
    · omega
  · intro i hi
    rfl

/-- The numerical heart of Proposition 1(ii).  A nondecreasing sequence of
diameters between `r+1` and `L`, with `L-1 ≤ kr`, has average signed gain
at least `r+1`. -/
lemma mul_add_one_le_sum_levSignedGain
    {r k L : ℕ} {a : ℕ → ℕ}
    (hr : 1 ≤ r)
    (haLo : ∀ i, 1 ≤ i → i ≤ k → r + 1 ≤ a i)
    (haMono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → a i ≤ a j)
    (haHi : ∀ i, 1 ≤ i → i ≤ k → a i ≤ L)
    (hL : L ≤ k * r + 1) :
    (k * (r + 1 : ℕ) : ℤ) ≤
      ∑ i ∈ Finset.Icc 1 k, levSignedGain r i (a i) := by
  classical
  let I := Finset.Icc 1 k
  let g : ℕ → ℤ := fun i ↦ levSignedGain r i (a i)
  have hpair : ∀ i ∈ I,
      (2 * (r + 1 : ℕ) : ℤ) ≤ g i + g (k + 1 - i) := by
    intro i hiI
    have hi := (Finset.mem_Icc.mp hiI)
    let j := k + 1 - i
    have hj : 1 ≤ j ∧ j ≤ k := by
      dsimp [j]
      omega
    have hij : i + j = k + 1 := by
      dsimp [j]
      omega
    rcases le_total i j with hijOrder | hjiOrder
    · exact two_mul_add_two_le_levSignedGain_add_rev hr hi.1 hij hijOrder
        (haLo i hi.1 hi.2) (haMono i j hi.1 hijOrder hj.2)
        (haHi j hj.1 hj.2) hL
    · have hpair' := two_mul_add_two_le_levSignedGain_add_rev hr hj.1
          (by omega : j + i = k + 1) hjiOrder
          (haLo j hj.1 hj.2) (haMono j i hj.1 hjiOrder hi.2)
          (haHi i hi.1 hi.2) hL
      simpa only [g, add_comm] using hpair'
  have hsumPair :
      ∑ i ∈ I, (2 * (r + 1 : ℕ) : ℤ) ≤
        ∑ i ∈ I, (g i + g (k + 1 - i)) := by
    exact Finset.sum_le_sum fun i hi ↦ hpair i hi
  have hcardI : I.card = k := by simp [I]
  have hrev : ∑ i ∈ I, g (k + 1 - i) = ∑ i ∈ I, g i := by
    simpa only [I, g] using sum_levSignedGain_rev r k a
  simp only [Finset.sum_add_distrib, hrev] at hsumPair
  rw [Finset.sum_const, hcardI] at hsumPair
  simp only [nsmul_eq_mul] at hsumPair
  dsimp [I, g] at hsumPair
  push_cast at hsumPair ⊢
  nlinarith only [hsumPair]

/-- The companion numerical estimate used in Proposition 1(i).  It is
obtained by appending the virtual terminal diameter `L` and applying the
reversal-pairing estimate to the resulting `(k+1)`-term sequence. -/
lemma sub_le_sum_levSignedGain
    {r k L : ℕ} {a : ℕ → ℕ}
    (hr : 1 ≤ r) (hrL : r + 1 ≤ L)
    (haLo : ∀ i, 1 ≤ i → i ≤ k → r + 1 ≤ a i)
    (haMono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → a i ≤ a j)
    (haHi : ∀ i, 1 ≤ i → i ≤ k → a i ≤ L)
    (hL : L ≤ (k + 1) * r + 1) :
    (((k + 1) * (r + 1 : ℕ) : ℕ) : ℤ) - L ≤
      ∑ i ∈ Finset.Icc 1 k, levSignedGain r i (a i) := by
  classical
  let a' : ℕ → ℕ := fun i ↦ if i ≤ k then a i else L
  have haLo' : ∀ i, 1 ≤ i → i ≤ k + 1 → r + 1 ≤ a' i := by
    intro i hi hik
    by_cases h : i ≤ k
    · simpa [a', h] using haLo i hi h
    · simp [a', h, hrL]
  have haMono' : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k + 1 → a' i ≤ a' j := by
    intro i j hi hij hj
    by_cases hjk : j ≤ k
    · have hik : i ≤ k := hij.trans hjk
      simp [a', hik, hjk, haMono i j hi hij hjk]
    · have hjEq : j = k + 1 := by omega
      subst j
      by_cases hik : i ≤ k
      · simp [a', hik, haHi i hi hik]
      · have hiEq : i = k + 1 := by omega
        subst i
        simp [a']
  have haHi' : ∀ i, 1 ≤ i → i ≤ k + 1 → a' i ≤ L := by
    intro i hi hik
    by_cases h : i ≤ k
    · simpa [a', h] using haHi i hi h
    · simp [a', h]
  have hg := mul_add_one_le_sum_levSignedGain
    (r := r) (k := k + 1) (L := L) (a := a')
    hr haLo' haMono' haHi' hL
  rw [Finset.sum_Icc_succ_top (by omega)] at hg
  have hsum :
      (∑ i ∈ Finset.Icc 1 k, levSignedGain r i (a' i)) =
        ∑ i ∈ Finset.Icc 1 k, levSignedGain r i (a i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := (Finset.mem_Icc.mp hi).2
    simp [a', hik]
  rw [hsum] at hg
  have hlast : levSignedGain r (k + 1) (a' (k + 1)) = (L : ℤ) := by
    have hmin : L - 1 ≤ (k + 1) * r := by omega
    have hLpos : 1 ≤ L := by omega
    simp only [a', if_neg (by omega : ¬k + 1 ≤ k), levSignedGain,
      min_eq_left hmin]
    rw [show L - 1 + 1 = L by omega]
    omega
  rw [hlast] at hg
  omega

/-- Proposition 1(i), stated directly for a prefix-cardinality lower bound.
The upper diameter condition has one extra virtual index, which produces
the characteristic `-L` term. -/
lemma lev_prop_one_i_of_prefix_bound
    {r k L cardS : ℕ} {a : ℕ → ℕ}
    (hr : 1 ≤ r) (hrL : r + 1 ≤ L)
    (haLo : ∀ i, 1 ≤ i → i ≤ k → r + 1 ≤ a i)
    (haMono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → a i ≤ a j)
    (haHi : ∀ i, 1 ≤ i → i ≤ k → a i ≤ L)
    (hL : L ≤ (k + 1) * r + 1)
    (hprefix : 1 + ∑ i ∈ Finset.Icc 1 k,
        (min (a i - 1) (i * r) + 1) ≤ cardS) :
    (∑ i ∈ Finset.Icc 1 k, a i) + (k + 1) * (r + 1) + 2 ≤
      2 * cardS + L := by
  have hg := sub_le_sum_levSignedGain hr hrL haLo haMono haHi hL
  rw [sum_levSignedGain_eq] at hg
  have hprefix2 :
      2 * (1 + ∑ i ∈ Finset.Icc 1 k,
        (min (a i - 1) (i * r) + 1)) ≤ 2 * cardS :=
    Nat.mul_le_mul_left 2 hprefix
  omega

/-- Proposition 1(ii), stated directly for any cardinality satisfying the
prefix-invariant lower bound. -/
lemma lev_prop_one_ii_of_prefix_bound
    {r k L cardS : ℕ} {a : ℕ → ℕ}
    (hr : 1 ≤ r)
    (haLo : ∀ i, 1 ≤ i → i ≤ k → r + 1 ≤ a i)
    (haMono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ k → a i ≤ a j)
    (haHi : ∀ i, 1 ≤ i → i ≤ k → a i ≤ L)
    (hL : L ≤ k * r + 1)
    (hprefix : 1 + ∑ i ∈ Finset.Icc 1 k,
        (min (a i - 1) (i * r) + 1) ≤ cardS) :
    (∑ i ∈ Finset.Icc 1 k, a i) + k * (r + 1) + 2 ≤
      2 * cardS := by
  have hg := mul_add_one_le_sum_levSignedGain hr haLo haMono haHi hL
  rw [sum_levSignedGain_eq] at hg
  have hprefix2 :
      2 * (1 + ∑ i ∈ Finset.Icc 1 k,
        (min (a i - 1) (i * r) + 1)) ≤ 2 * cardS :=
    Nat.mul_le_mul_left 2 hprefix
  omega

end Erdos360
