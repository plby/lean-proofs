import Util.Bernays.GoodNorms

/-!
# Splitting an invertible ideal at coprime factors of its norm
-/

open scoped nonZeroDivisors

namespace Bernays

theorem ideal_scalar_split_product {R : Type*} [CommRing R] (I : Ideal R) {a b : R}
    (hc : IsCoprime a b) (hab : a * b ∈ I) :
    (I + Ideal.span {a}) * (I + Ideal.span {b}) = I := by
  have hcop : IsCoprime (I + Ideal.span {a}) (I + Ideal.span {b}) := by
    apply Ideal.isCoprime_iff_sup_eq.mpr
    apply (Ideal.eq_top_iff_one _).mpr
    obtain ⟨u, v, huv⟩ := hc
    rw [← huv]
    exact (I + Ideal.span {a}).add_mem_sup
      ((show Ideal.span {a} ≤ I + Ideal.span {a} from le_sup_right)
        ((Ideal.span {a}).mul_mem_left u (Ideal.mem_span_singleton_self _)))
      ((show Ideal.span {b} ≤ I + Ideal.span {b} from le_sup_right)
        ((Ideal.span {b}).mul_mem_left v (Ideal.mem_span_singleton_self _)))
  apply le_antisymm
  · rw [mul_add, add_mul, add_mul]
    apply sup_le (sup_le Ideal.mul_le_left Ideal.mul_le_right)
    apply sup_le Ideal.mul_le_left
    rw [Ideal.span_singleton_mul_span_singleton]
    exact (Ideal.span_singleton_le_iff_mem I).mpr hab
  · rw [Ideal.mul_eq_inf_of_isCoprime hcop]
    exact le_inf le_sup_left le_sup_left

theorem coprime_factor_norms {a b m n : ℕ} (hmn : m.Coprime n)
    (hab : a * b = m * n) (ha : a ∣ m ^ 2) (hb : b ∣ n ^ 2) : a = m ∧ b = n := by
  have han : a.Coprime n := (hmn.pow_left 2).of_dvd_left ha
  have hmb : m.Coprime b := (hmn.pow_right 2).of_dvd_right hb
  have ham : a ∣ m := han.dvd_mul_right.mp (hab ▸ dvd_mul_right a b)
  have hma : m ∣ a := hmb.dvd_mul_right.mp (hab.symm ▸ dvd_mul_right m n)
  have hbm : b.Coprime m := hmb.symm
  have hna : n.Coprime a := han.symm
  have hbn : b ∣ n := hbm.dvd_mul_left.mp (hab ▸ dvd_mul_left b a)
  have hnb : n ∣ b := hna.dvd_mul_left.mp (hab.symm ▸ dvd_mul_left n m)
  exact ⟨Nat.dvd_antisymm ham hma, Nat.dvd_antisymm hbn hnb⟩

theorem exists_coprime_norm_factors {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b), ∀ m n : ℕ,
      m.Coprime n → (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m * n →
      ∃ J K : InvertibleIdeal (QuadraticAlgebra ℤ d b), J * K = I ∧
        (J : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = m ∧
        (K : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n := by
  let := quadraticOrderIsDomain hD
  intro I m n hmn hnorm
  let O := QuadraticAlgebra ℤ d b
  have hmnpos : 0 < m * n := hnorm ▸ I.cardQuot_pos
  have hm : 0 < m := Nat.pos_of_mul_pos_right hmnpos
  have hn : 0 < n := Nat.pos_of_mul_pos_left hmnpos
  have hscalar : IsCoprime (m : O) (n : O) := by
    simpa only [map_natCast] using hmn.isCoprime.map (Int.castRingHom O)
  have hmem : (m : O) * (n : O) ∈ (I : Ideal O) := by
    rw [← Nat.cast_mul, ← hnorm, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  let J₀ : Ideal O := I + Ideal.span {(m : O)}
  let K₀ : Ideal O := I + Ideal.span {(n : O)}
  have hprod : J₀ * K₀ = (I : Ideal O) := ideal_scalar_split_product (I : Ideal O) hscalar hmem
  have hu : IsUnit ((J₀ : FractionalIdeal O⁰ (FractionRing O)) *
      (K₀ : FractionalIdeal O⁰ (FractionRing O))) := by
    rw [← FractionalIdeal.coeIdeal_mul, hprod]
    exact I.2
  let J : InvertibleIdeal O := ⟨J₀, isUnit_of_mul_isUnit_left hu⟩
  let K : InvertibleIdeal O := ⟨K₀, isUnit_of_mul_isUnit_right hu⟩
  have hJK : J * K = I := InvertibleIdeal.ext hprod
  have hJnorm : (J : Ideal O).cardQuot ∣ m ^ 2 := by
    have hdiv := AddSubgroup.index_dvd_of_le (H := (Ideal.span {(m : O)}).toAddSubgroup)
      (K := J₀.toAddSubgroup) (show (Ideal.span {(m : O)}) ≤ J₀ from le_sup_right)
    change (J : Ideal O).cardQuot ∣ (Ideal.span {(m : O)}).cardQuot at hdiv
    have heq : (Ideal.span {(m : O)}).cardQuot = m ^ 2 := principal_nat_cardQuot hD hm
    rwa [heq] at hdiv
  have hKnorm : (K : Ideal O).cardQuot ∣ n ^ 2 := by
    have hdiv := AddSubgroup.index_dvd_of_le (H := (Ideal.span {(n : O)}).toAddSubgroup)
      (K := K₀.toAddSubgroup) (show (Ideal.span {(n : O)}) ≤ K₀ from le_sup_right)
    change (K : Ideal O).cardQuot ∣ (Ideal.span {(n : O)}).cardQuot at hdiv
    have heq : (Ideal.span {(n : O)}).cardQuot = n ^ 2 := principal_nat_cardQuot hD hn
    rwa [heq] at hdiv
  have hmul : (J : Ideal O).cardQuot * (K : Ideal O).cardQuot = m * n := by
    rw [← InvertibleIdeal.cardQuot_mul, hJK, hnorm]
  obtain ⟨hJ, hK⟩ := coprime_factor_norms hmn hmul hJnorm hKnorm
  exact ⟨J, K, hJK, hJ, hK⟩

theorem InvertibleIdeal.coprime_norm_product_add_scalar {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (I J : InvertibleIdeal R)
    (hcop : (I : Ideal R).cardQuot.Coprime (J : Ideal R).cardQuot) :
    (I : Ideal R) * (J : Ideal R) + Ideal.span {((I : Ideal R).cardQuot : R)} = (I : Ideal R) := by
  have hmI : ((I : Ideal R).cardQuot : R) ∈ (I : Ideal R) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  have hJ := Ideal.isCoprime_iff_sup_eq.mp (J.coprime_scalar_of_cardQuot_coprime _ hcop.symm)
  apply le_antisymm
  · exact sup_le Ideal.mul_le_left ((Ideal.span_singleton_le_iff_mem _).mpr hmI)
  · calc
      (I : Ideal R) = (I : Ideal R) * ((J : Ideal R) + Ideal.span {((I : Ideal R).cardQuot : R)}) := by
        change (I : Ideal R) = (I : Ideal R) * ((J : Ideal R) ⊔ Ideal.span {((I : Ideal R).cardQuot : R)})
        rw [hJ, Ideal.mul_top]
      _ = (I : Ideal R) * (J : Ideal R) +
          (I : Ideal R) * Ideal.span {((I : Ideal R).cardQuot : R)} := mul_add _ _ _
      _ ≤ _ := sup_le_sup_left Ideal.mul_le_right _

theorem InvertibleIdeal.coprime_norm_factors_unique {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] {I J K L : InvertibleIdeal R}
    (hprod : I * J = K * L)
    (hcop : (I : Ideal R).cardQuot.Coprime (J : Ideal R).cardQuot)
    (hIK : (I : Ideal R).cardQuot = (K : Ideal R).cardQuot)
    (hJL : (J : Ideal R).cardQuot = (L : Ideal R).cardQuot) : I = K ∧ J = L := by
  have hcop' : (K : Ideal R).cardQuot.Coprime (L : Ideal R).cardQuot := by rwa [← hIK, ← hJL]
  have hIK' : I = K := by
    apply InvertibleIdeal.ext
    have hsum := congrArg (fun A : InvertibleIdeal R =>
      (A : Ideal R) + Ideal.span {((I : Ideal R).cardQuot : R)}) hprod
    change (I : Ideal R) * (J : Ideal R) + Ideal.span {((I : Ideal R).cardQuot : R)} =
      (K : Ideal R) * (L : Ideal R) + Ideal.span {((I : Ideal R).cardQuot : R)} at hsum
    rw [I.coprime_norm_product_add_scalar J hcop, hIK,
      K.coprime_norm_product_add_scalar L hcop'] at hsum
    exact hsum
  refine ⟨hIK', ?_⟩
  subst K
  exact InvertibleIdeal.mul_right_cancel _ _ I (by simpa only [mul_comm] using hprod)

end Bernays
