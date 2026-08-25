import Util.Bernays.IdealNormMultiplicative
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Factorization away from a finite set of bad primes

The only local input is that maximal ideals coprime to the specified modulus
are invertible. Strong induction on the finite index then gives a prime-ideal
factorization, without a Dedekind-domain assumption on the order.
-/

open scoped nonZeroDivisors

namespace Bernays.InvertibleIdeal

variable {R : Type*} [CommRing R] [IsDomain R] [Ring.HasFiniteQuotients R]

theorem coprime_of_le {I J F : Ideal R} (hIJ : I ≤ J) (hI : IsCoprime I F) : IsCoprime J F := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply top_unique
  calc
    ⊤ = I ⊔ F := hI.sup_eq.symm
    _ ≤ J ⊔ F := sup_le_sup_right hIJ F

theorem factor_lt (P I : InvertibleIdeal R) (hP : (P : Ideal R).IsMaximal)
    (hIP : (I : Ideal R) ≤ P) :
    ∃ J : InvertibleIdeal R, P * J = I ∧ (J : Ideal R).cardQuot < (I : Ideal R).cardQuot := by
  obtain ⟨J, hJ⟩ := exists_mul_eq_of_le P I hIP
  refine ⟨J, hJ, ?_⟩
  have hcard := cardQuot_mul P J
  rw [hJ] at hcard
  have hP₁ : 1 < (P : Ideal R).cardQuot := by
    have hpos := P.cardQuot_pos
    have hne : (P : Ideal R).cardQuot ≠ 1 := by
      intro h
      exact hP.ne_top (Submodule.cardQuot_eq_one_iff.mp h)
    omega
  rw [hcard]
  exact lt_mul_of_one_lt_left J.cardQuot_pos hP₁

theorem exists_list_maximal_factors (F : Ideal R)
    (hmax : ∀ P : Ideal R, P.IsMaximal → IsCoprime P F →
      IsUnit (P : FractionalIdeal R⁰ (FractionRing R)))
    (I : InvertibleIdeal R) (hI : IsCoprime (I : Ideal R) F) :
    ∃ l : List (InvertibleIdeal R), l.prod = I ∧
      ∀ P ∈ l, (P : Ideal R).IsMaximal ∧ IsCoprime (P : Ideal R) F := by
  suffices ∀ N : ℕ, ∀ I : InvertibleIdeal R, (I : Ideal R).cardQuot = N →
      IsCoprime (I : Ideal R) F →
      ∃ l : List (InvertibleIdeal R), l.prod = I ∧
        ∀ P ∈ l, (P : Ideal R).IsMaximal ∧ IsCoprime (P : Ideal R) F from
    this _ I rfl hI
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro I hN hIF
    by_cases htop : (I : Ideal R) = ⊤
    · exact ⟨[], by simpa using (ext htop).symm, by simp⟩
    · obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal (I : Ideal R) htop
      have hPF := coprime_of_le hIP hIF
      let PU : InvertibleIdeal R := ⟨P, hmax P hP hPF⟩
      obtain ⟨J, hmul, hlt⟩ := factor_lt PU I hP hIP
      have hIJ : (I : Ideal R) ≤ (J : Ideal R) := by
        rw [← hmul, coe_mul]
        exact Ideal.mul_le_right
      obtain ⟨l, hl, hmaxl⟩ := ih (J : Ideal R).cardQuot (by rwa [← hN]) J rfl
        (coprime_of_le hIJ hIF)
      refine ⟨PU :: l, by simp only [List.prod_cons, hl, hmul], ?_⟩
      intro Q hQ
      rcases List.mem_cons.mp hQ with rfl | hQ
      · exact ⟨hP, hPF⟩
      · exact hmaxl Q hQ

theorem exists_maximal_factor_class_not_mem (F : Ideal R)
    (hmax : ∀ P : Ideal R, P.IsMaximal → IsCoprime P F →
      IsUnit (P : FractionalIdeal R⁰ (FractionRing R)))
    (H : Subgroup (ClassGroup R)) (I : InvertibleIdeal R)
    (hI : IsCoprime (I : Ideal R) F) (hc : I.idealClass ∉ H) :
    ∃ P J : InvertibleIdeal R, (P : Ideal R).IsMaximal ∧ IsCoprime (P : Ideal R) F ∧
      P.idealClass ∉ H ∧ P * J = I := by
  obtain ⟨l, hl, hmaxl⟩ := exists_list_maximal_factors F hmax I hI
  have hex : ∃ P ∈ l, P.idealClass ∉ H := by
    by_contra hnone
    simp only [not_exists, not_and, not_not] at hnone
    have hprod : l.prod.idealClass ∈ H := by
      clear hl hmaxl
      induction l with
      | nil => simpa using H.one_mem
      | cons P l ih =>
        simp only [List.prod_cons, idealClass_mul]
        exact H.mul_mem (hnone P (by simp)) (ih (by
          intro Q hQ
          exact hnone Q (List.mem_cons_of_mem _ hQ)))
    exact hc (hl ▸ hprod)
  obtain ⟨P, hPl, hcP⟩ := hex
  obtain ⟨l₁, l₂, heq⟩ := List.mem_iff_append.mp hPl
  refine ⟨P, l₁.prod * l₂.prod, (hmaxl P hPl).1, (hmaxl P hPl).2, hcP, ?_⟩
  rw [← hl, heq, List.prod_append, List.prod_cons]
  ac_rfl

end Bernays.InvertibleIdeal
