import Util.Bernays.PrimePowerMaximals
import Util.Bernays.TwoMaximalPowers
import Util.Bernays.GoodIdealNormFibers

/-!
# Exact enumeration of ideals with a good split-prime-power norm
-/

open scoped Classical

namespace Bernays

theorem InvertibleIdeal.cardQuot_dvd_listProd_of_mem {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] {P : InvertibleIdeal R} {l : List (InvertibleIdeal R)} (hP : P ∈ l) :
    (P : Ideal R).cardQuot ∣ ((l.prod : InvertibleIdeal R) : Ideal R).cardQuot := by
  obtain ⟨K, hK⟩ := List.dvd_prod hP
  exact ⟨(K : Ideal R).cardQuot, hK ▸ InvertibleIdeal.cardQuot_mul P K⟩

theorem SplitPrime.exists_powers_of_norm_primePower {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = s.1 ^ e →
      ∃ i : ℕ, i ≤ e ∧ I = s.ideal hD false ^ i * s.ideal hD true ^ (e - i) := by
  let := quadraticOrderIsDomain hD
  intro I hIF hnorm
  obtain ⟨l, hl, hmax⟩ := goodQuadraticIdeal_factorization hD I hIF
  have hsupport : ∀ P ∈ l, P = s.ideal hD false ∨ P = s.ideal hD true := by
    intro P hPl
    have hdiv : (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∣ s.1 ^ e := by
      rw [← hnorm, ← hl]
      exact InvertibleIdeal.cardQuot_dvd_listProd_of_mem hPl
    rcases goodMaximal_of_primePower_norm hD s.2.1 e P (hmax P hPl).1 (hmax P hPl).2 hdiv with
      h | ⟨t, ht, ε, hP⟩
    · exact False.elim (s.character_ne_neg_one hD.ne h.1)
    · have hts : t = s := Subtype.ext ht
      subst t
      cases ε
      · exact Or.inl hP
      · exact Or.inr hP
  let i := l.count (s.ideal hD false)
  let j := l.count (s.ideal hD true)
  have hprod : I = s.ideal hD false ^ i * s.ideal hD true ^ j :=
    hl.symm.trans (list_prod_two_values _ _ (s.ideal_ne_conjugate hD) l hsupport)
  have he : i + j = e := by
    apply Nat.pow_right_injective s.2.1.two_le
    have h := congrArg InvertibleIdeal.normHom hprod
    change (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = _ at h
    rw [map_mul, map_pow, map_pow] at h
    change (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot =
      (s.ideal hD false : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ^ i *
      (s.ideal hD true : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ^ j at h
    rw [hnorm, s.ideal_cardQuot hD false, s.ideal_cardQuot hD true, ← pow_add] at h
    exact h.symm
  exact ⟨i, by omega, by simpa only [show e - i = j by omega] using hprod⟩

noncomputable def SplitPrime.normPowerEquiv {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) (hc : s.1.Coprime (discriminantLevel (b ^ 2 + 4 * d))) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    Fin (e + 1) ≃ GoodIdealNormFiber (quadraticBadIdeal d b) (s.1 ^ e) := by
  letI := quadraticOrderIsDomain hD
  let O := QuadraticAlgebra ℤ d b
  have hnorm (i : Fin (e + 1)) :
      ((s.ideal hD false ^ i.1 * s.ideal hD true ^ (e - i.1) : InvertibleIdeal O) : Ideal O).cardQuot =
        s.1 ^ e := by
    change InvertibleIdeal.normHom (s.ideal hD false ^ i.1 * s.ideal hD true ^ (e - i.1)) = _
    rw [map_mul, map_pow, map_pow]
    change (s.ideal hD false : Ideal O).cardQuot ^ i.1 * (s.ideal hD true : Ideal O).cardQuot ^ (e - i.1) = _
    rw [s.ideal_cardQuot hD false, s.ideal_cardQuot hD true, ← pow_add, Nat.add_sub_of_le (by omega)]
  let f : Fin (e + 1) → GoodIdealNormFiber (quadraticBadIdeal d b) (s.1 ^ e) := fun i =>
    ⟨s.ideal hD false ^ i.1 * s.ideal hD true ^ (e - i.1), hnorm i,
      InvertibleIdeal.coprime_scalar_of_cardQuot_coprime _ _ (by rw [hnorm i]; exact hc.pow_left e)⟩
  apply Equiv.ofBijective f
  constructor
  · intro i j hij
    have hprod := congrArg Subtype.val hij
    have h := InvertibleIdeal.two_maximal_powers_injective _ _
      (s.ideal_isMaximal hD false) (s.ideal_isMaximal hD true) (s.ideal_ne_conjugate hD) hprod
    exact Fin.ext h.1
  · intro I
    obtain ⟨i, hie, hI⟩ := s.exists_powers_of_norm_primePower hD e I.1 I.2.2 I.2.1
    exact ⟨⟨i, by omega⟩, Subtype.ext hI.symm⟩

theorem SplitPrime.normPower_card {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    (s : SplitPrime d b) (hc : s.1.Coprime (discriminantLevel (b ^ 2 + 4 * d))) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    Nat.card (GoodIdealNormFiber (quadraticBadIdeal d b) (s.1 ^ e)) = e + 1 := by
  let := quadraticOrderIsDomain hD
  rw [← Nat.card_congr (s.normPowerEquiv hD hc e), Nat.card_fin]

end Bernays
