import Util.Bernays.QuadraticFactorData
import Util.Bernays.LocalParity
import Util.Bernays.SquareClassPrimes
import Mathlib.Data.Nat.Factorization.Induction

/-!
# Local conditions exactly characterize norms away from the discriminant
-/

namespace Bernays

theorem InvertibleIdeal.coprime_scalar_of_cardQuot_coprime {R : Type*} [CommRing R] [IsDomain R]
    [Ring.HasFiniteQuotients R] (I : InvertibleIdeal R) (M : ℕ)
    (h : (I : Ideal R).cardQuot.Coprime M) : IsCoprime (I : Ideal R) (Ideal.span {(M : R)}) := by
  have hc : IsCoprime ((I : Ideal R).cardQuot : R) (M : R) := by
    simpa only [map_natCast] using h.isCoprime.map (Int.castRingHom R)
  obtain ⟨a, b, hab⟩ := hc
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← hab]
  have hn : ((I : Ideal R).cardQuot : R) ∈ (I : Ideal R) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  exact (I : Ideal R).add_mem_sup
    ((I : Ideal R).mul_mem_left a hn)
    ((Ideal.span {(M : R)}).mul_mem_left b (Ideal.mem_span_singleton_self _))

theorem principal_nat_cardQuot {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) {n : ℕ} (hn : 0 < n) :
    letI := quadraticOrderIsDomain hD
    (InvertibleIdeal.principal (n : QuadraticAlgebra ℤ d b) (quadratic_natCast_ne_zero hn) :
      Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n ^ 2 := by
  let := quadraticOrderIsDomain hD
  rw [InvertibleIdeal.coe_principal, Erdos1081.cardQuot_span_singleton_eq_norm_natAbs,
    algebraNorm_quadraticOrder, QuadraticAlgebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast]

theorem parityAdmissible_mul (S : ℕ → Prop) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hSm : ParityAdmissible S m) (hSn : ParityAdmissible S n) : ParityAdmissible S (m * n) := by
  intro p hp hSp
  let : Fact p.Prime := ⟨hp⟩
  rw [padicValNat.mul hm.ne' hn.ne']
  exact (hSm p hp hSp).add (hSn p hp hSp)

theorem exists_ideal_primePower_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ p e : ℕ, p.Prime → 0 < e → (p ^ e).Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      ParityAdmissible (fun q : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne q = -1) (p ^ e) →
      ∃ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = p ^ e := by
  let := quadraticOrderIsDomain hD
  intro p e hp he hcop hlocal
  let : Fact p.Prime := ⟨hp⟩
  have hpcop : p.Coprime (discriminantLevel (b ^ 2 + 4 * d)) :=
    hcop.of_dvd_left (dvd_pow_self p he.ne')
  by_cases hχp : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1
  · have heven : Even e := ((parityAdmissible_prime_pow_iff _ hp).mp hlocal).resolve_left
      (not_not.mpr hχp)
    obtain ⟨t, ht⟩ := heven
    refine ⟨InvertibleIdeal.principal ((p ^ t : ℕ) : QuadraticAlgebra ℤ d b)
      (quadratic_natCast_ne_zero (pow_pos hp.pos _)), ?_⟩
    rw [principal_nat_cardQuot hD (pow_pos hp.pos _), ht, pow_add, pow_two]
  · obtain ⟨r, hr⟩ := (discriminantCharacter_root_iff hD.ne hpcop).mpr hχp
    have hpd : ¬(p : ℤ) ∣ b ^ 2 + 4 * d := by
      intro h
      have hdvd : p ∣ discriminantLevel (b ^ 2 + 4 * d) :=
        (show p ∣ (b ^ 2 + 4 * d).natAbs by simpa using Int.natAbs_dvd_natAbs.mpr h).trans (dvd_mul_left _ _)
      exact hp.not_dvd_one (hpcop.gcd_eq_one ▸ Nat.dvd_gcd (dvd_refl p) hdvd)
    let s : SplitPrime d b := ⟨p, hp, hpd, r, hr⟩
    refine ⟨s.ideal hD false ^ e, ?_⟩
    change InvertibleIdeal.normHom (s.ideal hD false ^ e) = p ^ e
    rw [map_pow]
    exact congrArg (fun n : ℕ => n ^ e) (s.ideal_cardQuot hD false)

theorem exists_ideal_norm_of_local {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ n : ℕ, 0 < n → n.Coprime (discriminantLevel (b ^ 2 + 4 * d)) →
      ParityAdmissible (fun p : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) n →
      ∃ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = n := by
  let := quadraticOrderIsDomain hD
  apply Nat.recOnPosPrimePosCoprime
  · intro p e hp he _ hc hl
    exact exists_ideal_primePower_norm hD p e hp he hc hl
  · intro h
    exact False.elim ((Nat.lt_irrefl 0) h)
  · intro _ _ _
    exact ⟨1, Submodule.cardQuot_top _ _⟩
  · intro m n hm hn hmn ih₁ ih₂ _ hc hl
    obtain ⟨hl₁, hl₂⟩ := (parityAdmissible_mul_iff _ (zero_lt_one.trans hm) (zero_lt_one.trans hn) hmn).mp hl
    obtain ⟨I, hI⟩ := ih₁ (zero_lt_one.trans hm) (hc.of_dvd_left (dvd_mul_right _ _)) hl₁
    obtain ⟨J, hJ⟩ := ih₂ (zero_lt_one.trans hn) (hc.of_dvd_left (dvd_mul_left _ _)) hl₂
    exact ⟨I * J, (InvertibleIdeal.cardQuot_mul I J).trans (by rw [hI, hJ])⟩

theorem local_of_goodMaximal_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ParityAdmissible (fun q : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne q = -1)
        (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  let := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, hq, hc, h | ⟨s, hs, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · rw [h.2.1]
    exact (parityAdmissible_prime_pow_iff _ hq).mpr (Or.inr (by decide))
  · rw [s.ideal_cardQuot hD ε]
    have h := (parityAdmissible_prime_pow_iff
      (fun q : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne q = -1) (k := 1) s.2.1).mpr
        (Or.inl (SplitPrime.character_ne_neg_one hD.ne s))
    simpa only [pow_one] using h

theorem local_of_goodIdeal_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ParityAdmissible (fun q : ℕ => discriminantCharacter (b ^ 2 + 4 * d) hD.ne q = -1)
        (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  let := quadraticOrderIsDomain hD
  intro I hIF
  obtain ⟨l, hl, hP⟩ := goodQuadraticIdeal_factorization hD I hIF
  rw [← hl]
  clear hl I hIF
  induction l with
  | nil => simp [ParityAdmissible, Submodule.cardQuot_top]
  | cons P l ih =>
    rw [List.prod_cons, InvertibleIdeal.cardQuot_mul]
    have hhead := hP P List.mem_cons_self
    exact parityAdmissible_mul _ P.cardQuot_pos l.prod.cardQuot_pos
      (local_of_goodMaximal_norm hD P hhead.1 hhead.2)
      (ih (fun Q hQ => hP Q (List.mem_cons_of_mem P hQ)))

end Bernays
