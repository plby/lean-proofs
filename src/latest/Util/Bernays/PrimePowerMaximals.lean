import Util.Bernays.QuadraticFactorData
import Util.Bernays.SquareClassPrimes

/-!
# Maximal ideal factors of a good prime-power norm
-/

namespace Bernays

theorem inertMaximal_eq_principal {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime) (hc : p.Coprime (discriminantLevel (b ^ 2 + 4 * d)))
    (hχ : discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = p ^ 2 →
      P = InvertibleIdeal.principal (p : QuadraticAlgebra ℤ d b) (quadratic_natCast_ne_zero hp.pos) := by
  let := quadraticOrderIsDomain hD
  let : Fact p.Prime := ⟨hp⟩
  intro P hP hnorm
  have hmem : (p : QuadraticAlgebra ℤ d b) ^ 2 ∈ (P : Ideal (QuadraticAlgebra ℤ d b)) := by
    rw [← Nat.cast_pow, ← hnorm, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact Ideal.Quotient.index_eq_zero _
  have hpd : ¬ (p : ℤ) ∣ b ^ 2 + 4 * d := by
    intro h
    have hdvd : p ∣ discriminantLevel (b ^ 2 + 4 * d) :=
      (show p ∣ (b ^ 2 + 4 * d).natAbs by simpa using Int.natAbs_dvd_natAbs.mpr h).trans (dvd_mul_left _ _)
    exact (hp.coprime_iff_not_dvd.mp hc) hdvd
  have hpmem : ((p : ℤ) : QuadraticAlgebra ℤ d b) ∈ (P : Ideal (QuadraticAlgebra ℤ d b)) := by
    simpa only [Int.cast_natCast] using hP.isPrime.mem_of_pow_mem 2 hmem
  rcases quadraticMaximal_split_or_inert d b p (P : Ideal (QuadraticAlgebra ℤ d b)) hP hpmem hpd with
    hprincipal | ⟨r, hr, _⟩
  · exact InvertibleIdeal.ext (by simpa only [InvertibleIdeal.coe_principal, Int.cast_natCast] using hprincipal)
  · exact False.elim (((discriminantCharacter_root_iff hD.ne hc).mp ⟨r, hr⟩) hχ)

theorem SplitPrime.ideal_ne_conjugate {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b) :
    letI := quadraticOrderIsDomain hD
    s.ideal hD false ≠ s.ideal hD true := by
  let := quadraticOrderIsDomain hD
  intro h
  have heq := congrArg (fun I : InvertibleIdeal (QuadraticAlgebra ℤ d b) =>
    (I : Ideal (QuadraticAlgebra ℤ d b))) h
  exact rootIdeal_ne_of_ne d b s.1 s.root_sq (s.orientedRoot_sq true)
    (quadratic_roots_distinct _ _ _ s.root_sq s.discr_ne_zero) heq

theorem goodMaximal_of_primePower_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0)
    {p : ℕ} (hp : p.Prime) (e : ℕ) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∣ p ^ e →
      ((discriminantCharacter (b ^ 2 + 4 * d) hD.ne p = -1 ∧
        P = InvertibleIdeal.principal (p : QuadraticAlgebra ℤ d b) (quadratic_natCast_ne_zero hp.pos)) ∨
        ∃ s : SplitPrime d b, s.1 = p ∧ ∃ ε : Bool, P = s.ideal hD ε) := by
  let := quadraticOrderIsDomain hD
  intro P hP hPF hdiv
  obtain ⟨q, hq, hc, h | ⟨s, hs, ε, hP'⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · have hqp : q = p := by
      have hqdvd : q ∣ p ^ e := (dvd_pow_self q (by decide : 2 ≠ 0)).trans (h.2.1 ▸ hdiv)
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqdvd)
    subst q
    exact Or.inl ⟨h.1, inertMaximal_eq_principal hD hp hc h.1 P hP h.2.1⟩
  · have hqp : q = p := by
      have hn : (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = q := by
        rw [hP', s.ideal_cardQuot hD ε, hs]
      exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow (hn ▸ hdiv))
    exact Or.inr ⟨s, hs.trans hqp, ε, hP'⟩

end Bernays
