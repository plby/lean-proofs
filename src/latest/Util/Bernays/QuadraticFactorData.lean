import Util.Bernays.ClassPrimeFactors
import Util.Bernays.ClassSieveUpper
import Util.Bernays.IdealNormMonoid

/-!
# Norm and class data of good maximal ideals
-/

namespace Bernays

theorem quadratic_natCast_ne_zero {d b : ℤ} {q : ℕ} (hq : 0 < q) :
    (q : QuadraticAlgebra ℤ d b) ≠ 0 := by
  intro h
  have hr := congrArg QuadraticAlgebra.re h
  have hz : (q : ℤ) = 0 := by simpa using hr
  exact hq.ne' (by exact_mod_cast hz)

theorem SplitPrime.rootIdeal_eq_oriented {d b : ℤ} (s : SplitPrime d b)
    (r : ZMod s.1) (hr : r ^ 2 = (d : ZMod s.1) + (b : ZMod s.1) * r) :
    ∃ ε : Bool, rootIdeal d b s.1 r hr =
      rootIdeal d b s.1 (s.orientedRoot ε) (s.orientedRoot_sq ε) := by
  rcases s.root_eq_or_conjugate r hr with h | h
  · exact ⟨false, rootIdeal_eq_of_root_eq hr _ h⟩
  · exact ⟨true, rootIdeal_eq_of_root_eq hr _ h⟩

theorem goodMaximal_prime_description {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∃ q : ℕ, q.Prime ∧ q.Coprime (discriminantLevel (b ^ 2 + 4 * d)) ∧
        ((discriminantCharacter (b ^ 2 + 4 * d) hD.ne q = -1 ∧
          (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = q ^ 2 ∧ P.idealClass = 1) ∨
        ∃ s : SplitPrime d b, s.1 = q ∧ ∃ ε : Bool, P = s.ideal hD ε) := by
  let := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, hq, hqP⟩ := exists_natPrime_under_quadraticMaximal hD
    (P : Ideal (QuadraticAlgebra ℤ d b)) hP
  let : Fact q.Prime := ⟨hq⟩
  have hmem : ((q : ℤ) : QuadraticAlgebra ℤ d b) ∈ (P : Ideal (QuadraticAlgebra ℤ d b)) := by
    change (q : ℤ) ∈ (P : Ideal (QuadraticAlgebra ℤ d b)).under ℤ
    rw [hqP]
    exact Ideal.mem_span_singleton_self _
  have hnot := prime_not_dvd_level_of_coprime _ hP hmem hPF
  have hcop := hq.coprime_iff_not_dvd.mpr hnot
  have hqD : ¬(q : ℤ) ∣ b ^ 2 + 4 * d := by
    intro h
    exact hnot ((show q ∣ (b ^ 2 + 4 * d).natAbs by
      simpa using Int.natAbs_dvd_natAbs.mpr h).trans (dvd_mul_left _ _))
  refine ⟨q, hq, hcop, ?_⟩
  rcases quadraticMaximal_split_or_inert d b q (P : Ideal (QuadraticAlgebra ℤ d b)) hP hmem hqD with
    hprincipal | ⟨r, hr, hroot⟩
  · left
    have hnorm : (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = q ^ 2 := by
      rw [hprincipal, ← quadraticReduction_ker, quadraticReduction_cardQuot]
    have hclass : P.idealClass = 1 := by
      have heq : P = InvertibleIdeal.principal (q : QuadraticAlgebra ℤ d b)
          (quadratic_natCast_ne_zero hq.pos) := InvertibleIdeal.ext (by simpa using hprincipal)
      rw [heq, InvertibleIdeal.idealClass_principal]
    refine ⟨?_, hnorm, hclass⟩
    by_contra hn
    obtain ⟨r, hr⟩ := (discriminantCharacter_root_iff hD.ne hcop).mpr hn
    let s : SplitPrime d b := ⟨q, hq, hqD, r, hr⟩
    have hle : (P : Ideal (QuadraticAlgebra ℤ d b)) ≤
        (s.ideal hD false : Ideal (QuadraticAlgebra ℤ d b)) := by
      rw [hprincipal]
      exact (Ideal.span_singleton_le_iff_mem _).mpr (s.natCast_mem_ideal hD false)
    have heq := hP.eq_of_le (s.ideal_isMaximal hD false).ne_top hle
    have hqeq : q ^ 2 = q := by
      rw [← hnorm, heq]
      exact s.ideal_cardQuot hD false
    have htwo := hq.two_le
    nlinarith
  · right
    let s : SplitPrime d b := ⟨q, hq, hqD, r, hr⟩
    obtain ⟨ε, hε⟩ := s.rootIdeal_eq_oriented r hr
    exact ⟨s, rfl, ε, InvertibleIdeal.ext (hroot.trans hε)⟩

theorem SplitPrime.idealClass_toggle {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) (s : SplitPrime d b)
    (ε : Bool) :
    letI := quadraticOrderIsDomain hD
    (s.ideal hD (!ε)).idealClass = ((s.ideal hD ε).idealClass)⁻¹ := by
  let := quadraticOrderIsDomain hD
  cases ε
  · exact s.idealClass_conjugate hD
  · simpa only [Bool.not_true, s.idealClass_conjugate hD, inv_inv] using
      (show (s.ideal hD false).idealClass = s.idealClass hD from rfl)

theorem goodMaximal_inverseClass_sameNorm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ P : InvertibleIdeal (QuadraticAlgebra ℤ d b),
      (P : Ideal (QuadraticAlgebra ℤ d b)).IsMaximal →
      IsCoprime (P : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) →
      ∃ Q : InvertibleIdeal (QuadraticAlgebra ℤ d b), Q.idealClass = P.idealClass⁻¹ ∧
        (Q : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot := by
  let := quadraticOrderIsDomain hD
  intro P hP hPF
  obtain ⟨q, hq, hc, h | ⟨s, hs, ε, rfl⟩⟩ := goodMaximal_prime_description hD P hP hPF
  · exact ⟨P, by simp only [h.2.2, inv_one], rfl⟩
  · exact ⟨s.ideal hD (!ε), s.idealClass_toggle hD ε,
      (s.ideal_cardQuot hD (!ε)).trans (s.ideal_cardQuot hD ε).symm⟩

end Bernays
