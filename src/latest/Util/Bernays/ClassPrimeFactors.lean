import Util.Bernays.SplitPrimeClasses

/-!
# Detecting a split-prime class outside a proper subgroup
-/

namespace Bernays

theorem rootIdeal_eq_of_root_eq {d b : ℤ} {q : ℕ} {r s : ZMod q}
    (hr : r ^ 2 = (d : ZMod q) + (b : ZMod q) * r)
    (hs : s ^ 2 = (d : ZMod q) + (b : ZMod q) * s) (hrs : r = s) :
    rootIdeal d b q r hr = rootIdeal d b q s hs := by
  subst s
  rfl

theorem exists_splitPrime_factor_outside {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ H : Subgroup (ClassGroup (QuadraticAlgebra ℤ d b)),
      ∀ I : InvertibleIdeal (QuadraticAlgebra ℤ d b),
        IsCoprime (I : Ideal (QuadraticAlgebra ℤ d b)) (quadraticBadIdeal d b) → I.idealClass ∉ H →
        ∃ s : SplitPrime d b, s.idealClass hD ∉ H ∧
          s.1 ≤ (I : Ideal (QuadraticAlgebra ℤ d b)).cardQuot ∧
          ∃ ε : Bool, ∃ J : InvertibleIdeal (QuadraticAlgebra ℤ d b), s.ideal hD ε * J = I := by
  letI := quadraticOrderIsDomain hD
  intro H I hIF hIH
  obtain ⟨P, J, hP, hPF, hPH, hPJ⟩ := InvertibleIdeal.exists_maximal_factor_class_not_mem
    (quadraticBadIdeal d b) (quadraticMaximal_coprime_isUnit hD) H I hIF hIH
  obtain ⟨q, hq, hqP⟩ := exists_natPrime_under_quadraticMaximal hD
    (P : Ideal (QuadraticAlgebra ℤ d b)) hP
  letI : Fact q.Prime := ⟨hq⟩
  have hmem : ((q : ℤ) : QuadraticAlgebra ℤ d b) ∈ (P : Ideal (QuadraticAlgebra ℤ d b)) := by
    change (q : ℤ) ∈ (P : Ideal (QuadraticAlgebra ℤ d b)).under ℤ
    rw [hqP]
    exact Ideal.mem_span_singleton_self _
  have hnot := prime_not_dvd_level_of_coprime (P : Ideal (QuadraticAlgebra ℤ d b)) hP hmem hPF
  have hqD : ¬ (q : ℤ) ∣ b ^ 2 + 4 * d := by
    intro hdvd
    have hn : q ∣ (b ^ 2 + 4 * d).natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hdvd
    exact hnot (hn.trans (dvd_mul_left _ _))
  rcases quadraticMaximal_split_or_inert d b q (P : Ideal (QuadraticAlgebra ℤ d b)) hP hmem hqD with
    hprincipal | ⟨r, hr, hroot⟩
  · exfalso
    apply hPH
    have hz : ((q : ℤ) : QuadraticAlgebra ℤ d b) ≠ 0 := by
      intro hz
      have h := congrArg QuadraticAlgebra.re hz
      have : (q : ℤ) = 0 := by simpa using h
      exact hq.ne_zero (by exact_mod_cast this)
    have heq : P = InvertibleIdeal.principal ((q : ℤ) : QuadraticAlgebra ℤ d b) hz :=
      InvertibleIdeal.ext hprincipal
    rw [heq, InvertibleIdeal.idealClass_principal]
    exact H.one_mem
  · let s : SplitPrime d b := ⟨q, hq, hqD, r, hr⟩
    have hs : ∃ ε : Bool, P = s.ideal hD ε := by
      rcases s.root_eq_or_conjugate r hr with h | h
      · refine ⟨false, InvertibleIdeal.ext ?_⟩
        change (P : Ideal (QuadraticAlgebra ℤ d b)) = rootIdeal d b q s.root s.root_sq
        exact hroot.trans (rootIdeal_eq_of_root_eq hr s.root_sq h)
      · refine ⟨true, InvertibleIdeal.ext ?_⟩
        change (P : Ideal (QuadraticAlgebra ℤ d b)) =
          rootIdeal d b q ((b : ZMod q) - s.root) (s.orientedRoot_sq true)
        exact hroot.trans (rootIdeal_eq_of_root_eq hr (s.orientedRoot_sq true) h)
    obtain ⟨ε, hε⟩ := hs
    refine ⟨s, ?_, ?_, ε, J, by rwa [← hε]⟩
    · intro h
      apply hPH
      rw [hε]
      exact (s.oriented_idealClass_mem_iff hD H ε).mpr h
    · have hnorm := InvertibleIdeal.cardQuot_mul P J
      rw [hPJ] at hnorm
      have hPnorm : (P : Ideal (QuadraticAlgebra ℤ d b)).cardQuot = s.1 := by
        rw [hε, s.ideal_cardQuot hD ε]
      rw [hnorm, ← hPnorm]
      exact Nat.le_mul_of_pos_right _ J.cardQuot_pos

end Bernays
