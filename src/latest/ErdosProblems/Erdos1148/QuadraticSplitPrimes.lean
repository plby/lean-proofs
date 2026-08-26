import ErdosProblems.Erdos1148.QuadraticRootArithmetic
import ErdosProblems.Erdos1148.LinearRootPrimeIdeal
import ErdosProblems.Erdos1148.QuadraticCharacterNonprincipal

/-! # Two prime ideals above a good prime with positive quadratic symbol -/

namespace Erdos1148.DukeArithmetic

open NumberField Polynomial

theorem exists_two_primeIdeals_of_legendre_one {d : ℤ} [Fact (¬IsSquare d)]
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) {p : ℕ} [Fact p.Prime]
    (hp : ¬(p : ℤ) ∣ 2 * d) (hleg : legendreSym p d = 1) :
    ∃ P Q : Ideal (𝓞 (QuadraticDiscrAlgebra d)),
      Prime P ∧ Prime Q ∧ P ≠ Q ∧ Ideal.absNorm P = p ∧ Ideal.absNorm Q = p := by
  have hd0 : (d : ZMod p) ≠ 0 := by
    intro h
    exact hp (dvd_mul_of_dvd_right ((ZMod.intCast_zmod_eq_zero_iff_dvd d p).mp h) 2)
  have ht0 : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdiv := (ZMod.intCast_zmod_eq_zero_iff_dvd 2 p).mp (by simpa using h)
    exact hp (dvd_mul_of_dvd_left hdiv d)
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff p hd0).mp hleg
  have hrsq : r ^ 2 = (d : ZMod p) := by simpa only [pow_two] using hr.symm
  have hr0 : r ≠ 0 := by
    intro h
    exact hd0 (by simpa only [h, zero_pow (by norm_num : 2 ≠ 0)] using hrsq.symm)
  have hne : r ≠ -r := by
    intro h
    have hz : (2 : ZMod p) * r = 0 := by linear_combination h
    exact (mul_ne_zero ht0 hr0) hz
  have hroot (s : ZMod p) (hs : s ^ 2 = (d : ZMod p)) :
      ((minpoly ℤ (quadraticIntegerRoot d)).map (Int.castRingHom (ZMod p))).eval s = 0 := by
    rw [quadraticIntegerRoot_minpoly]
    simp [hs]
  have hplus := hroot r hrsq
  have hminus := hroot (-r) (by simpa only [neg_sq] using hrsq)
  have hexp := quadraticIntegerRoot_prime_not_dvd_exponent ht hp
  refine ⟨linearRootPrimeIdeal hexp hplus, linearRootPrimeIdeal hexp hminus,
    linearRootPrimeIdeal_prime hexp hplus, linearRootPrimeIdeal_prime hexp hminus,
    ?_, linearRootPrimeIdeal_absNorm hexp hplus, linearRootPrimeIdeal_absNorm hexp hminus⟩
  exact fun h => hne (linearRootPrimeIdeal_injective hexp hplus hminus h)

end Erdos1148.DukeArithmetic
