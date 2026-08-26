import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.RamificationInertia.Inertia

/-! # Prime ideals of norm p from linear factors of a minimal polynomial -/

namespace Erdos1148.DukeArithmetic

open NumberField Polynomial RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]
variable {p : ℕ} [Fact p.Prime] {θ : 𝓞 K}

lemma linear_factor_mem_monicFactorsMod {r : ZMod p}
    (hr : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).eval r = 0) :
    X - C r ∈ monicFactorsMod θ p := by
  classical
  apply Multiset.mem_toFinset.mpr
  apply (Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic θ.isIntegral))).mpr
  exact ⟨irreducible_X_sub_C r, monic_X_sub_C r, dvd_iff_isRoot.mpr hr⟩

noncomputable def linearRootPrimeIdeal (hp : ¬p ∣ exponent θ) {r : ZMod p}
    (hr : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).eval r = 0) : Ideal (𝓞 K) :=
  ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
    ⟨X - C r, linear_factor_mem_monicFactorsMod hr⟩ : Ideal (𝓞 K))

theorem linearRootPrimeIdeal_prime (hp : ¬p ∣ exponent θ) {r : ZMod p}
    (hr : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).eval r = 0) :
    Prime (linearRootPrimeIdeal hp hr) := by
  apply Ideal.prime_of_mem_primesOver (by simp [NeZero.ne p] : Ideal.span {(p : ℤ)} ≠ ⊥)
  exact ((NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
    ⟨X - C r, linear_factor_mem_monicFactorsMod hr⟩).prop

theorem linearRootPrimeIdeal_absNorm (hp : ¬p ∣ exponent θ) {r : ZMod p}
    (hr : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).eval r = 0) :
    Ideal.absNorm (linearRootPrimeIdeal hp hr) = p := by
  let P := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm
    ⟨X - C r, linear_factor_mem_monicFactorsMod hr⟩
  have : P.val.IsPrime := P.prop.1
  have : P.val.LiesOver (Ideal.span {(p : ℤ)}) := P.prop.2
  change Ideal.absNorm P.val = p
  rw [← Ideal.pow_inertiaDeg p P.val]
  have hdeg := NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
    hp (linear_factor_mem_monicFactorsMod hr)
  change P.val.inertiaDeg ℤ = (X - C r).natDegree at hdeg
  rw [hdeg, natDegree_X_sub_C, pow_one]

theorem linearRootPrimeIdeal_injective (hp : ¬p ∣ exponent θ) {r s : ZMod p}
    (hr : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).eval r = 0)
    (hs : ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).eval s = 0)
    (heq : linearRootPrimeIdeal hp hr = linearRootPrimeIdeal hp hs) : r = s := by
  have hsub := (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp).symm.injective
    (Subtype.ext heq)
  have hpoly := congrArg Subtype.val hsub
  have hcoeff := congrArg (fun f : (ZMod p)[X] => f.coeff 0) hpoly
  simpa only [coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, neg_inj] using hcoeff

end Erdos1148.DukeArithmetic
