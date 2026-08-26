import ErdosProblems.Erdos941.SplitSphereOrbits
import ErdosProblems.Erdos941.PairLocal.IntegerLocalCount

/-! # The odd-prime local sphere-pair count -/

namespace Erdos941

theorem exists_padic_sphere_split (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ F : (PadicInt p × PadicInt p × PadicInt p) ≃ₗ[PadicInt p]
      (PadicInt p × PadicInt p × PadicInt p),
      ∀ v, PairLocal.discr (F v) = -normThree v := by
  obtain ⟨a, b, hab⟩ := padic_exists_sq_add_sq_neg_one p hp2
  have h2 : IsUnit (2 : PadicInt p) := by
    apply PadicInt.isUnit_iff.mpr
    apply PadicInt.norm_natCast_eq_one_iff.mpr
    exact (Nat.coprime_primes hp.out Nat.prime_two).mpr hp2
  let t : PadicInt p := ↑h2.unit⁻¹
  have ht : 2 * t = 1 := by
    have hu : (h2.unit : PadicInt p) * (↑h2.unit⁻¹ : PadicInt p) = 1 := by simp
    simpa only [h2.unit_spec] using hu
  exact ⟨sphereSplitEquiv hab ht, discr_sphereSplitEquiv hab ht⟩

theorem sphere_split_nondegenerate {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]
    {n e : R} (h : e ^ 2 ≠ n ^ 2) : (-(2 * e)) ^ 2 ≠ 4 * (-n) ^ 2 := by
  intro hh
  apply h
  apply mul_left_cancel₀ (by norm_num : (4 : R) ≠ 0)
  linear_combination hh

theorem card_padicSpherePairOrbits_le (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    {n e : ℤ} (base : SpherePair (PadicInt p) (n : PadicInt p) (e : PadicInt p))
    (hn : n ≠ 0) (hne : e ^ 2 ≠ n ^ 2) :
    Nat.card (SpherePairOrbits (PadicInt p) (n : PadicInt p) (e : PadicInt p)) ≤
      16 * (((-(2 * e)) ^ 2 - 4 * (-n) ^ 2).natAbs.factorization p + 1) *
        p ^ (((-n).natAbs.gcd (-(2 * e)).natAbs).factorization p / 2) := by
  obtain ⟨F, hF⟩ := exists_padic_sphere_split p hp2
  have hnd : (-(2 * e)) ^ 2 ≠ 4 * (-n) ^ 2 := sphere_split_nondegenerate hne
  have hndK := PairLocal.map_nondegenerate (Int.castRingHom (PadicInt p)) Int.cast_injective hnd
  let pair : PairLocal.FormPair (PadicInt p) ((-n : ℤ) : PadicInt p)
      ((-(2 * e) : ℤ) : PadicInt p) := by
    convert splitSpherePair F hF base using 1 <;> push_cast <;> rfl
  letI : Finite (PairLocal.SpecialPairOrbits (PadicInt p)
      (-(n : PadicInt p)) (-(2 * (e : PadicInt p)))) := by
    apply PairLocal.finite_padic_specialPairOrbits p (splitSpherePair F hF base)
    simpa only [Int.coe_castRingHom, Int.cast_neg, Int.cast_mul, Int.cast_ofNat] using hndK
  have hc := Nat.card_le_card_of_injective _ (splitSphereOrbitMap_injective F hF
    (n := (n : PadicInt p)) (e := (e : PadicInt p)))
  have hb := PairLocal.card_padicPairOrbits_le_factorization p pair (neg_ne_zero.mpr hn) hnd
  have he : Nat.card (PairLocal.SpecialPairOrbits (PadicInt p)
      (-(n : PadicInt p)) (-(2 * (e : PadicInt p)))) =
      Nat.card (PairLocal.SpecialPairOrbits (PadicInt p) ((-n : ℤ) : PadicInt p)
        ((-(2 * e) : ℤ) : PadicInt p)) := by push_cast; rfl
  rw [he] at hc
  exact hc.trans hb

end Erdos941
