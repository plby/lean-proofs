import ErdosProblems.Erdos941.SphereGlobalToLocal
import ErdosProblems.Erdos941.PadicSphereCount

/-! # Bounding integral sphere-pair orbits by a finite product at odd primes -/

namespace Erdos941

open PairLocal

def spherePairDiscriminant (n e : ℤ) : ℤ := (-(2 * e)) ^ 2 - 4 * (-n) ^ 2

theorem spherePairDiscriminant_eq (n e : ℤ) :
    spherePairDiscriminant n e = -4 * (n ^ 2 - e ^ 2) := by
  dsimp [spherePairDiscriminant]
  ring

theorem spherePairDiscriminant_ne_zero {n e : ℤ} (h : e ^ 2 ≠ n ^ 2) :
    spherePairDiscriminant n e ≠ 0 := sub_ne_zero.mpr (sphere_split_nondegenerate h)

theorem spherePairOrbits_subsingleton_of_unit {R : Type*} [CommRing R]
    [NoZeroDivisors R] [CharZero R] {n e : R} (hunit : IsUnit (n ^ 2 - e ^ 2)) :
    Subsingleton (SpherePairOrbits R n e) := by
  refine ⟨fun x y => ?_⟩
  induction x, y using Quotient.inductionOn₂ with | h p q =>
    apply Quotient.sound
    apply MulAction.orbitRel_apply.mpr
    apply MulAction.mem_orbit_iff.mpr
    refine ⟨sphereFrameTransport q p hunit, ?_⟩
    apply Subtype.ext
    exact Prod.ext (sphereFrameTransport_first q p hunit)
      (sphereFrameTransport_second q p hunit)

theorem padic_isUnit_sphere_discriminant (p : ℕ) [Fact p.Prime] (n e : ℤ)
    (hgood : ¬ (p : ℤ) ∣ spherePairDiscriminant n e) :
    IsUnit ((n : PadicInt p) ^ 2 - (e : PadicInt p) ^ 2) := by
  have hunitZ : IsUnit ((n ^ 2 - e ^ 2 : ℤ) : PadicInt p) := by
    rw [PadicInt.isUnit_iff]
    apply le_antisymm (PadicInt.norm_le_one _)
    apply not_lt.mp
    rw [PadicInt.norm_int_lt_one_iff_dvd]
    intro h
    apply hgood
    rw [spherePairDiscriminant_eq]
    exact dvd_mul_of_dvd_right h (-4)
  simpa only [Int.cast_sub, Int.cast_pow] using hunitZ

theorem finite_padic_spherePairOrbits (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    {n e : PadicInt p} (base : SpherePair (PadicInt p) n e) (hnd : e ^ 2 ≠ n ^ 2) :
    Finite (SpherePairOrbits (PadicInt p) n e) := by
  obtain ⟨F, hF⟩ := exists_padic_sphere_split p hp2
  let := finite_padic_specialPairOrbits p (splitSpherePair F hF base)
    (sphere_split_nondegenerate hnd)
  exact Finite.of_injective (splitSphereOrbitMap F hF) (splitSphereOrbitMap_injective F hF)

abbrev BadSpherePrime (n e : ℤ) :=
  {p : ℕ // p ∈ (spherePairDiscriminant n e).natAbs.primeFactors.erase 2}

def BadLocalSphereOrbit (n e : ℤ) (p : BadSpherePrime n e) :=
  letI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase p.2)⟩
  SpherePairOrbits (PadicInt p.1) n e

noncomputable def badSphereOrbitMap {n e : ℤ} (x : SpherePairOrbits ℤ n e) :
    ∀ p : BadSpherePrime n e, BadLocalSphereOrbit n e p := fun p => by
  letI : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase p.2)⟩
  exact spherePairOrbitBaseChange (Int.castRingHom (PadicInt p.1)) x

theorem badSphereOrbitMap_injective {n e : ℤ} (hnd : e ^ 2 ≠ n ^ 2) :
    Function.Injective (badSphereOrbitMap (n := n) (e := e)) := by
  intro x y hxy
  induction x, y using Quotient.inductionOn₂ with | h src dst =>
    apply integer_pairOrbit_eq_of_local_eq src dst hnd
    intro p hp hp2
    by_cases hbad : p ∈ (spherePairDiscriminant n e).natAbs.primeFactors
    · exact congrFun hxy ⟨p, Finset.mem_erase.mpr ⟨hp2, hbad⟩⟩
    · have hgood : ¬ (p : ℤ) ∣ spherePairDiscriminant n e := by
        intro hdiv
        apply hbad
        exact (Fact.out : p.Prime).mem_primeFactors (Int.natCast_dvd.mp hdiv)
          (Int.natAbs_ne_zero.mpr (spherePairDiscriminant_ne_zero hnd))
      let := spherePairOrbits_subsingleton_of_unit (padic_isUnit_sphere_discriminant p n e hgood)
      exact Subsingleton.elim _ _

theorem finite_badLocalSphereOrbit {n e : ℤ} (base : SpherePair ℤ n e)
    (hnd : e ^ 2 ≠ n ^ 2) (p : BadSpherePrime n e) : Finite (BadLocalSphereOrbit n e p) := by
  let : Fact p.1.Prime := ⟨Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase p.2)⟩
  exact finite_padic_spherePairOrbits p.1 (Finset.ne_of_mem_erase p.2)
    (mapSpherePair (Int.castRingHom (PadicInt p.1)) base)
    (map_sphere_nondegenerate (Int.castRingHom (PadicInt p.1)) Int.cast_injective hnd)

theorem card_integer_spherePairOrbits_le_local_product {n e : ℤ} (base : SpherePair ℤ n e)
    (hnd : e ^ 2 ≠ n ^ 2) :
    Nat.card (SpherePairOrbits ℤ n e) ≤
      ∏ p : BadSpherePrime n e, Nat.card (BadLocalSphereOrbit n e p) := by
  let : ∀ p : BadSpherePrime n e, Finite (BadLocalSphereOrbit n e p) :=
    finite_badLocalSphereOrbit base hnd
  have h := Nat.card_le_card_of_injective _ (badSphereOrbitMap_injective hnd)
  rwa [Nat.card_pi] at h

end Erdos941
