import ErdosProblems.Erdos633.ReptileCosineDegree
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Cyclotomic degree from a quadratic cosine

A root of a quadratic over a field of degree at most two has degree at most
four. Applied to the complex exponential of an angle, this bounds the
totient of its rational rotation denominator. The cosine hypothesis is
supplied by the actual reptiling boundary matrix, not postulated for tiles.
-/

namespace Erdos633

open Polynomial

theorem quadratic_over_quadratic_degree_le_four (a z : ℂ)
    (ha : IsIntegral ℚ a) (hdeg : (minpoly ℚ a).natDegree ≤ 2)
    (hrel : z ^ 2 - 2 * a * z + 1 = 0) :
    IsIntegral ℚ z ∧ (minpoly ℚ z).natDegree ≤ 4 := by
  let K := IntermediateField.adjoin ℚ ({a} : Set ℂ)
  let aK : K := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ a⟩
  let p : K[X] := X ^ 2 - C (2 * aK) * X + 1
  have hp : p.Monic := by dsimp [p]; monicity <;> norm_num
  have hpdeg : p.natDegree ≤ 2 := by dsimp [p]; compute_degree
  have hcoe : (algebraMap K ℂ) aK = a := rfl
  have heval : aeval z p = 0 := by
    simpa only [p, map_add, map_sub, map_mul, map_pow, map_one, aeval_X, aeval_C,
      map_ofNat, hcoe] using hrel
  have hzK : IsIntegral K z := ⟨p, hp, heval⟩
  have hzdeg : (minpoly K z).natDegree ≤ 2 :=
    (natDegree_le_natDegree (minpoly.min K z hp heval)).trans hpdeg
  let L := IntermediateField.adjoin K ({z} : Set ℂ)
  let : FiniteDimensional ℚ K := IntermediateField.adjoin.finiteDimensional ha
  let : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hzK
  let : FiniteDimensional ℚ L := Module.Finite.trans K L
  have hK : Module.finrank ℚ K ≤ 2 := by
    rw [IntermediateField.adjoin.finrank ha]
    exact hdeg
  have hL : Module.finrank K L ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hzK]
    exact hzdeg
  have hdim : Module.finrank ℚ L ≤ 4 := by
    rw [← Module.finrank_mul_finrank ℚ K L]
    nlinarith only [hK, hL, Nat.mul_le_mul hK hL]
  let w : L := ⟨z, IntermediateField.mem_adjoin_simple_self K z⟩
  have hw : IsIntegral ℚ w := IsIntegral.of_finite ℚ w
  have hmap : minpoly ℚ z = minpoly ℚ w :=
    minpoly.algebraMap_eq (algebraMap L ℂ).injective w
  refine ⟨hw.map (IsScalarTower.toAlgHom ℚ L ℂ), ?_⟩
  rw [hmap]
  exact (minpoly.natDegree_le w).trans hdim

theorem complex_exp_angle_quadratic (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) ^ 2 -
      2 * (Real.cos θ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) + 1 = 0 := by
  have he : Complex.exp (-(θ : ℂ) * Complex.I) *
      Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add, show -(θ : ℂ) * Complex.I + (θ : ℂ) * Complex.I = 0 by ring,
      Complex.exp_zero]
  have h := congrArg (fun w : ℂ => w * Complex.exp ((θ : ℂ) * Complex.I))
    (Complex.two_cos (θ : ℂ))
  rw [add_mul, he, ← Complex.ofReal_cos] at h
  linear_combination -h

theorem exp_angle_degree_le_four (θ : ℝ)
    (hcos : IsIntegral ℚ (Real.cos θ)) (hdeg : (minpoly ℚ (Real.cos θ)).natDegree ≤ 2) :
    IsIntegral ℚ (Complex.exp ((θ : ℂ) * Complex.I)) ∧
      (minpoly ℚ (Complex.exp ((θ : ℂ) * Complex.I))).natDegree ≤ 4 := by
  have ha : IsIntegral ℚ (Real.cos θ : ℂ) :=
    hcos.map (IsScalarTower.toAlgHom ℚ ℝ ℂ)
  have hmap : minpoly ℚ (Real.cos θ : ℂ) = minpoly ℚ (Real.cos θ) :=
    minpoly.algebraMap_eq (algebraMap ℝ ℂ).injective (Real.cos θ)
  exact quadratic_over_quadratic_degree_le_four _ _ ha (hmap ▸ hdeg)
    (complex_exp_angle_quadratic θ)

theorem rational_rotation_totient_le_four (q : ℚ)
    (hcos : IsIntegral ℚ (Real.cos (2 * Real.pi * q)))
    (hdeg : (minpoly ℚ (Real.cos (2 * Real.pi * q))).natDegree ≤ 2) :
    q.den.totient ≤ 4 := by
  have h := (exp_angle_degree_le_four (2 * Real.pi * q) hcos hdeg).2
  have he : (((2 * Real.pi * (q : ℝ) : ℝ) : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I * q := by push_cast; ring
  rw [he, ← cyclotomic_eq_minpoly_rat (Complex.isPrimitiveRoot_exp_rat q) q.den_pos,
    natDegree_cyclotomic] at h
  exact h

end Erdos633
