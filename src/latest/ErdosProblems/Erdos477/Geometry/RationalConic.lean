/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Rational-function evaluation of the explicit conic parametrization.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.CenteredConic

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

lemma eval₂_planeTranslate {R : Type*} [CommRing R] (φ : K →+* R)
    (b : Fin 2 → K) (z : Fin 2 → R) (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval₂Hom φ z (planeTranslate b P) =
      MvPolynomial.eval₂Hom φ (fun i => z i + φ (b i)) P := by
  have hhom : (MvPolynomial.eval₂Hom φ z).comp (planeTranslate b) =
      MvPolynomial.eval₂Hom φ (fun i => z i + φ (b i)) := by
    ext i : 2
    · simp
    · simp
  exact congrArg (fun f : MvPolynomial (Fin 2) K →+* R => f P) hhom

lemma eval₂_planeQuadratic {R : Type*} [CommRing R] (φ : K →+* R)
    (a : Fin 6 → K) (x y : R) :
    MvPolynomial.eval₂Hom φ ![x, y] (planeQuadratic a) =
      φ (a 0) * x ^ 2 + φ (a 1) * x * y + φ (a 2) * y ^ 2 +
        φ (a 3) * x + φ (a 4) * y + φ (a 5) := by
  simp [planeQuadratic_eq]

lemma conicDenominator_ne_zero (a b c d e : K) (he : e ≠ 0)
    (h : a * e ^ 2 - b * d * e + c * d ^ 2 ≠ 0) : conicDenominator a b c ≠ 0 := by
  obtain ⟨v, hv, _, _, hbase⟩ := conicCoordinates_at_base a b c d e he h
  intro hzero
  change (conicDenominator a b c).eval (-d / e) = v at hbase
  rw [hzero, eval_zero] at hbase
  exact hv hbase.symm

noncomputable def conicRationalCoordinates (a b c d e : K) : Fin 2 → RatFunc K :=
  ![algebraMap K[X] (RatFunc K) (conicNumerator d e) /
      algebraMap K[X] (RatFunc K) (conicDenominator a b c),
    algebraMap K[X] (RatFunc K) (X * conicNumerator d e) /
      algebraMap K[X] (RatFunc K) (conicDenominator a b c)]

theorem conicRationalCoordinates_root (a b c d e : K) (he : e ≠ 0)
    (h : a * e ^ 2 - b * d * e + c * d ^ 2 ≠ 0) :
    MvPolynomial.eval₂Hom RatFunc.C (conicRationalCoordinates a b c d e)
      (planeQuadratic ![a, b, c, d, e, 0]) = 0 := by
  have hW : algebraMap K[X] (RatFunc K) (conicDenominator a b c) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr
      (conicDenominator_ne_zero a b c d e he h)
  have hidentity := congrArg (algebraMap K[X] (RatFunc K)) (conicCoordinates_identity a b c d e)
  simp only [map_add, map_mul, map_pow, map_zero, RatFunc.algebraMap_C] at hidentity
  change RatFunc.C a *
      algebraMap K[X] (RatFunc K) (conicNumerator d e) ^ 2 +
    RatFunc.C b * algebraMap K[X] (RatFunc K) (conicNumerator d e) *
      algebraMap K[X] (RatFunc K) (X * conicNumerator d e) +
    RatFunc.C c * algebraMap K[X] (RatFunc K) (X * conicNumerator d e) ^ 2 +
    RatFunc.C d * algebraMap K[X] (RatFunc K) (conicNumerator d e) *
      algebraMap K[X] (RatFunc K) (conicDenominator a b c) +
    RatFunc.C e * algebraMap K[X] (RatFunc K) (X * conicNumerator d e) *
      algebraMap K[X] (RatFunc K) (conicDenominator a b c) = 0 at hidentity
  rw [conicRationalCoordinates, eval₂_planeQuadratic]
  change RatFunc.C a *
      (algebraMap K[X] (RatFunc K) (conicNumerator d e) /
        algebraMap K[X] (RatFunc K) (conicDenominator a b c)) ^ 2 +
    RatFunc.C b *
      (algebraMap K[X] (RatFunc K) (conicNumerator d e) /
        algebraMap K[X] (RatFunc K) (conicDenominator a b c)) *
      (algebraMap K[X] (RatFunc K) (X * conicNumerator d e) /
        algebraMap K[X] (RatFunc K) (conicDenominator a b c)) +
    RatFunc.C c *
      (algebraMap K[X] (RatFunc K) (X * conicNumerator d e) /
        algebraMap K[X] (RatFunc K) (conicDenominator a b c)) ^ 2 +
    RatFunc.C d *
      (algebraMap K[X] (RatFunc K) (conicNumerator d e) /
        algebraMap K[X] (RatFunc K) (conicDenominator a b c)) +
    RatFunc.C e *
      (algebraMap K[X] (RatFunc K) (X * conicNumerator d e) /
        algebraMap K[X] (RatFunc K) (conicDenominator a b c)) + RatFunc.C 0 = 0
  rw [map_zero, add_zero]
  field_simp
  linear_combination hidentity

#print axioms conicRationalCoordinates_root
-- 'Erdos477.Geometry.conicRationalCoordinates_root' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
