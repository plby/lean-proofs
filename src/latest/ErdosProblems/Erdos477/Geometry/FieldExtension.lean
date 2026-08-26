/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Preserving the auxiliary-polynomial properties under extension to characteristic zero.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SurfaceIrreducible
import ErdosProblems.Erdos477.Counting.SurfacePolynomial

namespace Erdos477.Geometry

variable {σ R S : Type*} [CommSemiring R] [CommSemiring S]

lemma degreeOf_map_of_injective (f : R →+* S) (hf : Function.Injective f)
    (P : MvPolynomial σ R) (i : σ) : (MvPolynomial.map f P).degreeOf i = P.degreeOf i := by
  classical
  simp only [MvPolynomial.degreeOf, MvPolynomial.degrees_map_of_injective P hf]

lemma totalDegree_map_of_injective (f : R →+* S) (hf : Function.Injective f)
    (P : MvPolynomial σ R) : (MvPolynomial.map f P).totalDegree = P.totalDegree := by
  simp only [MvPolynomial.totalDegree, MvPolynomial.support_map_of_injective P hf]

variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
lemma map_integer_sexticSurface (c : ℤ) :
    MvPolynomial.map (Int.castRingHom K) (Counting.sexticSurface c) =
      sexticSurface (c : K) := by
  simp [Counting.sexticSurface, sexticSurface]

lemma degreeOf_integer_sexticSurface (c : ℤ) :
    (sexticSurface (c : K)).degreeOf 2 = 6 := by
  rw [← map_integer_sexticSurface, degreeOf_map_of_injective _ Int.cast_injective,
    Counting.degreeOf_sexticSurface]

/-- The auxiliary is still nonzero and independent of the surface after
extending coefficients; its degrees are unchanged. -/
theorem integer_auxiliary_field_extension (c : ℤ) (P : MvPolynomial (Fin 3) ℤ)
    (hP : P ≠ 0) (hdegree : P.degreeOf 2 ≤ 5) :
    let Q := MvPolynomial.map (Int.castRingHom K) P
    Q ≠ 0 ∧ Q.degreeOf 2 ≤ 5 ∧ Q.totalDegree = P.totalDegree ∧
      ¬ sexticSurface (c : K) ∣ Q := by
  intro Q
  have hinj : Function.Injective (MvPolynomial.map (σ := Fin 3) (Int.castRingHom K)) :=
    MvPolynomial.map_injective _ Int.cast_injective
  have hQ : Q ≠ 0 := by
    intro h
    apply hP
    exact hinj (h.trans (map_zero _).symm)
  have hQdegree : Q.degreeOf 2 ≤ 5 := by
    rw [degreeOf_map_of_injective _ Int.cast_injective]
    exact hdegree
  refine ⟨hQ, hQdegree, totalDegree_map_of_injective _ Int.cast_injective P, ?_⟩
  rintro ⟨G, hG⟩
  have hG0 : G ≠ 0 := by intro h; rw [h, mul_zero] at hG; exact hQ hG
  have hF0 : sexticSurface (c : K) ≠ 0 :=
    MvPolynomial.ne_zero_of_degreeOf_ne_zero (by rw [degreeOf_integer_sexticSurface]; decide)
  rw [hG, MvPolynomial.degreeOf_mul_eq hF0 hG0, degreeOf_integer_sexticSurface] at hQdegree
  omega

omit [CharZero K] in
lemma eval_integer_polynomial_map (P : MvPolynomial σ ℤ) (z : σ → ℤ) :
    MvPolynomial.eval (fun i => (z i : K)) (MvPolynomial.map (Int.castRingHom K) P) =
      (MvPolynomial.eval z P : K) := by
  rw [MvPolynomial.eval_map]
  change MvPolynomial.eval₂ (Int.castRingHom K) ((Int.castRingHom K) ∘ z) P = _
  rw [← MvPolynomial.eval₂_comp]
  rfl

#print axioms integer_auxiliary_field_extension
-- 'Erdos477.Geometry.integer_auxiliary_field_extension' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
