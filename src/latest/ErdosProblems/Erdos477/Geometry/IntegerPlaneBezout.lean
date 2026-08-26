/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Applying the plane intersection bound to finite sets of integer points.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.PlaneBezout
import ErdosProblems.Erdos477.Geometry.FieldExtension

namespace Erdos477.Geometry

variable {K : Type*} [Field K] [CharZero K]

theorem card_integer_plane_common_zeroes_le (P Q : MvPolynomial (Fin 2) ℤ)
    (hP : Irreducible (MvPolynomial.map (Int.castRingHom K) P))
    (hdiv : ¬ MvPolynomial.map (Int.castRingHom K) P ∣ MvPolynomial.map (Int.castRingHom K) Q)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, MvPolynomial.eval z P = 0 ∧ MvPolynomial.eval z Q = 0) :
    S.card ≤ P.totalDegree * Q.totalDegree := by
  classical
  let π : (Fin 2 → ℤ) → K × K := fun z => (z 0, z 1)
  have hinj : Function.Injective π := by
    intro z w h
    have h0 : z 0 = w 0 := Int.cast_injective (congrArg Prod.fst h)
    have h1 : z 1 = w 1 := Int.cast_injective (congrArg Prod.snd h)
    ext k
    fin_cases k
    · exact h0
    · exact h1
  have h := card_common_zeroes_le (MvPolynomial.map (Int.castRingHom K) P)
    (MvPolynomial.map (Int.castRingHom K) Q) hP hdiv (S.image π) (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      have hvec : ![(π z).1, (π z).2] = fun k => (z k : K) := by ext k; fin_cases k <;> rfl
      rw [hvec, eval_integer_polynomial_map, eval_integer_polynomial_map,
        (hS z hz).1, (hS z hz).2, Int.cast_zero]
      exact ⟨rfl, rfl⟩)
  rw [Finset.card_image_of_injective _ hinj,
    totalDegree_map_of_injective _ Int.cast_injective,
    totalDegree_map_of_injective _ Int.cast_injective] at h
  exact h

theorem card_integer_plane_common_zeroes_le_of_degreeOf (d : ℕ) (hd : 0 < d)
    (P Q : MvPolynomial (Fin 2) ℤ)
    (hP : Irreducible (MvPolynomial.map (Int.castRingHom K) P))
    (hPdegree : P.degreeOf 0 = d) (hQ : Q ≠ 0) (hQdegree : Q.degreeOf 0 ≤ d - 1)
    (S : Finset (Fin 2 → ℤ))
    (hS : ∀ z ∈ S, MvPolynomial.eval z P = 0 ∧ MvPolynomial.eval z Q = 0) :
    S.card ≤ P.totalDegree * Q.totalDegree := by
  have hQmap : MvPolynomial.map (Int.castRingHom K) Q ≠ 0 := by
    intro h
    exact hQ ((MvPolynomial.map_injective _ Int.cast_injective) (h.trans (map_zero _).symm))
  apply card_integer_plane_common_zeroes_le (K := K) P Q hP _ S hS
  rintro ⟨G, hG⟩
  have hG0 : G ≠ 0 := by intro h; rw [h, mul_zero] at hG; exact hQmap hG
  have hdeg : (MvPolynomial.map (Int.castRingHom K) Q).degreeOf 0 ≤ d - 1 := by
    rw [degreeOf_map_of_injective _ Int.cast_injective]
    exact hQdegree
  rw [hG, MvPolynomial.degreeOf_mul_eq hP.ne_zero hG0,
    degreeOf_map_of_injective _ Int.cast_injective, hPdegree] at hdeg
  omega

#print axioms card_integer_plane_common_zeroes_le_of_degreeOf
-- 'Erdos477.Geometry.card_integer_plane_common_zeroes_le_of_degreeOf' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
