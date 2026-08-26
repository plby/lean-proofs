/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Both coordinate charts for a conic parametrization at a nonsingular point.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.SmallPlaneParametrization

namespace Erdos477.Geometry

open Polynomial

variable {K : Type*} [Field K]

def planeSwap : Fin 2 ≃ Fin 2 := Equiv.swap 0 1

def swappedPoint (z : Fin 2 → K) : Fin 2 → K := z ∘ planeSwap

omit [Field K] in
lemma swappedPoint_comp_swap (z : Fin 2 → K) : swappedPoint z ∘ planeSwap = z := by
  funext i
  simp [swappedPoint, planeSwap]

noncomputable def SmallPlaneParametrization.swap {P : MvPolynomial (Fin 2) K} {z : Fin 2 → K}
    (h : SmallPlaneParametrization (MvPolynomial.rename planeSwap P) (swappedPoint z)) :
    SmallPlaneParametrization P z := by
  let f := h.coordinate
  let g : Fin 3 → K[X] := ![f 1, f 0, f 2]
  refine {
    coordinate := g
    parameter := h.parameter
    scale := h.scale
    degree_le := ?_
    nonconstant := ?_
    no_common_root := ?_
    denominator_ne_zero := h.denominator_ne_zero
    scale_ne_zero := h.scale_ne_zero
    eval_first := ?_
    eval_second := ?_
    eval_denominator := h.eval_denominator
    equation := ?_ }
  · intro i
    fin_cases i
    · exact h.degree_le 1
    · exact h.degree_le 0
    · exact h.degree_le 2
  · obtain ⟨i, hi⟩ := h.nonconstant
    fin_cases i
    · exact ⟨1, hi⟩
    · exact ⟨0, hi⟩
    · exact ⟨2, hi⟩
  · intro r
    obtain ⟨i, hi⟩ := h.no_common_root r
    fin_cases i
    · exact ⟨1, hi⟩
    · exact ⟨0, hi⟩
    · exact ⟨2, hi⟩
  · change (h.coordinate 1).eval h.parameter = h.scale * z 0
    exact h.eval_second
  · change (h.coordinate 0).eval h.parameter = h.scale * z 1
    exact h.eval_first
  · have hcoords : rationalPlaneCoordinates g = rationalPlaneCoordinates f ∘ planeSwap := by
      funext i
      fin_cases i <;> rfl
    rw [hcoords]
    simpa only [MvPolynomial.eval₂Hom_rename] using h.equation

theorem exists_small_conic_parametrization (P : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) (hdegree : P.totalDegree = 2)
    (z : Fin 2 → K) (hroot : MvPolynomial.eval z P = 0)
    (hgradient : ∃ i, MvPolynomial.eval z (MvPolynomial.pderiv i P) ≠ 0) :
    Nonempty (SmallPlaneParametrization P z) := by
  obtain ⟨i, hi⟩ := hgradient
  fin_cases i
  · have hQ : Irreducible (MvPolynomial.rename planeSwap P) :=
      (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv K planeSwap)).mpr hP
    have hQdegree : (MvPolynomial.rename planeSwap P).totalDegree = 2 :=
      (MvPolynomial.totalDegree_renameEquiv planeSwap P).trans hdegree
    have hQroot : MvPolynomial.eval (swappedPoint z) (MvPolynomial.rename planeSwap P) = 0 := by
      rw [MvPolynomial.eval_rename, swappedPoint_comp_swap]
      exact hroot
    have hderiv : MvPolynomial.pderiv 1 (MvPolynomial.rename planeSwap P) =
        MvPolynomial.rename planeSwap (MvPolynomial.pderiv 0 P) := by
      simpa only [planeSwap, Equiv.swap_apply_left] using
        MvPolynomial.pderiv_rename planeSwap.injective 0 P
    have hQgradient : MvPolynomial.eval (swappedPoint z)
        (MvPolynomial.pderiv 1 (MvPolynomial.rename planeSwap P)) ≠ 0 := by
      rw [hderiv, MvPolynomial.eval_rename, swappedPoint_comp_swap]
      exact hi
    obtain ⟨h⟩ := exists_small_conic_parametrization_second_chart _ hQ hQdegree _ hQroot hQgradient
    exact ⟨h.swap⟩
  · exact exists_small_conic_parametrization_second_chart P hP hdegree z hroot hi

#print axioms exists_small_conic_parametrization
-- 'Erdos477.Geometry.exists_small_conic_parametrization' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
