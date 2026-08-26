/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A degree-preserving shear of the affine plane.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.LinearSubstitution

namespace Erdos477.Geometry

variable {K : Type*} [Field K]

noncomputable def shear (a : K) : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C
    ![MvPolynomial.X 0, MvPolynomial.X 1 - MvPolynomial.C a * MvPolynomial.X 0]

@[simp] lemma shear_C (a b : K) : shear a (MvPolynomial.C b) = MvPolynomial.C b := by
  simp [shear]

@[simp] lemma shear_X_zero (a : K) : shear a (MvPolynomial.X 0) = MvPolynomial.X 0 := by
  simp [shear]

@[simp] lemma shear_X_one (a : K) : shear a (MvPolynomial.X 1) =
    MvPolynomial.X 1 - MvPolynomial.C a * MvPolynomial.X 0 := by
  simp [shear]

lemma shear_comp_neg (a : K) : (shear a).comp (shear (-a)) = RingHom.id _ := by
  ext i : 2
  · simp
  · fin_cases i
    · simp
    · simp

noncomputable def shearEquiv (a : K) : MvPolynomial (Fin 2) K ≃+* MvPolynomial (Fin 2) K :=
  { toFun := fun P => shear a P
    invFun := fun P => shear (-a) P
    left_inv := fun P => by
      have h := congrArg (fun φ : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K => φ P)
        (shear_comp_neg (-a))
      simpa only [neg_neg, RingHom.comp_apply, RingHom.id_apply] using h
    right_inv := fun P => congrArg
      (fun φ : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K => φ P) (shear_comp_neg a)
    map_mul' := (shear a).map_mul
    map_add' := (shear a).map_add }

lemma totalDegree_shear_le (a : K) (P : MvPolynomial (Fin 2) K) :
    (shear a P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_linear_substitution
  intro i
  fin_cases i
  · simp
  · change (MvPolynomial.X 1 - MvPolynomial.C a * MvPolynomial.X (0 : Fin 2)).totalDegree ≤ 1
    apply (MvPolynomial.totalDegree_sub _ _).trans
    apply max_le
    · simp
    · have h := MvPolynomial.totalDegree_mul (MvPolynomial.C a) (MvPolynomial.X (0 : Fin 2))
      simpa only [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, zero_add] using h

lemma totalDegree_shear (a : K) (P : MvPolynomial (Fin 2) K) :
    (shear a P).totalDegree = P.totalDegree := by
  apply (totalDegree_shear_le a P).antisymm
  have h := totalDegree_shear_le (-a) (shear a P)
  have hinv := (shearEquiv a).left_inv P
  change shear (-a) (shear a P) = P at hinv
  rwa [hinv] at h

lemma eval_shear (a x y : K) (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval ![x, y + a * x] (shear a P) = MvPolynomial.eval ![x, y] P := by
  have hhom : (MvPolynomial.eval ![x, y + a * x]).comp (shear a) =
      MvPolynomial.eval ![x, y] := by
    ext i : 2
    · simp
    · fin_cases i
      · simp
      · simp
  exact congrArg (fun φ : MvPolynomial (Fin 2) K →+* K => φ P) hhom

#print axioms totalDegree_shear
-- 'Erdos477.Geometry.totalDegree_shear' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
