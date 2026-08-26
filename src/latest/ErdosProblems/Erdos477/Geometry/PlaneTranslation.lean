/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Translation of plane polynomials preserves total degree and irreducibility.
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Geometry.LinearSubstitution

namespace Erdos477.Geometry

variable {K : Type*} [Field K]

noncomputable def planeTranslate (b : Fin 2 → K) :
    MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (fun i => MvPolynomial.X i + MvPolynomial.C (b i))

@[simp] lemma planeTranslate_C (b : Fin 2 → K) (c : K) :
    planeTranslate b (MvPolynomial.C c) = MvPolynomial.C c := by simp [planeTranslate]

@[simp] lemma planeTranslate_X (b : Fin 2 → K) (i : Fin 2) :
    planeTranslate b (MvPolynomial.X i) = MvPolynomial.X i + MvPolynomial.C (b i) := by
  simp [planeTranslate]

lemma planeTranslate_comp_neg (b : Fin 2 → K) :
    (planeTranslate b).comp (planeTranslate (-b)) = RingHom.id _ := by
  ext i : 2
  · simp
  · simp

noncomputable def planeTranslateEquiv (b : Fin 2 → K) :
    MvPolynomial (Fin 2) K ≃+* MvPolynomial (Fin 2) K :=
  { toFun := fun P => planeTranslate b P
    invFun := fun P => planeTranslate (-b) P
    left_inv := fun P => by
      have h := congrArg (fun f : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K => f P)
        (planeTranslate_comp_neg (-b))
      simpa only [neg_neg, RingHom.comp_apply, RingHom.id_apply] using h
    right_inv := fun P => congrArg
      (fun f : MvPolynomial (Fin 2) K →+* MvPolynomial (Fin 2) K => f P)
      (planeTranslate_comp_neg b)
    map_mul' := (planeTranslate b).map_mul
    map_add' := (planeTranslate b).map_add }

lemma totalDegree_planeTranslate_le (b : Fin 2 → K) (P : MvPolynomial (Fin 2) K) :
    (planeTranslate b P).totalDegree ≤ P.totalDegree := by
  apply totalDegree_linear_substitution
  intro i
  exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

lemma totalDegree_planeTranslate (b : Fin 2 → K) (P : MvPolynomial (Fin 2) K) :
    (planeTranslate b P).totalDegree = P.totalDegree := by
  apply (totalDegree_planeTranslate_le b P).antisymm
  have h := totalDegree_planeTranslate_le (-b) (planeTranslate b P)
  have hinv := (planeTranslateEquiv b).left_inv P
  change planeTranslate (-b) (planeTranslate b P) = P at hinv
  rwa [hinv] at h

lemma eval_planeTranslate (b z : Fin 2 → K) (P : MvPolynomial (Fin 2) K) :
    MvPolynomial.eval z (planeTranslate b P) = MvPolynomial.eval (z + b) P := by
  have hhom : (MvPolynomial.eval z).comp (planeTranslate b) = MvPolynomial.eval (z + b) := by
    ext i : 2
    · simp
    · simp
  exact congrArg (fun f : MvPolynomial (Fin 2) K →+* K => f P) hhom

lemma irreducible_planeTranslate (b : Fin 2 → K) (P : MvPolynomial (Fin 2) K)
    (hP : Irreducible P) : Irreducible (planeTranslate b P) :=
  (MulEquiv.irreducible_iff (planeTranslateEquiv b)).mpr hP

lemma pderiv_planeTranslate (b : Fin 2 → K) (P : MvPolynomial (Fin 2) K) (i : Fin 2) :
    MvPolynomial.pderiv i (planeTranslate b P) = planeTranslate b (MvPolynomial.pderiv i P) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p j hp =>
      by_cases h : i = j
      · subst j
        simp [hp, mul_comm, add_comm]
      · simp [hp, h, mul_comm]

lemma coeff_zero_planeTranslate (b : Fin 2 → K) (P : MvPolynomial (Fin 2) K) :
    (planeTranslate b P).coeff 0 = MvPolynomial.eval b P := by
  have h := eval_planeTranslate b 0 P
  simpa only [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq, zero_add] using h

lemma coeff_linear_planeTranslate (b : Fin 2 → K) (P : MvPolynomial (Fin 2) K) (i : Fin 2) :
    (planeTranslate b P).coeff (Finsupp.single i 1) =
      MvPolynomial.eval b (MvPolynomial.pderiv i P) := by
  have h := coeff_zero_planeTranslate b (MvPolynomial.pderiv i P)
  rw [← pderiv_planeTranslate, MvPolynomial.coeff_pderiv] at h
  simpa only [zero_add, Finsupp.zero_apply, Nat.cast_zero, Nat.cast_one, mul_one] using h

#print axioms irreducible_planeTranslate
-- 'Erdos477.Geometry.irreducible_planeTranslate' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477.Geometry
