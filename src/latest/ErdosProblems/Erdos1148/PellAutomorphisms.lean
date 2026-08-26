import ErdosProblems.Erdos1148.FormAction

/-!
# Integral automorphisms from Pell's equation

Every integral form of positive nonsquare discriminant has a nontrivial
integral special-linear automorphism. This is the arithmetic input to
periodicity of its real diagonal-flow orbit.
-/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

def pellFormMatrix {R : Type*} [CommRing R] (t : R × R × R) (x y : R) :
    Matrix (Fin 2) (Fin 2) R :=
  !![x - t.2.1 * y, -2 * t.2.2 * y; 2 * t.1 * y, x + t.2.1 * y]

lemma det_pellFormMatrix {R : Type*} [CommRing R] (t : R × R × R) (x y : R) :
    (pellFormMatrix t x y).det = x ^ 2 - discr t * y ^ 2 := by
  simp only [Matrix.det_fin_two]
  dsimp [pellFormMatrix, discr]
  ring

lemma adjugate_pellFormMatrix {R : Type*} [CommRing R] (t : R × R × R) (x y : R) :
    (pellFormMatrix t x y).adjugate = pellFormMatrix t x (-y) := by
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> dsimp [pellFormMatrix] <;> ring

lemma transform_pellFormMatrix {R : Type*} [CommRing R] (t : R × R × R) (x y : R) :
    transform (pellFormMatrix t x y) t = (x ^ 2 - discr t * y ^ 2) • t := by
  ext <;> dsimp [transform, pellFormMatrix, discr] <;> ring

def pellFormAutomorphism {R : Type*} [CommRing R] (t : R × R × R) (x y : R)
    (h : x ^ 2 - discr t * y ^ 2 = 1) : SL(2, R) :=
  ⟨pellFormMatrix t x y, (det_pellFormMatrix t x y).trans h⟩

lemma pellFormAutomorphism_fixes {R : Type*} [CommRing R] (t : R × R × R) (x y : R)
    (h : x ^ 2 - discr t * y ^ 2 = 1) :
    formAction (pellFormAutomorphism t x y h) t = t := by
  rw [formAction, Matrix.SpecialLinearGroup.coe_inv]
  change transform (pellFormMatrix t x y).adjugate t = t
  rw [adjugate_pellFormMatrix, transform_pellFormMatrix, neg_sq, h, one_smul]

theorem exists_integral_form_automorphism {d : ℤ} (hd : 0 < d) (hns : ¬IsSquare d)
    {t : ℤ × ℤ × ℤ} (ht : discr t = d) :
    ∃ γ : SL(2, ℤ), formAction γ t = t ∧ 2 < γ 0 0 + γ 1 1 := by
  obtain ⟨p, hpx, _⟩ := Pell.Solution₁.exists_pos_of_not_isSquare hd hns
  have hp : p.x ^ 2 - discr t * p.y ^ 2 = 1 := by rw [ht]; exact p.prop
  refine ⟨pellFormAutomorphism t p.x p.y hp, pellFormAutomorphism_fixes _ _ _ _, ?_⟩
  change 2 < (p.x - t.2.1 * p.y) + (p.x + t.2.1 * p.y)
  omega

end Erdos1148.DukeArithmetic
