import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Ordered coordinates for sums of finite integral lattices

These equivalences compose Mathlib's sum-indexed function equivalence
with the usual equivalence `Fin a ⊕ Fin b ≃ Fin (a+b)`. The first block
is the left endpoint and the second block is the right endpoint, with
explicit evaluation formulas for both directions.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyFreeCoordinates

/-- Concatenate two integral coordinate blocks, keeping the left block first. -/
def freeCoordinateSumEquiv (a b : ℕ) :
    ((Fin a → ℤ) × (Fin b → ℤ)) ≃ₗ[ℤ] (Fin (a + b) → ℤ) :=
  (((LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin b) ℤ ℤ).symm.toAddEquiv).trans
    (LinearEquiv.piCongrLeft' ℤ (fun _ : Fin a ⊕ Fin b => ℤ)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).toAddEquiv).toIntLinearEquiv

/-- Left-block coordinates are unchanged by concatenation. -/
@[simp] theorem freeCoordinateSumEquiv_apply_left (a b : ℕ)
    (x : Fin a → ℤ) (y : Fin b → ℤ) (i : Fin a) :
    freeCoordinateSumEquiv a b (x, y) (Fin.castAdd b i) = x i := by
  change Sum.elim x y (finSumFinEquiv.symm (Fin.castAdd b i)) = x i
  rw [finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- Right-block coordinates are unchanged, after the left block. -/
@[simp] theorem freeCoordinateSumEquiv_apply_right (a b : ℕ)
    (x : Fin a → ℤ) (y : Fin b → ℤ) (i : Fin b) :
    freeCoordinateSumEquiv a b (x, y) (Fin.natAdd a i) = y i := by
  change Sum.elim x y (finSumFinEquiv.symm (Fin.natAdd a i)) = y i
  rw [finSumFinEquiv_symm_apply_natAdd]
  rfl

/-- The inverse restricts to the two actual coordinate blocks. -/
@[simp] theorem freeCoordinateSumEquiv_symm_apply (a b : ℕ) (z : Fin (a + b) → ℤ) :
    (freeCoordinateSumEquiv a b).symm z =
      (fun i => z (Fin.castAdd b i), fun i => z (Fin.natAdd a i)) := by
  apply Prod.ext
  · funext i
    exact (freeCoordinateSumEquiv_apply_left a b
      ((freeCoordinateSumEquiv a b).symm z).1 ((freeCoordinateSumEquiv a b).symm z).2 i).symm.trans
        (congrFun ((freeCoordinateSumEquiv a b).apply_symm_apply z) (Fin.castAdd b i))
  · funext i
    exact (freeCoordinateSumEquiv_apply_right a b
      ((freeCoordinateSumEquiv a b).symm z).1 ((freeCoordinateSumEquiv a b).symm z).2 i).symm.trans
        (congrFun ((freeCoordinateSumEquiv a b).apply_symm_apply z) (Fin.natAdd a i))

@[simp] theorem freeCoordinateSumEquiv_symm_fst (a b : ℕ)
    (z : Fin (a + b) → ℤ) (i : Fin a) :
    ((freeCoordinateSumEquiv a b).symm z).1 i = z (Fin.castAdd b i) := by
  rw [freeCoordinateSumEquiv_symm_apply]

@[simp] theorem freeCoordinateSumEquiv_symm_snd (a b : ℕ)
    (z : Fin (a + b) → ℤ) (i : Fin b) :
    ((freeCoordinateSumEquiv a b).symm z).2 i = z (Fin.natAdd a i) := by
  rw [freeCoordinateSumEquiv_symm_apply]

/-- The useful case of one integer coordinate followed by a finite block. -/
def integerFreeCoordinateEquiv (b : ℕ) :
    (ℤ × (Fin b → ℤ)) ≃ₗ[ℤ] (Fin (1 + b) → ℤ) :=
  ((((LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm.toAddEquiv.prodCongr
      (AddEquiv.refl (Fin b → ℤ))).trans
        (freeCoordinateSumEquiv 1 b).toAddEquiv)).toIntLinearEquiv

/-- The integer left endpoint occupies the first coordinate. -/
@[simp] theorem integerFreeCoordinateEquiv_apply_head (b : ℕ)
    (z : ℤ) (v : Fin b → ℤ) :
    integerFreeCoordinateEquiv b (z, v) (Fin.castAdd b (0 : Fin 1)) = z := by
  change freeCoordinateSumEquiv 1 b ((fun _ => z), v)
    (Fin.castAdd b (0 : Fin 1)) = z
  exact freeCoordinateSumEquiv_apply_left 1 b (fun _ => z) v 0

/-- The right endpoint retains its ordered coordinates after the first entry. -/
@[simp] theorem integerFreeCoordinateEquiv_apply_tail (b : ℕ)
    (z : ℤ) (v : Fin b → ℤ) (i : Fin b) :
    integerFreeCoordinateEquiv b (z, v) (Fin.natAdd 1 i) = v i := by
  change freeCoordinateSumEquiv 1 b ((fun _ => z), v) (Fin.natAdd 1 i) = v i
  exact freeCoordinateSumEquiv_apply_right 1 b (fun _ => z) v i

@[simp] theorem integerFreeCoordinateEquiv_symm_fst (b : ℕ)
    (v : Fin (1 + b) → ℤ) :
    ((integerFreeCoordinateEquiv b).symm v).1 = v (Fin.castAdd b (0 : Fin 1)) := rfl

@[simp] theorem integerFreeCoordinateEquiv_symm_snd (b : ℕ)
    (v : Fin (1 + b) → ℤ) (i : Fin b) :
    ((integerFreeCoordinateEquiv b).symm v).2 i = v (Fin.natAdd 1 i) :=
  freeCoordinateSumEquiv_symm_snd 1 b v i

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyFreeCoordinates
