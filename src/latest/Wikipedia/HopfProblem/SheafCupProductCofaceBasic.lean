import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.Abel

/-!
# Low-degree ring cofaces and their actual alternating differential

The only identities in the data are the usual cosimplicial coface
identities. The square-zero identities for the alternating differential
are proved from those identities, not included as assumptions.
-/

universe u₀ u₁ u₂ u₃

namespace Wikipedia.HopfProblem.SheafCupProduct.Coface

structure Data (R0 : Type u₀) (R1 : Type u₁) (R2 : Type u₂) (R3 : Type u₃)
    [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3] where
  δ0 : Fin 2 → R0 →+* R1
  δ1 : Fin 3 → R1 →+* R2
  δ2 : Fin 4 → R2 →+* R3
  coface01 : ∀ (i j : Fin 2), i ≤ j →
    (δ1 j.succ).comp (δ0 i) = (δ1 i.castSucc).comp (δ0 j)
  coface12 : ∀ (i j : Fin 3), i ≤ j →
    (δ2 j.succ).comp (δ1 i) = (δ2 i.castSucc).comp (δ1 j)

namespace Data

variable {R0 : Type u₀} {R1 : Type u₁} {R2 : Type u₂} {R3 : Type u₃}
variable [CommRing R0] [CommRing R1] [CommRing R2] [CommRing R3]
variable (D : Data R0 R1 R2 R3)

theorem coface01_apply (i j : Fin 2) (hij : i ≤ j) (r : R0) :
    D.δ1 j.succ (D.δ0 i r) = D.δ1 i.castSucc (D.δ0 j r) :=
  congrArg (fun f : R0 →+* R2 => f r) (D.coface01 i j hij)

theorem coface12_apply (i j : Fin 3) (hij : i ≤ j) (a : R1) :
    D.δ2 j.succ (D.δ1 i a) = D.δ2 i.castSucc (D.δ1 j a) :=
  congrArg (fun f : R1 →+* R3 => f a) (D.coface12 i j hij)

theorem coface01_00 (r : R0) : D.δ1 1 (D.δ0 0 r) = D.δ1 0 (D.δ0 0 r) := by
  simpa using D.coface01_apply 0 0 (by decide) r

theorem coface01_01 (r : R0) : D.δ1 2 (D.δ0 0 r) = D.δ1 0 (D.δ0 1 r) := by
  simpa using D.coface01_apply 0 1 (by decide) r

theorem coface01_11 (r : R0) : D.δ1 2 (D.δ0 1 r) = D.δ1 1 (D.δ0 1 r) := by
  simpa using D.coface01_apply 1 1 (by decide) r

theorem coface12_00 (a : R1) : D.δ2 1 (D.δ1 0 a) = D.δ2 0 (D.δ1 0 a) := by
  simpa using D.coface12_apply 0 0 (by decide) a

theorem coface12_01 (a : R1) : D.δ2 2 (D.δ1 0 a) = D.δ2 0 (D.δ1 1 a) := by
  simpa using D.coface12_apply 0 1 (by decide) a

theorem coface12_02 (a : R1) : D.δ2 3 (D.δ1 0 a) = D.δ2 0 (D.δ1 2 a) := by
  simpa using D.coface12_apply 0 2 (by decide) a

theorem coface12_11 (a : R1) : D.δ2 2 (D.δ1 1 a) = D.δ2 1 (D.δ1 1 a) := by
  simpa using D.coface12_apply 1 1 (by decide) a

theorem coface12_12 (a : R1) : D.δ2 3 (D.δ1 1 a) = D.δ2 1 (D.δ1 2 a) := by
  simpa using D.coface12_apply 1 2 (by decide) a

theorem coface12_22 (a : R1) : D.δ2 3 (D.δ1 2 a) = D.δ2 2 (D.δ1 2 a) := by
  simpa using D.coface12_apply 2 2 (by decide) a

def d0 : R0 →+ R1 := (D.δ0 0).toAddMonoidHom - (D.δ0 1).toAddMonoidHom

def d1 : R1 →+ R2 :=
  (D.δ1 0).toAddMonoidHom - (D.δ1 1).toAddMonoidHom + (D.δ1 2).toAddMonoidHom

def d2 : R2 →+ R3 :=
  (D.δ2 0).toAddMonoidHom - (D.δ2 1).toAddMonoidHom +
    (D.δ2 2).toAddMonoidHom - (D.δ2 3).toAddMonoidHom

@[simp] theorem d0_apply (r : R0) : D.d0 r = D.δ0 0 r - D.δ0 1 r := rfl

@[simp] theorem d1_apply (a : R1) : D.d1 a = D.δ1 0 a - D.δ1 1 a + D.δ1 2 a := rfl

@[simp] theorem d2_apply (a : R2) :
    D.d2 a = D.δ2 0 a - D.δ2 1 a + D.δ2 2 a - D.δ2 3 a := rfl

@[simp] theorem d1_d0 (r : R0) : D.d1 (D.d0 r) = 0 := by
  simp only [d1_apply, d0_apply, map_sub]
  rw [D.coface01_00, D.coface01_01, D.coface01_11]
  abel

@[simp] theorem d2_d1 (a : R1) : D.d2 (D.d1 a) = 0 := by
  simp only [d2_apply, d1_apply, map_sub, map_add]
  rw [D.coface12_00, D.coface12_01, D.coface12_02,
    D.coface12_11, D.coface12_12, D.coface12_22]
  abel

theorem d1_comp_d0 : D.d1.comp D.d0 = 0 := by
  ext r
  exact D.d1_d0 r

theorem d2_comp_d1 : D.d2.comp D.d1 = 0 := by
  ext a
  exact D.d2_d1 a

end Data

end Wikipedia.HopfProblem.SheafCupProduct.Coface
