import ErdosProblems.Erdos941.HurwitzOrder
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-! # The integral basis of the Hurwitz order -/

namespace Erdos941

open scoped Quaternion

theorem hurwitzCoordinates_zsmul (r a b c d : ℤ) :
    r • hurwitzCoordinates a b c d = hurwitzCoordinates (r * a) (r * b) (r * c) (r * d) := by
  apply Quaternion.ext
  · rw [Quaternion.re_smul]
    dsimp [hurwitzCoordinates]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  · rw [Quaternion.imI_smul]
    dsimp [hurwitzCoordinates]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  · rw [Quaternion.imJ_smul]
    dsimp [hurwitzCoordinates]
    simp only [zsmul_eq_mul]
    push_cast
    ring
  · rw [Quaternion.imK_smul]
    dsimp [hurwitzCoordinates]
    simp only [zsmul_eq_mul]
    push_cast
    ring

def hurwitzParam : (Fin 4 → ℤ) →ₗ[ℤ] hurwitzOrder where
  toFun f := ⟨hurwitzCoordinates (f 0) (f 1) (f 2) (f 3), ⟨_, _, _, _, rfl⟩⟩
  map_add' f g := Subtype.ext (hurwitzCoordinates_add _ _ _ _ _ _ _ _).symm
  map_smul' r f := Subtype.ext (hurwitzCoordinates_zsmul _ _ _ _ _).symm

theorem hurwitzParam_injective : Function.Injective hurwitzParam := by
  intro f g h
  have hR := congrArg (fun q : hurwitzOrder => (q : ℍ[ℚ]).re) h
  have hI := congrArg (fun q : hurwitzOrder => (q : ℍ[ℚ]).imI) h
  have hJ := congrArg (fun q : hurwitzOrder => (q : ℍ[ℚ]).imJ) h
  have hK := congrArg (fun q : hurwitzOrder => (q : ℍ[ℚ]).imK) h
  change (f 0 : ℚ) + (f 3 : ℚ) / 2 = (g 0 : ℚ) + (g 3 : ℚ) / 2 at hR
  change (f 1 : ℚ) + (f 3 : ℚ) / 2 = (g 1 : ℚ) + (g 3 : ℚ) / 2 at hI
  change (f 2 : ℚ) + (f 3 : ℚ) / 2 = (g 2 : ℚ) + (g 3 : ℚ) / 2 at hJ
  change (f 3 : ℚ) / 2 = (g 3 : ℚ) / 2 at hK
  have h3 : (f 3 : ℚ) = g 3 := by linarith
  have h0 : (f 0 : ℚ) = g 0 := by linarith
  have h1 : (f 1 : ℚ) = g 1 := by linarith
  have h2 : (f 2 : ℚ) = g 2 := by linarith
  funext i
  fin_cases i
  · exact_mod_cast h0
  · exact_mod_cast h1
  · exact_mod_cast h2
  · exact_mod_cast h3

theorem hurwitzParam_surjective : Function.Surjective hurwitzParam := by
  intro q
  obtain ⟨a, b, c, d, hq⟩ := q.property
  exact ⟨![a, b, c, d], Subtype.ext hq.symm⟩

noncomputable def hurwitzBasis : Module.Basis (Fin 4) ℤ hurwitzOrder :=
  (Pi.basisFun ℤ (Fin 4)).map
    (LinearEquiv.ofBijective hurwitzParam ⟨hurwitzParam_injective, hurwitzParam_surjective⟩)

instance hurwitzOrder_moduleFinite : Module.Finite ℤ hurwitzOrder :=
  Module.Finite.of_basis hurwitzBasis

instance hurwitzOrder_moduleFree : Module.Free ℤ hurwitzOrder :=
  Module.Free.of_basis hurwitzBasis

end Erdos941
