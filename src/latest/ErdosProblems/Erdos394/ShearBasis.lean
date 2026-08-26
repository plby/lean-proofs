import Mathlib

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary swaps and integer shears of a two-element basis
-/

open Module
open scoped Matrix

namespace Erdos394

noncomputable def shearLinearEquiv {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Basis (Fin 2) R M) (n : R) : M ≃ₗ[R] M := by
  let f : M →ₗ[R] M := (b.constr R) ![b 0, b 1 - n • b 0]
  let g : M →ₗ[R] M := (b.constr R) ![b 0, b 1 + n • b 0]
  apply LinearEquiv.ofLinear f g
  · apply b.ext
    intro i
    fin_cases i
    · simp [f, g, LinearMap.comp_apply, Basis.constr_basis]
    · simp [f, g, LinearMap.comp_apply, Basis.constr_basis]
  · apply b.ext
    intro i
    fin_cases i
    · simp [f, g, LinearMap.comp_apply, Basis.constr_basis]
    · simp [f, g, LinearMap.comp_apply, Basis.constr_basis]

/-- Replace the second basis vector by `v - n u`. -/
noncomputable def shearSecondBasis {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Basis (Fin 2) R M) (n : R) :
    Basis (Fin 2) R M := b.map (shearLinearEquiv b n)

@[simp] theorem shearSecondBasis_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Basis (Fin 2) R M) (n : R) :
    shearSecondBasis b n 0 = b 0 := by
  simp [shearSecondBasis, shearLinearEquiv, Basis.constr_basis]

@[simp] theorem shearSecondBasis_one {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Basis (Fin 2) R M) (n : R) :
    shearSecondBasis b n 1 = b 1 - n • b 0 := by
  simp [shearSecondBasis, shearLinearEquiv, Basis.constr_basis]

/-- Swap the two vectors of a two-element basis. -/
noncomputable def swapBasis {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Basis (Fin 2) R M) : Basis (Fin 2) R M :=
  b.reindex (Equiv.swap 0 1)

@[simp] theorem swapBasis_zero {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Basis (Fin 2) R M) :
    swapBasis b 0 = b 1 := by
  simp [swapBasis, Basis.reindex_apply]

@[simp] theorem swapBasis_one {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (b : Basis (Fin 2) R M) :
    swapBasis b 1 = b 0 := by
  simp [swapBasis, Basis.reindex_apply]

end Erdos394
