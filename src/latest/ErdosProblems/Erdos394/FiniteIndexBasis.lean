import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.LinearAlgebra.StdBasis

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A canonical two-element basis for a finite-index submodule of `ℤ²`
-/

open Module Submodule

namespace Erdos394

/-- A finite-index submodule of `ℤ²` has a two-element integer basis. -/
noncomputable def finiteIndexBasis (Λ : Submodule ℤ (Fin 2 → ℤ))
    [Finite ((Fin 2 → ℤ) ⧸ Λ)] : Basis (Fin 2) ℤ Λ := by
  have hrank : Module.finrank ℤ Λ = Module.finrank ℤ (Fin 2 → ℤ) :=
    (Submodule.finiteQuotient_iff Λ).mp inferInstance
  let b := Module.Free.chooseBasis ℤ Λ
  let e : Module.Free.ChooseBasisIndex ℤ Λ ≃ Fin 2 := Fintype.equivOfCardEq (by
    rw [← finrank_eq_card_chooseBasisIndex, hrank,
      finrank_fintype_fun_eq_card])
  exact b.reindex e

/-- Explicit existence form, convenient when the finite quotient instance is
available only locally. -/
theorem exists_fin_two_basis_of_finite_quotient
    (Λ : Submodule ℤ (Fin 2 → ℤ)) (hfin : Finite ((Fin 2 → ℤ) ⧸ Λ)) :
    Nonempty (Basis (Fin 2) ℤ Λ) := by
  letI := hfin
  exact ⟨finiteIndexBasis Λ⟩

end Erdos394
