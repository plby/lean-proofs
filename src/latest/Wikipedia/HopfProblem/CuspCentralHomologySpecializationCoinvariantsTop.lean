import Wikipedia.HopfProblem.PeriodTorusHigherHomologyExteriorBasis
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.Preorder.Finite

/-!
# The actual top exterior-power coinvariants of cusp monodromy

The fourth exterior power of the original rank-four integral lattice has
one ordered basis vector. Its actual induced map has coefficient equal to
the determinant of the original matrix. In particular the original cusp
matrix `M₀` acts as the identity, so its top exterior coinvariants have one
free integral coordinate. No dual action or separate model is substituted.
-/

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants

open PeriodTorusHigherHomologyExterior

/-- The full ordered set of the four original lattice indices. -/
noncomputable def topExteriorIndex : Set.powersetCard (Fin 4) 4 :=
  Set.powersetCard.ofFinEmbEquiv
    (OrderEmbedding.ofStrictMono (id : Fin 4 → Fin 4) strictMono_id)

theorem topExteriorIndex_ordered :
    (Set.powersetCard.ofFinEmbEquiv.symm topExteriorIndex : Fin 4 → Fin 4) = id := by
  rw [topExteriorIndex, Equiv.symm_apply_apply]
  rfl

/-- Every top-degree index set is the full index set. -/
theorem topExteriorIndex_unique (s : Set.powersetCard (Fin 4) 4) :
    s = topExteriorIndex := by
  apply Set.powersetCard.ofFinEmbEquiv.symm.injective
  apply DFunLike.coe_injective
  exact (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono.eq_id.trans
    topExteriorIndex_ordered.symm

/-- The coordinate of the actual top exterior-power basis vector. -/
noncomputable def topExteriorCoordinates : latticeExterior 4 ≃ₗ[ℤ] ℤ := by
  letI : Unique (Set.powersetCard (Fin 4) 4) :=
    ⟨⟨topExteriorIndex⟩, topExteriorIndex_unique⟩
  exact (latticeExteriorBasis 4).equivFun.trans
    (LinearEquiv.funUnique (Set.powersetCard (Fin 4) 4) ℤ ℤ)

theorem topExteriorCoordinates_apply (x : latticeExterior 4) :
    topExteriorCoordinates x = (latticeExteriorBasis 4).repr x topExteriorIndex :=
  congrFun ((latticeExteriorBasis 4).equivFun_apply x) topExteriorIndex

theorem topExteriorCoordinates_basis :
    topExteriorCoordinates (latticeExteriorBasis 4 topExteriorIndex) = 1 := by
  rw [topExteriorCoordinates_apply, Module.Basis.repr_self_apply]
  simp

/-- The actual fourth exterior-power action is determinant times the identity. -/
theorem topExteriorMap_eq_det_smul (A : LatticeMatrix) :
    exteriorPower.map 4 A.mulVecLin =
      A.det • (LinearMap.id : latticeExterior 4 →ₗ[ℤ] latticeExterior 4) := by
  classical
  have hemb (s : Set.powersetCard (Fin 4) 4) :
      (Set.powersetCard.ofFinEmbEquiv.symm s : Fin 4 → Fin 4) = id :=
    (Set.powersetCard.ofFinEmbEquiv.symm s).strictMono.eq_id
  apply (standardExteriorBasis 4 4).ext
  intro t
  apply (standardExteriorBasis 4 4).repr.injective
  apply Finsupp.ext
  intro s
  have hst : s = t := (topExteriorIndex_unique s).trans (topExteriorIndex_unique t).symm
  rw [standardExterior_map_coefficient, hemb s, hemb t, Matrix.submatrix_id_id]
  simp [LinearMap.id_apply, hst]

theorem topExteriorCoordinates_map (A : LatticeMatrix) (x : latticeExterior 4) :
    topExteriorCoordinates (exteriorPower.map 4 A.mulVecLin x) =
      A.det * topExteriorCoordinates x := by
  rw [topExteriorMap_eq_det_smul, LinearMap.smul_apply, LinearMap.id_apply,
    map_smul, smul_eq_mul]

/-- The determinant-one cusp matrix acts trivially on the actual top exterior power. -/
theorem topExteriorMap_M₀ :
    exteriorPower.map 4 M₀.mulVecLin =
      (LinearMap.id : latticeExterior 4 →ₗ[ℤ] latticeExterior 4) := by
  rw [topExteriorMap_eq_det_smul, show M₀.det = 1 by decide, one_smul]

/-- The original cusp action minus identity on the actual fourth exterior power. -/
noncomputable def topExteriorDifference : latticeExterior 4 →ₗ[ℤ] latticeExterior 4 :=
  exteriorPower.map 4 M₀.mulVecLin - LinearMap.id

theorem topExteriorDifference_eq_zero : topExteriorDifference = 0 := by
  apply LinearMap.ext
  intro x
  change exteriorPower.map 4 M₀.mulVecLin x - x = 0
  rw [topExteriorMap_M₀, LinearMap.id_apply, sub_self]

theorem topExteriorDifference_range_eq_bot : LinearMap.range topExteriorDifference = ⊥ := by
  rw [topExteriorDifference_eq_zero, LinearMap.range_zero]

/-- The literal quotient by the range of the original cusp action minus identity. -/
abbrev TopExteriorCoinvariants := latticeExterior 4 ⧸ LinearMap.range topExteriorDifference

/-- A single integral coordinate on the actual top exterior coinvariant quotient. -/
noncomputable def topExteriorCoinvariantEquiv : TopExteriorCoinvariants ≃ₗ[ℤ] ℤ :=
  ((LinearMap.range topExteriorDifference).quotEquivOfEqBot
    topExteriorDifference_range_eq_bot).trans topExteriorCoordinates

theorem topExteriorCoinvariantEquiv_mk (x : latticeExterior 4) :
    topExteriorCoinvariantEquiv (Submodule.Quotient.mk x) = topExteriorCoordinates x := rfl

theorem topExteriorCoinvariantEquiv_symm_apply (z : ℤ) :
    topExteriorCoinvariantEquiv.symm z =
      Submodule.Quotient.mk (topExteriorCoordinates.symm z) := rfl

theorem topExteriorCoinvariant_finrank : Module.finrank ℤ TopExteriorCoinvariants = 1 := by
  rw [topExteriorCoinvariantEquiv.finrank_eq, Module.finrank_self]

theorem topExteriorCoinvariant_rank : Module.rank ℤ TopExteriorCoinvariants = 1 := by
  rw [topExteriorCoinvariantEquiv.rank_eq, Module.rank_self]

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationCoinvariants
