import ErdosProblems.Erdos941.HurwitzBasis
import ErdosProblems.Erdos941.SphereQuadraticField
import Mathlib.Algebra.Module.Lattice

/-! # The rank-two integral lattice in an intertwiner plane -/

namespace Erdos941

open scoped Quaternion

def quaternionParam {v : Triple} {n : ℕ} (hv : tripleNorm v = n) (q : hurwitzOrder) :
    SphereQuadraticField n →ₗ[ℚ] ℍ[ℚ] :=
  (LinearMap.mulLeft ℚ (q : ℍ[ℚ])).comp (sphereFieldEmbedding hv).toLinearMap

theorem quaternionParam_apply {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (q : hurwitzOrder) (z : SphereQuadraticField n) :
    quaternionParam hv q z = (q : ℍ[ℚ]) * sphereFieldEmbedding hv z := rfl

def parameterLattice {v : Triple} {n : ℕ} (hv : tripleNorm v = n) (q : hurwitzOrder) :
    Submodule ℤ (SphereQuadraticField n) :=
  hurwitzOrder.toAddSubgroup.toIntSubmodule.comap ((quaternionParam hv q).restrictScalars ℤ)

def parameterLatticeMap {v : Triple} {n : ℕ} (hv : tripleNorm v = n) (q : hurwitzOrder) :
    parameterLattice hv q →ₗ[ℤ] hurwitzOrder where
  toFun z := ⟨quaternionParam hv q z, z.property⟩
  map_add' z t := Subtype.ext ((quaternionParam hv q).map_add _ _)
  map_smul' r z := Subtype.ext (((quaternionParam hv q).restrictScalars ℤ).map_smul r z)

theorem quaternionParam_injective {v : Triple} {n : ℕ} [Fact (0 < n)]
    (hv : tripleNorm v = n) {q : hurwitzOrder} (hq : q ≠ 0) :
    Function.Injective (quaternionParam hv q) := by
  intro z t h
  have hq' : (q : ℍ[ℚ]) ≠ 0 := fun h => hq (Subtype.ext h)
  apply sphereFieldEmbedding_injective hv
  exact mul_left_cancel₀ hq' h

theorem parameterLatticeMap_injective {v : Triple} {n : ℕ} [Fact (0 < n)]
    (hv : tripleNorm v = n) {q : hurwitzOrder} (hq : q ≠ 0) :
    Function.Injective (parameterLatticeMap hv q) := by
  intro z t h
  apply Subtype.ext
  exact quaternionParam_injective hv hq (congrArg Subtype.val h)

theorem parameterLattice_finite {v : Triple} {n : ℕ} [Fact (0 < n)]
    (hv : tripleNorm v = n) {q : hurwitzOrder} (hq : q ≠ 0) :
    Module.Finite ℤ (parameterLattice hv q) :=
  Module.Finite.of_injective (parameterLatticeMap hv q) (parameterLatticeMap_injective hv hq)

theorem parameterLattice_one {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (q : hurwitzOrder) : (1 : SphereQuadraticField n) ∈ parameterLattice hv q := by
  change (q : ℍ[ℚ]) * sphereFieldEmbedding hv 1 ∈ hurwitzOrder
  rw [map_one, mul_one]
  exact q.property

theorem parameterLattice_omega {v : Triple} {n : ℕ} (hv : tripleNorm v = n)
    (q : hurwitzOrder) : QuadraticAlgebra.omega ∈ parameterLattice hv q := by
  change (q : ℍ[ℚ]) * sphereFieldEmbedding hv QuadraticAlgebra.omega ∈ hurwitzOrder
  rw [sphereFieldEmbedding_omega]
  exact hurwitzOrder.mul_mem q.property (pureQuaternion_mem v)

theorem parameterLattice_isLattice {v : Triple} {n : ℕ} [Fact (0 < n)]
    (hv : tripleNorm v = n) {q : hurwitzOrder} (hq : q ≠ 0) :
    Submodule.IsLattice ℚ (parameterLattice hv q) where
  fg := by
    letI := parameterLattice_finite hv hq
    exact Module.Finite.iff_fg.mp inferInstance
  span_eq_top := by
    apply top_unique
    intro z _
    have h1 := Submodule.subset_span (R := ℚ) (parameterLattice_one hv q)
    have hw := Submodule.subset_span (R := ℚ) (parameterLattice_omega hv q)
    have hz : z = z.re • (1 : SphereQuadraticField n) + z.im • QuadraticAlgebra.omega := by
      ext <;> simp
    rw [hz]
    exact Submodule.add_mem _ (Submodule.smul_mem _ z.re h1) (Submodule.smul_mem _ z.im hw)

theorem parameterLattice_finrank {v : Triple} {n : ℕ} [Fact (0 < n)]
    (hv : tripleNorm v = n) {q : hurwitzOrder} (hq : q ≠ 0) :
    Module.finrank ℤ (parameterLattice hv q) = 2 := by
  letI := parameterLattice_isLattice hv hq
  apply Module.finrank_eq_of_rank_eq
  rw [Submodule.IsLattice.rank' ℚ]
  exact QuadraticAlgebra.rank_eq_two _ _

noncomputable def parameterLatticeBasis {v : Triple} {n : ℕ} [Fact (0 < n)]
    (hv : tripleNorm v = n) {q : hurwitzOrder} (hq : q ≠ 0) :
    Module.Basis (Fin 2) ℤ (parameterLattice hv q) := by
  letI := parameterLattice_isLattice hv hq
  exact (Module.finBasis ℤ (parameterLattice hv q)).reindex
    (finCongr (parameterLattice_finrank hv hq))

theorem quaternionParam_intertwines {v w : Triple} {n : ℕ} (hv : tripleNorm v = n)
    {q : hurwitzOrder}
    (hq : (q : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * q)
    (z : SphereQuadraticField n) :
    quaternionParam hv q z * pureQuaternion v = pureQuaternion w * quaternionParam hv q z := by
  have hc : sphereFieldEmbedding hv z * pureQuaternion v =
      pureQuaternion v * sphereFieldEmbedding hv z := by
    rw [← sphereFieldEmbedding_omega hv, ← map_mul, ← map_mul, mul_comm]
  rw [quaternionParam_apply, mul_assoc, hc, ← mul_assoc, hq, mul_assoc]

theorem parameterLattice_covers_intertwiners {v w : Triple} {n : ℕ}
    (hv : tripleNorm v = n) (hv0 : v ≠ 0) {q : hurwitzOrder} (hq0 : q ≠ 0)
    (hq : (q : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * q)
    {r : hurwitzOrder}
    (hr : (r : ℍ[ℚ]) * pureQuaternion v = pureQuaternion w * r) :
    ∃ z : parameterLattice hv q, parameterLatticeMap hv q z = r := by
  have hq0' : (q : ℍ[ℚ]) ≠ 0 := fun h => hq0 (Subtype.ext h)
  obtain ⟨a, b, hab⟩ := (pureQuaternion_commutes_iff hv0 _).mp
    (quaternion_intertwiner_commutes hq0' hq hr)
  let z : SphereQuadraticField n := ⟨a, b⟩
  have hz : quaternionParam hv q z = (r : ℍ[ℚ]) := by
    rw [quaternionParam_apply]
    change (q : ℍ[ℚ]) * (a • 1 + b • pureQuaternion v) = _
    rw [← hab, ← mul_assoc, mul_inv_cancel₀ hq0', one_mul]
  have hzmem : z ∈ parameterLattice hv q := by
    change quaternionParam hv q z ∈ hurwitzOrder
    rw [hz]
    exact r.property
  exact ⟨⟨z, hzmem⟩, Subtype.ext hz⟩

end Erdos941
