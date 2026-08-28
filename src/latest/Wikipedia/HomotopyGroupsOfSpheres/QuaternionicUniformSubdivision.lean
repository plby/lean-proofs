import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCompatibleLogarithm
import Wikipedia.NoExoticSixSphere.OrthogonalUniformSubdivision

/-! # Uniform partitions of compact symplectic path families -/

open Set
open scoped Topology unitInterval

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.UniformTimePartition

variable {n : ℕ}

theorem exists_uniform_increment_partition {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (H : C(I × X, symplecticSubgroup n)) (U : Set (symplecticSubgroup n))
    (hU : U ∈ nhds (1 : symplecticSubgroup n)) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ ∀ i : Fin (m + 1),
      ∀ u ∈ Icc (unitTime m i.castSucc) (unitTime m i.succ), ∀ x,
        (H (unitTime m i.castSucc, x))⁻¹ * H (u, x) ∈ U := by
  rw [nhds_subtype] at hU
  obtain ⟨V, hV, hsub⟩ := Filter.mem_comap.mp hU
  let HO : C(I × X, OrthogonalOperators (4 * n + 4)) :=
    ⟨fun p => (H p).val, continuous_subtype_val.comp H.continuous⟩
  obtain ⟨m, hm, hsmall⟩ :=
    NoExoticSixSphere.OrthogonalExponential.exists_uniform_increment_partition HO V hV N
  exact ⟨m, hm, fun i u hu x => hsub (hsmall i u hu x)⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.Exponential
