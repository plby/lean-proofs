import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexQuotientGeometry

/-!
# The signed cube tetrahedra of a boundary-based three-simplex

Exactly the principal tetrahedron maps to the original simplex. The other
five map to its based boundary. Their original permutation signs sum to
minus one, giving the corrected chain `simplex - constant` exactly.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz Geometry

/-- The three even and three odd coordinate orders have zero total sign. -/
theorem threeCubeOrientation_sum :
    ∑ e : Equiv.Perm (Fin 3), cubeOrientation e = 0 := by
  have h := Equiv.sum_comp (Equiv.mulRight (Equiv.swap (0 : Fin 3) 1)) cubeOrientation
  change (∑ e : Equiv.Perm (Fin 3), cubeOrientation ((Equiv.swap 0 1).trans e)) =
    ∑ e : Equiv.Perm (Fin 3), cubeOrientation e at h
  simp_rw [cubeOrientation_swap _ (by decide : (0 : Fin 3) ≠ 1)] at h
  rw [Finset.sum_neg_distrib] at h
  omega

variable {X : Type} [TopologicalSpace X] {x : X}

/-- The actual signed six-tetrahedron chain evaluates to the original
three-simplex minus the actual constant three-simplex. -/
theorem basedThreeSimplex_tetrahedronChain_sum (τ : BasedThreeSimplex x) :
    (∑ e : Equiv.Perm (Fin 3), cubeOrientation e •
      simplexChain X 3 ((basedThreeSimplexLoop τ).val.comp (cubeTetrahedron e))) =
        basedThreeSimplexChain τ := by
  classical
  let c := simplexChain X 3 (ContinuousMap.const (Simplex 3) x)
  have heq (e : Equiv.Perm (Fin 3)) :
      cubeOrientation e •
        simplexChain X 3 ((basedThreeSimplexLoop τ).val.comp (cubeTetrahedron e)) =
      (if e = Equiv.refl (Fin 3) then basedThreeSimplexChain τ else 0) +
        cubeOrientation e • c := by
    by_cases he : e = Equiv.refl (Fin 3)
    · subst e
      rw [basedThreeSimplexLoop_cubeTetrahedron_refl, cubeOrientation_refl,
        one_smul, if_pos rfl, one_smul]
      change simplexChain X 3 τ.val = (simplexChain X 3 τ.val - c) + c
      abel
    · rw [basedThreeSimplexLoop_cubeTetrahedron_other τ e he, if_neg he, zero_add]
  calc
    _ = ∑ e : Equiv.Perm (Fin 3),
        ((if e = Equiv.refl (Fin 3) then basedThreeSimplexChain τ else 0) +
          cubeOrientation e • c) := Finset.sum_congr rfl (fun e _ => heq e)
    _ = basedThreeSimplexChain τ + (∑ e : Equiv.Perm (Fin 3), cubeOrientation e) • c := by
      rw [Finset.sum_add_distrib]
      have hc : (∑ e : Equiv.Perm (Fin 3), cubeOrientation e) • c =
          ∑ e : Equiv.Perm (Fin 3), cubeOrientation e • c := by
        let f : ℤ →+ Chains X 3 :=
          { toFun := fun n => n • c
            map_zero' := zero_zsmul c
            map_add' := fun a b => add_zsmul c a b }
        exact map_sum f cubeOrientation Finset.univ
      rw [← hc]
      simp
    _ = basedThreeSimplexChain τ := by
      rw [threeCubeOrientation_sum, zero_smul, add_zero]

end Wikipedia.HopfProblem.ThirdHurewicz
