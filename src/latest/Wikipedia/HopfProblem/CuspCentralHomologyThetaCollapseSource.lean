import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseTopology
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseCover

/-!
# Actual midpoint classes in the theta-product Mayer--Vietoris kernel

The three sections put the unchanged compact fibre torus at height one half
of the three literal edges. Both cone projections send these sections to the
identity. Their actual induced homology maps are injective, so a zero-sum
family of fibre classes gives a class in the Mayer--Vietoris kernel.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual overlap of the two product-cone open subsets. -/
abbrev ThetaBelt := thetaNorth ∩ thetaSouth

/-- The unchanged phase torus at the midpoint of the indicated actual edge. -/
def thetaBeltSection (j : Fin 3) : C(CompactFibreTorus, ThetaBelt) :=
  suspensionProductMiddleSection CompactFibreTorus (Fin 3) j

@[simp] theorem thetaBeltSection_coe (j : Fin 3) (u : CompactFibreTorus) :
    (thetaBeltSection j u : CompactFibreTorus × Theta) =
      (u, Suspension.mk ⟨1 / 2, by norm_num⟩ j) := rfl

/-- The literal first-coordinate projection on the actual belt. -/
def thetaBeltProjection : C(ThetaBelt, CompactFibreTorus) :=
  rightPreimageProjection CompactFibreTorus Theta (Suspension.middleBand (Fin 3))

@[simp] theorem thetaBeltProjection_apply (p : ThetaBelt) :
    thetaBeltProjection p = p.1.1 := rfl

@[simp] theorem thetaBeltProjection_comp_section (j : Fin 3) :
    thetaBeltProjection.comp (thetaBeltSection j) = ContinuousMap.id CompactFibreTorus := rfl

/-- Projection sends each actual midpoint section to the identity on homology. -/
@[simp] theorem thetaBeltProjection_homology_section (j : Fin 3) (n : ℕ)
    (a : SingularHomology CompactFibreTorus n) :
    singularHomologyMap thetaBeltProjection n
      (singularHomologyMap (thetaBeltSection j) n a) = a := by
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp,
    thetaBeltProjection_comp_section, singularHomologyMap_id, LinearMap.id_apply]

/-- Sum the actual degree-one homology classes on the three midpoint sections. -/
def thetaBeltSum (v : Fin 3 → SingularHomology CompactFibreTorus 1) :
    SingularHomology ThetaBelt 1 :=
  ∑ j, singularHomologyMap (thetaBeltSection j) 1 (v j)

theorem thetaBeltSum_apply (v : Fin 3 → SingularHomology CompactFibreTorus 1) :
    thetaBeltSum v = ∑ j, singularHomologyMap (thetaBeltSection j) 1 (v j) := rfl

/-- The actual first projection adds the three fibre classes. -/
@[simp] theorem thetaBeltProjection_homology_sum
    (v : Fin 3 → SingularHomology CompactFibreTorus 1) :
    singularHomologyMap thetaBeltProjection 1 (thetaBeltSum v) = ∑ j, v j := by
  simp only [thetaBeltSum, map_sum, thetaBeltProjection_homology_section]

/-- Any actual map out of the belt evaluates the sum by composing with its
three literal midpoint sections. -/
theorem thetaBeltSum_map {Y : Type} [TopologicalSpace Y] (f : C(ThetaBelt, Y))
    (v : Fin 3 → SingularHomology CompactFibreTorus 1) :
    singularHomologyMap f 1 (thetaBeltSum v) =
      ∑ j, singularHomologyMap (f.comp (thetaBeltSection j)) 1 (v j) := by
  simp only [thetaBeltSum, map_sum, singularHomologyMap_comp, LinearMap.comp_apply]

/-- A belt class with zero first projection maps to zero in both actual cones. -/
theorem thetaBelt_mem_ker_of_projection_eq_zero (n : ℕ)
    (a : SingularHomology ThetaBelt n)
    (ha : singularHomologyMap thetaBeltProjection n a = 0) :
    leftHomologyMap thetaNorth thetaSouth n a = 0 := by
  have hleft : singularHomologyMap
      (ContinuousMap.inclusion (inter_subset_left : ThetaBelt ⊆ thetaNorth)) n a = 0 := by
    let proj : C(thetaNorth, CompactFibreTorus) :=
      rightPreimageProjection CompactFibreTorus Theta Suspension.northOpen
    apply (show Function.Injective (singularHomologyMap proj n) from
      rightPreimageProjection_homology_injective CompactFibreTorus Theta
        Suspension.northOpen n)
    rw [map_zero, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    exact ha
  have hright : singularHomologyMap
      (ContinuousMap.inclusion (inter_subset_right : ThetaBelt ⊆ thetaSouth)) n a = 0 := by
    let proj : C(thetaSouth, CompactFibreTorus) :=
      rightPreimageProjection CompactFibreTorus Theta Suspension.southOpen
    apply (show Function.Injective (singularHomologyMap proj n) from
      rightPreimageProjection_homology_injective CompactFibreTorus Theta
        Suspension.southOpen n)
    rw [map_zero, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    exact ha
  rw [leftHomologyMap_apply, hleft, hright, neg_zero]
  rfl

/-- A zero-sum family gives an actual class in the Mayer--Vietoris kernel. -/
theorem thetaBeltSum_mem_ker (v : Fin 3 → SingularHomology CompactFibreTorus 1)
    (hv : ∑ j, v j = 0) :
    leftHomologyMap thetaNorth thetaSouth 1 (thetaBeltSum v) = 0 := by
  apply thetaBelt_mem_ker_of_projection_eq_zero
  rw [thetaBeltProjection_homology_sum, hv]

end Wikipedia.HopfProblem.CuspCentralHomology
