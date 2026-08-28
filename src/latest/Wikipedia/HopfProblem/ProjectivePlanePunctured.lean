import Wikipedia.HopfProblem.ProjectivePlaneManifold
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.LinearAlgebra.Projectivization.Collinear

/-!
# Affine charts away from the three projective coordinate points

Each standard affine patch contains exactly one of the three centers.
Removing the centers therefore removes just the origin in each affine
chart.  The restricted charts are genuine biholomorphisms onto open
patches of the complement.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ProjectivePlane

open ToricCharts

def coordinatePoints : Set Space := range coordinatePoint

theorem coordinatePoints_isClosed : IsClosed coordinatePoints :=
  (finite_range coordinatePoint).isClosed

@[simp] theorem coordinatePoint_mem_coordinatePoints (k : Fin 3) :
    coordinatePoint k ∈ coordinatePoints := mem_range_self k

/-- No projective line contains all three coordinate points. -/
theorem coordinatePoints_not_collinear : ¬Projectivization.IsCollinear coordinatePoints := by
  rintro ⟨M, _, hdim, hsub⟩
  have hb (k : Fin 3) : homogeneous k 0 ∈ M.submodule := by
    change ∀ h : homogeneous k 0 ≠ 0, Projectivization.mk ℂ (homogeneous k 0) h ∈ M
    intro _
    exact hsub (coordinatePoint_mem_coordinatePoints k)
  have htop : M.submodule = ⊤ := by
    apply top_unique
    rw [← (Pi.basisFun ℂ (Fin 3)).span_eq]
    apply Submodule.span_le.mpr
    rintro v ⟨k, rfl⟩
    change (Pi.basisFun ℂ (Fin 3)) k ∈ M.submodule
    rw [Pi.basisFun_apply, ← homogeneous_zero]
    exact hb k
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card] at hdim
  norm_num at hdim

theorem affineMap_eq_coordinatePoint_iff (i j : Fin 3) (z : CoordinateSpace 2) :
    affineMap i z = coordinatePoint j ↔ i = j ∧ z = 0 := by
  constructor
  · intro h
    have ht : coordinatePoint j ∈ affineTarget i := h ▸ affineMap_mem_target i z
    have hji := (coordinatePoint_mem_target_iff j i).mp ht
    subst j
    exact ⟨rfl, affineMap_injective i h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem affineMap_mem_coordinatePoints_iff (i : Fin 3) (z : CoordinateSpace 2) :
    affineMap i z ∈ coordinatePoints ↔ z = 0 := by
  constructor
  · rintro ⟨j, hj⟩
    exact ((affineMap_eq_coordinatePoint_iff i j z).mp hj.symm).2
  · rintro rfl
    exact coordinatePoint_mem_coordinatePoints i

theorem affineMap_preimage_coordinatePoints (i : Fin 3) :
    affineMap i ⁻¹' coordinatePoints = {0} := by
  ext z
  exact affineMap_mem_coordinatePoints_iff i z

theorem affineTarget_inter_coordinatePoints (i : Fin 3) :
    affineTarget i ∩ coordinatePoints = {coordinatePoint i} := by
  ext x
  constructor
  · rintro ⟨ht, j, rfl⟩
    have hj := (coordinatePoint_mem_target_iff j i).mp ht
    simp only [mem_singleton_iff, hj]
  · rintro rfl
    exact ⟨affineMap_mem_target i 0, coordinatePoint_mem_coordinatePoints i⟩

/-- The ordinary punctured affine plane, with its inherited complex structure. -/
def puncturedBase : TopologicalSpace.Opens (CoordinateSpace 2) :=
  ⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩

/-- The projective plane with the three blow-up centers removed. -/
def puncturedSpace : TopologicalSpace.Opens Space :=
  ⟨coordinatePointsᶜ, coordinatePoints_isClosed.isOpen_compl⟩

@[simp] theorem mem_puncturedBase (z : CoordinateSpace 2) :
    z ∈ puncturedBase ↔ z ≠ 0 := Iff.rfl

@[simp] theorem mem_puncturedSpace (x : Space) :
    x ∈ puncturedSpace ↔ x ∉ coordinatePoints := Iff.rfl

instance puncturedBase_nonempty : Nonempty puncturedBase := ⟨⟨1, one_ne_zero⟩⟩

theorem affineMap_mem_puncturedSpace_iff (i : Fin 3) (z : CoordinateSpace 2) :
    affineMap i z ∈ puncturedSpace ↔ z ∈ puncturedBase := by
  simp only [mem_puncturedSpace, mem_puncturedBase, affineMap_mem_coordinatePoints_iff]

theorem affineMap_mapsTo_punctured (i : Fin 3) :
    MapsTo (affineMap i) puncturedBase puncturedSpace :=
  fun z hz => (affineMap_mem_puncturedSpace_iff i z).mpr hz

def puncturedAffine (i : Fin 3) : puncturedBase → puncturedSpace :=
  (affineMap_mapsTo_punctured i).restrict

@[simp] theorem puncturedAffine_coe (i : Fin 3) (z : puncturedBase) :
    (puncturedAffine i z : Space) = affineMap i z := rfl

theorem puncturedAffine_isOpenEmbedding (i : Fin 3) : IsOpenEmbedding (puncturedAffine i) :=
  (affineMap_isOpenEmbedding i).restrict (affineMap_mapsTo_punctured i) puncturedBase.isOpen

theorem puncturedAffine_jointly_surjective (x : puncturedSpace) :
    ∃ i : Fin 3, ∃ z : puncturedBase, puncturedAffine i z = x := by
  obtain ⟨i, z, hz⟩ := affineMap_jointly_surjective x.1
  have hm : affineMap i z ∈ puncturedSpace := hz ▸ x.2
  exact ⟨i, ⟨z, (affineMap_mem_puncturedSpace_iff i z).mp hm⟩, Subtype.ext hz⟩

theorem puncturedAffine_holomorphic (i : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (puncturedAffine i) := by
  intro z
  have he : ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω
      (fun w => (puncturedAffine i w : Space)) z ↔
    ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (puncturedAffine i) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (((affineMap_holomorphic i).comp contMDiff_subtype_val) z)

/-- The part of the `i`th affine patch disjoint from all three centers. -/
def puncturedPatch (i : Fin 3) : TopologicalSpace.Opens Space :=
  ⟨affineTarget i ∩ coordinatePointsᶜ,
    (affineTarget_isOpen i).inter coordinatePoints_isClosed.isOpen_compl⟩

theorem affineMap_mem_puncturedPatch (i : Fin 3) (z : puncturedBase) :
    affineMap i z ∈ puncturedPatch i :=
  ⟨affineMap_mem_target i z, (affineMap_mem_puncturedSpace_iff i z).mpr z.2⟩

instance puncturedPatch_nonempty (i : Fin 3) : Nonempty (puncturedPatch i) :=
  ⟨⟨affineMap i 1, affineMap_mem_puncturedPatch i ⟨1, one_ne_zero⟩⟩⟩

theorem affineCoords_mem_puncturedBase (i : Fin 3) (x : puncturedPatch i) :
    affineCoords i x ∈ puncturedBase := by
  apply (affineMap_mem_puncturedSpace_iff i _).mp
  rw [affineMap_affineCoords i x x.2.1]
  exact x.2.2

def puncturedPatchHomeomorph (i : Fin 3) : puncturedBase ≃ₜ puncturedPatch i where
  toFun z := ⟨affineMap i z, affineMap_mem_puncturedPatch i z⟩
  invFun x := ⟨affineCoords i x, affineCoords_mem_puncturedBase i x⟩
  left_inv z := Subtype.ext (affineCoords_affineMap i z)
  right_inv x := Subtype.ext (affineMap_affineCoords i x x.2.1)
  continuous_toFun := ((affineMap_continuous i).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((affineCoords_continuousOn i).comp_continuous
    continuous_subtype_val (fun x : puncturedPatch i => x.2.1)).subtype_mk _

@[simp] theorem puncturedPatchHomeomorph_coe (i : Fin 3) (z : puncturedBase) :
    (puncturedPatchHomeomorph i z : Space) = affineMap i z := rfl

@[simp] theorem puncturedPatchHomeomorph_symm_coe (i : Fin 3) (x : puncturedPatch i) :
    ((puncturedPatchHomeomorph i).symm x : CoordinateSpace 2) = affineCoords i x := rfl

theorem puncturedPatchHomeomorph_holomorphic (i : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (puncturedPatchHomeomorph i) := by
  intro z
  have he : ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω
      (fun w => (puncturedPatchHomeomorph i w : Space)) z ↔
    ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (puncturedPatchHomeomorph i) z :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (((affineMap_holomorphic i).comp contMDiff_subtype_val) z)

theorem puncturedPatchHomeomorph_symm_holomorphic (i : Fin 3) :
    ContMDiff (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (puncturedPatchHomeomorph i).symm := by
  intro x
  have he : ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω
      (fun y => ((puncturedPatchHomeomorph i).symm y : CoordinateSpace 2)) x ↔
    ContMDiffAt (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) ω (puncturedPatchHomeomorph i).symm x :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  apply he.mp
  exact ((affineCoords_holomorphicOn i).contMDiffAt
    ((affineTarget_isOpen i).mem_nhds x.2.1)).comp _ contMDiff_subtype_val.contMDiffAt

/-- Each complement patch is biholomorphic to the punctured affine plane. -/
def puncturedPatchBiholomorph (i : Fin 3) :
    Diffeomorph (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 2)) puncturedBase (puncturedPatch i) ω where
  toEquiv := (puncturedPatchHomeomorph i).toEquiv
  contMDiff_toFun := puncturedPatchHomeomorph_holomorphic i
  contMDiff_invFun := puncturedPatchHomeomorph_symm_holomorphic i

theorem puncturedPatch_cover :
    (⋃ i : Fin 3, (puncturedPatch i : Set Space)) = coordinatePointsᶜ := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hi.2
  · intro hx
    obtain ⟨i, z, rfl⟩ := affineMap_jointly_surjective x
    exact mem_iUnion.mpr ⟨i, affineMap_mem_target i z, hx⟩

end Wikipedia.HopfProblem.ProjectivePlane
