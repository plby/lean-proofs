import Wikipedia.NoExoticSixSphere.PuncturedDiskRetraction
import Wikipedia.NoExoticSixSphere.OpenPushoutRestriction
import Wikipedia.HopfProblem.OrbitPairPushoutDeformation

/-!
# An attached cell minus an interior point retracts onto the original base

The punctured subspace carries its actual subspace topology. Restriction
of the original pushout gives its attaching square, and the boundary-fixed
disk deformation descends to a strong deformation retraction fixing the
whole base. Neither a replacement attaching map nor a central puncture
is used.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Set Metric Topology TopologicalSpace
open scoped unitInterval
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.PuncturedCellAttachment

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev Disk (E : Type u) [NormedAddCommGroup E] := closedBall (0 : E) 1

def boundary : TopCat.of (sphere (0 : E) 1) ⟶ TopCat.of (Disk E) :=
  TopCat.ofHom ⟨fun x ↦ ⟨x.val, sphere_subset_closedBall x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem boundary_injective : Function.Injective (boundary (E := E)) := by
  intro x y h
  exact Subtype.ext (congrArg (fun z : Disk E ↦ z.val) h)

def point (p : E) (hp : ‖p‖ < 1) : Disk E :=
  ⟨p, mem_closedBall_zero_iff.mpr hp.le⟩

theorem point_not_boundary (p : E) (hp : ‖p‖ < 1) :
    point p hp ∉ Set.range (boundary (E := E)) := by
  rintro ⟨x, hx⟩
  have he : x.val = p := congrArg Subtype.val hx
  exact hp.ne (he ▸ mem_sphere_zero_iff_norm.mp x.property)

variable {A P : TopCat.{u}} [T1Space P]
  {f : TopCat.of (sphere (0 : E) 1) ⟶ A}
  {i : A ⟶ P} {j : TopCat.of (Disk E) ⟶ P}
  (hP : IsPushout f boundary i j) (p : E) (hp : ‖p‖ < 1)

def punctured : Opens P := ⟨{z | z ≠ j (point p hp)}, isOpen_compl_singleton⟩

include hP in
theorem base_mem (a : A) : i a ∈ punctured (j := j) p hp :=
  (PushoutOutsideAttachment.ne_other_of_notMem_range hP (point_not_boundary p hp) a).symm

include hP in
theorem cell_mem_iff (x : Disk E) : j x ∈ punctured (j := j) p hp ↔ x.val ≠ p := by
  change j x ≠ j (point p hp) ↔ x.val ≠ p
  constructor
  · intro h he
    exact h (congrArg j (Subtype.ext he))
  · intro h he
    have hpx := PushoutOutsideAttachment.eq_of_notMem_range hP (point_not_boundary p hp) he.symm
    exact h (congrArg Subtype.val hpx).symm

def cellHomeomorph : (j ⁻¹' (punctured (j := j) p hp : Set P)) ≃ₜ
    PuncturedDiskRetraction.Space p where
  toFun x := ⟨x.val.val, x.val.property, (cell_mem_iff hP p hp x.val).mp x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, (cell_mem_iff hP p hp _).mpr x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

def baseInclusion : A ⟶ TopCat.of (punctured (j := j) p hp) :=
  OpenPushoutRestriction.left _ (base_mem hP p hp)

def cellInclusion : TopCat.of (j ⁻¹' (punctured (j := j) p hp : Set P)) ⟶
    TopCat.of (punctured (j := j) p hp) :=
  OpenPushoutRestriction.right _

def attaching : TopCat.of (sphere (0 : E) 1) ⟶
    TopCat.of (j ⁻¹' (punctured (j := j) p hp : Set P)) :=
  OpenPushoutRestriction.attaching hP _ (base_mem hP p hp)

theorem isPushout : IsPushout f (attaching hP p hp) (baseInclusion hP p hp)
    (cellInclusion (j := j) p hp) :=
  OpenPushoutRestriction.isPushout hP _ (base_mem hP p hp) boundary_injective

def cellRetraction : TopCat.of (j ⁻¹' (punctured (j := j) p hp : Set P)) ⟶
    TopCat.of (sphere (0 : E) 1) :=
  TopCat.ofHom ((PuncturedDiskRetraction.retraction p hp).comp
    (cellHomeomorph hP p hp : C(_, _)))

theorem cellRetraction_attaching : attaching hP p hp ≫ cellRetraction hP p hp = 𝟙 _ := by
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact PuncturedDiskRetraction.retraction_inclusion p hp x

def cellDeformation :
    (ContinuousMap.id (j ⁻¹' (punctured (j := j) p hp : Set P))).Homotopy
      (cellRetraction hP p hp ≫ attaching hP p hp).hom where
  toFun q := (cellHomeomorph hP p hp).symm
    (PuncturedDiskRetraction.deformation p hp (q.1, cellHomeomorph hP p hp q.2))
  continuous_toFun := (cellHomeomorph hP p hp).symm.continuous.comp
    ((PuncturedDiskRetraction.deformation p hp).continuous.comp
      (continuous_fst.prodMk ((cellHomeomorph hP p hp).continuous.comp continuous_snd)))
  map_zero_left x := by
    rw [ContinuousMap.Homotopy.apply_zero]
    exact (cellHomeomorph hP p hp).symm_apply_apply x
  map_one_left x := by
    rw [ContinuousMap.Homotopy.apply_one]
    rfl

def cellDeformationRel :
    (ContinuousMap.id (j ⁻¹' (punctured (j := j) p hp : Set P))).HomotopyRel
      (cellRetraction hP p hp ≫ attaching hP p hp).hom (Set.range (attaching hP p hp)) :=
  ⟨cellDeformation hP p hp, by
    rintro t x ⟨y, rfl⟩
    change (cellHomeomorph hP p hp).symm
      (PuncturedDiskRetraction.deformation p hp
        (t, cellHomeomorph hP p hp (attaching hP p hp y))) = attaching hP p hp y
    rw [PuncturedDiskRetraction.deformation_fixed p hp t _ y.property]
    exact (cellHomeomorph hP p hp).symm_apply_apply _⟩

theorem retraction_compatible : f ≫ 𝟙 A = attaching hP p hp ≫ (cellRetraction hP p hp ≫ f) := by
  rw [← Category.assoc, cellRetraction_attaching, Category.id_comp, Category.comp_id]

def retraction : TopCat.of (punctured (j := j) p hp) ⟶ A :=
  (isPushout hP p hp).desc (𝟙 A) (cellRetraction hP p hp ≫ f) (retraction_compatible hP p hp)

theorem retraction_baseInclusion : baseInclusion hP p hp ≫ retraction hP p hp = 𝟙 A :=
  (isPushout hP p hp).inl_desc _ _ (retraction_compatible hP p hp)

theorem retraction_cellInclusion : cellInclusion (j := j) p hp ≫ retraction hP p hp =
    cellRetraction hP p hp ≫ f :=
  (isPushout hP p hp).inr_desc _ _ (retraction_compatible hP p hp)

def deformationRel :
    (ContinuousMap.id (punctured (j := j) p hp)).HomotopyRel
      (retraction hP p hp ≫ baseInclusion hP p hp).hom (Set.range (baseInclusion hP p hp)) :=
  PushoutHomotopy.deformation (isPushout hP p hp) (retraction hP p hp)
    (cellRetraction hP p hp) (retraction_baseInclusion hP p hp)
    (retraction_cellInclusion hP p hp) (cellDeformationRel hP p hp)

theorem deformation_fixed (t : I) (a : A) :
    deformationRel hP p hp (t, baseInclusion hP p hp a) = baseInclusion hP p hp a :=
  (deformationRel hP p hp).eq_fst t (Set.mem_range_self a)

end NoExoticSixSphere.PuncturedCellAttachment
