import Wikipedia.NoExoticSixSphere.JamesSphereStageCofibration
import Wikipedia.NoExoticSixSphere.JamesSphereCellCharts
import Wikipedia.NoExoticSixSphere.CellAttachmentChart

/-!
# Removing an arbitrary point of the top cell of the actual James stage

The genuine characteristic disk gives a pushout with its sphere boundary
and the preceding stage. Removing any interior characteristic point then
gives a strong deformation retraction onto that preceding stage, fixing
it pointwise. The original word-space maps are retained.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Metric Topology
open scoped unitInterval

namespace NoExoticSixSphere.JamesSphere.PuncturedStage

abbrev Coordinates (n k : ℕ) := Fin ((k + 1) * n) → ℝ

def presentation (n k : ℕ) : TopCat.of (PuncturedCellAttachment.Disk (Coordinates n k)) ⟶
    TopCat.of (James.stage (spherePole n) (k + 1)) :=
  TopCat.ofHom (Cell.closedPresentation n (k + 1))

theorem boundary_iff (n k : ℕ) (x : PuncturedCellAttachment.Disk (Coordinates n k)) :
    presentation n k x ∈ StageAttachment.lower n k ↔ x.val ∈ sphere (0 : Coordinates n k) 1 := by
  change James.size (spherePole n) (Cell.characteristic n (k + 1) x.val) ≤ k ↔ _
  constructor
  · intro hx
    apply mem_sphere.mpr
    have hle := mem_closedBall.mp x.property
    have hnot : ¬dist x.val 0 < 1 := by
      intro hb
      have he := (Cell.size_characteristic_eq_iff n (k + 1) x.val).mpr hb
      omega
    exact le_antisymm hle (le_of_not_gt hnot)
  · intro hx
    have h := Cell.boundary_size_lt n (k + 1) hx
    omega

theorem fiber_condition (n k : ℕ) (x y : PuncturedCellAttachment.Disk (Coordinates n k))
    (he : presentation n k x = presentation n k y) :
    presentation n k x ∈ StageAttachment.lower n k ∨ x = y := by
  by_cases hx : presentation n k x ∈ StageAttachment.lower n k
  · exact Or.inl hx
  · right
    have hy : presentation n k y ∉ StageAttachment.lower n k := he ▸ hx
    have hxb : x.val ∈ ball 0 1 := by
      have hn := mt (boundary_iff n k x).mpr hx
      exact lt_of_le_of_ne (mem_closedBall.mp x.property) (fun h ↦ hn h)
    have hyb : y.val ∈ ball 0 1 := by
      have hn := mt (boundary_iff n k y).mpr hy
      exact lt_of_le_of_ne (mem_closedBall.mp y.property) (fun h ↦ hn h)
    exact Subtype.ext (Cell.injOn_ball n (k + 1) hxb hyb (congrArg Subtype.val he))

def boundaryHomeomorph (n k : ℕ) : sphere (0 : Coordinates n k) 1 ≃ₜ
    (presentation n k ⁻¹' StageAttachment.lower n k) where
  toFun x := ⟨PuncturedCellAttachment.boundary x, (boundary_iff n k _).mpr x.property⟩
  invFun x := ⟨x.val.val, (boundary_iff n k x.val).mp x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (PuncturedCellAttachment.boundary.hom.continuous).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

def attaching (n k : ℕ) : TopCat.of (sphere (0 : Coordinates n k) 1) ⟶
    TopCat.of (StageAttachment.lower n k) :=
  (TopCat.isoOfHomeo (boundaryHomeomorph n k)).hom ≫
    QuotientAttachment.boundaryMap (presentation n k) (StageAttachment.lower n k)

theorem isPushout (n k : ℕ) (hn : 0 < n) : IsPushout (attaching n k)
    PuncturedCellAttachment.boundary (StageAttachment.lowerInclusion n k) (presentation n k) := by
  have hQ := QuotientAttachment.isPushout (presentation n k) (StageAttachment.lower n k)
    (Cell.isQuotientMap_closedPresentation n (k + 1) hn) (fiber_condition n k)
  apply hQ.of_iso' (TopCat.isoOfHomeo (boundaryHomeomorph n k))
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl
  · apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]

def openCell (n k : ℕ) (hn : 0 < n) := CellAttachmentChart.openCell (isPushout n k hn)

def chart (n k : ℕ) (hn : 0 < n) : Coordinates n k ≃ₜ openCell n k hn :=
  CellAttachmentChart.chart (isPushout n k hn)

theorem openCell_eq_topStratum (n k : ℕ) (hn : 0 < n) :
    (openCell n k hn : Set (James.stage (spherePole n) (k + 1))) =
      Cell.topStratum n (k + 1) := by
  ext w
  constructor
  · rintro ⟨x, rfl⟩
    exact (Cell.size_characteristic_eq_iff n (k + 1) x.val).mpr x.property
  · intro hw
    obtain ⟨x, rfl⟩ := Cell.closedPresentation_surjective n (k + 1) hn w
    have hx : x.val ∈ ball 0 1 := (Cell.size_characteristic_eq_iff n (k + 1) x.val).mp hw
    exact ⟨⟨x.val, hx⟩, rfl⟩

def punctured (n k : ℕ) (p : Coordinates n k) (hp : ‖p‖ < 1) :=
  PuncturedCellAttachment.punctured (j := presentation n k) p hp

def inclusion (n k : ℕ) (hn : 0 < n) (p : Coordinates n k) (hp : ‖p‖ < 1) :
    C(James.stage (spherePole n) k, punctured n k p hp) :=
  (PuncturedCellAttachment.baseInclusion (isPushout n k hn) p hp).hom.comp
    (StageAttachment.lowerHomeomorph n k : C(_, _))

def retraction (n k : ℕ) (hn : 0 < n) (p : Coordinates n k) (hp : ‖p‖ < 1) :
    C(punctured n k p hp, James.stage (spherePole n) k) :=
  ((StageAttachment.lowerHomeomorph n k).symm : C(_, _)).comp
    (PuncturedCellAttachment.retraction (isPushout n k hn) p hp).hom

theorem inclusion_val (n k : ℕ) (hn : 0 < n) (p : Coordinates n k) (hp : ‖p‖ < 1)
    (x : James.stage (spherePole n) k) : (inclusion n k hn p hp x).val.val = x.val := rfl

theorem retraction_inclusion (n k : ℕ) (hn : 0 < n) (p : Coordinates n k) (hp : ‖p‖ < 1)
    (x : James.stage (spherePole n) k) :
    retraction n k hn p hp (inclusion n k hn p hp x) = x := by
  have h := congrArg (fun m ↦ m (StageAttachment.lowerHomeomorph n k x))
    (PuncturedCellAttachment.retraction_baseInclusion (isPushout n k hn) p hp)
  change PuncturedCellAttachment.retraction (isPushout n k hn) p hp
    (PuncturedCellAttachment.baseInclusion (isPushout n k hn) p hp
      (StageAttachment.lowerHomeomorph n k x)) = StageAttachment.lowerHomeomorph n k x at h
  change (StageAttachment.lowerHomeomorph n k).symm
    ((PuncturedCellAttachment.retraction (isPushout n k hn) p hp)
      (PuncturedCellAttachment.baseInclusion (isPushout n k hn) p hp
        (StageAttachment.lowerHomeomorph n k x))) = x
  rw [h]
  exact (StageAttachment.lowerHomeomorph n k).symm_apply_apply x

def deformation (n k : ℕ) (hn : 0 < n) (p : Coordinates n k) (hp : ‖p‖ < 1) :
    (ContinuousMap.id (punctured n k p hp)).Homotopy
      ((inclusion n k hn p hp).comp (retraction n k hn p hp)) where
  toContinuousMap :=
    (PuncturedCellAttachment.deformationRel (isPushout n k hn) p hp).toHomotopy.toContinuousMap
  map_zero_left x :=
    (PuncturedCellAttachment.deformationRel (isPushout n k hn) p hp).map_zero_left x
  map_one_left x := by
    have h := (PuncturedCellAttachment.deformationRel (isPushout n k hn) p hp).map_one_left x
    refine h.trans ?_
    change PuncturedCellAttachment.baseInclusion (isPushout n k hn) p hp
      (PuncturedCellAttachment.retraction (isPushout n k hn) p hp x) =
      PuncturedCellAttachment.baseInclusion (isPushout n k hn) p hp
        (StageAttachment.lowerHomeomorph n k ((StageAttachment.lowerHomeomorph n k).symm _))
    rw [Homeomorph.apply_symm_apply]
    rfl

theorem deformation_fixed (n k : ℕ) (hn : 0 < n) (p : Coordinates n k) (hp : ‖p‖ < 1)
    (t : I) (x : James.stage (spherePole n) k) :
    deformation n k hn p hp (t, inclusion n k hn p hp x) = inclusion n k hn p hp x :=
  PuncturedCellAttachment.deformation_fixed (isPushout n k hn) p hp t
    (StageAttachment.lowerHomeomorph n k x)

def deformationRel (n k : ℕ) (hn : 0 < n) (p : Coordinates n k) (hp : ‖p‖ < 1) :
    (ContinuousMap.id (punctured n k p hp)).HomotopyRel
      ((inclusion n k hn p hp).comp (retraction n k hn p hp))
        (Set.range (inclusion n k hn p hp)) :=
  ⟨deformation n k hn p hp, by
    rintro t x ⟨y, rfl⟩
    exact deformation_fixed n k hn p hp t y⟩

end NoExoticSixSphere.JamesSphere.PuncturedStage
