import Wikipedia.HopfProblem.DegreeCollapseSurgeryInteriorCoordinates
import Wikipedia.SmoothSixDPoincare.PuncturedBallHomotopy

/-!
# Homotopy coordinates for the actual surgery open cover

The open product piece contracts to the original attaching sphere. Its
intersection with the core complement is the genuine punctured open
product. A sphere of radius one half gives homotopy coordinates on this
intersection. Both inclusion maps retain their actual geometric formulas.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryInteriorCoordinates

open Wikipedia.SmoothSixDPoincare PuncturedHandle

variable {E F R X Y : Type} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y)

abbrev overlapSet : Set X := d.OldComplement ∩ interiorSet d

theorem oldPiece_mem_overlap_iff (p : UnitSphere E × UnitBall F) :
    d.oldPiece p ∈ overlapSet d ↔ p.2.val ≠ 0 ∧ ‖p.2.val‖ < 1 := by
  change (d.oldPiece p ∉ range d.attachingSphere ∧ d.oldPiece p ∈ interiorSet d) ↔ _
  rw [d.oldPiece_mem_core_iff, oldPiece_mem_interior_iff]

def overlapParameterHomeomorph :
    (UnitSphere E × PuncturedBall.Space F 1) ≃ₜ (d.oldPiece ⁻¹' overlapSet d) where
  toFun p := ⟨(p.1, ⟨p.2.val, p.2.property.2.le⟩),
    (oldPiece_mem_overlap_iff d _).mpr p.2.property⟩
  invFun p := (p.val.1, ⟨p.val.2.val, (oldPiece_mem_overlap_iff d _).mp p.property⟩)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  continuous_invFun :=
    (continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)).subtype_mk _)

def overlapHomeomorph : (UnitSphere E × PuncturedBall.Space F 1) ≃ₜ overlapSet d :=
  (overlapParameterHomeomorph d).trans
    (d.oldPiece_closed.isEmbedding.homeomorphOfSubsetRange
      (fun _ hx ↦ interior_subset_range d hx.2))

theorem overlapHomeomorph_point (p : UnitSphere E × PuncturedBall.Space F 1) :
    (overlapHomeomorph d p).val = d.oldPiece (p.1, ⟨p.2.val, p.2.property.2.le⟩) := rfl

variable [NormedSpace ℝ F]

def zeroSection : C(UnitSphere E, UnitSphere E × OpenBall F) :=
  ContinuousMap.id _ |>.prodMk (ContinuousMap.const _ ⟨0, by simp⟩)

def openProductDeformation :
    (ContinuousMap.id (UnitSphere E × OpenBall F)).Homotopy
      ((zeroSection (E := E) (F := F)).comp ContinuousMap.fst) where
  toFun p := (p.2.1, ⟨(1 - (p.1 : ℝ)) • p.2.2.val, by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr p.1.property.2)]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _)
      (sub_le_self _ p.1.property.1)) p.2.2.property⟩)
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_snd
    · apply Continuous.subtype_mk
      exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  map_zero_left p := by ext <;> simp
  map_one_left p := by ext <;> simp [zeroSection]

def openProductHomotopyEquiv : UnitSphere E ≃ₕ (UnitSphere E × OpenBall F) where
  toFun := zeroSection
  invFun := ContinuousMap.fst
  left_inv := by
    have h : ContinuousMap.fst.comp (zeroSection (E := E) (F := F)) =
        ContinuousMap.id (UnitSphere E) := rfl
    rw [h]
  right_inv := ⟨openProductDeformation.symm⟩

def coreHomotopyEquiv : UnitSphere E ≃ₕ interiorSet d :=
  openProductHomotopyEquiv.trans (interiorHomeomorph d).toHomotopyEquiv

theorem coreHomotopyEquiv_point (u : UnitSphere E) :
    (coreHomotopyEquiv d u).val = d.attachingSphere u := rfl

def halfRadius : Radius := ⟨1 / 2, by norm_num, by norm_num⟩

def overlapHomotopyEquiv : (UnitSphere E × UnitSphere F) ≃ₕ overlapSet d :=
  ((ContinuousMap.HomotopyEquiv.refl (UnitSphere E)).prodCongr
    (PuncturedBall.sphereHomotopyEquiv 1 (1 / 2) (by norm_num) (by norm_num))).trans
      (overlapHomeomorph d).toHomotopyEquiv

theorem overlap_left :
    (ContinuousMap.inclusion (inter_subset_left : overlapSet d ⊆ d.OldComplement)).comp
      (overlapHomotopyEquiv d).toFun = SurgeryExteriorRetraction.radialSphereMap d halfRadius := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  rfl

theorem overlap_right_projection :
    (coreHomotopyEquiv d).invFun.comp
      ((ContinuousMap.inclusion (inter_subset_right : overlapSet d ⊆ interiorSet d)).comp
        (overlapHomotopyEquiv d).toFun) = ContinuousMap.fst := by
  apply ContinuousMap.ext
  intro q
  let v := PuncturedBall.fromSphere (E := F) 1 (1 / 2) (by norm_num) (by norm_num) q.2
  have h : (ContinuousMap.inclusion
      (inter_subset_right : overlapSet d ⊆ interiorSet d)) (overlapHomotopyEquiv d q) =
        interiorHomeomorph d (q.1, ⟨v.val, v.property.2⟩) := by
    apply Subtype.ext
    rfl
  change ((interiorHomeomorph d).symm
    ((ContinuousMap.inclusion (inter_subset_right : overlapSet d ⊆ interiorSet d))
      (overlapHomotopyEquiv d q))).1 = q.1
  rw [h, (interiorHomeomorph d).symm_apply_apply]

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryInteriorCoordinates
