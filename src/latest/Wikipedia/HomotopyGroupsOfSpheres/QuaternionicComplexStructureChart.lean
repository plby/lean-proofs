import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicComplexStructureCayley

/-!
# A native open partial homeomorphism on the quaternionic complex-structure space

The source is the actual relative Cayley neighborhood. The target is the
entire real anticommuting skew subspace at the chosen complex structure.
The inverse chart also has a smooth ambient operator expression.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.Cayley

variable {n : ℕ}

def homeomorph (J : Space n) : domain J ≃ₜ AntiSkewSpace J where
  toFun p := coordinate J p.val p.property
  invFun K := ⟨point J K, point_mem_domain J K⟩
  left_inv p := Subtype.ext (point_coordinate J p.val p.property)
  right_inv := coordinate_point J
  continuous_toFun := continuous_coordinate J
  continuous_invFun := (continuous_point J).subtype_mk _

def coordinates (J J' : Space n) : AntiSkewSpace J := by
  classical
  exact if h : J' ∈ domain J then coordinate J J' h else 0

theorem coordinates_of_mem (J J' : Space n) (h : J' ∈ domain J) :
    coordinates J J' = coordinate J J' h := dif_pos h

def chart (J : Space n) : OpenPartialHomeomorph (Space n) (AntiSkewSpace J) where
  toFun := coordinates J
  invFun := point J
  source := domain J
  target := univ
  map_source' _ _ := mem_univ _
  map_target' K _ := point_mem_domain J K
  left_inv' J' h := by
    rw [coordinates_of_mem J J' h]
    exact point_coordinate J J' h
  right_inv' K _ := by
    rw [coordinates_of_mem J _ (point_mem_domain J K)]
    exact coordinate_point J K
  open_source := isOpen_domain J
  open_target := isOpen_univ
  continuousOn_toFun := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact (continuous_coordinate J).congr
      (fun p ↦ (coordinates_of_mem J p.val p.property).symm)
  continuousOn_invFun := (continuous_point J).continuousOn

theorem self_mem_chart_source (J : Space n) : J ∈ (chart J).source := self_mem_domain J

theorem chart_self (J : Space n) : chart J J = 0 := by
  change coordinates J J = 0
  rw [coordinates_of_mem J J (self_mem_domain J), coordinate_self]

theorem chart_symm_zero (J : Space n) : (chart J).symm 0 = J := point_zero J

theorem point_operator (J : Space n) (K : AntiSkewSpace J) :
    (point J K).val.val = J.val.val.comp (NoExoticSixSphere.CayleyTransform.fraction K.val) := rfl

theorem contDiff_point_operator (J : Space n) :
    ContDiff ℝ ∞ (fun K : AntiSkewSpace J ↦ (point J K).val.val) := by
  let L := (toOrthogonalSkew n).comp (antiSkewToSkew J)
  have hL : ContDiff ℝ ∞ L :=
    finiteLinearMap_contDiff (E := AntiSkewSpace J)
      (F := NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4)) L
  have hf := (NoExoticSixSphere.CayleyTransform.contDiff_operator (n := 4 * n + 4)).comp hL
  exact contDiff_const.clm_comp hf

theorem contMDiff_point_toSymplectic (J : Space n) :
    ContMDiff 𝓘(ℝ, AntiSkewSpace J) 𝓘(ℝ, SkewSpace n) ∞
      (fun K : AntiSkewSpace J ↦ toSymplectic (point J K)) :=
  Smoothness.contMDiff_iff_operator.mpr (contDiff_point_operator J).contMDiff

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.ComplexStructures.Cayley
