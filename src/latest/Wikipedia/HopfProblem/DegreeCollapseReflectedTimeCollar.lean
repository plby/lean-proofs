import Wikipedia.HopfProblem.DegreeCollapseReflectedOpenHalf
import Wikipedia.HopfProblem.DegreeCollapseReflectedPositiveAttaching
import Wikipedia.HopfProblem.DegreeCollapseTimeCollar

/-!
# The explicit time collar of the original reflected fiber

The old constant seam coordinates give an actual interval-product
homeomorphism. This supplies the collar data to be retained through later
surgeries, without requiring the later manifold to be a reflected double.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def seamTimeBandCoordinates (ε : ℝ) (hc : Icc (-ε) ε ⊆ seamCollarTimes d) :
    TimeBand (time d) ε ≃ₜ Ioo (-ε) ε × EndpointFiber d where
  toFun p := (⟨p.val.val.1, p.property⟩,
    ⟨p.val.val.2, (map_on_seamCollar d p.val.val.1
      (hc ⟨p.property.1.le, p.property.2.le⟩) p.val.val.2).symm.trans p.val.property⟩)
  invFun p := ⟨seamCollarPoint d p.1.val (hc ⟨p.1.property.1.le, p.1.property.2.le⟩) p.2,
    p.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    exact ((continuous_fst.comp (continuous_subtype_val.comp
      continuous_subtype_val)).subtype_mk _).prodMk
      ((continuous_snd.comp (continuous_subtype_val.comp
        continuous_subtype_val)).subtype_mk _)
  continuous_invFun := by
    exact (((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _).subtype_mk _

def timeCollarOfWidth (ε : ℝ) (hε : 0 < ε) (hc : Icc (-ε) ε ⊆ seamCollarTimes d) :
    TimeCollar (time d) (EndpointFiber d) where
  width := ε
  width_pos := hε
  continuous_time := continuous_time d
  coordinates := seamTimeBandCoordinates d ε hc
  coordinate_time _ := rfl

def seamTimeCollar : TimeCollar (time d) (EndpointFiber d) :=
  timeCollarOfWidth d (exists_seam_width d).choose
    (exists_seam_width d).choose_spec.1 (exists_seam_width d).choose_spec.2

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
