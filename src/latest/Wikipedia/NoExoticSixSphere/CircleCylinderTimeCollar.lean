import Wikipedia.NoExoticSixSphere.CircleCylinderClosedCollar
import Wikipedia.HopfProblem.DegreeCollapseTimeCollar

/-!
# An explicit time collar on the genuine two-ended circle double

Restrict the proved closed-band homeomorphism to the literal open time
band. The resulting `TimeCollar` has the original endpoint sum as boundary,
retains the actual seam time, and has the original endpoint inclusions
as its zero points. No existence or connectedness premise is added.
-/

noncomputable section

open Set Wikipedia.HopfProblem.DegreeCollapse
open scoped Manifold

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem continuous_time : Continuous (time d) :=
  contMDiff_seam.continuous.comp (continuous_fst.comp continuous_subtype_val)

def openBandToClosed : C(TimeBand (time d) (collarWidth d), ClosedTimeBand d) where
  toFun p := ⟨p.val, p.property.1.le, p.property.2.le⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def openIntervalToClosed : C(Ioo (-collarWidth d) (collarWidth d), CollarInterval d) where
  toFun s := ⟨s.val, s.property.1.le, s.property.2.le⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

def openCollarInverse :
    C(Ioo (-collarWidth d) (collarWidth d) × Endpoints d,
      TimeBand (time d) (collarWidth d)) where
  toFun p := ⟨(closedCollar d (openIntervalToClosed d p.1, p.2)).val,
    (time_closedCollar d (openIntervalToClosed d p.1, p.2)).symm ▸ p.1.property⟩
  continuous_toFun := (continuous_subtype_val.comp ((closedCollar d).continuous.comp
    (((openIntervalToClosed d).continuous.comp continuous_fst).prodMk
      continuous_snd))).subtype_mk _

theorem time_openCollarInverse
    (p : Ioo (-collarWidth d) (collarWidth d) × Endpoints d) :
    time d (openCollarInverse d p).val = p.1.val := time_closedCollar d _

def collarCoordinates : TimeBand (time d) (collarWidth d) ≃ₜ
    Ioo (-collarWidth d) (collarWidth d) × Endpoints d where
  toFun p := (⟨time d p.val, p.property⟩, ((closedCollar d).symm (openBandToClosed d p)).2)
  invFun := openCollarInverse d
  left_inv p := by
    apply Subtype.ext
    let q := (closedCollar d).symm (openBandToClosed d p)
    have he : (openIntervalToClosed d ⟨time d p.val, p.property⟩, q.2) = q := by
      apply Prod.ext
      · exact Subtype.ext (closedCollar_symm_time d (openBandToClosed d p)).symm
      · rfl
    change (closedCollar d (openIntervalToClosed d ⟨time d p.val, p.property⟩, q.2)).val = p.val
    rw [he]
    change (closedCollar d ((closedCollar d).symm (openBandToClosed d p))).val = p.val
    rw [(closedCollar d).apply_symm_apply]
    rfl
  right_inv p := by
    apply Prod.ext
    · exact Subtype.ext (time_openCollarInverse d p)
    · have he : openBandToClosed d (openCollarInverse d p) =
          closedCollar d (openIntervalToClosed d p.1, p.2) := Subtype.ext rfl
      change ((closedCollar d).symm (openBandToClosed d (openCollarInverse d p))).2 = p.2
      rw [he, (closedCollar d).symm_apply_apply]
  continuous_toFun := ((continuous_time d).comp continuous_subtype_val).subtype_mk _ |>.prodMk
    (continuous_snd.comp ((closedCollar d).symm.continuous.comp (openBandToClosed d).continuous))
  continuous_invFun := (openCollarInverse d).continuous

theorem collarCoordinates_time (p : TimeBand (time d) (collarWidth d)) :
    (collarCoordinates d p).1.val = time d p.val := rfl

def timeCollar : TimeCollar (time d) (Endpoints d) where
  width := collarWidth d
  width_pos := collarWidth_pos d
  continuous_time := continuous_time d
  coordinates := collarCoordinates d
  coordinate_time := collarCoordinates_time d

theorem timeCollar_zeroPoint (x : Endpoints d) :
    ((timeCollar d).zeroPoint x).val = endpointsMap d x := by
  exact closedCollar_zero d x

theorem timeCollar_zeroPoint_inl (x : {x : Sphere m // d.leftMap x = b}) :
    ((timeCollar d).zeroPoint (Sum.inl x)).val = leftInclusion d x :=
  timeCollar_zeroPoint d (Sum.inl x)

theorem timeCollar_zeroPoint_inr (x : {x : Sphere m // d.rightMap x = b}) :
    ((timeCollar d).zeroPoint (Sum.inr x)).val = rightInclusion d x :=
  timeCollar_zeroPoint d (Sum.inr x)

end NoExoticSixSphere.CircleCylinder
