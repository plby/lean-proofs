import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Sets.Opens

/-!
# An explicit time collar for the actual cut space

The collar identifies a literal open time band with an interval times
the specified boundary space, retaining the original time coordinate.
This is topological data to construct for the original filling and to
transport through each actual surgery, not a recognition assumption.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.DegreeCollapse

abbrev TimeBand {M : Type*} (t : M → ℝ) (ε : ℝ) := {p : M // t p ∈ Ioo (-ε) ε}

structure TimeCollar {M : Type*} [TopologicalSpace M] (t : M → ℝ)
    (B : Type*) [TopologicalSpace B] where
  width : ℝ
  width_pos : 0 < width
  continuous_time : Continuous t
  coordinates : TimeBand t width ≃ₜ Ioo (-width) width × B
  coordinate_time : ∀ p, (coordinates p).1.val = t p.val

namespace TimeCollar

variable {M B : Type*} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

theorem band_isOpen : IsOpen {p : M | t p ∈ Ioo (-C.width) C.width} :=
  isOpen_Ioo.preimage C.continuous_time

def bandOpen : TopologicalSpace.Opens M := ⟨{p | t p ∈ Ioo (-C.width) C.width}, C.band_isOpen⟩

theorem inverse_time (p : Ioo (-C.width) C.width × B) :
    t (C.coordinates.symm p).val = p.1.val := by
  have he := C.coordinate_time (C.coordinates.symm p)
  rw [C.coordinates.apply_symm_apply] at he
  exact he.symm

def changeBoundary {B' : Type*} [TopologicalSpace B'] (e : B ≃ₜ B') : TimeCollar t B' where
  width := C.width
  width_pos := C.width_pos
  continuous_time := C.continuous_time
  coordinates := C.coordinates.trans ((Homeomorph.refl (Ioo (-C.width) C.width)).prodCongr e)
  coordinate_time := C.coordinate_time

def zeroPoint (b : B) : TimeBand t C.width :=
  C.coordinates.symm (⟨0, neg_lt_zero.mpr C.width_pos, C.width_pos⟩, b)

theorem zeroPoint_time (b : B) : t (C.zeroPoint b).val = 0 := C.inverse_time _

def widenBandPoint {ε : ℝ} (hε : ε ≤ C.width) (p : TimeBand t ε) :
    TimeBand t C.width :=
  ⟨p.val, (neg_le_neg hε).trans_lt p.property.1, p.property.2.trans_le hε⟩

def widenInterval {ε : ℝ} (hε : ε ≤ C.width) (s : Ioo (-ε) ε) :
    Ioo (-C.width) C.width :=
  ⟨s.val, (neg_le_neg hε).trans_lt s.property.1, s.property.2.trans_le hε⟩

def restrictedInverse {ε : ℝ} (hε : ε ≤ C.width) (p : Ioo (-ε) ε × B) :
    TimeBand t ε :=
  ⟨(C.coordinates.symm (C.widenInterval hε p.1, p.2)).val, by
    rw [C.inverse_time]
    exact p.1.property⟩

def restrictedCoordinates {ε : ℝ} (hε : ε ≤ C.width) :
    TimeBand t ε ≃ₜ Ioo (-ε) ε × B where
  toFun p := (⟨t p.val, p.property⟩, (C.coordinates (C.widenBandPoint hε p)).2)
  invFun := C.restrictedInverse hε
  left_inv p := by
    apply Subtype.ext
    change (C.coordinates.symm
      (C.widenInterval hε ⟨t p.val, p.property⟩,
        (C.coordinates (C.widenBandPoint hε p)).2)).val = p.val
    have he : (C.widenInterval hε ⟨t p.val, p.property⟩,
        (C.coordinates (C.widenBandPoint hε p)).2) =
        C.coordinates (C.widenBandPoint hε p) := by
      apply Prod.ext
      · exact Subtype.ext (C.coordinate_time (C.widenBandPoint hε p)).symm
      · rfl
    rw [he, C.coordinates.symm_apply_apply]
    rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact C.inverse_time _
    · have he : C.widenBandPoint hε (C.restrictedInverse hε p) =
          C.coordinates.symm (C.widenInterval hε p.1, p.2) := Subtype.ext rfl
      change (C.coordinates (C.widenBandPoint hε (C.restrictedInverse hε p))).2 = p.2
      rw [he, C.coordinates.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (C.continuous_time.comp continuous_subtype_val).subtype_mk _
    · exact continuous_snd.comp (C.coordinates.continuous.comp
        (continuous_subtype_val.subtype_mk _))
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (C.coordinates.symm.continuous.comp
      (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd))

def restrict (ε : ℝ) (hε : 0 < ε) (hεw : ε ≤ C.width) : TimeCollar t B where
  width := ε
  width_pos := hε
  continuous_time := C.continuous_time
  coordinates := C.restrictedCoordinates hεw
  coordinate_time _ := rfl

end TimeCollar
end Wikipedia.HopfProblem.DegreeCollapse
