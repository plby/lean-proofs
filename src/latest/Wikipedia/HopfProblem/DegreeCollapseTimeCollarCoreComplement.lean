import Wikipedia.HopfProblem.DegreeCollapseTimeCollarCompactCore
import Mathlib.Analysis.Convex.PathConnected

/-!
# The complement of each small interior core is the actual collar strip

The original collar coordinates identify the complement of t >= c in
the positive interior with (0,c) times the specified boundary. In
particular, a path-connected boundary gives a path-connected complement.
-/

noncomputable section

open Set Function TopologicalSpace

namespace Wikipedia.HopfProblem.DegreeCollapse.TimeCollar

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B) (c : ℝ) (hc : c < C.width)

theorem coreComplement_time_lt (p : ↥((C.interiorCore c)ᶜ)) : t p.val.val < c :=
  not_le.mp (show ¬ c ≤ t p.val.val from p.property)

def coreComplementBandPoint (p : ↥((C.interiorCore c)ᶜ)) : TimeBand t C.width :=
  ⟨p.val.val, (neg_lt_zero.mpr C.width_pos).trans p.val.property,
    (C.coreComplement_time_lt c p).trans hc⟩

def coreComplementInverse (p : Ioo (0 : ℝ) c × B) : ↥((C.interiorCore c)ᶜ) :=
  ⟨⟨(C.coordinates.symm
    (⟨p.1.val, (neg_lt_zero.mpr C.width_pos).trans p.1.property.1,
      p.1.property.2.trans hc⟩, p.2)).val, by
      change 0 < t _
      rw [C.inverse_time]
      exact p.1.property.1⟩, by
    change ¬ c ≤ t _
    rw [C.inverse_time]
    exact not_le.mpr p.1.property.2⟩

def coreComplementHomeomorph : ↥((C.interiorCore c)ᶜ) ≃ₜ Ioo (0 : ℝ) c × B where
  toFun p := (⟨t p.val.val, p.val.property, C.coreComplement_time_lt c p⟩,
    (C.coordinates (C.coreComplementBandPoint c hc p)).2)
  invFun := C.coreComplementInverse c hc
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    change (C.coordinates.symm _).val = p.val.val
    have he : (⟨t p.val.val,
        (neg_lt_zero.mpr C.width_pos).trans p.val.property,
        (C.coreComplement_time_lt c p).trans hc⟩,
        (C.coordinates (C.coreComplementBandPoint c hc p)).2) =
        C.coordinates (C.coreComplementBandPoint c hc p) := by
      apply Prod.ext
      · exact Subtype.ext (C.coordinate_time (C.coreComplementBandPoint c hc p)).symm
      · rfl
    rw [he, C.coordinates.symm_apply_apply]
    rfl
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact C.inverse_time _
    · have he : C.coreComplementBandPoint c hc (C.coreComplementInverse c hc p) =
          C.coordinates.symm
            (⟨p.1.val, (neg_lt_zero.mpr C.width_pos).trans p.1.property.1,
              p.1.property.2.trans hc⟩, p.2) := Subtype.ext rfl
      change (C.coordinates (C.coreComplementBandPoint c hc
        (C.coreComplementInverse c hc p))).2 = p.2
      rw [he, C.coordinates.apply_symm_apply]
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (C.continuous_time.comp
        (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    · exact continuous_snd.comp (C.coordinates.continuous.comp
        ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (C.coordinates.symm.continuous.comp
      (((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd))

include hc in
theorem pathConnectedSpace_coreComplement (hc0 : 0 < c) [PathConnectedSpace B] :
    PathConnectedSpace ↥((C.interiorCore c)ᶜ) := by
  let : PathConnectedSpace (Ioo (0 : ℝ) c) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ioo (0 : ℝ) c).isPathConnected (nonempty_Ioo.mpr hc0))
  apply pathConnectedSpace_iff_univ.mpr
  have h := (isPathConnected_univ : IsPathConnected (univ : Set (Ioo (0 : ℝ) c × B))).image
    (C.coreComplementHomeomorph c hc).symm.continuous
  simpa only [image_univ, (C.coreComplementHomeomorph c hc).symm.surjective.range_eq] using h

end Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
