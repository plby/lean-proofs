import Wikipedia.HopfProblem.CuspControlledRetractionCoordinates
import Wikipedia.HopfProblem.CuspControlledRetractionInterpolation
import Wikipedia.HopfProblem.CuspHoneycombHomeomorph
import Wikipedia.HopfProblem.CuspPositiveRetractionStrong

/-!
# The actual height-supported central endpoint interpolation

Apply the explicit affine cutoff construction in the genuine honeycomb
coordinates of the positive central fibre. The old endpoint is retained
near height zero, while the chosen positive height is sent exactly to the
normalized logarithmic honeycomb map. Every interpolated map is central,
and the actual positive lattice action commutes with the interpolation.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspControlledRetraction

open ToricSpace CuspPositiveRetraction CuspCollapse CuspHoneycomb CuspPositive

def positiveHeight {η : ℝ} (q : ClosedPositiveTube η) : ℝ := ‖time (q.1 : Space)‖

theorem positiveHeight_continuous {η : ℝ} :
    Continuous (positiveHeight : ClosedPositiveTube η → ℝ) :=
  (time_holomorphic.continuous.comp
    (continuous_subtype_val.comp continuous_subtype_val)).norm

theorem positiveHeight_translate (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (η : ℝ)
    (v : Fin 2 → ℤ) (q : ClosedPositiveTube η) :
    positiveHeight (closedPositiveTranslate C₀ η v q) = positiveHeight q := by
  change ‖time (twistedTranslate (positiveTwist C₀) v (q.1 : Space))‖ = _
  rw [time_twistedTranslate]
  rfl

variable {η : ℝ} (P : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η))
variable (hone : ∀ q : ClosedPositiveTube η, time ((P (1, q)).1 : Space) = 0)

/-- The old endpoint regarded as a map to the literal positive central fibre. -/
def positiveEndpoint : C(ClosedPositiveTube η, PositiveCentralFibre) where
  toFun q := ⟨(P (1, q)).1, hone q⟩
  continuous_toFun := (continuous_subtype_val.comp
    (P.continuous.comp (continuous_const.prodMk continuous_id))).subtype_mk _

variable (C₀ : Matrix (Fin 2) (Fin 2) ℂ)

/-- The old endpoint in the constructed planar honeycomb coordinates. -/
def endpointPosition : C(ClosedPositiveTube η, CuspHoneycombTiling.Plane) where
  toFun q := (honeycombHomeomorph C₀).symm (positiveEndpoint P hone q)
  continuous_toFun := (honeycombHomeomorph C₀).symm.continuous.comp
    (positiveEndpoint P hone).continuous

theorem positiveEndpoint_equivariant
    (hequiv : ∀ s v q, P (s, closedPositiveTranslate C₀ η v q) =
      closedPositiveTranslate C₀ η v (P (s, q)))
    (v : Fin 2 → ℤ) (q : ClosedPositiveTube η) :
    positiveEndpoint P hone (closedPositiveTranslate C₀ η v q) =
      positiveCentralTranslate C₀ v (positiveEndpoint P hone q) := by
  apply Subtype.ext
  exact congrArg (fun x : ClosedPositiveTube η => x.1) (hequiv 1 v q)

theorem endpointPosition_equivariant
    (hequiv : ∀ s v q, P (s, closedPositiveTranslate C₀ η v q) =
      closedPositiveTranslate C₀ η v (P (s, q)))
    (v : Fin 2 → ℤ) (q : ClosedPositiveTube η) :
    endpointPosition P hone C₀ (closedPositiveTranslate C₀ η v q) =
      endpointPosition P hone C₀ q + CuspHoneycombTiling.latticePoint (cuspVector v) := by
  change (honeycombHomeomorph C₀).symm
    (positiveEndpoint P hone (closedPositiveTranslate C₀ η v q)) = _
  rw [positiveEndpoint_equivariant P hone C₀ hequiv, honeycombHomeomorph_symm_equivariant]
  rfl

variable {ε : ℝ} (hε1 : ε < 1) (hR : SmallDrift (positiveTwist C₀) ε)
variable (hηε : η < ε) (hη : 0 ≤ η) (ρ : ℝ) (hρ : 0 < ρ)

include hε1 hR hηε in
private theorem normalizedPosition_height_continuousOn :
    ContinuousOn (fun q : ClosedPositiveTube η => normalizedPosition C₀ (q.1 : Space))
      {q | positiveHeight q ≠ 0} := by
  simpa only [positiveHeight, ne_eq, norm_eq_zero] using
    normalizedPosition_closedPositive_continuousOn C₀ hε1 hR hηε

/-- The actual central homotopy with the explicit height cutoff. -/
def centralInterpolation : C(unitInterval × ClosedPositiveTube η, ClosedPositiveTube η) where
  toFun p := positiveCentralInclusion η hη (honeycombHomeomorph C₀
    (Interpolation.interpolate ρ positiveHeight (endpointPosition P hone C₀)
      (fun q => normalizedPosition C₀ (q.1 : Space)) p))
  continuous_toFun := (positiveCentralInclusion η hη).continuous.comp
    ((honeycombHomeomorph C₀).continuous.comp
      (Interpolation.interpolate_continuous ρ positiveHeight (endpointPosition P hone C₀)
        (fun q => normalizedPosition C₀ (q.1 : Space)) hρ positiveHeight_continuous
        (endpointPosition P hone C₀).continuous
        (normalizedPosition_height_continuousOn C₀ hε1 hR hηε)))

theorem centralInterpolation_apply (s : unitInterval) (q : ClosedPositiveTube η) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q) =
      positiveCentralInclusion η hη
        (honeycombHomeomorph C₀ (Interpolation.interpolate ρ positiveHeight
          (endpointPosition P hone C₀) (fun r => normalizedPosition C₀ (r.1 : Space))
            (s, q))) := rfl

theorem centralInterpolation_zero (q : ClosedPositiveTube η) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (0, q) = P (1, q) := by
  rw [centralInterpolation_apply, Interpolation.interpolate_zero]
  change positiveCentralInclusion η hη
    (honeycombHomeomorph C₀ ((honeycombHomeomorph C₀).symm (positiveEndpoint P hone q))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem centralInterpolation_central (s : unitInterval) (q : ClosedPositiveTube η) :
    time ((centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)).1 : Space) = 0 :=
  (honeycombHomeomorph C₀ (Interpolation.interpolate ρ positiveHeight
    (endpointPosition P hone C₀) (fun r => normalizedPosition C₀ (r.1 : Space)) (s, q))).2

theorem centralInterpolation_eq_endpoint_of_height_le_half
    (s : unitInterval) (q : ClosedPositiveTube η) (hq : positiveHeight q ≤ ρ / 2) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q) = P (1, q) := by
  rw [centralInterpolation_apply,
    Interpolation.interpolate_eq_left_of_height_le_half _ _ _ _ hρ s q hq]
  change positiveCentralInclusion η hη
    (honeycombHomeomorph C₀ ((honeycombHomeomorph C₀).symm (positiveEndpoint P hone q))) = _
  rw [Homeomorph.apply_symm_apply]
  rfl

theorem centralInterpolation_fixed
    (hfix : ∀ s q, time (q.1 : Space) = 0 → P (s, q) = q)
    (s : unitInterval) (q : ClosedPositiveTube η) (hq : time (q.1 : Space) = 0) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q) = q := by
  rw [centralInterpolation_eq_endpoint_of_height_le_half P hone C₀ hε1 hR hηε hη ρ hρ s q
    (by simpa only [positiveHeight, hq, norm_zero] using (half_pos hρ).le)]
  exact hfix 1 q hq

theorem centralInterpolation_equivariant
    (hequiv : ∀ s v q, P (s, closedPositiveTranslate C₀ η v q) =
      closedPositiveTranslate C₀ η v (P (s, q)))
    (s : unitInterval) (v : Fin 2 → ℤ) (q : ClosedPositiveTube η) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ
      (s, closedPositiveTranslate C₀ η v q) =
      closedPositiveTranslate C₀ η v
        (centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)) := by
  have he := Interpolation.interpolate_translate ρ positiveHeight
    (endpointPosition P hone C₀) (fun q => normalizedPosition C₀ (q.1 : Space)) hρ
    (closedPositiveTranslate C₀ η v) (CuspHoneycombTiling.latticePoint (cuspVector v))
    (positiveHeight_translate C₀ η v)
    (endpointPosition_equivariant P hone C₀ hequiv v)
    (fun q hq => normalizedPosition_closedPositive_twistedTranslate C₀ hε1 hR hηε v
      (norm_ne_zero_iff.mp hq)) s q
  rw [centralInterpolation_apply, he, honeycombHomeomorph_equivariant]
  rfl

theorem centralInterpolation_nonincreasing (s : unitInterval) (q : ClosedPositiveTube η) :
    positiveHeight (centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)) ≤
      positiveHeight q := by
  change ‖time ((centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (s, q)).1 : Space)‖ ≤ _
  rw [centralInterpolation_central, norm_zero]
  exact norm_nonneg _

/-- At the chosen positive height the new endpoint is exactly the
constructed logarithmic honeycomb collapse, not only homotopic to it. -/
theorem centralInterpolation_one_of_height_eq (q : ClosedPositiveTube η)
    (hq : positiveHeight q = ρ) :
    centralInterpolation P hone C₀ hε1 hR hηε hη ρ hρ (1, q) =
      positiveCentralInclusion η hη
        (honeycombHomeomorph C₀ (normalizedPosition C₀ (q.1 : Space))) := by
  rw [centralInterpolation_apply, Interpolation.interpolate_one_of_height_eq _ _ _ _ q hq]

end Wikipedia.HopfProblem.CuspControlledRetraction
