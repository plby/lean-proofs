import StackExchange.Puzzling139335.N5.Prepared.Geometry
import StackExchange.Puzzling139335.N5.TopFace.Coordinates
import StackExchange.Puzzling139335.N5Facet

/-!
# Both strict suffix orientations in the actual prepared configuration

The chosen source point is the inverse image of one endpoint of the
fourth piece's complete top interval.  The source arm endpoint and the
placed images of the actual right and incoming contacts supply the scalar
obstruction's inequalities.
-/

open Set

namespace Puzzling139335.N5

open PlaneIsometries

private theorem suffix_support_bounds {d : SquareDissection} (q : Prepared d)
    {ψ : ℝ} {X : Plane} (hX : X ∈ d.piece 0) (hXtop : q.eD X 1 = 1)
    (hrow₀ : linearMatrix q.eD 1 0 = -Real.sin ψ)
    (hrow₁ : linearMatrix q.eD 1 1 = Real.cos ψ) :
    0 ≤ -Real.sin q.θ * (q.C 0 - (1 - q.b) * Real.cos q.θ - X 0) +
      Real.cos q.θ * (q.C 1 - (1 - q.b) * Real.sin q.θ - X 1) ∧
    -Real.sin ψ * (q.C 0 - (1 - q.b) * Real.cos q.θ - X 0) +
      Real.cos ψ * (q.C 1 - (1 - q.b) * Real.sin q.θ - X 1) ≤ 0 := by
  have hC := (q.corner_support X hX).2
  constructor
  · nlinarith only [hC]
  · simpa only [hrow₀, hrow₁, Matrix.cons_val_zero, Matrix.cons_val_one] using
      q.fourth_top_support hX hXtop _ q.right_arm_endpoint_mem

/-- A strict suffix normal cannot be the top row of the actual fourth
placement.  Both isometry orientations are excluded using actual images
of source contact points. -/
theorem Prepared.suffix_face_impossible {d : SquareDissection} (q : Prepared d)
    {ψ : ℝ} (hθψ : q.θ < ψ) (hψ : ψ < Real.pi / 4)
    (hrow₀ : linearMatrix q.eD 1 0 = -Real.sin ψ)
    (hrow₁ : linearMatrix q.eD 1 1 = Real.cos ψ) : False := by
  have hunit : (-Real.sin ψ) ^ 2 + Real.cos ψ ^ 2 = 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq ψ]
  have hT : 0 < 1 - q.m := sub_pos.mpr q.m_lt_one
  have hTL : 1 - q.m < 1 - q.b := sub_lt_sub_left q.b_lt_m 1
  rcases eD_top_row_forms q.eD (-Real.sin ψ) (Real.cos ψ) hrow₀ hrow₁ with
    hform | hform
  · let X : Plane := q.eD.symm (Schoenflies.Plane.mk q.m 1)
    let Y : Plane := q.eD.symm (Schoenflies.Plane.mk q.b 1)
    have hX : X ∈ d.piece 0 := q.D_right_mem
    have hY : Y ∈ d.piece 0 := q.D_left_mem
    have hXimage : q.eD X = Schoenflies.Plane.mk q.m 1 := q.eD.apply_symm_apply _
    have hXtop : q.eD X 1 = 1 := congrArg (fun p : Plane => p 1) hXimage
    obtain ⟨hC, hXsupport⟩ := suffix_support_bounds q hX hXtop hrow₀ hrow₁
    obtain ⟨hXY₀, _⟩ := eD_top_inverse_endpoints_first hunit hform q.b q.m
    change X 0 = Y 0 + (q.m - q.b) * Real.cos ψ at hXY₀
    have hYbound : ((1 - q.b) - (1 - q.m)) * Real.cos ψ ≤ X 0 := by
      have hYnonneg : 0 ≤ Y 0 := (d.piece_subset 0 hY).1.1
      nlinarith only [hXY₀, hYnonneg]
    have hF : q.C 0 + (1 - q.m) * Real.sin q.θ ≤ 1 :=
      (d.piece_subset 0 q.incoming_arm_endpoint_mem).1.2
    have hEfit : q.eD (Schoenflies.Plane.mk 1 q.b) 0 ≤ 1 :=
      (q.fit_D (mem_image_of_mem q.eD q.right_contact_mem)).1.2
    rw [hform] at hEfit
    change Real.cos ψ * 1 - (-Real.sin ψ) * q.b + (q.eD 0) 0 ≤ 1 at hEfit
    have hXfirst : q.eD X 0 = q.m := congrArg (fun p : Plane => p 0) hXimage
    rw [hform] at hXfirst
    change Real.cos ψ * X 0 - (-Real.sin ψ) * X 1 + (q.eD 0) 0 = q.m at hXfirst
    have himage : Real.cos ψ + Real.sin ψ * q.b - (1 - q.m) ≤
        Real.cos ψ * X 0 + Real.sin ψ * X 1 := by
      nlinarith only [hEfit, hXfirst]
    exact N5Facet.suffix_right_impossible q.angle.1 hθψ hψ q.b_pos rfl hT hTL
      q.b_lt_ratio hC hXsupport hYbound (q.normalized.below_diagonal hX) hF himage
  · let X : Plane := q.eD.symm (Schoenflies.Plane.mk q.b 1)
    have hX : X ∈ d.piece 0 := q.D_left_mem
    have hXimage : q.eD X = Schoenflies.Plane.mk q.b 1 := q.eD.apply_symm_apply _
    have hXtop : q.eD X 1 = 1 := congrArg (fun p : Plane => p 1) hXimage
    obtain ⟨hC, hXsupport⟩ := suffix_support_bounds q hX hXtop hrow₀ hrow₁
    have hFfit : 0 ≤ q.eD
        (!₂[q.C 0 + (1 - q.m) * Real.sin q.θ,
          q.C 1 - (1 - q.m) * Real.cos q.θ]) 0 :=
      (q.fit_D (mem_image_of_mem q.eD q.incoming_arm_endpoint_mem)).1.1
    rw [hform] at hFfit
    change 0 ≤ -Real.cos ψ * (q.C 0 + (1 - q.m) * Real.sin q.θ) +
      (-Real.sin ψ) * (q.C 1 - (1 - q.m) * Real.cos q.θ) + (q.eD 0) 0 at hFfit
    have hXfirst : q.eD X 0 = q.b := congrArg (fun p : Plane => p 0) hXimage
    rw [hform] at hXfirst
    change -Real.cos ψ * X 0 + (-Real.sin ψ) * X 1 + (q.eD 0) 0 = q.b at hXfirst
    have himage : Real.cos ψ * (q.C 0 + (1 - q.m) * Real.sin q.θ - X 0) +
        Real.sin ψ * (q.C 1 - (1 - q.m) * Real.cos q.θ - X 1) ≤ q.b := by
      nlinarith only [hFfit, hXfirst]
    exact N5Facet.suffix_left_impossible q.angle.1 hθψ hψ rfl hT hTL q.b_lt_ratio
      hC hXsupport himage

end Puzzling139335.N5
