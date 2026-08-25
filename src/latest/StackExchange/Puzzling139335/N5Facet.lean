import StackExchange.Puzzling139335.N5Facet.Elementary
import StackExchange.Puzzling139335.N5Facet.Aligned
import StackExchange.Puzzling139335.N5Facet.SuffixAlgebra
import StackExchange.Puzzling139335.N5Facet.Trigonometry
import StackExchange.Puzzling139335.N5Facet.TranslationAligned

/-!
# The N5 strict facet obstructions

The source corner is `(h,k)`, its two supporting arms have lengths `L,T`,
and the outgoing face has endpoints `X,Y`, with
`X - Y = (L-T) * (cos ψ, sin ψ)`.  All hypotheses below are explicit
coordinate inequalities for these actual points and support lines.

The region classification and the existence of the actual supporting
segments are deliberately separate from these fully proved calculations.
-/

namespace Puzzling139335.N5Facet

/-- The two source support lines control both the first coordinate and
the projection of `E-X`, where `E=(h,k)-L*(cos t,sin t)`. -/
theorem outgoing_support_projections {t ψ h k L Xx Xy : ℝ}
    (ht : 0 < t) (htψ : t < ψ) (hψ4 : ψ < Real.pi / 4)
    (hC : 0 ≤ -Real.sin t * (h - L * Real.cos t - Xx) +
      Real.cos t * (k - L * Real.sin t - Xy))
    (hX : -Real.sin ψ * (h - L * Real.cos t - Xx) +
      Real.cos ψ * (k - L * Real.sin t - Xy) ≤ 0) :
    Xx ≤ h - L * Real.cos t ∧
      0 ≤ Real.cos ψ * (h - L * Real.cos t - Xx) +
        Real.sin ψ * (k - L * Real.sin t - Xy) := by
  obtain ⟨hc, hs, hp, hq⟩ := suffix_trig_pos ht htψ hψ4
  have hd : 0 < Real.cos t * Real.sin ψ - Real.sin t * Real.cos ψ := by
    have h := sin_sub_pos ht htψ hψ4
    rw [Real.sin_sub] at h
    nlinarith only [h]
  have hunit : Real.cos ψ ^ 2 + Real.sin ψ ^ 2 = 1 := by
    nlinarith only [Real.sin_sq_add_cos_sq ψ]
  obtain ⟨hx, hz⟩ := cone_projection_bounds hc hp hs.le hq.le hd hunit hC hX
  exact ⟨by linarith, hz⟩

/-- Rightward image of the outgoing face.  The lower bound on `Xx` is
exactly the nonnegative first coordinate of its other endpoint `Y`. -/
theorem suffix_right_impossible {t ψ h k b L T Xx Xy : ℝ}
    (ht : 0 < t) (htψ : t < ψ) (hψ4 : ψ < Real.pi / 4)
    (hb : 0 < b) (hL : L = 1 - b) (hT : 0 < T) (hTL : T < L)
    (hbsmall : b < Real.sin t / (1 + Real.cos t))
    (hC : 0 ≤ -Real.sin t * (h - L * Real.cos t - Xx) +
      Real.cos t * (k - L * Real.sin t - Xy))
    (hX : -Real.sin ψ * (h - L * Real.cos t - Xx) +
      Real.cos ψ * (k - L * Real.sin t - Xy) ≤ 0)
    (hY : (L - T) * Real.cos ψ ≤ Xx) (htri : Xy ≤ Xx)
    (hF : h + T * Real.sin t ≤ 1)
    (himage : Real.cos ψ + Real.sin ψ * b - T ≤
      Real.cos ψ * Xx + Real.sin ψ * Xy) : False := by
  obtain ⟨hc, hs, hp, hq⟩ := suffix_trig_pos ht htψ hψ4
  obtain ⟨hxx, _hproj⟩ := outgoing_support_projections ht htψ hψ4 hC hX
  have hspan : L * (Real.cos t + Real.sin t) < 1 :=
    source_span (sub_pos.mpr hTL) (sin_lt_other_cos ht htψ hψ4) hxx hY hF
  have ht6 : Real.pi / 6 < t :=
    pi_div_six_lt_of_contact_bounds ht (htψ.trans hψ4) hb hbsmall
      (by simpa only [hL] using hspan)
  have hbL : b = 1 - L := by linarith
  have hfit : Real.cos ψ + Real.sin ψ * (1 - L) - T ≤
      Real.cos ψ * Xx + Real.sin ψ * Xy := by
    simpa only [hbL] using himage
  exact right_suffix_algebra (hT.trans hTL) hTL hp hq hxx htri hF hfit
    (suffix_coefficient_pos ht htψ hψ4) (suffix_coefficients_lt ht htψ hψ4 ht6)

/-- Leftward image of the outgoing face.  Its image of the actual endpoint
`F=(h,k)-T*(-sin t,cos t)` must still have nonnegative first coordinate. -/
theorem suffix_left_impossible {t ψ h k b L T Xx Xy : ℝ}
    (ht : 0 < t) (htψ : t < ψ) (hψ4 : ψ < Real.pi / 4)
    (hL : L = 1 - b) (hT : 0 < T) (hTL : T < L)
    (hbsmall : b < Real.sin t / (1 + Real.cos t))
    (hC : 0 ≤ -Real.sin t * (h - L * Real.cos t - Xx) +
      Real.cos t * (k - L * Real.sin t - Xy))
    (hX : -Real.sin ψ * (h - L * Real.cos t - Xx) +
      Real.cos ψ * (k - L * Real.sin t - Xy) ≤ 0)
    (himage : Real.cos ψ * (h + T * Real.sin t - Xx) +
      Real.sin ψ * (k - T * Real.cos t - Xy) ≤ b) : False := by
  obtain ⟨_hxx, hproj⟩ := outgoing_support_projections ht htψ hψ4 hC hX
  have hleg : b < L * Real.sin t := by
    rw [hL]
    exact contact_lt_remaining_mul_sin ht (htψ.trans hψ4) hbsmall
  have hsource :
      (Real.cos ψ * (h - L * Real.cos t - Xx) +
        Real.sin ψ * (k - L * Real.sin t - Xy)) +
        L * Real.cos (ψ - t) - T * Real.sin (ψ - t) ≤ b := by
    calc
      _ = Real.cos ψ * (h + T * Real.sin t - Xx) +
          Real.sin ψ * (k - T * Real.cos t - Xy) := by
        rw [Real.cos_sub, Real.sin_sub]
        ring
      _ ≤ b := himage
  exact left_suffix_algebra (hT.trans hTL) hTL
    (sin_sub_pos ht htψ hψ4) (sin_lt_cos_sub_sub_sin_sub ht htψ hψ4)
    hproj hleg hsource

end Puzzling139335.N5Facet
