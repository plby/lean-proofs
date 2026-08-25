import StackExchange.Puzzling139335.N5.Normalized

/-!
# A singleton-corner placement sends the base origin off the diagonal

The conclusion follows from the actual affine coordinate classification
and the source-point support inequalities.  It is useful for excluding
diagonal invariance of the remaining singleton-corner piece.
-/

open Set

namespace Puzzling139335.N5

theorem Normalized.origin_image_off_diagonal {d : SquareDissection}
    (h : Normalized d) (hprotected : d.HasProtectedCenter)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2) :
    e (corner 0) 0 ≠ e (corner 0) 1 := by
  intro hdiag
  let C := e.symm (corner 2)
  obtain ⟨hC, hCA, hCB⟩ := h.third_corner_preimage e he
  have hefit : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 2
  have heC : e C = corner 2 := e.apply_symm_apply _
  obtain ⟨hk, c, s, hunit, hs, hsc, hc, hsupportA, hsupportB, hform⟩ :=
    cornerFrame_of_placement (d.piece_subset 0) h.below_diagonal
      h.bottom_left h.bottom_right hC hCA hCB e hefit heC
  have hCmem : C ∈ d.piece 0 := hC
  have hkh : C 1 ≤ C 0 := h.below_diagonal hCmem
  have hx1 : C 0 ≤ 1 := (d.piece_subset 0 hCmem).1.2
  have hzero : c * (C 0 - C 1) + s * (C 0 + C 1) = 0 := by
    rcases hform with hform | hform
    · rw [hform (corner 0)] at hdiag
      norm_num [corner, Fin.ext_iff] at hdiag
      change 1 - c * C 0 - s * C 1 = 1 + s * C 0 - c * C 1 at hdiag
      nlinarith only [hdiag]
    · rw [hform (corner 0)] at hdiag
      norm_num [corner, Fin.ext_iff] at hdiag
      change 1 + s * C 0 - c * C 1 = 1 - c * C 0 - s * C 1 at hdiag
      nlinarith only [hdiag]
  have hfirst : 0 ≤ c * (C 0 - C 1) := mul_nonneg hc.le (sub_nonneg.mpr hkh)
  have hsum : 0 < C 0 + C 1 := by linarith
  have hsecond : 0 ≤ s * (C 0 + C 1) := mul_nonneg hs hsum.le
  have hfirstZero : c * (C 0 - C 1) = 0 := by linarith
  have hsecondZero : s * (C 0 + C 1) = 0 := by linarith
  have hxy : C 0 = C 1 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfirstZero).resolve_left hc.ne')
  have hsZero : s = 0 :=
    (mul_eq_zero.mp hsecondZero).resolve_right hsum.ne'
  have hxGe : 1 ≤ C 0 := by
    change c * (1 - C 0) ≤ s * C 1 at hsupportB
    rw [hsZero, zero_mul] at hsupportB
    have hnonpos : 1 - C 0 ≤ 0 := by
      exact le_of_mul_le_mul_left
        (show c * (1 - C 0) ≤ c * 0 by simpa only [mul_zero] using hsupportB) hc
    linarith
  have hx : C 0 = 1 := le_antisymm hx1 hxGe
  have hy : C 1 = 1 := hxy.symm.trans hx
  have hCtr : C = corner 2 := by
    apply PlaneIsometries.plane_ext <;> norm_num [corner, Fin.ext_iff, hx, hy]
  exact d.no_opposite_corners hprotected 0 0 ⟨h.bottom_left, hCtr ▸ hCmem⟩

end Puzzling139335.N5
