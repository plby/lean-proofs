import Wikipedia.HopfProblem.TriangleCornerCoordinates
import Wikipedia.HopfProblem.TriangleCornerRootSectors

/-!
# Upper-half-plane parameters at the two actual triangle corners

The cubic principal root, and the fourth root rotated by `-π / 4`, are
composed with the concrete centered Cayley inverses.  The resulting maps
are holomorphic on the upper side, continuous on its closure, take the
upper side into the half-Ford triangle, and take the real side outside its
interior.  Their exact cubic and quartic power coordinates are proved.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

open RiemannBoundary

def cornerParameterThree (w : ℂ) : ℂ := cayley centerOne (principalRoot 3 w)

def cornerParameterFour (w : ℂ) : ℂ := cayley centerTwo (rotatedPrincipalRootFour w)

@[simp] theorem cornerParameterThree_zero : cornerParameterThree 0 = centerOne := by
  simp [cornerParameterThree, principalRoot_zero (by norm_num : 0 < 3)]

@[simp] theorem cornerParameterFour_zero : cornerParameterFour 0 = centerTwo := by
  simp [cornerParameterFour]

theorem continuousAt_cornerParameterThree_zero : ContinuousAt cornerParameterThree 0 := by
  have hc : ContinuousAt (cayley (centerOne : ℂ)) 0 :=
    (cayley_analyticAt centerOne (by simp)).continuousAt
  have h0 : principalRoot 3 (0 : ℂ) = 0 := principalRoot_zero (by norm_num)
  exact (h0 ▸ hc).comp (continuousAt_principalRoot_zero (by norm_num : 0 < 3))

theorem continuousAt_cornerParameterFour_zero : ContinuousAt cornerParameterFour 0 := by
  have hc : ContinuousAt (cayley (centerTwo : ℂ)) 0 :=
    (cayley_analyticAt centerTwo (by simp)).continuousAt
  exact (rotatedPrincipalRootFour_zero ▸ hc).comp
    continuousAt_rotatedPrincipalRootFour_zero

theorem cornerParameterThree_im_pos {w : ℂ} (hw : ‖principalRoot 3 w‖ < 1) :
    0 < (cornerParameterThree w).im := cayley_im_pos centerOne.im_pos hw

theorem cornerParameterFour_im_pos {w : ℂ} (hw : ‖rotatedPrincipalRootFour w‖ < 1) :
    0 < (cornerParameterFour w).im := cayley_im_pos centerTwo.im_pos hw

theorem cayley_coordinate_inverse (a : UpperHalfPlane) {z : ℂ} (hz : ‖z‖ < 1) :
    (cayley a z - a) / (cayley a z - conj (a : ℂ)) = z := by
  have he := congrArg Subtype.val (toDisc_fromDisc a ⟨z, by simpa [unitDisc] using hz⟩)
  simpa only [toDisc_val, cayleyCoordinate, fromDisc_val] using he

/-- The cubic corner coordinate has exactly the original upper-half-plane
parameter as its cube. -/
theorem cornerParameterThree_power {w : ℂ} (hw : ‖principalRoot 3 w‖ < 1) :
    ((cornerParameterThree w - centerOne) /
      (cornerParameterThree w - conj (centerOne : ℂ))) ^ 3 = w := by
  rw [cornerParameterThree, cayley_coordinate_inverse centerOne hw,
    principalRoot_pow (by norm_num : 0 < 3)]

/-- The quartic corner coordinate has fourth power equal to the negative
of the upper-half-plane parameter, as required by its rotation. -/
theorem cornerParameterFour_power {w : ℂ} (hw : ‖rotatedPrincipalRootFour w‖ < 1) :
    ((cornerParameterFour w - centerTwo) /
      (cornerParameterFour w - conj (centerTwo : ℂ))) ^ 4 = -w := by
  rw [cornerParameterFour, cayley_coordinate_inverse centerTwo hw,
    rotatedPrincipalRootFour_pow]

private theorem exists_small_root_ball {f : ℂ → ℂ}
    (hf : ContinuousAt f 0) (hf0 : f 0 = 0) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ ball (0 : ℂ) δ, ‖f w‖ < r := by
  have hn : ∀ᶠ w in 𝓝 (0 : ℂ), ‖f w‖ < r :=
    hf.norm.eventually_lt continuousAt_const (by simpa only [hf0, norm_zero] using hr)
  exact Metric.mem_nhds_iff.mp hn

theorem cornerParameterThree_analyticOnNhd {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖principalRoot 3 w‖ < 1) :
    AnalyticOnNhd ℂ cornerParameterThree (U ∩ {w : ℂ | 0 < w.im}) := by
  intro w hw
  exact (cayley_analyticAt centerOne
    (one_sub_ne_zero_of_norm_lt_one (hU w hw.1))).comp
      (analyticOnNhd_principalRoot_upper 3 w hw.2)

theorem cornerParameterFour_analyticOnNhd {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖rotatedPrincipalRootFour w‖ < 1) :
    AnalyticOnNhd ℂ cornerParameterFour (U ∩ {w : ℂ | 0 < w.im}) := by
  intro w hw
  exact (cayley_analyticAt centerTwo
    (one_sub_ne_zero_of_norm_lt_one (hU w hw.1))).comp
      (analyticOnNhd_rotatedPrincipalRootFour_upper w hw.2)

theorem cornerParameterThree_continuousOn {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖principalRoot 3 w‖ < 1) :
    ContinuousOn cornerParameterThree (U ∩ {w : ℂ | 0 ≤ w.im}) := by
  have hc := (cayley_contDiffOn (centerOne : ℂ)).continuousOn
  exact hc.comp
    ((continuousOn_principalRoot_closedUpper (by norm_num : 0 < 3)).mono
      (fun _ h => h.2))
    (fun w hw => by simpa using hU w hw.1)

theorem cornerParameterFour_continuousOn {U : Set ℂ}
    (hU : ∀ w ∈ U, ‖rotatedPrincipalRootFour w‖ < 1) :
    ContinuousOn cornerParameterFour (U ∩ {w : ℂ | 0 ≤ w.im}) := by
  have hc := (cayley_contDiffOn (centerTwo : ℂ)).continuousOn
  exact hc.comp
    (continuousOn_rotatedPrincipalRootFour_closedUpper.mono (fun _ h => h.2))
    (fun w hw => by simpa using hU w hw.1)

/-- A genuine closed-upper-half parameter neighborhood of the first
elliptic corner, with every geometric condition proved for the actual
half-Ford triangle. -/
theorem exists_cornerParameterThree_neighborhood :
    ∃ δ : ℝ, 0 < δ ∧
      AnalyticOnNhd ℂ cornerParameterThree
        (ball 0 δ ∩ {w : ℂ | 0 < w.im}) ∧
      ContinuousOn cornerParameterThree
        (ball 0 δ ∩ {w : ℂ | 0 ≤ w.im}) ∧
      MapsTo cornerParameterThree (ball 0 δ ∩ {w : ℂ | 0 < w.im}) triangleInterior ∧
      (∀ t : ℝ, (t : ℂ) ∈ ball 0 δ → cornerParameterThree (t : ℂ) ∉ triangleInterior) ∧
      (∀ w ∈ ball 0 δ, 0 < (cornerParameterThree w).im) ∧
      (∀ w ∈ ball 0 δ,
        ((cornerParameterThree w - centerOne) /
          (cornerParameterThree w - conj (centerOne : ℂ))) ^ 3 = w) := by
  obtain ⟨r, hr, hr1, hsector⟩ := exists_cornerThree_radius
  obtain ⟨δ, hδ, hδr⟩ := exists_small_root_ball
    (continuousAt_principalRoot_zero (by norm_num : 0 < 3))
    (principalRoot_zero (by norm_num : 0 < 3)) hr
  have hδ1 : ∀ w ∈ ball (0 : ℂ) δ, ‖principalRoot 3 w‖ < 1 :=
    fun w hw => (hδr w hw).trans_le hr1
  refine ⟨δ, hδ, cornerParameterThree_analyticOnNhd hδ1,
    cornerParameterThree_continuousOn hδ1, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact (hsector _ (hδr w hw.1)).mpr (principalRoot_three_upper hw.2)
  · intro t ht hmem
    have hs := (hsector _ (hδr (t : ℂ) ht)).mp hmem
    rcases principalRoot_three_real_boundary (ofReal_im t) with h | h
    · exact hs.1.ne' h
    · exact hs.2.ne h
  · exact fun w hw => cornerParameterThree_im_pos (hδ1 w hw)
  · exact fun w hw => cornerParameterThree_power (hδ1 w hw)

/-- The corresponding genuine upper-half parameter at the order-four
vertex.  Its fourth-power relation records the negative sign. -/
theorem exists_cornerParameterFour_neighborhood :
    ∃ δ : ℝ, 0 < δ ∧
      AnalyticOnNhd ℂ cornerParameterFour
        (ball 0 δ ∩ {w : ℂ | 0 < w.im}) ∧
      ContinuousOn cornerParameterFour
        (ball 0 δ ∩ {w : ℂ | 0 ≤ w.im}) ∧
      MapsTo cornerParameterFour (ball 0 δ ∩ {w : ℂ | 0 < w.im}) triangleInterior ∧
      (∀ t : ℝ, (t : ℂ) ∈ ball 0 δ → cornerParameterFour (t : ℂ) ∉ triangleInterior) ∧
      (∀ w ∈ ball 0 δ, 0 < (cornerParameterFour w).im) ∧
      (∀ w ∈ ball 0 δ,
        ((cornerParameterFour w - centerTwo) /
          (cornerParameterFour w - conj (centerTwo : ℂ))) ^ 4 = -w) := by
  obtain ⟨r, hr, hr1, hsector⟩ := exists_cornerFour_radius
  obtain ⟨δ, hδ, hδr⟩ := exists_small_root_ball
    continuousAt_rotatedPrincipalRootFour_zero rotatedPrincipalRootFour_zero hr
  have hδ1 : ∀ w ∈ ball (0 : ℂ) δ, ‖rotatedPrincipalRootFour w‖ < 1 :=
    fun w hw => (hδr w hw).trans_le hr1
  refine ⟨δ, hδ, cornerParameterFour_analyticOnNhd hδ1,
    cornerParameterFour_continuousOn hδ1, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact (hsector _ (hδr w hw.1)).mpr (rotatedPrincipalRootFour_upper hw.2)
  · intro t ht hmem
    have hs := (hsector _ (hδr (t : ℂ) ht)).mp hmem
    rcases rotatedPrincipalRootFour_real_boundary (ofReal_im t) with h | h
    · exact hs.1.ne h
    · exact hs.2.ne' h
  · exact fun w hw => cornerParameterFour_im_pos (hδ1 w hw)
  · exact fun w hw => cornerParameterFour_power (hδ1 w hw)

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
