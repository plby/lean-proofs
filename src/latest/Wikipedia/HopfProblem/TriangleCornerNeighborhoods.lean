import Wikipedia.HopfProblem.TriangleCornerParameters
import Wikipedia.HopfProblem.TriangleCornerSectorsTopology

/-!
# Complex-plane neighborhoods of the actual elliptic corners

The centered coordinates here are the literal rational Cayley maps.  They
agree with the already established upper-half-plane biholomorphisms and
are analytic at the actual corners.  This supplies genuine ambient
neighborhoods, not only points selected along a parameterized approach.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

def cornerCoordinate (a : UpperHalfPlane) (z : ℂ) : ℂ :=
  (z - a) / (z - conj (a : ℂ))

@[simp] theorem cornerCoordinate_self (a : UpperHalfPlane) :
    cornerCoordinate a a = 0 := by simp [cornerCoordinate]

@[simp] theorem cornerCoordinate_coe (a z : UpperHalfPlane) :
    cornerCoordinate a z = cayleyCoordinate a z := rfl

theorem cornerCoordinate_analyticAt (a : UpperHalfPlane) {z : ℂ}
    (hz : z - conj (a : ℂ) ≠ 0) : AnalyticAt ℂ (cornerCoordinate a) z :=
  (analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const) hz

theorem cornerCoordinate_analyticAt_self (a : UpperHalfPlane) :
    AnalyticAt ℂ (cornerCoordinate a) (a : ℂ) :=
  cornerCoordinate_analyticAt a (sub_conj_ne_zero a a)

theorem cornerCoordinate_norm_lt_one (a : UpperHalfPlane) {z : ℂ} (hz : 0 < z.im) :
    ‖cornerCoordinate a z‖ < 1 :=
  cayleyCoordinate_norm_lt_one a ⟨z, hz⟩

theorem cayley_cornerCoordinate (a : UpperHalfPlane) {z : ℂ} (hz : 0 < z.im) :
    cayley a (cornerCoordinate a z) = z := by
  have he := congrArg (fun w : UpperHalfPlane => (w : ℂ)) (fromDisc_toDisc a ⟨z, hz⟩)
  simpa only [fromDisc_val, toDisc_val, cornerCoordinate, cayleyCoordinate] using he

theorem cornerCoordinate_cayley (a : UpperHalfPlane) {z : ℂ} (hz : ‖z‖ < 1) :
    cornerCoordinate a (cayley a z) = z := cayley_coordinate_inverse a hz

/-- The exact power coordinate on the order-three corner. -/
def cornerPowerThree (z : ℂ) : ℂ := cornerCoordinate centerOne z ^ 3

/-- The oriented power coordinate on the order-four corner. -/
def cornerPowerFour (z : ℂ) : ℂ := -(cornerCoordinate centerTwo z ^ 4)

@[simp] theorem cornerPowerThree_center : cornerPowerThree centerOne = 0 := by
  simp only [cornerPowerThree, cornerCoordinate_self, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true]

@[simp] theorem cornerPowerFour_center : cornerPowerFour centerTwo = 0 := by
  simp only [cornerPowerFour, cornerCoordinate_self, zero_pow, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, neg_zero]

theorem cornerPowerThree_analyticAt_center :
    AnalyticAt ℂ cornerPowerThree (centerOne : ℂ) :=
  (cornerCoordinate_analyticAt_self centerOne).pow 3

theorem cornerPowerFour_analyticAt_center :
    AnalyticAt ℂ cornerPowerFour (centerTwo : ℂ) :=
  ((cornerCoordinate_analyticAt_self centerTwo).pow 4).neg

theorem exists_cornerCoordinate_neighborhood (a : UpperHalfPlane)
    {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ ball (a : ℂ) ε,
      0 < z.im ∧ ‖cornerCoordinate a z‖ < r := by
  have him : ∀ᶠ z : ℂ in 𝓝 (a : ℂ), 0 < z.im :=
    continuousAt_const.eventually_lt continuous_im.continuousAt a.im_pos
  have hnorm : ∀ᶠ z : ℂ in 𝓝 (a : ℂ), ‖cornerCoordinate a z‖ < r :=
    (cornerCoordinate_analyticAt_self a).continuousAt.norm.eventually_lt
      continuousAt_const (by simpa only [cornerCoordinate_self, norm_zero] using hr)
  exact Metric.mem_nhds_iff.mp (him.and hnorm)

/-- The direct centered coordinate identifies a complete ambient
neighborhood of the first vertex with its actual linear corner sector. -/
theorem exists_cornerThree_neighborhood :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ ball (centerOne : ℂ) ε,
      0 < z.im ∧
      (z ∈ triangleInterior ↔ cornerCoordinate centerOne z ∈ cornerSectorThree) := by
  obtain ⟨r, hr, _, hsector⟩ := exists_cornerThree_radius
  obtain ⟨ε, hε, hball⟩ := exists_cornerCoordinate_neighborhood centerOne hr
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have h := hball z hz
  refine ⟨h.1, ?_⟩
  have he := hsector _ h.2
  rwa [cayley_cornerCoordinate centerOne h.1] at he

/-- The analogous complete neighborhood at the second vertex. -/
theorem exists_cornerFour_neighborhood :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ ball (centerTwo : ℂ) ε,
      0 < z.im ∧
      (z ∈ triangleInterior ↔ cornerCoordinate centerTwo z ∈ cornerSectorFour) := by
  obtain ⟨r, hr, _, hsector⟩ := exists_cornerFour_radius
  obtain ⟨ε, hε, hball⟩ := exists_cornerCoordinate_neighborhood centerTwo hr
  refine ⟨ε, hε, ?_⟩
  intro z hz
  have h := hball z hz
  refine ⟨h.1, ?_⟩
  have he := hsector _ h.2
  rwa [cayley_cornerCoordinate centerTwo h.1] at he

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
