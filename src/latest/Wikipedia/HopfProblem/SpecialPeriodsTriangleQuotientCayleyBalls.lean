import Wikipedia.HopfProblem.SpecialPeriodsTriangleLinearization
import Mathlib.Topology.Sets.Opens

/-!
# Round Cayley neighbourhoods for the triangle quotient

The inverse images of round discs under the actual Cayley coordinate
form a neighbourhood basis.  Every positive radius at most one gives a
normalized biholomorphism to the unit disc, and an actual determinant-one
matrix fixing the centre acts in this chart by its derivative multiplier.
-/

noncomputable section

open Set Topology TopologicalSpace UpperHalfPlane
open scoped ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- A round ball in the actual centred Cayley coordinate. -/
def cayleyBall (a : ℍ) (r : ℝ) : Opens ℍ :=
  ⟨{z | ‖cayleyCoordinate a z‖ < r},
    isOpen_lt (cayleyCoordinate_holomorphic a).continuous.norm continuous_const⟩

@[simp] theorem mem_cayleyBall (a z : ℍ) (r : ℝ) :
    z ∈ cayleyBall a r ↔ ‖cayleyCoordinate a z‖ < r := Iff.rfl

@[simp] theorem center_mem_cayleyBall (a : ℍ) (r : ℝ) :
    a ∈ cayleyBall a r ↔ 0 < r := by
  simp [cayleyBall, cayleyCoordinate]

theorem cayleyBall_mono (a : ℍ) {r s : ℝ} (hrs : r ≤ s) :
    cayleyBall a r ≤ cayleyBall a s := fun _ hz => lt_of_lt_of_le hz hrs

theorem cayleyBall_mem_nhds (a : ℍ) {r : ℝ} (hr : 0 < r) :
    (cayleyBall a r : Set ℍ) ∈ 𝓝 a :=
  (cayleyBall a r).isOpen.mem_nhds ((center_mem_cayleyBall a r).mpr hr)

@[simp] theorem cayleyBall_one (a : ℍ) : cayleyBall a 1 = ⊤ := by
  ext z
  change ‖cayleyCoordinate a z‖ < 1 ↔ True
  exact iff_true_intro (cayleyCoordinate_norm_lt_one a z)

/-- Normalized forward coordinate on a positive-radius Cayley ball. -/
def cayleyBallToDisc (a : ℍ) (r : ℝ) (hr : 0 < r) (z : cayleyBall a r) : Disc :=
  ⟨cayleyCoordinate a z / (r : ℂ), by
    have hn : ‖cayleyCoordinate a z / (r : ℂ)‖ < 1 := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (div_lt_one hr).mpr z.property
    simpa [unitDisc] using hn⟩

@[simp] theorem cayleyBallToDisc_val (a : ℍ) (r : ℝ) (hr : 0 < r)
    (z : cayleyBall a r) :
    (cayleyBallToDisc a r hr z : ℂ) = cayleyCoordinate a z / (r : ℂ) := rfl

/-- Dilation of the unit disc used by the inverse normalized chart. -/
def cayleyBallDiscScale (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (z : Disc) : Disc :=
  ⟨(r : ℂ) * z, by
    have hn : ‖(r : ℂ) * (z : ℂ)‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      exact (mul_lt_of_lt_one_right hr (disc_norm_lt_one z)).trans_le hr1
    simpa [unitDisc] using hn⟩

@[simp] theorem cayleyBallDiscScale_val (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (z : Disc) :
    (cayleyBallDiscScale r hr hr1 z : ℂ) = (r : ℂ) * z := rfl

theorem cayleyBallDiscScale_norm (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) (z : Disc) :
    ‖(cayleyBallDiscScale r hr hr1 z : ℂ)‖ < r := by
  rw [cayleyBallDiscScale_val, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  exact mul_lt_of_lt_one_right hr (disc_norm_lt_one z)

/-- The explicit inverse of the normalized Cayley coordinate. -/
def cayleyBallFromDisc (a : ℍ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : Disc) : cayleyBall a r :=
  ⟨fromDisc a (cayleyBallDiscScale r hr hr1 z), by
    change ‖(toDisc a (fromDisc a (cayleyBallDiscScale r hr hr1 z)) : ℂ)‖ < r
    rw [toDisc_fromDisc]
    exact cayleyBallDiscScale_norm r hr hr1 z⟩

@[simp] theorem cayleyBallFromDisc_val (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) (z : Disc) :
    (cayleyBallFromDisc a r hr hr1 z : ℍ) =
      fromDisc a (cayleyBallDiscScale r hr hr1 z) := rfl

@[simp] theorem cayleyBallFromDisc_coe (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) (z : Disc) :
    ((cayleyBallFromDisc a r hr hr1 z : ℍ) : ℂ) =
      cayley a ((r : ℂ) * z) := by
  rw [cayleyBallFromDisc_val, fromDisc_val, cayleyBallDiscScale_val]

theorem cayleyBallFromDisc_toDisc (a : ℍ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : cayleyBall a r) :
    cayleyBallFromDisc a r hr hr1 (cayleyBallToDisc a r hr z) = z := by
  apply Subtype.ext
  change fromDisc a (cayleyBallDiscScale r hr hr1 (cayleyBallToDisc a r hr z)) = z
  have he : cayleyBallDiscScale r hr hr1 (cayleyBallToDisc a r hr z) = toDisc a z := by
    apply Subtype.ext
    simp only [cayleyBallDiscScale_val, cayleyBallToDisc_val, toDisc_val]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')
  rw [he, fromDisc_toDisc]

theorem cayleyBallToDisc_fromDisc (a : ℍ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1)
    (z : Disc) :
    cayleyBallToDisc a r hr (cayleyBallFromDisc a r hr hr1 z) = z := by
  apply Subtype.ext
  change (toDisc a (fromDisc a (cayleyBallDiscScale r hr hr1 z)) : ℂ) / (r : ℂ) = z
  rw [toDisc_fromDisc, cayleyBallDiscScale_val]
  exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr hr.ne')

theorem cayleyBallToDisc_holomorphic (a : ℍ) (r : ℝ) (hr : 0 < r) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBallToDisc a r hr) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω
      (fun z : cayleyBall a r => cayleyCoordinate a z / (r : ℂ)) :=
    ((cayleyCoordinate_holomorphic a).comp contMDiff_subtype_val).div₀
      contMDiff_const (fun _ => Complex.ofReal_ne_zero.mpr hr.ne')
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp (hc z)

theorem cayleyBallDiscScale_holomorphic (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBallDiscScale r hr hr1) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : Disc => (r : ℂ) * z) :=
    contMDiff_const.mul contMDiff_subtype_val
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp (hc z)

theorem cayleyBallFromDisc_holomorphic (a : ℍ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (cayleyBallFromDisc a r hr hr1) := by
  have hc := (fromDisc_holomorphic a).comp (cayleyBallDiscScale_holomorphic r hr hr1)
  intro z
  exact (ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..).mp (hc z)

/-- Every round Cayley ball of radius in `(0, 1]` is biholomorphic to the
unit disc by the explicitly normalized Cayley coordinate. -/
def cayleyBallBiholomorph (a : ℍ) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    Diffeomorph 𝓘(ℂ) 𝓘(ℂ) (cayleyBall a r) Disc ω where
  toFun := cayleyBallToDisc a r hr
  invFun := cayleyBallFromDisc a r hr hr1
  left_inv := cayleyBallFromDisc_toDisc a r hr hr1
  right_inv := cayleyBallToDisc_fromDisc a r hr hr1
  contMDiff_toFun := cayleyBallToDisc_holomorphic a r hr
  contMDiff_invFun := cayleyBallFromDisc_holomorphic a r hr hr1

@[simp] theorem cayleyBallBiholomorph_val (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) (z : cayleyBall a r) :
    (cayleyBallBiholomorph a r hr hr1 z : ℂ) = cayleyCoordinate a z / (r : ℂ) := rfl

@[simp] theorem cayleyBallBiholomorph_symm_val (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) (z : Disc) :
    ((cayleyBallBiholomorph a r hr hr1).symm z : ℍ) =
      fromDisc a (cayleyBallDiscScale r hr hr1 z) := rfl

@[simp] theorem cayleyBallToDisc_center (a : ℍ) (r : ℝ) (hr : 0 < r) :
    cayleyBallToDisc a r hr ⟨a, (center_mem_cayleyBall a r).mpr hr⟩ = discZero := by
  apply Subtype.ext
  simp [cayleyBallToDisc_val, cayleyCoordinate]

@[simp] theorem cayleyBallBiholomorph_center (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) :
    cayleyBallBiholomorph a r hr hr1 ⟨a, (center_mem_cayleyBall a r).mpr hr⟩ = discZero :=
  cayleyBallToDisc_center a r hr

/-- The round Cayley balls of radius at most one form a neighbourhood
basis at the chosen centre. -/
theorem exists_cayleyBall_subset (a : ℍ) {U : Set ℍ} (hU : U ∈ 𝓝 a) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ (cayleyBall a r : Set ℍ) ⊆ U := by
  have hc : fromDisc a discZero = a := by
    apply UpperHalfPlane.ext
    simp [fromDisc_val]
  have hpre : fromDisc a ⁻¹' U ∈ 𝓝 discZero :=
    (fromDisc_holomorphic a).continuous.continuousAt.preimage_mem_nhds (by simpa [hc] using hU)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨min r 1, lt_min hr zero_lt_one, min_le_right _ _, ?_⟩
  intro z hz
  have hm : toDisc a z ∈ Metric.ball discZero r := by
    change dist (toDisc a z : ℂ) (discZero : ℂ) < r
    rw [toDisc_val, discZero_val, dist_zero_right]
    exact lt_of_lt_of_le hz (min_le_left _ _)
  simpa only [mem_preimage, fromDisc_toDisc] using hsub hm

/-- A matrix fixing the centre preserves every round Cayley ball. -/
theorem smul_mem_cayleyBall_iff (g : SL(2, ℝ)) (a z : ℍ) (r : ℝ)
    (hfix : g • a = a) :
    g • z ∈ cayleyBall a r ↔ z ∈ cayleyBall a r := by
  simp only [mem_cayleyBall, cayleyCoordinate_smul g a z hfix, norm_mul,
    slMultiplier_norm g a hfix, one_mul]

theorem mapsTo_cayleyBall (g : SL(2, ℝ)) (a : ℍ) (r : ℝ) (hfix : g • a = a) :
    MapsTo (fun z : ℍ => g • z) (cayleyBall a r) (cayleyBall a r) :=
  fun z hz => (smul_mem_cayleyBall_iff g a z r hfix).mpr hz

theorem image_cayleyBall (g : SL(2, ℝ)) (a : ℍ) (r : ℝ) (hfix : g • a = a) :
    (fun z : ℍ => g • z) '' (cayleyBall a r : Set ℍ) = cayleyBall a r := by
  apply Set.Subset.antisymm (mapsTo_cayleyBall g a r hfix).image_subset
  intro z hz
  refine ⟨g⁻¹ • z, ?_, smul_inv_smul g z⟩
  exact (smul_mem_cayleyBall_iff g a (g⁻¹ • z) r hfix).mp (by simpa using hz)

/-- The normalized coordinate has exactly the same derivative multiplier
as the unscaled Cayley coordinate. -/
theorem cayleyBallToDisc_smul (g : SL(2, ℝ)) (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hfix : g • a = a) (z : cayleyBall a r) :
    cayleyBallToDisc a r hr ⟨g • (z : ℍ), mapsTo_cayleyBall g a r hfix z.property⟩ =
      discScalar (slMultiplier g a) (slMultiplier_norm g a hfix)
        (cayleyBallToDisc a r hr z) := by
  apply Subtype.ext
  simp only [cayleyBallToDisc_val, discScalar_val, cayleyCoordinate_smul g a z hfix]
  exact mul_div_assoc _ _ _

/-- Equivariance as a statement about the actual biholomorphic chart. -/
theorem cayleyBallBiholomorph_smul (g : SL(2, ℝ)) (a : ℍ) (r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) (hfix : g • a = a) (z : cayleyBall a r) :
    cayleyBallBiholomorph a r hr hr1
        ⟨g • (z : ℍ), mapsTo_cayleyBall g a r hfix z.property⟩ =
      discScalar (slMultiplier g a) (slMultiplier_norm g a hfix)
        (cayleyBallBiholomorph a r hr hr1 z) :=
  cayleyBallToDisc_smul g a r hr hfix z

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
