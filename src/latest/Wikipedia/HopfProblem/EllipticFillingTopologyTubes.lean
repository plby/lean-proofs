import Wikipedia.HopfProblem.EllipticFillingTopologySurface
import Wikipedia.HopfProblem.EllipticFillingTopologyRestriction

/-!
# Radial retractions of open and closed elliptic tubes

The radial deformation multiplies the base coordinate by `(1−u)^m`.
Consequently it preserves every open or closed radius tube. Restricting the
actual deformation proves the elliptic assertion for the closed pieces
`N'_j` in Lemma 7.3(i), as well as for the open neighbourhoods.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.Elliptic

/-- The exact action of radial contraction on the ramified base coordinate. -/
theorem fillingRadial_projection_coe (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (u : unitInterval) (x : Filling j v hv) :
    (fillingProjection j v hv (fillingRadial j v hv u x) : ℂ) =
      (((1 - (u : ℝ) : ℝ) : ℂ) ^ j.order) * (fillingProjection j v hv x : ℂ) := by
  obtain ⟨y, rfl⟩ := fillingQuotient_surjective j v hv x
  rw [fillingRadial_fillingQuotient]
  change ((1 - (u : ℝ)) • (y.1 : ℂ)) ^ j.order =
    (((1 - (u : ℝ) : ℝ) : ℂ) ^ j.order) * (y.1 : ℂ) ^ j.order
  rw [Complex.real_smul, mul_pow]

theorem fillingRadial_projection_norm (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (u : unitInterval) (x : Filling j v hv) :
    ‖(fillingProjection j v hv (fillingRadial j v hv u x) : ℂ)‖ =
      (1 - (u : ℝ)) ^ j.order * ‖(fillingProjection j v hv x : ℂ)‖ := by
  rw [fillingRadial_projection_coe, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr u.property.2)]

theorem fillingRadial_projection_norm_le (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (u : unitInterval) (x : Filling j v hv) :
    ‖(fillingProjection j v hv (fillingRadial j v hv u x) : ℂ)‖ ≤
      ‖(fillingProjection j v hv x : ℂ)‖ := by
  rw [fillingRadial_projection_norm]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (sub_nonneg.mpr u.property.2) (by linarith [u.property.1]))

def fillingClosedTube (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (ρ : ℝ) :
    Set (Filling j v hv) := {x | ‖(fillingProjection j v hv x : ℂ)‖ ≤ ρ}

def fillingOpenTube (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v) (ρ : ℝ) :
    Set (Filling j v hv) := {x | ‖(fillingProjection j v hv x : ℂ)‖ < ρ}

theorem fillingClosedTube_isClosed (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (ρ : ℝ) : IsClosed (fillingClosedTube j v hv ρ) :=
  isClosed_le ((continuous_subtype_val.comp (fillingProjection_proper j v hv).continuous).norm)
    continuous_const

theorem fillingOpenTube_isOpen (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (ρ : ℝ) : IsOpen (fillingOpenTube j v hv ρ) :=
  isOpen_lt ((continuous_subtype_val.comp (fillingProjection_proper j v hv).continuous).norm)
    continuous_const

/-- Every closed tube with radius strictly below the ambient disc radius is
an actual compact subset of the filling. -/
theorem fillingClosedTube_isCompact (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) {ρ : ℝ} (hρ : ρ < 1) :
    IsCompact (fillingClosedTube j v hv ρ) := by
  have hbase : IsCompact {z : SpecialPeriods.Disc | ‖(z : ℂ)‖ ≤ ρ} := by
    have he : (Subtype.val : SpecialPeriods.Disc → ℂ) ''
        {z : SpecialPeriods.Disc | ‖(z : ℂ)‖ ≤ ρ} = Metric.closedBall (0 : ℂ) ρ := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        simpa only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right] using hw
      · intro hz
        have hz' : ‖z‖ ≤ ρ := by
          simpa only [Metric.mem_closedBall, dist_zero_right] using hz
        exact ⟨⟨z, by simpa [SpecialPeriods.unitDisc] using hz'.trans_lt hρ⟩, hz', rfl⟩
    apply (show IsEmbedding (Subtype.val : SpecialPeriods.Disc → ℂ) from
      IsEmbedding.subtypeVal).isCompact_iff.mpr
    rw [he]
    exact isCompact_closedBall (0 : ℂ) ρ
  exact (fillingProjection_proper j v hv).isCompact_preimage hbase

theorem fillingClosedTube_radial_stable (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (ρ : ℝ) (u : unitInterval) :
    MapsTo (fillingRadial j v hv u) (fillingClosedTube j v hv ρ)
      (fillingClosedTube j v hv ρ) :=
  fun x hx => (fillingRadial_projection_norm_le j v hv u x).trans hx

theorem fillingOpenTube_radial_stable (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) (ρ : ℝ) (u : unitInterval) :
    MapsTo (fillingRadial j v hv u) (fillingOpenTube j v hv ρ)
      (fillingOpenTube j v hv ρ) :=
  fun x hx => (fillingRadial_projection_norm_le j v hv u x).trans_lt hx

theorem surface_subset_fillingClosedTube (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    range (surfaceIntoFilling j v hv) ⊆ fillingClosedTube j v hv ρ := by
  rintro _ ⟨x, rfl⟩
  change ‖(fillingProjection j v hv (centralFibreInclusion j v hv x) : ℂ)‖ ≤ ρ
  simpa only [fillingProjection_centralFibreInclusion, discZero_coe, norm_zero] using hρ

theorem surface_subset_fillingOpenTube (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) {ρ : ℝ} (hρ : 0 < ρ) :
    range (surfaceIntoFilling j v hv) ⊆ fillingOpenTube j v hv ρ := by
  rintro _ ⟨x, rfl⟩
  change ‖(fillingProjection j v hv (centralFibreInclusion j v hv x) : ℂ)‖ < ρ
  simpa only [fillingProjection_centralFibreInclusion, discZero_coe, norm_zero] using hρ

/-- The actual central surface included in a closed radius tube. -/
def surfaceIntoClosedTube (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ContinuousMap (Surface j (centralPeriod j) v hv) (fillingClosedTube j v hv ρ) :=
  restrictedRetractionInclusion (surfaceIntoFilling j v hv) (fillingClosedTube j v hv ρ)
    (surface_subset_fillingClosedTube j v hv hρ)

/-- The actual central surface included in an open radius tube. -/
def surfaceIntoOpenTube (j : Kind) (v : Lattice) (hv : AdmissibleTwist j v)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ContinuousMap (Surface j (centralPeriod j) v hv) (fillingOpenTube j v hv ρ) :=
  restrictedRetractionInclusion (surfaceIntoFilling j v hv) (fillingOpenTube j v hv ρ)
    (surface_subset_fillingOpenTube j v hv hρ)

/-- The displayed strong deformation restricts to every closed tube,
fixing the central surface pointwise. -/
def closedTubeStrongDeformationRetraction (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (ContinuousMap.id (fillingClosedTube j v hv ρ)).HomotopyRel
      ((surfaceIntoClosedTube j v hv hρ).comp
        (restrictedRetraction (fillingSurfaceRetraction j v hv) (fillingClosedTube j v hv ρ)))
      (range (surfaceIntoClosedTube j v hv hρ)) :=
  restrictedRetractionHomotopy (surfaceIntoFilling j v hv) (fillingSurfaceRetraction j v hv)
    (fillingSurfaceStrongDeformationRetraction j v hv) (fillingClosedTube j v hv ρ)
    (surface_subset_fillingClosedTube j v hv hρ) (fillingClosedTube_radial_stable j v hv ρ)

/-- The same explicit strong deformation restricts to every positive open tube. -/
def openTubeStrongDeformationRetraction (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) {ρ : ℝ} (hρ : 0 < ρ) :
    (ContinuousMap.id (fillingOpenTube j v hv ρ)).HomotopyRel
      ((surfaceIntoOpenTube j v hv hρ).comp
        (restrictedRetraction (fillingSurfaceRetraction j v hv) (fillingOpenTube j v hv ρ)))
      (range (surfaceIntoOpenTube j v hv hρ)) :=
  restrictedRetractionHomotopy (surfaceIntoFilling j v hv) (fillingSurfaceRetraction j v hv)
    (fillingSurfaceStrongDeformationRetraction j v hv) (fillingOpenTube j v hv ρ)
    (surface_subset_fillingOpenTube j v hv hρ) (fillingOpenTube_radial_stable j v hv ρ)

def closedTubeSurfaceHomotopyEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    Surface j (centralPeriod j) v hv ≃ₕ fillingClosedTube j v hv ρ :=
  restrictedRetractionHomotopyEquiv (surfaceIntoFilling j v hv) (fillingSurfaceRetraction j v hv)
    (fillingSurfaceRetraction_comp_inclusion j v hv)
    (fillingSurfaceStrongDeformationRetraction j v hv)
    (fillingClosedTube j v hv ρ) (surface_subset_fillingClosedTube j v hv hρ)
    (fillingClosedTube_radial_stable j v hv ρ)

def openTubeSurfaceHomotopyEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) {ρ : ℝ} (hρ : 0 < ρ) :
    Surface j (centralPeriod j) v hv ≃ₕ fillingOpenTube j v hv ρ :=
  restrictedRetractionHomotopyEquiv (surfaceIntoFilling j v hv) (fillingSurfaceRetraction j v hv)
    (fillingSurfaceRetraction_comp_inclusion j v hv)
    (fillingSurfaceStrongDeformationRetraction j v hv)
    (fillingOpenTube j v hv ρ) (surface_subset_fillingOpenTube j v hv hρ)
    (fillingOpenTube_radial_stable j v hv ρ)

def closedTubeSurfaceFundamentalGroupEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (a : Surface j (centralPeriod j) v hv) :
    FundamentalGroup (Surface j (centralPeriod j) v hv) a ≃*
      FundamentalGroup (fillingClosedTube j v hv ρ) (surfaceIntoClosedTube j v hv hρ a) :=
  restrictedRetractionFundamentalGroupEquiv (surfaceIntoFilling j v hv)
    (fillingSurfaceRetraction j v hv) (fillingSurfaceRetraction_comp_inclusion j v hv)
    (fillingSurfaceStrongDeformationRetraction j v hv) (fillingClosedTube j v hv ρ)
    (surface_subset_fillingClosedTube j v hv hρ) (fillingClosedTube_radial_stable j v hv ρ) a

def openTubeSurfaceFundamentalGroupEquiv (j : Kind) (v : Lattice)
    (hv : AdmissibleTwist j v) {ρ : ℝ} (hρ : 0 < ρ)
    (a : Surface j (centralPeriod j) v hv) :
    FundamentalGroup (Surface j (centralPeriod j) v hv) a ≃*
      FundamentalGroup (fillingOpenTube j v hv ρ) (surfaceIntoOpenTube j v hv hρ a) :=
  restrictedRetractionFundamentalGroupEquiv (surfaceIntoFilling j v hv)
    (fillingSurfaceRetraction j v hv) (fillingSurfaceRetraction_comp_inclusion j v hv)
    (fillingSurfaceStrongDeformationRetraction j v hv) (fillingOpenTube j v hv ρ)
    (surface_subset_fillingOpenTube j v hv hρ) (fillingOpenTube_radial_stable j v hv ρ) a

end Wikipedia.HopfProblem.Elliptic
