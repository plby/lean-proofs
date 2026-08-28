import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsDerivativesCharts
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalSectionsDerivativesMultiplier
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPullbackLocal

/-!
# Intrinsic elliptic pullback of the ambient canonical volume

The source's multiplier is the determinant of the genuine manifold
derivative on the original varying-period torus family.  Consequently
it gives pullback of the actual full three-covector volume and of the
native holomorphic canonical-bundle section.  No assertion about the
canonical bundle of the central surface is substituted for this ambient
three-dimensional calculation.
-/

noncomputable section

open Set Topology
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.Elliptic.Equivariant.Data.Canonical

open SpecialPeriods TrianglePeriodFamily.Canonical

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₃" => modelWithCornersSelf ℂ Model

variable {j : Kind} (D : Equivariant.Data j)

local instance nativeFamilyChartedSpace : ChartedSpace Model D.TotalSpace :=
  D.periods.totalChartedSpace

local instance nativeFamilyManifold : IsManifold I₃ ω D.TotalSpace :=
  D.periods.totalSpace_isManifold

/-- The determinant in any two valid native quotient charts, evaluated
at an actual point of the varying-period family. -/
theorem permutationCoordinate_det_at (v : Lattice) (a b x : D.TotalSpace)
    (ha : x ∈ (familyChart D.periods a).source)
    (hb : D.permutation v x ∈ (familyChart D.periods b).source) :
    LinearMap.det
      (fderiv ℂ (permutationCoordinate D v a b) (familyChart D.periods a x)).toLinearMap =
        multiplier D x.1 := by
  have h := permutationCoordinate_det_fderiv D v a b
    ((familyChart D.periods a).map_source ha)
    (by simpa only [(familyChart D.periods a).left_inv ha] using hb)
  simpa only [matrixCoordinate, familyChart_inverse_base D.periods a x ha, multiplier]
    using h

/-- The actual manifold derivative has exactly the source's multiplier. -/
theorem permutation_mfderiv_det (v : Lattice) (x : D.TotalSpace) :
    LinearMap.det (mfderiv I₃ I₃ (D.permutation v) x).toLinearMap =
      multiplier D x.1 := by
  have hf : MDifferentiableAt I₃ I₃ (D.permutation v) x :=
    (D.permutation_holomorphic v).contMDiffAt.mdifferentiableAt (by simp)
  have h := Pullback.chartDeterminant_eq_jacobians (D.permutation v)
    (achart Model x) (achart Model (D.permutation v x))
    (mem_chart_source Model x) (mem_chart_source Model (D.permutation v x)) hf
  rw [Atlas.jacobian_self D.TotalSpace _ (mem_chart_source Model (D.permutation v x)),
    Atlas.jacobian_self D.TotalSpace _ (mem_chart_source Model x), one_mul, mul_one] at h
  exact h.symm.trans (permutationCoordinate_det_at D v x (D.permutation v x) x
    (mem_chart_source Model x) (mem_chart_source Model (D.permutation v x)))

/-- Intrinsic pullback of the full ambient three-covector volume. -/
theorem permutation_volume_pullback (v : Lattice) (x : D.TotalSpace) :
    volume.compContinuousLinearMap (mfderiv I₃ I₃ (D.permutation v) x) =
      multiplier D x.1 • volume := by
  exact (volume_pullback (mfderiv I₃ I₃ (D.permutation v) x)).trans
    (congrArg (fun c : ℂ => c • volume) (permutation_mfderiv_det D v x))

/-- The ambient canonical-bundle frame satisfies the same intrinsic
pullback identity in its original bundle topology and native atlas. -/
theorem permutation_canonicalVolume_pullback (v : Lattice) (x : D.TotalSpace) :
    Pullback.pullbackLinear (D.permutation v) x
      (familyCanonicalVolume D.periods (D.permutation v x)) =
        multiplier D x.1 • familyCanonicalVolume D.periods x := by
  change id (α := ℂ) (Pullback.pullbackLinear (D.permutation v) x
    (familyCanonicalVolume D.periods (D.permutation v x))) = multiplier D x.1 * 1
  rw [Pullback.pullbackLinear_preferred_coefficient, permutation_mfderiv_det D v x]
  rfl

/-- Multiplying the genuine volume by a base function gives the precise
formula `(F ∘ rotation) χ`, with no regularity assumption needed for this
pointwise pullback identity. -/
theorem permutation_weightedVolume_pullback (v : Lattice) (F : Disc → ℂ)
    (x : D.TotalSpace) :
    Pullback.pullbackLinear (D.permutation v) x
      (F (D.permutation v x).1 • familyCanonicalVolume D.periods (D.permutation v x)) =
        (F (familyRotation j x.1) * multiplier D x.1) •
          familyCanonicalVolume D.periods x := by
  rw [map_smul, permutation_canonicalVolume_pullback D v x, smul_smul]
  rfl

/-- The actual affine generator is a native biholomorphism whenever the
twist is invariant; no freeness hypothesis is necessary here. -/
def permutationBiholomorph (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    Diffeomorph I₃ I₃ D.TotalSpace D.TotalSpace ω :=
  D.actionBiholomorph v hv (CyclicAction.generator j.order)

@[simp] theorem permutationBiholomorph_apply (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (x : D.TotalSpace) :
    permutationBiholomorph D v hv x = D.permutation v x :=
  familyAction_generator_smul j v hv x

theorem permutation_isLocalDiffeomorph (v : Lattice) (hv : j.matrix *ᵥ v = v) :
    IsLocalDiffeomorph I₃ I₃ ω (D.permutation v) := by
  have he : (permutationBiholomorph D v hv : D.TotalSpace → D.TotalSpace) =
      D.permutation v := funext (permutationBiholomorph_apply D v hv)
  rw [← he]
  exact (permutationBiholomorph D v hv).isLocalDiffeomorph

/-- The same canonical-volume formula for the genuine fibrewise pullback
continuous linear equivalence. -/
theorem permutation_canonicalVolume_pullbackEquiv (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (x : D.TotalSpace) :
    Pullback.pullbackEquiv (permutation_isLocalDiffeomorph D v hv) x
      (familyCanonicalVolume D.periods (D.permutation v x)) =
        multiplier D x.1 • familyCanonicalVolume D.periods x :=
  permutation_canonicalVolume_pullback D v x

theorem permutation_weightedVolume_pullbackEquiv (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (F : Disc → ℂ) (x : D.TotalSpace) :
    Pullback.pullbackEquiv (permutation_isLocalDiffeomorph D v hv) x
      (F (D.permutation v x).1 • familyCanonicalVolume D.periods (D.permutation v x)) =
        (F (familyRotation j x.1) * multiplier D x.1) •
          familyCanonicalVolume D.periods x :=
  permutation_weightedVolume_pullback D v F x

end Wikipedia.HopfProblem.Elliptic.Equivariant.Data.Canonical
