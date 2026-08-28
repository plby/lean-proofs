import Wikipedia.HopfProblem.EllipticHigherHomologySurfaceMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductNaturality

/-!
# The actual adjacent-degree splitting of the elliptic period torus

The proved period-coordinate homeomorphism, followed by the actual signed
circle-product splitting, identifies positive-degree period-torus homology
with the two adjacent homology groups of the three-dimensional fibre torus.
The first summand is the actual fibre inclusion at circle coordinate zero.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology CircleTopology

/-- The original affine generator, viewed as its actual homeomorphism. -/
def periodAffineHomeomorph (j : Kind) (p : FixedPeriod j) :
    p.val.Torus ≃ₜ p.val.Torus :=
  (affineBiholomorph j p j.twist).toHomeomorph

@[simp] theorem periodAffineHomeomorph_apply (j : Kind) (p : FixedPeriod j)
    (x : p.val.Torus) :
    periodAffineHomeomorph j p x = affineBiholomorph j p j.twist x := rfl

@[simp] theorem periodAffineHomeomorph_symm_apply (j : Kind) (p : FixedPeriod j)
    (x : p.val.Torus) :
    (periodAffineHomeomorph j p).symm x = (affineBiholomorph j p j.twist).symm x := rfl

/-- The actual circle-factor splitting in every positive homological degree. -/
def periodCircleHomologyEquiv (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    SingularHomology p.val.Torus (n + 1) ≃ₗ[ℤ]
      (SingularHomology (ProductTorus 3) (n + 1) × SingularHomology (ProductTorus 3) n) :=
  (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1)).trans
    (circleProductHomologyEquiv (ProductTorus 3) n)

/-- The two coordinates are actual fibre projection and the signed circle connecting map. -/
@[simp] theorem periodCircleHomologyEquiv_apply (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology p.val.Torus (n + 1)) :
    periodCircleHomologyEquiv j p n a =
      (circleProjectionHomology (ProductTorus 3) (n + 1)
          (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1) a),
        circleBoundary (ProductTorus 3) n
          (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1) a)) := rfl

/-- In particular, the second coordinate retains the proved lower-component minus sign. -/
theorem periodCircleHomologyEquiv_apply_boundaryCoordinates (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology p.val.Torus (n + 1)) :
    periodCircleHomologyEquiv j p n a =
      (circleProjectionHomology (ProductTorus 3) (n + 1)
          (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1) a),
        -(circleBoundaryCoordinates (ProductTorus 3) n
          (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1) a)).1) := rfl

@[simp] theorem periodCircleHomologyEquiv_symm_apply (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology (ProductTorus 3) (n + 1) ×
      SingularHomology (ProductTorus 3) n) :
    (periodCircleHomologyEquiv j p n).symm a =
      (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1)).symm
        ((circleProductHomologyEquiv (ProductTorus 3) n).symm a) := rfl

/-- The original primitive fibre inclusion becomes the literal zero section. -/
theorem splitPeriodTorusHomeomorph_comp_fibreIntoPeriodTorus (j : Kind) (p : FixedPeriod j) :
    (splitPeriodTorusHomeomorph j p.val : C(p.val.Torus, Circle × ProductTorus 3)).comp
        (fibreIntoPeriodTorus j p) = productSection (ProductTorus 3) := by
  apply ContinuousMap.ext
  intro x
  change splitPeriodTorusHomeomorph j p.val
    ((splitPeriodTorusHomeomorph j p.val).symm (0, x)) = (0, x)
  exact (splitPeriodTorusHomeomorph j p.val).apply_symm_apply (0, x)

/-- The actual fibre map commutes with the homology splitting before taking adjacent degrees. -/
theorem splitPeriodTorusHomology_fibre_map (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n).toLinearMap.comp
        (singularHomologyMap (fibreIntoPeriodTorus j p) n) =
      circleSectionHomology (ProductTorus 3) n := by
  rw [homeomorphHomologyEquiv_toLinearMap, ← singularHomologyMap_comp,
    splitPeriodTorusHomeomorph_comp_fibreIntoPeriodTorus]

theorem splitPeriodTorusHomology_fibre (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology (ProductTorus 3) n) :
    homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n
        (singularHomologyMap (fibreIntoPeriodTorus j p) n a) =
      circleSectionHomology (ProductTorus 3) n a :=
  DFunLike.congr_fun (splitPeriodTorusHomology_fibre_map j p n) a

/-- Every actual fibre class occupies exactly the first summand. -/
@[simp] theorem periodCircleHomologyEquiv_fibre (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology (ProductTorus 3) (n + 1)) :
    periodCircleHomologyEquiv j p n
        (singularHomologyMap (fibreIntoPeriodTorus j p) (n + 1) a) = (a, 0) := by
  change circleProductHomologyEquiv (ProductTorus 3) n
    (homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) (n + 1)
      (singularHomologyMap (fibreIntoPeriodTorus j p) (n + 1) a)) = _
  rw [splitPeriodTorusHomology_fibre, circleProductHomologyEquiv_section]

@[simp] theorem periodCircleHomologyEquiv_symm_inl (j : Kind) (p : FixedPeriod j)
    (n : ℕ) (a : SingularHomology (ProductTorus 3) (n + 1)) :
    (periodCircleHomologyEquiv j p n).symm (a, 0) =
      singularHomologyMap (fibreIntoPeriodTorus j p) (n + 1) a := by
  apply (periodCircleHomologyEquiv j p n).injective
  rw [LinearEquiv.apply_symm_apply, periodCircleHomologyEquiv_fibre]

end Wikipedia.HopfProblem.Elliptic.HigherHomology
