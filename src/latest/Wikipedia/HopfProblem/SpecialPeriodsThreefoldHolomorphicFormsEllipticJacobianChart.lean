import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticJacobianLift

/-!
# The full-source native elliptic root chart in the upper half-plane

Compose the actual root-domain inclusion, the original inverse normalized
elliptic chart, and the actual elliptic-neighborhood inclusion. This gives
an analytic partial diffeomorphism whose source is the whole root domain
and whose open target contains the elliptic center. Its genuine inverse
therefore transports holomorphic functions on the root neighborhood to
holomorphic germs on the original upper half-plane.
-/

noncomputable section

open Function Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover

open Elliptic

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- The original inverse elliptic chart on the whole chosen root domain,
as an actual partial biholomorphism into the original upper half-plane. -/
def baseParametrization (j : Kind) : PartialDiffeomorph I₁ I₁ (Root j) ℍ ω :=
  (opensInclusionPartialDiffeomorph I₁ (rootDomain j) ⟨rootZero j⟩).trans
    ((Triangle.ellipticNeighborhoodChart j).symm.toPartialDiffeomorph.trans
      (opensInclusionPartialDiffeomorph I₁ (Triangle.ellipticNeighborhood j)
        ⟨(Triangle.ellipticNeighborhoodChart j).symm SpecialPeriods.discZero⟩))

@[simp] theorem baseParametrization_source (j : Kind) :
    (baseParametrization j).source = Set.univ := by
  simp [baseParametrization, PartialDiffeomorph.trans,
    Diffeomorph.toPartialDiffeomorph, opensInclusionPartialDiffeomorph]

@[simp] theorem baseParametrization_apply (j : Kind) (z : Root j) :
    baseParametrization j z = baseLift j z := rfl

/-- The target is precisely the image of the entire actual root domain. -/
theorem baseParametrization_target (j : Kind) :
    (baseParametrization j).target = Set.range (baseLift j) := by
  ext y
  constructor
  · intro hy
    exact ⟨(baseParametrization j).symm y, (baseParametrization j).right_inv' hy⟩
  · rintro ⟨z, rfl⟩
    exact (baseParametrization j).map_source' (by simp only [baseParametrization_source, mem_univ])

theorem baseParametrization_target_isOpen (j : Kind) :
    IsOpen (baseParametrization j).target := (baseParametrization j).open_target

theorem ellipticCenter_mem_baseParametrization_target (j : Kind) :
    Triangle.ellipticCenter j ∈ (baseParametrization j).target := by
  rw [baseParametrization_target]
  exact ⟨rootZero j, baseLift_rootZero j⟩

theorem baseParametrization_target_mem_nhds_center (j : Kind) :
    (baseParametrization j).target ∈ 𝓝 (Triangle.ellipticCenter j) :=
  (baseParametrization j).open_target.mem_nhds
    (ellipticCenter_mem_baseParametrization_target j)

/-- The inverse is holomorphic throughout its actual open target. -/
theorem baseParametrization_symm_holomorphicOn (j : Kind) :
    ContMDiffOn I₁ I₁ ω (baseParametrization j).symm (baseParametrization j).target :=
  (baseParametrization j).contMDiffOn_invFun

theorem baseParametrization_symm_holomorphicAt (j : Kind) (y : ℍ)
    (hy : y ∈ (baseParametrization j).target) :
    ContMDiffAt I₁ I₁ ω (baseParametrization j).symm y :=
  (baseParametrization_symm_holomorphicOn j).contMDiffAt
    ((baseParametrization j).open_target.mem_nhds hy)

@[simp] theorem baseParametrization_symm_apply (j : Kind) (z : Root j) :
    (baseParametrization j).symm (baseLift j z) = z :=
  (baseParametrization j).left_inv' (by simp only [baseParametrization_source, mem_univ])

theorem baseLift_baseParametrization_symm (j : Kind) (y : ℍ)
    (hy : y ∈ (baseParametrization j).target) :
    baseLift j ((baseParametrization j).symm y) = y :=
  (baseParametrization j).right_inv' hy

@[simp] theorem baseParametrization_symm_center (j : Kind) :
    (baseParametrization j).symm (Triangle.ellipticCenter j) = rootZero j := by
  rw [← baseLift_rootZero j, baseParametrization_symm_apply]

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.EllipticCover
