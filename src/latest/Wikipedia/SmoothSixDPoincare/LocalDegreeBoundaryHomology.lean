import Wikipedia.SmoothSixDPoincare.LocalDegreeBoundaryData
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The original small-boundary map has the derivative's actual homology map

The zero-avoiding homotopy identifies the original nonlinear boundary map
with the actual invertible derivative. In particular it induces a homology
isomorphism; this does not yet assign its orientation sign.
-/

noncomputable section

open Set Metric Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.LocalDegree

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def puncturedLinearHomeomorph (L : E ≃L[ℝ] F) :
    PuncturedRadial.Space E ≃ₜ PuncturedRadial.Space F :=
  L.toHomeomorph.subtype (fun x => by
    change x ≠ 0 ↔ L x ≠ 0
    constructor
    · intro hx h
      exact hx (L.injective (h.trans (map_zero L).symm))
    · intro hx h
      exact hx (h ▸ map_zero L))

def linearSphereEquiv (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    sphere (0 : E) 1 ≃ₕ PuncturedRadial.Space F :=
  (PuncturedRadial.sphereHomotopyEquiv r hr).trans
    (puncturedLinearHomeomorph L).toHomotopyEquiv

theorem linearSphereEquiv_toFun (L : E ≃L[ℝ] F) (r : ℝ) (hr : 0 < r) :
    (linearSphereEquiv L r hr).toFun = linearSphereMap L r hr := rfl

namespace BoundaryData

variable {f : E → F} {L : E ≃L[ℝ] F} {s : Set E} (b : BoundaryData f L s)

/-- Equality of actual induced maps, before choosing any top-homology generators. -/
theorem homology_compare (k : ℕ) :
    singularHomologyMap b.map k = singularHomologyMap (linearSphereMap L b.radius b.radius_pos) k :=
  (homotopy_homologyMap b.homotopy k).symm

def homologyEquiv (k : ℕ) :
    SingularHomology (sphere (0 : E) 1) k ≃ₗ[ℤ]
      SingularHomology (PuncturedRadial.Space F) k :=
  LinearEquiv.ofBijective (singularHomologyMap b.map k) (by
    rw [b.homology_compare]
    exact (homotopyEquivHomologyEquiv (linearSphereEquiv L b.radius b.radius_pos) k).bijective)

theorem homologyEquiv_apply (k : ℕ) (a : SingularHomology (sphere (0 : E) 1) k) :
    b.homologyEquiv k a = singularHomologyMap b.map k a := rfl

def normalizedMap : C(sphere (0 : E) 1, sphere (0 : F) 1) :=
  PuncturedRadial.toSphere.comp b.map

def normalizedHomologyEquiv (k : ℕ) :
    SingularHomology (sphere (0 : E) 1) k ≃ₗ[ℤ] SingularHomology (sphere (0 : F) 1) k :=
  (b.homologyEquiv k).trans
    (homotopyEquivHomologyEquiv (PuncturedRadial.sphereHomotopyEquiv 1 (by norm_num)).symm k)

theorem normalizedHomologyEquiv_apply (k : ℕ)
    (a : SingularHomology (sphere (0 : E) 1) k) :
    b.normalizedHomologyEquiv k a = singularHomologyMap b.normalizedMap k a := by
  change singularHomologyMap PuncturedRadial.toSphere k (singularHomologyMap b.map k a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

end BoundaryData

end Wikipedia.SmoothSixDPoincare.LocalDegree
