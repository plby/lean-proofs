import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorSeeds
import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorCover

/-!
# Actual overlap functions of the constructed beta sections

The local sections are the equivariant extensions of zero on regular sheets,
the explicit elliptic finite averages, and minus tau at the cusp.  Their
differences are invariant because the constructed all-word cocycle is
additive.  Actual holomorphic descent through the full quotient and its
finite coordinate then constructs the overlap functions used by Cousin
gluing.  No local beta sections or overlap cocycles are input data.
-/

noncomputable section

open Set Topology UpperHalfPlane TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor.Data

open MuTorsor

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

variable (D : Data)

/-- The difference of the two genuinely constructed local functions. -/
def overlapDifference (i j : Cover.Index) (z : ℍ) : ℂ :=
  D.localSection i z - D.localSection j z

theorem overlapDifference_invariant (i j : Cover.Index) (g : TriangleGroup)
    (z : ℍ) (hz : z ∈ overlapDomain i j) :
    D.overlapDifference i j (triangleGeometricRepresentation g z) =
      D.overlapDifference i j z := by
  dsimp only [overlapDifference]
  rw [D.localSection_additive i g z hz.1, D.localSection_additive j g z hz.2]
  ring

theorem overlapDifference_holomorphic (i j : Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.overlapDifference i j) (overlapDomain i j) :=
  ((D.localSection_holomorphic i).mono (fun _ hz => hz.1)).sub
    ((D.localSection_holomorphic j).mono (fun _ hz => hz.2))

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

/-- The actual holomorphic overlap function on the finite base. -/
def overlapCocycle (i j : Cover.Index) : ℂ → ℂ :=
  finiteDescent π hπ (overlapDomain i j) (D.overlapDifference i j)

theorem overlapCocycle_analytic (i j : Cover.Index) :
    AnalyticOnNhd ℂ (D.overlapCocycle π hπ i j)
      ((Cover.finitePatch π i : Set ℂ) ∩ Cover.finitePatch π j) := by
  have h := finiteDescent_analytic π hπ (overlapDomain i j) (D.overlapDifference i j)
    (overlapDomain_invariant i j) (D.overlapDifference_invariant i j)
    (D.overlapDifference_holomorphic i j)
  rw [finiteDescentDomain_overlap] at h
  exact h

theorem localSection_difference (i j : Cover.Index) (z : ℍ)
    (hi : finiteProjection π z ∈ Cover.finitePatch π i)
    (hj : finiteProjection π z ∈ Cover.finitePatch π j) :
    D.localSection i z - D.localSection j z =
      D.overlapCocycle π hπ i j (finiteProjection π z) :=
  (finiteDescent_projection π hπ (overlapDomain i j) (D.overlapDifference i j)
    (overlapDomain_invariant i j) (D.overlapDifference_invariant i j)
    ⟨(finiteProjection_mem_patch π hπ i z).mp hi,
      (finiteProjection_mem_patch π hπ j z).mp hj⟩).symm

include hπ in
theorem localSection_holomorphic_finite (i : Cover.Index) :
    ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω (D.localSection i)
      (finiteProjection π ⁻¹' (Cover.finitePatch π i : Set ℂ)) := by
  rw [finiteProjection_preimage_patch π hπ]
  exact D.localSection_holomorphic i

include hπ in
theorem localSection_additive_finite (i : Cover.Index) (g : TriangleGroup) (z : ℍ)
    (hz : finiteProjection π z ∈ Cover.finitePatch π i) :
    D.localSection i (triangleGeometricRepresentation g z) =
      D.localSection i z + D.shift g z :=
  D.localSection_additive i g z ((finiteProjection_mem_patch π hπ i z).mp hz)

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor.Data
