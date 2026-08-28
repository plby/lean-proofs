import Wikipedia.HopfProblem.SphereHomology
import Wikipedia.HopfProblem.SixSphereComplexTransport

/-!
# Homology and cohomology of the original standard six-sphere

The space here is the literal unit sphere in real Euclidean seven-space,
the same standard sphere used by the complex-atlas transport statement.
Its homology is computed from the actual latitude homeomorphisms and
singular Mayer--Vietoris sequence, and its cohomology from the native
evaluation pairing. None of these results identifies the constructed
threefold with that sphere or assumes a recognition theorem.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SixSphereHomology

open SingularMayerVietoris SingularCohomologyFree SphereHomology

/-- Actual degree-zero integral singular homology of the standard six-sphere. -/
def homologyZeroEquiv : SingularHomology SixSphere 0 ≃ₗ[ℤ] ℤ :=
  unitSphereHomologyZeroEquiv 5

/-- Actual degree-six integral singular homology of the standard six-sphere. -/
def homologySixEquiv : SingularHomology SixSphere 6 ≃ₗ[ℤ] ℤ :=
  unitSphereHomologyTopEquiv 5

/-- The genuine top cycle marked by iterated singular suspension. -/
def topClass : SingularHomology SixSphere 6 := unitSphereTopClass 5

@[simp] theorem homologySixEquiv_topClass : homologySixEquiv topClass = 1 :=
  unitSphereHomologyTopEquiv_topClass 5

theorem topClass_ne_zero : topClass ≠ 0 := unitSphereTopClass_ne_zero 5

/-- Every other positive-degree integral singular homology group vanishes. -/
theorem homology_subsingleton (k : ℕ) (hk : k ≠ 0) (hk6 : k ≠ 6) :
    Subsingleton (SingularHomology SixSphere k) :=
  unitSphere_homology_subsingleton 5 k hk hk6

theorem homology_free (k : ℕ) : Module.Free ℤ (SingularHomology SixSphere k) :=
  unitSphere_homology_free 5 k

theorem homology_finite (k : ℕ) : Module.Finite ℤ (SingularHomology SixSphere k) :=
  unitSphere_homology_finite 5 k

theorem homology_finrank (k : ℕ) :
    Module.finrank ℤ (SingularHomology SixSphere k) =
      if k = 0 ∨ k = 6 then 1 else 0 :=
  unitSphere_homology_finrank 5 k

def cohomologyZeroEquiv : SingularCohomology SixSphere 0 ≃ₗ[ℤ] ℤ :=
  unitSphereCohomologyZeroEquiv 5

def cohomologySixEquiv : SingularCohomology SixSphere 6 ≃ₗ[ℤ] ℤ :=
  unitSphereCohomologyTopEquiv 5

def topCohomologyClass : SingularCohomology SixSphere 6 :=
  unitSphereTopCohomologyClass 5

/-- The native cochain-cycle evaluation of these actual generators is one. -/
@[simp] theorem topCohomologyClass_pairing :
    singularEvaluation SixSphere 6 topCohomologyClass topClass = 1 :=
  unitSphereTopCohomologyClass_pairing 5

theorem topCohomologyClass_ne_zero : topCohomologyClass ≠ 0 :=
  unitSphereTopCohomologyClass_ne_zero 5

/-- Native integral cohomology has the same two nonzero degrees. -/
theorem cohomology_subsingleton (k : ℕ) (hk : k ≠ 0) (hk6 : k ≠ 6) :
    Subsingleton (SingularCohomology SixSphere k) :=
  unitSphere_cohomology_subsingleton 5 k hk hk6

theorem cohomology_finrank (k : ℕ) :
    Module.finrank ℤ (SingularCohomology SixSphere k) =
      if k = 0 ∨ k = 6 then 1 else 0 :=
  unitSphere_cohomology_finrank 5 k

/-- The complete integral singular homology statement for the literal standard sphere. -/
theorem homology :
    Nonempty (SingularHomology SixSphere 0 ≃ₗ[ℤ] ℤ) ∧
      Nonempty (SingularHomology SixSphere 6 ≃ₗ[ℤ] ℤ) ∧
      ∀ k, k ≠ 0 → k ≠ 6 → Subsingleton (SingularHomology SixSphere k) :=
  ⟨⟨homologyZeroEquiv⟩, ⟨homologySixEquiv⟩, homology_subsingleton⟩

end Wikipedia.HopfProblem.SixSphereHomology
