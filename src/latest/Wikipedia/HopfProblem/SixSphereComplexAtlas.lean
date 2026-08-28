import Wikipedia.SmoothSixDPoincare.TheoremA
import Wikipedia.HopfProblem.DegreeCollapseHomotopyEquivalence
import Wikipedia.HopfProblem.SixSphereComplexTransportAtlas
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldRealManifold
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCuspPieceModelChange

/-!
# A complex atlas on the topological six-sphere

The original constructed threefold is homotopy equivalent to the literal unit
six-sphere. Smale's theorem supplies a homeomorphism, along which its complex
atlas transports. A complex-linear change of coordinates gives the requested
model `EuclideanSpace ℂ (Fin 3)`.

The sphere keeps its Euclidean subspace topology. No compatibility with its
standard real smooth atlas is asserted, and no smooth-rigidity hypothesis is
used. The existential atlas is explicitly installed in its manifold assertion.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SixSphereComplexAtlas

open SpecialPeriods

/-- The literal unit `n`-sphere in real Euclidean `(n + 1)`-space. -/
abbrev unitSphere (n : ℕ) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold
  Threefold.space_isSmoothRealManifold Threefold.space_compact
  Threefold.space_t2Space Threefold.space_secondCountable

/-- Apply the unconditional Smale theorem to the original homotopy equivalence. -/
def threefoldHomeomorph : Threefold.Space ≃ₜ unitSphere 6 :=
  Classical.choice
    (Wikipedia.SmoothSixDPoincare.homeomorphic_sixSphere_of_homotopySixSphere
      (ℂ × ComplexPlane₂) Threefold.Space Threefold.real_dimension
      DegreeCollapse.threefoldHomotopyEquiv)

/-- Change only the coordinate model, by a continuous complex-linear equivalence. -/
def modelEquiv : (ℂ × ComplexPlane₂) ≃L[ℂ] EuclideanSpace ℂ (Fin 3) :=
  Threefold.cuspModelEquiv.symm.trans (EuclideanSpace.equiv (Fin 3) ℂ).symm

/-- Unconditionally, the topological six-sphere admits a complex analytic atlas. -/
theorem exists_complex_analytic_atlas :
    ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      letI := atlas
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) ω (unitSphere 6) := by
  let := ManifoldAtlasTransport.chartedSpace (H := ℂ × ComplexPlane₂) threefoldHomeomorph
  let := ManifoldAtlasTransport.isManifold 𝓘(ℂ, ℂ × ComplexPlane₂) ω threefoldHomeomorph
  exact ⟨Threefold.ModelChange.chartedSpace modelEquiv (unitSphere 6),
    Threefold.ModelChange.isManifold modelEquiv (unitSphere 6) ω⟩

/-- The requested `C¹` complex-manifold statement, with no recognition premise. -/
theorem exists_complex_atlas :
    ∃ atlas : ChartedSpace (EuclideanSpace ℂ (Fin 3)) (unitSphere 6),
      letI := atlas
      IsManifold 𝓘(ℂ, EuclideanSpace ℂ (Fin 3)) 1 (unitSphere 6) := by
  obtain ⟨atlas, h⟩ := exists_complex_analytic_atlas
  refine ⟨atlas, ?_⟩
  let := atlas
  let := h
  infer_instance

end Wikipedia.HopfProblem.SixSphereComplexAtlas
