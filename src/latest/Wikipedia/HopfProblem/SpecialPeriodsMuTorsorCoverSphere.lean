import Wikipedia.HopfProblem.SpecialPeriodsTriangleCuspAtlas
import Wikipedia.HopfProblem.RiemannSphere

/-!
# Finite-coordinate transport of actual quotient neighbourhoods

A supplied analytic identification of the compact quotient with the sphere
transports its open patches to the finite complex plane. The normalization
at the actual cusp implies that every cusp neighbourhood contains the
inverse image of the complement of some positive-radius complex ball.
No existence of the supplied sphere identification is asserted here.
-/

noncomputable section

open Set Filter Topology Bornology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Cover

attribute [local instance] triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)

/-- The actual inverse sphere identification on its finite affine chart. -/
def finiteInverse (z : ℂ) : TriangleCompactifiedOrbitSpace := π.symm (z : RiemannSphere)

@[simp] theorem apply_finiteInverse (z : ℂ) :
    π (finiteInverse π z) = (z : RiemannSphere) := π.apply_symm_apply _

theorem finiteInverse_continuous : Continuous (finiteInverse π) :=
  π.symm.continuous.comp OnePoint.continuous_coe

theorem finiteInverse_holomorphic : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (finiteInverse π) := by
  have hc : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun z : ℂ => (z : RiemannSphere)) :=
    RiemannSphere.standardCharts.affineMap_holomorphic false
  exact π.symm.contMDiff.comp hc

theorem finiteInverse_isOpenEmbedding : IsOpenEmbedding (finiteInverse π) :=
  π.symm.toHomeomorph.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe

/-- Pullback of an actual open quotient patch to the finite coordinate. -/
def finitePullback (V : TopologicalSpace.Opens TriangleCompactifiedOrbitSpace) :
    TopologicalSpace.Opens ℂ :=
  ⟨finiteInverse π ⁻¹' (V : Set TriangleCompactifiedOrbitSpace),
    V.isOpen.preimage (finiteInverse_continuous π)⟩

@[simp] theorem mem_finitePullback (V : TopologicalSpace.Opens TriangleCompactifiedOrbitSpace)
    (z : ℂ) : z ∈ finitePullback π V ↔ finiteInverse π z ∈ V := Iff.rfl

variable (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

theorem symm_infty : π.symm (∞ : RiemannSphere) = triangleCuspPoint := by
  exact π.injective ((π.apply_symm_apply _).trans hπ.symm)

theorem finiteInverse_ne_cusp (z : ℂ) : finiteInverse π z ≠ triangleCuspPoint := by
  intro h
  exact OnePoint.coe_ne_infty z
    ((apply_finiteInverse π z).symm.trans ((congrArg π h).trans hπ))

/-- The finite affine chart is exactly the original quotient, with its cusp
removed, after the supplied normalization. -/
theorem range_finiteInverse :
    range (finiteInverse π) = {triangleCuspPoint}ᶜ := by
  ext q
  change (∃ z, finiteInverse π z = q) ↔ q ≠ triangleCuspPoint
  constructor
  · rintro ⟨z, rfl⟩
    exact finiteInverse_ne_cusp π hπ z
  · intro hq
    have hπq : π q ≠ (∞ : RiemannSphere) := by
      intro h
      exact hq (π.injective (h.trans hπ.symm))
    obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hπq
    exact ⟨z, π.injective ((apply_finiteInverse π z).trans hz)⟩

/-- Escape in the finite complex coordinate tends to the actual cusp. -/
theorem finiteInverse_tendsto_cusp :
    Tendsto (finiteInverse π) (cobounded ℂ) (𝓝 triangleCuspPoint) := by
  have hc : Tendsto (fun z : ℂ => (z : RiemannSphere))
      (cobounded ℂ) (𝓝 (∞ : RiemannSphere)) := by
    simpa only [coclosedCompact_eq_cocompact, Metric.cobounded_eq_cocompact] using
      (OnePoint.tendsto_coe_infty (X := ℂ))
  have h := π.symm.continuous.continuousAt.tendsto.comp hc
  change Tendsto (finiteInverse π) (cobounded ℂ) (𝓝 (π.symm (∞ : RiemannSphere))) at h
  simpa only [symm_infty π hπ] using h

/-- Every genuine cusp neighbourhood contains all sufficiently large finite
coordinates, with a positive radius and the complement of an open ball. -/
theorem finitePullback_contains_exterior
    (V : TopologicalSpace.Opens TriangleCompactifiedOrbitSpace)
    (hV : triangleCuspPoint ∈ V) :
    ∃ R : ℝ, 0 < R ∧ (Metric.ball (0 : ℂ) R)ᶜ ⊆ finitePullback π V := by
  have hmem : (finitePullback π V : Set ℂ) ∈ cobounded ℂ :=
    (finiteInverse_tendsto_cusp π hπ) (V.isOpen.mem_nhds hV)
  obtain ⟨r, _, hr⟩ := (Metric.hasBasis_cobounded_compl_ball (0 : ℂ)).mem_iff.mp hmem
  refine ⟨max r 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  exact (compl_subset_compl.mpr (Metric.ball_subset_ball (le_max_left r 1))).trans hr

end Wikipedia.HopfProblem.SpecialPeriods.MuTorsor.Cover
