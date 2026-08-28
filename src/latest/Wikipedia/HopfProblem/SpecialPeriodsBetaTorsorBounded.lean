import Wikipedia.HopfProblem.SpecialPeriodsBetaTorsorDescent
import Mathlib.Analysis.Complex.Liouville

/-!
# Bounded-cusp classification on the actual triangle quotient

Every sufficiently large finite base point has a representative in an
arbitrarily high actual horodisc.  This follows from the constructed cusp
neighborhoods and the supplied normalized sphere biholomorphism, not from an
assumed lifting property.

An invariant holomorphic function bounded on a high horodisc therefore has a
bounded entire descended function.  The actual descent is constructed using
the proved quotient descent theorem, and Liouville makes it constant.  Applied
to the difference of two beta-functions, this proves uniqueness up to a
constant under the original bounded-cusp condition, without assuming analytic
extensions of their cusp expressions.
-/

noncomputable section

open Function Filter Metric Set Topology UpperHalfPlane
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor

attribute [local instance] triangleOrbitChartedSpace triangleCompactifiedChartedSpace

variable (π : Diffeomorph 𝓘(ℂ) 𝓘(ℂ)
  TriangleCompactifiedOrbitSpace RiemannSphere ω)
  (hπ : π triangleCuspPoint = (∞ : RiemannSphere))

include hπ

/-- Every sufficiently large finite coordinate has an actual representative
above any prescribed height in the upper half-plane. -/
theorem exists_cusp_tail_lifts (Y : ℝ) :
    ∃ R : ℝ, 0 < R ∧ ∀ t : ℂ, R < ‖t‖ →
      ∃ z : ℍ, Y < z.im ∧ finiteProjection π z = t := by
  obtain ⟨R, hR, hRU⟩ := MuTorsor.Cover.finitePullback_contains_exterior π hπ
    (Triangle.cuspNeighborhood Y) (Triangle.cuspPoint_mem_cuspNeighborhood Y)
  refine ⟨R, hR, ?_⟩
  intro t ht
  have htU : MuTorsor.Cover.finiteInverse π t ∈ Triangle.cuspNeighborhood Y := hRU (by
    simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using ht.le)
  rw [← openInclusion_finiteOrbitInverse π hπ t] at htU
  have hq := (Triangle.openInclusion_mem_cuspNeighborhood Y
    (finiteOrbitInverse π hπ t)).mp htU
  obtain ⟨z, hz, hzt⟩ := (Triangle.mem_cuspImage Y (finiteOrbitInverse π hπ t)).mp hq
  refine ⟨z, hz, ?_⟩
  change finiteOrbitCoordinate π (triangleOrbitProjection z) = t
  rw [hzt, finiteOrbitCoordinate_inverse π hπ]

/-- A holomorphic invariant function bounded on one actual high horodisc is
constant.  Both the entire descended function and the tail lifts are proved
internally from the genuine quotient geometry. -/
theorem invariant_holomorphic_eq_const_of_horodisc_bounded (f : ℍ → ℂ)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hInv : ∀ g : TriangleGroup, ∀ z : ℍ,
      f (triangleGeometricRepresentation g z) = f z)
    (hbound : ∃ Y C : ℝ, ∀ z : ℍ, Y < z.im → ‖f z‖ ≤ C) :
    ∃ c : ℂ, ∀ z : ℍ, f z = c := by
  obtain ⟨F, hF, hdesc⟩ := exists_entire_descent π hπ f hf hInv
  obtain ⟨Y, C, hC⟩ := hbound
  obtain ⟨R, _, hlift⟩ := exists_cusp_tail_lifts π hπ Y
  have hDF : Differentiable ℂ F := fun t => (hF t).differentiableAt
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hDF.continuous.continuousOn
  have hbounded : Bornology.IsBounded (range F) := by
    apply isBounded_iff_forall_norm_le.mpr
    refine ⟨max C₀ C, ?_⟩
    rintro _ ⟨t, rfl⟩
    by_cases ht : ‖t‖ ≤ R
    · exact (hC₀ t (by simpa only [mem_closedBall, dist_zero_right] using ht)).trans
        (le_max_left _ _)
    · obtain ⟨z, hz, hzt⟩ := hlift t (lt_of_not_ge ht)
      have he : F t = f z := by rw [← hzt]; exact hdesc z
      rw [he]
      exact (hC z hz).trans (le_max_right _ _)
  obtain ⟨c, hc⟩ := hDF.exists_const_forall_eq_of_bounded hbounded
  exact ⟨c, fun z => (hdesc z).symm.trans (hc (finiteProjection π z))⟩

/-- Two actual holomorphic beta-functions with invariant difference and
bounded cusp sums differ by a constant.  The two boundedness hypotheses may
use different horodiscs and different bounds. -/
theorem exists_const_beta_difference_of_bounded (β γ τ : ℍ → ℂ)
    (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (hγ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω γ)
    (hInv : ∀ g : TriangleGroup, ∀ z : ℍ,
      β (triangleGeometricRepresentation g z) - γ (triangleGeometricRepresentation g z) =
        β z - γ z)
    (hβbound : ∃ Y C : ℝ, ∀ z : ℍ, Y < z.im → ‖β z + τ z‖ ≤ C)
    (hγbound : ∃ Y C : ℝ, ∀ z : ℍ, Y < z.im → ‖γ z + τ z‖ ≤ C) :
    ∃ c : ℂ, ∀ z : ℍ, β z = γ z + c := by
  obtain ⟨Yβ, Cβ, hCβ⟩ := hβbound
  obtain ⟨Yγ, Cγ, hCγ⟩ := hγbound
  have hbound : ∃ Y C : ℝ, ∀ z : ℍ, Y < z.im → ‖β z - γ z‖ ≤ C := by
    refine ⟨max Yβ Yγ, Cβ + Cγ, ?_⟩
    intro z hz
    have hzβ : Yβ < z.im := (le_max_left Yβ Yγ).trans_lt hz
    have hzγ : Yγ < z.im := (le_max_right Yβ Yγ).trans_lt hz
    calc
      ‖β z - γ z‖ = ‖(β z + τ z) - (γ z + τ z)‖ := by congr 1; ring
      _ ≤ ‖β z + τ z‖ + ‖γ z + τ z‖ := norm_sub_le _ _
      _ ≤ Cβ + Cγ := add_le_add (hCβ z hzβ) (hCγ z hzγ)
  obtain ⟨c, hc⟩ := invariant_holomorphic_eq_const_of_horodisc_bounded π hπ
    (fun z => β z - γ z) (hβ.sub hγ) hInv hbound
  refine ⟨c, fun z => ?_⟩
  exact (sub_eq_iff_eq_add.mp (hc z)).trans (add_comm _ _)

omit hπ in
private theorem holomorphic_of_mdifferentiable_upperHalfPlane (f : ℍ → ℂ)
    (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  have ha : AnalyticOnNhd ℂ (f ∘ UpperHalfPlane.ofComplex) upperHalfPlaneSet :=
    (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd isOpen_upperHalfPlaneSet
  intro z
  exact UpperHalfPlane.contMDiffAt_iff.mpr (ha z z.im_pos).contDiffAt

/-- The same classification stated directly with complex differentiability,
the usual native holomorphy hypothesis on the upper half-plane. -/
theorem exists_const_beta_difference_of_bounded_mdifferentiable (β γ τ : ℍ → ℂ)
    (hβ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) β) (hγ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) γ)
    (hInv : ∀ g : TriangleGroup, ∀ z : ℍ,
      β (triangleGeometricRepresentation g z) - γ (triangleGeometricRepresentation g z) =
        β z - γ z)
    (hβbound : ∃ Y C : ℝ, ∀ z : ℍ, Y < z.im → ‖β z + τ z‖ ≤ C)
    (hγbound : ∃ Y C : ℝ, ∀ z : ℍ, Y < z.im → ‖γ z + τ z‖ ≤ C) :
    ∃ c : ℂ, ∀ z : ℍ, β z = γ z + c :=
  exists_const_beta_difference_of_bounded π hπ β γ τ
    (holomorphic_of_mdifferentiable_upperHalfPlane β hβ)
    (holomorphic_of_mdifferentiable_upperHalfPlane γ hγ) hInv hβbound hγbound

/-- Shared actual additive-affine laws imply the invariant-difference
hypothesis, so bounded solutions of the same laws form one constant family. -/
theorem exists_const_beta_difference_of_same_law_bounded (β γ τ : ℍ → ℂ)
    (hβ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω β) (hγ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω γ)
    (δ : TriangleGroup → ℍ → ℂ)
    (hβlaw : ∀ g z, β (triangleGeometricRepresentation g z) = β z + δ g z)
    (hγlaw : ∀ g z, γ (triangleGeometricRepresentation g z) = γ z + δ g z)
    (hβbound : ∃ Y C : ℝ, ∀ z : ℍ, Y < z.im → ‖β z + τ z‖ ≤ C)
    (hγbound : ∃ Y C : ℝ, ∀ z : ℍ, Y < z.im → ‖γ z + τ z‖ ≤ C) :
    ∃ c : ℂ, ∀ z : ℍ, β z = γ z + c := by
  apply exists_const_beta_difference_of_bounded π hπ β γ τ hβ hγ ?_ hβbound hγbound
  intro g z
  rw [hβlaw g z, hγlaw g z]
  ring

end Wikipedia.HopfProblem.SpecialPeriods.BetaTorsor
