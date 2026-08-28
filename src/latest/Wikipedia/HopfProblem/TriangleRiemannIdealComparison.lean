import Wikipedia.HopfProblem.TriangleRiemannCorners
import Wikipedia.HopfProblem.TriangleRiemannIdeal
import Wikipedia.HopfProblem.RiemannBoundaryIdealTopology

/-!
# The three distinct boundary values of the actual triangle Riemann map

The ideal logarithmic parameter is continuous at zero in `OnePoint ℂ`.
Transporting the original domain by its actual finite-point inclusion lets
the same inverse-uniformization theorem compare its ideal and finite
boundary germs. Their values cannot coincide, because their inverse limits
are respectively infinity and finite points.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology OnePoint

namespace Wikipedia.HopfProblem.RiemannMapping

open SpecialPeriods.Triangle RiemannBoundary

/-- The actual analytic cusp extension gives a boundary germ for the
logarithmic parameter. Its source function need not have a finite limit at
zero; only the analytic disc-valued germ is part of this structure. -/
theorem exists_triangleIdealGerm : Nonempty (TriangleBoundaryGerm triangleCuspLog) := by
  obtain ⟨r, hr, H, hHa, hHe, _, hHc, hHd, hHn, hHside⟩ :=
    exists_triangleMap_extension_ideal_vertex
  obtain ⟨R, hR, hheight⟩ :=
    exists_logHalfStrip_height_radius stripLeft 1 triangleCuspScale_pos
  refine ⟨{
    function := H
    radius := r
    radius_pos := hr
    analytic := hHa
    agrees := hHe
    unit := hHc 0 (mem_ball_self hr)
    strictDeriv := hHd
    deriv_ne_zero := hHn
    sourceCorrespondence := ?_ }⟩
  filter_upwards [hHside, ball_mem_nhds (0 : ℂ) hr, ball_mem_nhds (0 : ℂ) hR]
    with q hq hrq hRq hn
  have hi : 0 < q.im := hq.mp hn
  have hq0 : q ≠ 0 := by
    intro heq
    rw [heq, zero_im] at hi
    exact (lt_irrefl 0) hi
  have hRe := logHalfStrip_re_mem_Ioo stripLeft triangleCuspScale_pos hi
  have hD : triangleCuspLog q ∈ triangleInterior :=
    triangle_high_halfStrip_mem _ hRe.1 hRe.2 (hheight q hRq hq0)
  exact ⟨hD, (hHe ⟨hrq, hi⟩).symm⟩

/-- A chosen actual analytic germ at the ideal vertex. -/
def triangleIdealGerm : TriangleBoundaryGerm triangleCuspLog :=
  Classical.choice exists_triangleIdealGerm

/-- The original triangle domain, with its natural topology, viewed
inside the one-point compactification of the plane. -/
def triangleDiscOnOnePointDomain :
    onePointDomain triangleInterior ≃ₜ ball (0 : ℂ) 1 :=
  onePointDomainDiscHomeomorph triangleBiholomorph.toHomeomorph

/-- An ambient representative of the original map on the finite domain.
Its arbitrary value at infinity is not a claimed boundary value. -/
def triangleOnePointRepresentative (z : OnePoint ℂ) : ℂ :=
  z.elim 0 triangleMap

@[simp] theorem triangleOnePointRepresentative_coe (z : ℂ) :
    triangleOnePointRepresentative (z : OnePoint ℂ) = triangleMap z := rfl

theorem triangleOnePointRepresentative_homeomorph (z : onePointDomain triangleInterior) :
    triangleOnePointRepresentative z = (triangleDiscOnOnePointDomain z : ℂ) :=
  onePointDomainDiscHomeomorph_representative triangleBiholomorph.toHomeomorph
    triangleMap_biholomorph 0 z

/-- The actual ideal source coordinate, continuous at its ideal value. -/
def triangleIdealParameter : ℂ → OnePoint ℂ :=
  onePointLogHalfStrip stripLeft triangleCuspScale

@[simp] theorem triangleIdealParameter_zero : triangleIdealParameter 0 = ∞ :=
  onePointLogHalfStrip_zero _ _

theorem continuousAt_triangleIdealParameter_zero : ContinuousAt triangleIdealParameter 0 :=
  continuousAt_onePointLogHalfStrip_zero stripLeft triangleCuspScale_pos

/-- Finite boundary source correspondences are unchanged by the actual
inclusion into the one-point compactification. -/
theorem TriangleBoundaryGerm.onePoint_sourceCorrespondence
    {φ : ℂ → ℂ} (g : TriangleBoundaryGerm φ) :
    ∀ᶠ z in 𝓝 (0 : ℂ), ‖g.function z‖ < 1 →
      (φ z : OnePoint ℂ) ∈ onePointDomain triangleInterior ∧
        triangleOnePointRepresentative (φ z : OnePoint ℂ) = g.function z := by
  filter_upwards [g.sourceCorrespondence] with z hz hn
  obtain ⟨hmem, hvalue⟩ := hz hn
  exact ⟨coe_mem_onePointDomain.mpr hmem, hvalue⟩

/-- The cusp germ has the same actual source correspondence after its
source parameter is filled by infinity. -/
theorem triangleIdeal_onePoint_sourceCorrespondence :
    ∀ᶠ z in 𝓝 (0 : ℂ), ‖triangleIdealGerm.function z‖ < 1 →
      triangleIdealParameter z ∈ onePointDomain triangleInterior ∧
        triangleOnePointRepresentative (triangleIdealParameter z) =
          triangleIdealGerm.function z := by
  filter_upwards [triangleIdealGerm.sourceCorrespondence] with z hz hn
  have hzne : z ≠ 0 := by
    intro heq
    rw [heq, triangleIdealGerm.unit] at hn
    exact (lt_irrefl 1) hn
  have hparameter : triangleIdealParameter z = (triangleCuspLog z : OnePoint ℂ) :=
    onePointLogHalfStrip_of_ne_zero stripLeft triangleCuspScale hzne
  rw [hparameter]
  obtain ⟨hmem, hvalue⟩ := hz hn
  exact ⟨coe_mem_onePointDomain.mpr hmem, hvalue⟩

/-- The actual inverse uniformization tends to the filled ideal point
at the cusp's constructed unit-circle value. -/
theorem triangleIdeal_inverse_limit :
    Tendsto (discHomeomorphInverse triangleDiscOnOnePointDomain)
      (𝓝[ball (0 : ℂ) 1] (triangleIdealGerm.function 0))
      (𝓝 (∞ : OnePoint ℂ)) := by
  simpa only [triangleIdealParameter_zero] using
    tendsto_discHomeomorphInverse_of_boundary_chart triangleDiscOnOnePointDomain
      triangleOnePointRepresentative_homeomorph continuousAt_triangleIdealParameter_zero
      triangleIdealGerm.strictDeriv triangleIdealGerm.deriv_ne_zero
      triangleIdeal_onePoint_sourceCorrespondence

/-- Any finite boundary germ has a different disc value from the ideal
germ. Equality would give a finite point equal to infinity by uniqueness
of the actual inverse-uniformization limit. -/
theorem TriangleBoundaryGerm.value_ne_ideal {φ : ℂ → ℂ} (g : TriangleBoundaryGerm φ)
    (hφ : ContinuousAt φ 0) : g.function 0 ≠ triangleIdealGerm.function 0 := by
  intro hvalue
  have hφc : ContinuousAt (fun z => (φ z : OnePoint ℂ)) 0 :=
    OnePoint.continuous_coe.continuousAt.comp hφ
  have hp := boundary_points_eq_of_equal_disc_values triangleDiscOnOnePointDomain
    triangleOnePointRepresentative_homeomorph hφc continuousAt_triangleIdealParameter_zero
    g.strictDeriv g.deriv_ne_zero triangleIdealGerm.strictDeriv triangleIdealGerm.deriv_ne_zero
    g.onePoint_sourceCorrespondence triangleIdeal_onePoint_sourceCorrespondence g.unit hvalue
  rw [triangleIdealParameter_zero] at hp
  exact OnePoint.coe_ne_infty (φ 0) hp

theorem triangleCornerThree_boundary_value_ne_ideal :
    triangleCornerThreeGerm.function 0 ≠ triangleIdealGerm.function 0 :=
  triangleCornerThreeGerm.value_ne_ideal continuousAt_cornerParameterThree_zero

theorem triangleCornerFour_boundary_value_ne_ideal :
    triangleCornerFourGerm.function 0 ≠ triangleIdealGerm.function 0 :=
  triangleCornerFourGerm.value_ne_ideal continuousAt_cornerParameterFour_zero

/-- The actual boundary values in the order cubic corner, quartic
corner, ideal vertex. -/
def triangleVertexBoundaryValue : Fin 3 → ℂ :=
  ![triangleCornerThreeGerm.function 0, triangleCornerFourGerm.function 0,
    triangleIdealGerm.function 0]

theorem triangleVertexBoundaryValue_unit (i : Fin 3) :
    ‖triangleVertexBoundaryValue i‖ = 1 := by
  fin_cases i <;> simp [triangleVertexBoundaryValue, triangleCornerThreeGerm.unit,
    triangleCornerFourGerm.unit, triangleIdealGerm.unit]

/-- All three actual unit-circle vertex values are pairwise distinct;
distinctness is a proved property, not a normalization assumption. -/
theorem triangleVertexBoundaryValue_injective :
    Function.Injective triangleVertexBoundaryValue := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [triangleVertexBoundaryValue, triangleCorner_boundary_values_ne,
      triangleCornerThree_boundary_value_ne_ideal, triangleCornerFour_boundary_value_ne_ideal,
      Ne.symm triangleCorner_boundary_values_ne,
      Ne.symm triangleCornerThree_boundary_value_ne_ideal,
      Ne.symm triangleCornerFour_boundary_value_ne_ideal]

end Wikipedia.HopfProblem.RiemannMapping
