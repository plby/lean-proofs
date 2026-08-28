import Wikipedia.HopfProblem.CuspCentralHomologyOpenRetraction
import Wikipedia.HopfProblem.CuspHoneycombCollapse
import Wikipedia.HopfProblem.CuspFirstHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Actual integral singular homology of the central cusp in degrees zero and one

Path connectedness follows from the genuine phase-plane parametrization.
In degree one, the constructed norm-monotone deformation identifies the
central fibre with an actual sufficiently small open cusp.  Its proved
universal-cover marking then gives integral singular first homology `ℤ²`.
The forward homology map is identified with the actual central inclusion;
no cell model or homology rank is assumed.
-/

noncomputable section

open Set Topology
open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology

open ToricSpace CuspQuotient CuspRetraction CuspHoneycomb
open SingularMayerVietoris PeriodTorusHigherHomology

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ)

/-- The literal central fibre is path connected, without any regularity
or small-drift hypothesis on the twisting function. -/
theorem central_pathConnectedSpace (hr : 0 < r) :
    PathConnectedSpace (QuotientCentralFibre C r) := by
  exact (honeycombCollapseMap_surjective C r hr).pathConnectedSpace
    (honeycombCollapseMap_continuous C r hr)

/-- The actual central point corresponding to the centre of the zero
hexagon with all compact phases equal to one. -/
def centralBasePoint (hr : 0 < r) : QuotientCentralFibre C r :=
  honeycombCollapseMap C r hr (1, 0)

/-- The actual singular augmentation in degree zero. -/
def centralSingularH0Equiv (hr : 0 < r) :
    SingularHomology (QuotientCentralFibre C r) 0 ≃ₗ[ℤ] ℤ := by
  let := central_pathConnectedSpace C r hr
  exact connectedHomologyZeroEquiv (QuotientCentralFibre C r)

@[simp] theorem centralSingularH0Equiv_pointClass (hr : 0 < r)
    (q : QuotientCentralFibre C r) :
    centralSingularH0Equiv C r hr (pointClass q) = 1 := by
  let := central_pathConnectedSpace C r hr
  exact connectedHomologyZeroEquiv_pointClass q

/-- Every genuine specialization from a path-connected fibre has the
identity degree-zero map in the augmentation markings. -/
theorem centralSingularH0Equiv_natural (hr : 0 < r)
    {X : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (f : C(X, QuotientCentralFibre C r)) (a : SingularHomology X 0) :
    centralSingularH0Equiv C r hr (singularHomologyMap f 0 a) =
      connectedHomologyZeroEquiv X a := by
  let := central_pathConnectedSpace C r hr
  exact connectedHomologyZeroEquiv_natural f a

/-- Constructed comparison data for a genuinely smaller admissible
open cusp.  The existence theorem below supplies every field. -/
structure SmallCentralModel
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) where
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt : radius < r
  radius_lt_one : radius < 1
  smallDrift : SmallDrift C radius
  equivalence : QuotientCentralFibre C r ≃ₕ QuotientSpace C radius
  inclusion_eq : equivalence.toFun = centralIntoSmallerQuotient C r radius
    radius_pos radius_lt.le hC

theorem exists_smallCentralModel (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    Nonempty (SmallCentralModel C r hC) := by
  obtain ⟨δ₀, hδ₀, hδ₀r, _hδ₀1, he⟩ := exists_centralHomotopyEquiv C r hr hC
  have hCδ₀ : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 δ₀) :=
    fun i j => (hC i j).mono (Metric.ball_subset_ball hδ₀r.le)
  obtain ⟨δ, hδ, hδδ₀, hδ1, hR, _hCδ⟩ := exists_admissible_radius C hδ₀ hCδ₀
  have hδr := hδδ₀.trans hδ₀r
  obtain ⟨e, he⟩ := he δ hδ hδδ₀.le hδr.le
  exact ⟨⟨δ, hδ, hδr, hδ1, hR, e, he⟩⟩

/-- A choice of the comparison data whose existence was proved from the
actual cusp deformation and analytic small-radius estimates. -/
def smallCentralModel (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SmallCentralModel C r hC :=
  Classical.choice (exists_smallCentralModel C r hr hC)

namespace SmallCentralModel

variable {C r}
variable {hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)}

theorem holomorphic (M : SmallCentralModel C r hC) :
    ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 M.radius) :=
  fun i j => (hC i j).mono (Metric.ball_subset_ball M.radius_lt.le)

/-- The marked equivalence is induced by the actual comparison map and
the actual cusp singular-Hurewicz equivalence. -/
def singularH1Equiv (M : SmallCentralModel C r hC) (q : QuotientCentralFibre C r) :
    SingularHomology (QuotientCentralFibre C r) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (homotopyEquivHomologyEquiv M.equivalence 1).trans
    (CuspQuotient.singularH1Equiv C M.radius M.radius_pos M.radius_lt_one
      M.holomorphic M.smallDrift (M.equivalence q))

/-- The forward map really is the actual central inclusion at the
smaller radius, not a separately postulated lattice marking. -/
theorem singularH1Equiv_inclusion (M : SmallCentralModel C r hC)
    (q : QuotientCentralFibre C r) (a : SingularHomology (QuotientCentralFibre C r) 1) :
    M.singularH1Equiv q a =
      CuspQuotient.singularH1Equiv C M.radius M.radius_pos M.radius_lt_one
        M.holomorphic M.smallDrift (M.equivalence q)
        (singularHomologyMap (centralIntoSmallerQuotient C r M.radius
          M.radius_pos M.radius_lt.le hC) 1 a) := by
  change CuspQuotient.singularH1Equiv C M.radius M.radius_pos M.radius_lt_one
    M.holomorphic M.smallDrift (M.equivalence q)
      (singularHomologyMap M.equivalence.toFun 1 a) = _
  rw [M.inclusion_eq]

end SmallCentralModel

/-- Integral singular first homology of the actual central fibre is the
rank-two deck lattice.  The analytic and geometric estimates needed for
the comparison are all derived at a smaller radius. -/
def centralSingularH1Equiv (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r)) :
    SingularHomology (QuotientCentralFibre C r) 1 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (smallCentralModel C r hr hC).singularH1Equiv (centralBasePoint C r hr)

theorem centralSingularH0_free (hr : 0 < r) :
    Module.Free ℤ (SingularHomology (QuotientCentralFibre C r) 0) :=
  Module.Free.of_equiv (centralSingularH0Equiv C r hr).symm

theorem centralSingularH0_finite (hr : 0 < r) :
    Module.Finite ℤ (SingularHomology (QuotientCentralFibre C r) 0) :=
  Module.Finite.of_surjective (centralSingularH0Equiv C r hr).symm.toLinearMap
    (centralSingularH0Equiv C r hr).symm.surjective

theorem centralSingularH0_finrank (hr : 0 < r) :
    Module.finrank ℤ (SingularHomology (QuotientCentralFibre C r) 0) = 1 := by
  rw [(centralSingularH0Equiv C r hr).finrank_eq]
  simp

theorem centralSingularH0_torsionFree (hr : 0 < r) :
    Module.IsTorsionFree ℤ (SingularHomology (QuotientCentralFibre C r) 0) := by
  let := centralSingularH0_free C r hr
  infer_instance

variable (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

include hr hC

theorem centralSingularH1_free :
    Module.Free ℤ (SingularHomology (QuotientCentralFibre C r) 1) :=
  Module.Free.of_equiv (centralSingularH1Equiv C r hr hC).symm

theorem centralSingularH1_finite :
    Module.Finite ℤ (SingularHomology (QuotientCentralFibre C r) 1) :=
  Module.Finite.of_surjective (centralSingularH1Equiv C r hr hC).symm.toLinearMap
    (centralSingularH1Equiv C r hr hC).symm.surjective

theorem centralSingularH1_finrank :
    Module.finrank ℤ (SingularHomology (QuotientCentralFibre C r) 1) = 2 := by
  rw [(centralSingularH1Equiv C r hr hC).finrank_eq]
  simp

theorem centralSingularH1_torsionFree :
    Module.IsTorsionFree ℤ (SingularHomology (QuotientCentralFibre C r) 1) := by
  let := centralSingularH1_free C r hr hC
  infer_instance

end Wikipedia.HopfProblem.CuspCentralHomology
