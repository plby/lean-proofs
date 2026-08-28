import Wikipedia.HopfProblem.CuspSimplyConnected
import Wikipedia.HopfProblem.CuspFibreTori
import Wikipedia.HopfProblem.FirstHurewiczChainNaturality

/-!
# Path-connectedness of the actual cusp quotient and fibres

The quotient is the continuous image of the simply connected toric tube.
Each nonzero fibre is the continuous image of the actual exponential
parametrization. These topological statements do not assume a homology
presentation or a Hurewicz isomorphism.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem

namespace CuspQuotient

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)

/-- The actual cusp quotient is path connected for every positive radius,
without any regularity or small-drift assumption on the twisting function. -/
theorem quotient_pathConnected (hε : 0 < ε) : PathConnectedSpace (QuotientSpace C ε) := by
  let : SimplyConnectedSpace (ToricSpace.Tube (disc ε)) := tube_simplyConnected hε
  have hq : Function.Surjective (quotientMap C ε) := Quotient.mk_surjective
  exact hq.pathConnectedSpace (quotientMap_continuous C ε)

end CuspQuotient

namespace CuspUniformization

open ToricCharts ToricSpace CuspQuotient

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε)

/-- The exponential parametrization covers the actual nonzero fibre,
independently of whether its full period quotient has yet been constructed. -/
theorem fibreCover_range :
    range (fibreCover C ε s hs) = projection C ε ⁻¹' {exponential s} := by
  ext q
  constructor
  · rintro ⟨z, rfl⟩
    exact projection_fibreCover C ε s hs z
  · induction q using Quotient.inductionOn with
    | h x =>
      intro hx
      have ht : time (x : Space) = exponential s := hx
      obtain ⟨z, hz⟩ := exponentialPoint_surjective_fibre (exponential_ne_zero s) ht
      refine ⟨z, ?_⟩
      apply congrArg (quotientMap C ε)
      exact Subtype.ext hz

include hs in
/-- Every exponential nonzero fibre is path connected with its actual
subspace topology. No analytic estimates are needed for this fact. -/
theorem exponential_fibre_pathConnectedSpace :
    PathConnectedSpace (projection C ε ⁻¹' {exponential s}) := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  rw [← fibreCover_range C ε s hs]
  exact isPathConnected_range (fibreCover_continuous C ε s hs)

/-- Every nonzero fibre over a point of the radius disc is path connected,
even before imposing the analytic hypotheses needed for a Hausdorff quotient. -/
theorem nonzero_fibre_pathConnectedSpace_of_norm_lt {t : ℂ}
    (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    PathConnectedSpace (projection C ε ⁻¹' {t}) := by
  let s := logarithm t
  have hst : exponential s = t := exponential_logarithm ht0
  have hs : ‖exponential s‖ < ε := by simpa only [hst] using ht
  apply isPathConnected_iff_pathConnectedSpace.mp
  have hp : IsPathConnected (projection C ε ⁻¹' {exponential s}) :=
    isPathConnected_iff_pathConnectedSpace.mpr (exponential_fibre_pathConnectedSpace C ε s hs)
  simpa only [hst] using hp

/-- The path-connected-space form of the established period-torus fibre theorem. -/
theorem nonzero_fibre_pathConnectedSpace (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : SmallDrift C ε) {t : ℂ} (ht0 : t ≠ 0) (ht : ‖t‖ < ε) :
    PathConnectedSpace (projection C ε ⁻¹' {t}) :=
  isPathConnected_iff_pathConnectedSpace.mp
    (nonzero_fibre_pathConnected C ε hε hε1 hC hR ht0 ht)

end CuspUniformization

namespace FirstHurewicz

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A homeomorphism induces a linear equivalence of actual singular homology,
whose inverse is induced by the inverse homeomorphism. -/
def homeomorphHomologyEquiv (e : X ≃ₜ Y) : SingularH1 X ≃ₗ[ℤ] SingularH1 Y where
  toLinearMap := inducedHomology (e : C(X, Y))
  invFun := inducedHomology (e.symm : C(Y, X))
  left_inv h := by
    have he : (e.symm : C(Y, X)).comp (e : C(X, Y)) = ContinuousMap.id X := by
      ext x
      exact e.symm_apply_apply x
    have hcomp := inducedHomology_comp (e : C(X, Y)) (e.symm : C(Y, X))
    rw [he, inducedHomology_id] at hcomp
    exact congrArg (fun f => f h) hcomp.symm
  right_inv h := by
    have he : (e : C(X, Y)).comp (e.symm : C(Y, X)) = ContinuousMap.id Y := by
      ext y
      exact e.apply_symm_apply y
    have hcomp := inducedHomology_comp (e.symm : C(Y, X)) (e : C(X, Y))
    rw [he, inducedHomology_id] at hcomp
    exact congrArg (fun f => f h) hcomp.symm

@[simp] theorem homeomorphHomologyEquiv_toLinearMap (e : X ≃ₜ Y) :
    (homeomorphHomologyEquiv e).toLinearMap = inducedHomology (e : C(X, Y)) := rfl

@[simp] theorem homeomorphHomologyEquiv_apply (e : X ≃ₜ Y) (h : SingularH1 X) :
    homeomorphHomologyEquiv e h = inducedHomology (e : C(X, Y)) h := rfl

@[simp] theorem homeomorphHomologyEquiv_symm_apply (e : X ≃ₜ Y) (h : SingularH1 Y) :
    (homeomorphHomologyEquiv e).symm h = inducedHomology (e.symm : C(Y, X)) h := rfl

@[simp] theorem homeomorphHomologyEquiv_symm (e : X ≃ₜ Y) :
    (homeomorphHomologyEquiv e).symm = homeomorphHomologyEquiv e.symm := by
  ext h
  rfl

end FirstHurewicz

end Wikipedia.HopfProblem
