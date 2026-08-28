import Wikipedia.HopfProblem.RiemannMappingExistence
import Wikipedia.HopfProblem.RiemannMappingBiholomorph

/-!
# The actual normalized Riemann biholomorphism

Every nonempty simply connected proper open complex domain is
biholomorphic to the actual unit disc.  Both manifolds use their
inherited open-set complex charts.  The inverse is proved analytic by
the inverse function theorem, using the everywhere nonzero derivative
established in the extremal construction.

The existence proof is adapted from Yury Kudryashov's Apache-2.0 proof
in mathlib4 PR #33505; the adapted proof files retain its attribution.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.RiemannMapping

/-- The actual open unit disc in the complex plane. -/
def unitDisc : TopologicalSpace.Opens ℂ := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩

def discZero : unitDisc := ⟨0, by simp [unitDisc]⟩

variable (U : TopologicalSpace.Opens ℂ) (hUc : IsSimplyConnected (U : Set ℂ))
    (hU : (U : Set ℂ) ≠ univ) (x₀ : U)

/-- The actual function supplied by the compact extremal construction. -/
def riemannMap : ℂ → ℂ :=
  (exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero U.isOpen hUc hU x₀.property).choose

theorem riemannMap_spec :
    DifferentiableOn ℂ (riemannMap U hUc hU x₀) (U : Set ℂ) ∧
      BijOn (riemannMap U hUc hU x₀) (U : Set ℂ) (unitDisc : Set ℂ) ∧
      (∀ z ∈ U, deriv (riemannMap U hUc hU x₀) z ≠ 0) ∧
      riemannMap U hUc hU x₀ x₀ = 0 :=
  (exists_bijOn_unitBall_deriv_ne_zero_map_eq_zero U.isOpen hUc hU x₀.property).choose_spec

/-- **Riemann mapping theorem**, as an actual analytic diffeomorphism
of the two inherited open-set complex manifolds. -/
def biholomorphUnitDisc :
    Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U unitDisc ω :=
  biholomorphOfBijOn U unitDisc (riemannMap U hUc hU x₀)
    (riemannMap_spec U hUc hU x₀).1 (riemannMap_spec U hUc hU x₀).2.1
    (riemannMap_spec U hUc hU x₀).2.2.1

@[simp] theorem biholomorphUnitDisc_apply_coe (z : U) :
    (biholomorphUnitDisc U hUc hU x₀ z : ℂ) = riemannMap U hUc hU x₀ z := rfl

@[simp] theorem biholomorphUnitDisc_basepoint :
    biholomorphUnitDisc U hUc hU x₀ x₀ = discZero := by
  apply Subtype.ext
  exact (riemannMap_spec U hUc hU x₀).2.2.2

theorem biholomorphUnitDisc_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (biholomorphUnitDisc U hUc hU x₀) :=
  (biholomorphUnitDisc U hUc hU x₀).contMDiff_toFun

theorem biholomorphUnitDisc_symm_holomorphic :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (biholomorphUnitDisc U hUc hU x₀).symm :=
  (biholomorphUnitDisc U hUc hU x₀).contMDiff_invFun

include hUc hU in
/-- The normalization can be imposed at any chosen point of the domain. -/
theorem exists_normalized_biholomorph :
    ∃ e : Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U unitDisc ω,
      e x₀ = discZero :=
  ⟨biholomorphUnitDisc U hUc hU x₀, biholomorphUnitDisc_basepoint U hUc hU x₀⟩

include hUc hU in
/-- No base point needs to be supplied for the usual existence statement. -/
theorem exists_biholomorph_unitDisc :
    Nonempty (Diffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) U unitDisc ω) := by
  obtain ⟨z, hz⟩ := hUc.nonempty
  exact ⟨biholomorphUnitDisc U hUc hU ⟨z, hz⟩⟩

end Wikipedia.HopfProblem.RiemannMapping
