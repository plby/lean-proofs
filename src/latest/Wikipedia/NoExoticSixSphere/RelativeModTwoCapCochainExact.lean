import Wikipedia.NoExoticSixSphere.RelativeModTwoCapHomology

/-!
# Relative cochain boundaries act trivially on cap homology

The actual relative cap boundary formula supplies a primitive for cap
with an incoming relative coboundary. Additivity is proved on actual
relative cycle representatives.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (U : Set X)

/-- Actual cohomology of the relative integral-chain dual. -/
abbrev Cohomology (p : ℕ) := (complex U).homology p

/-- The original kernel of the relative coboundary. -/
abbrev Cocycle (p : ℕ) := SingularCohomologyFree.Cocycle (complex U) p

theorem cocycle_coboundary_zero (p : ℕ) (α : Cocycle U p) : coboundary U α.val = 0 :=
  SingularCohomologyFree.cocycle_condition (complex U) p α

end NoExoticSixSphere.RelativeModTwoCochains

namespace NoExoticSixSphere.RelativeModTwoCap

open ModTwoCapProduct (Coefficient)
open RelativeModTwoCochains (Cochain coboundary)

variable {X : Type} [TopologicalSpace X] (U : Set X)

theorem homologyCap_zero (p q : ℕ) (h0 : coboundary U (0 : Cochain U p) = 0) :
    homologyCap U p q (0 : Cochain U p) h0 = 0 := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext
    (RelativeCoefficients.complex Coefficient U) (p + q)
  intro c
  rw [homologyCap_cycleClass, LinearMap.zero_apply]
  have he : capCycles U p q (0 : Cochain U p) h0 c = 0 := by
    apply Subtype.ext
    change capInDegree U (p := p) (q := q) rfl (0 : Cochain U p) c.val = 0
    rw [capInDegree_zero, LinearMap.zero_apply]
  rw [he, map_zero]

theorem homologyCap_add (p q : ℕ) (α β : Cochain U p)
    (hα : coboundary U α = 0) (hβ : coboundary U β = 0)
    (hαβ : coboundary U (α + β) = 0) :
    homologyCap U p q (α + β) hαβ = homologyCap U p q α hα + homologyCap U p q β hβ := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext
    (RelativeCoefficients.complex Coefficient U) (p + q)
  intro c
  rw [homologyCap_cycleClass, LinearMap.add_apply,
    homologyCap_cycleClass, homologyCap_cycleClass]
  have he : capCycles U p q (α + β) hαβ c =
      capCycles U p q α hα c + capCycles U p q β hβ c := by
    apply Subtype.ext
    exact LinearMap.congr_fun (capInDegree_add U (p := p) (q := q) rfl α β) c.val
  exact (congrArg (ModuleHomology.cycleClass (modComplex 2 X) q) he).trans (map_add _ _ _)

/-- Cap with a relative coboundary has an explicit absolute boundary primitive. -/
theorem homologyCap_coboundary (p q : ℕ) (β : Cochain U p) :
    homologyCap U (p + 1) q (coboundary U β)
      (RelativeModTwoCochains.coboundary_squared U p β) = 0 := by
  apply PeriodTorusHigherHomology.homologyLinearMap_ext
    (RelativeCoefficients.complex Coefficient U) ((p + 1) + q)
  intro c
  rw [homologyCap_cycleClass, LinearMap.zero_apply]
  apply (ModuleHomology.cycleClass_eq_zero_iff (modComplex 2 X) q _).mpr
  refine ⟨capInDegree U (p := p) (q := q + 1) (n := (p + 1) + q) (by omega) β c.val, ?_⟩
  have hc := ModuleHomology.cycle_condition
    (RelativeCoefficients.complex Coefficient U) ((p + 1) + q) c
  rw [show ((p + 1) + q) - 1 = p + q by omega] at hc
  have he := boundary_capInDegree U (p := p) (q := q) (n := (p + 1) + q) (by omega) β c.val
  rw [hc, map_zero, zero_add] at he
  exact he

end NoExoticSixSphere.RelativeModTwoCap
