import Wikipedia.HopfProblem.DegreeCollapseCommonCutFamily

/-!
# Literal common-cut identifications compose on maps and integral homology

The underlying maps are identities on ambient points. Their induced
homology equivalences compose exactly, so finite native rearrangements
retain one explicit basis transport from the original sublevel.
-/

noncomputable section

open ContinuousMap
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open SingularMayerVietoris PeriodTorusHigherHomology

local notation "S₂" => Hemisphere.Sphere 2

variable {M : Type} [TopologicalSpace M] {f g h : M → ℝ} {a : ℝ}

theorem equalCutSection_refl (γ : C(S₂, {y : M // f y = a})) :
    equalCutSection (fun _ => Iff.rfl) γ = γ := rfl

theorem equalCutSection_trans
    (hfg : ∀ y, g y = a ↔ f y = a) (hgh : ∀ y, h y = a ↔ g y = a)
    (γ : C(S₂, {y : M // f y = a})) :
    equalCutSection hgh (equalCutSection hfg γ) =
      equalCutSection (fun y => (hgh y).trans (hfg y)) γ := rfl

theorem equalCutHomologyEquiv_refl :
    equalCutHomologyEquiv (f := f) (a := a) (fun _ => Iff.rfl) =
      LinearEquiv.refl ℤ (SingularHomology {y : M // f y ≤ a} 2) := by
  apply LinearEquiv.ext
  intro x
  change singularHomologyMap
    (equalCutSublevelHomeomorph (f := f) (a := a) (fun _ => Iff.rfl)).toHomotopyEquiv.toFun 2 x = x
  have hmap : (equalCutSublevelHomeomorph (f := f) (a := a)
      (fun _ => Iff.rfl)).toHomotopyEquiv.toFun = ContinuousMap.id {y : M // f y ≤ a} := rfl
  rw [hmap, singularHomologyMap_id]
  rfl

theorem equalCutHomologyEquiv_trans
    (hfg : ∀ y, g y ≤ a ↔ f y ≤ a) (hgh : ∀ y, h y ≤ a ↔ g y ≤ a) :
    (equalCutHomologyEquiv hfg).trans (equalCutHomologyEquiv hgh) =
      equalCutHomologyEquiv (fun y => (hgh y).trans (hfg y)) := by
  apply LinearEquiv.ext
  intro x
  change singularHomologyMap (equalCutSublevelHomeomorph hgh).toHomotopyEquiv.toFun 2
    (singularHomologyMap (equalCutSublevelHomeomorph hfg).toHomotopyEquiv.toFun 2 x) =
      singularHomologyMap (equalCutSublevelHomeomorph
        (fun y => (hgh y).trans (hfg y))).toHomotopyEquiv.toFun 2 x
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
