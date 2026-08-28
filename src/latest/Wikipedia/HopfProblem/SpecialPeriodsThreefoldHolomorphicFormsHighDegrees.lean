import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsRegularCover
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsDegree

/-!
# Actual holomorphic forms above degree three

The original tangent model has its explicit three-element complex
basis. Thus its genuine alternating cotangent sections in higher
degrees vanish, without a global-topology or cohomology hypothesis.
-/

noncomputable section

open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms

open HolomorphicDifferentialForms (Form)
open RegularCover (Model)

attribute [local instance] chartedSpace space_isManifold

theorem form_eq_zero_of_three_lt {p : ℕ} (hp : 3 < p)
    (θ : Form Model Threefold.Space p) : θ = 0 :=
  HolomorphicDifferentialForms.form_eq_zero_of_basis_card_lt
    HolomorphicDifferentialForms.Coordinates.basis hp θ

theorem forms_subsingleton_of_three_lt {p : ℕ} (hp : 3 < p) :
    Subsingleton (Form Model Threefold.Space p) :=
  ⟨fun θ η => (form_eq_zero_of_three_lt hp θ).trans
    (form_eq_zero_of_three_lt hp η).symm⟩

theorem forms_finrank_of_three_lt {p : ℕ} (hp : 3 < p) :
    Module.finrank ℂ (Form Model Threefold.Space p) = 0 := by
  let := forms_subsingleton_of_three_lt hp
  exact Module.finrank_zero_of_subsingleton

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms
