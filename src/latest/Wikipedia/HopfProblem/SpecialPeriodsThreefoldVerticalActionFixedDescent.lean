import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.Connected

/-!
# A continuous fixed orbit lifts to a fixed point

A local homeomorphism has discrete fibres.  A continuous map from a
preconnected space into one fibre is therefore constant.  In particular,
an actual continuous complex-time orbit whose projection is fixed cannot
move between different covering representatives.  No separation or
covering-lift uniqueness hypothesis is required.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedDescent

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B] {q : E → B}

/-- The actual fibres of a local homeomorphism have their discrete
subspace topology, without any Hausdorff assumption on either space. -/
theorem fibre_discrete (hq : IsLocalHomeomorph q) (b : B) :
    DiscreteTopology (q ⁻¹' {b}) := by
  have hs : (q '' (q ⁻¹' {b})).Subsingleton := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (show q x = b from hx).trans (show q y = b from hy).symm
  exact (hq.isLocalHomeomorphOn.isDiscrete_of_image hs.isDiscrete).to_subtype

/-- A continuous map from a preconnected parameter space, contained in
one actual fibre, is determined by its value at one parameter. -/
theorem eq_const_of_preconnected {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    {c : T → E} {t₀ : T} {x : E} (hq : IsLocalHomeomorph q) (hc : Continuous c)
    (h₀ : c t₀ = x) (hf : ∀ t, q (c t) = q x) : ∀ t, c t = x := by
  let := fibre_discrete hq (q x)
  let c' : T → q ⁻¹' {q x} := fun t => ⟨c t, hf t⟩
  have hc' : Continuous c' := hc.subtype_mk _
  intro t
  exact (congrArg Subtype.val
    (TotallyDisconnectedSpace.eq_of_continuous c' hc' t t₀)).trans h₀

/-- A continuous complex-time curve above one fixed quotient point is
the constant curve at its actual initial lift. -/
theorem eq_const_of_isLocalHomeomorph {c : ℂ → E} {x : E}
    (hq : IsLocalHomeomorph q) (hc : Continuous c)
    (h₀ : c 0 = x) (hf : ∀ s : ℂ, q (c s) = q x) : ∀ s : ℂ, c s = x :=
  eq_const_of_preconnected hq hc h₀ hf

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.VerticalAction.FixedDescent
