/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CardinalInduction

/-!
# Audit of the direct lower-cardinal shortcut in the regular extension step

The universal induction hypothesis below `κ` immediately links every
unhindered auxiliary web whose *whole source* has cardinality below `κ`.
This useful reduction does not by itself prove the extension clause at `κ`:
an extension instance contains a designated source set of cardinality
exactly `κ`, so the source of that web cannot have cardinality below `κ`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-- The exact direct consequence of the lower-cardinal induction hypothesis:
an unhindered web with fewer than `κ` sources is linkable. -/
theorem linkable_of_universalCardinalInductionBelow_of_source_lt
    {κ : Cardinal.{u}} (hlower : UniversalCardinalInductionBelow V κ)
    (Γ : DWeb V) (hΓ : Γ.IsUnhindered) (hsource : #Γ.source < κ) :
    IsLinkable Γ := by
  exact linkable_of_cardinalInductionAt_source Γ
    (hlower #Γ.source hsource Γ hΓ)

/-- A designated set of `κ` sources forces the whole source to have
cardinality at least `κ`. -/
theorem cardinal_le_source_of_designated
    {Γ : DWeb V} {A₀ : Set V} {κ : Cardinal.{u}}
    (hA₀ : A₀ ⊆ Γ.source) (hcard : #A₀ = κ) :
    κ ≤ #Γ.source := by
  rw [← hcard]
  exact Cardinal.mk_subtype_mono hA₀

/-- Consequently the direct small-source consequence of the lower induction
hypothesis is unavailable in an extension-clause instance at `κ`. -/
theorem source_not_lt_of_designated
    {Γ : DWeb V} {A₀ : Set V} {κ : Cardinal.{u}}
    (hA₀ : A₀ ⊆ Γ.source) (hcard : #A₀ = κ) :
    ¬ #Γ.source < κ := by
  exact not_lt_of_ge (cardinal_le_source_of_designated hA₀ hcard)

/-- At every *infinite* strictly smaller cardinal, the lower induction
hypothesis exposes both simultaneous clauses.  At finite cardinals only the
extension clause belongs to the source-faithful induction assertion; finite
sets are handled directly by the safe-link construction. -/
theorem lower_extension_and_halfway
    {κ μ : Cardinal.{u}} (hlower : UniversalCardinalInductionBelow V κ)
    (hμ : μ < κ) (hμinf : ℵ₀ ≤ μ) (Γ : DWeb V) (hΓ : Γ.IsUnhindered) :
    ExtensionClauseAt Γ μ ∧ HalfwayClauseAt Γ μ := by
  have hstep := hlower μ hμ Γ hΓ
  exact ⟨hstep.extension, hstep.halfway hμinf⟩

end CardinalInduction
end Erdos599
