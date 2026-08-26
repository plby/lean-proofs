import ErdosProblems.Erdos593.TripleSystem.ObligatoryDisjointUnion
import Mathlib.SetTheory.Cardinal.Order

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Cardinal-minimal bad triple-system cores

This module isolates the cardinal-minimal-counterexample consequence needed
for the positive-atom theorem.  It deliberately does not attempt the global
colouring or the remaining closure/layering construction.
-/

namespace Erdos593

open scoped Cardinal

universe u v

namespace TripleSystem

/-- `AtomFreeUncountablyChromaticCard F κ` says that there is a triple system
on a carrier of cardinality `κ` which is uncountably chromatic and avoids the
fixed atom `F` as a non-induced subconfiguration.  The witnesses remain in the
fixed universes, so the cardinal minimisation below is universe-local. -/
def AtomFreeUncountablyChromaticCard
    {A : Type u} {E : Type v} (F : TripleSystem A E) (κ : Cardinal.{u}) : Prop :=
  ∃ (W : Type u) (D : Type v) (H : TripleSystem W D),
    Cardinal.mk W = κ ∧
      ℵ₀ < H.chromaticCardinal ∧
        ¬ F.Appears H

/-- Select the least vertex cardinality of an uncountably chromatic triple
system which avoids a fixed atom.  This is cardinal minimisation, not
minimisation under subconfiguration inclusion. -/
theorem exists_minimalAtomFreeUncountablyChromaticCard
    {A : Type u} {E : Type v} (F : TripleSystem A E)
    (h : ∃ κ : Cardinal.{u}, AtomFreeUncountablyChromaticCard F κ) :
    ∃ κ : Cardinal.{u},
      AtomFreeUncountablyChromaticCard F κ ∧
        ∀ κ' : Cardinal.{u}, κ' < κ →
          ¬ AtomFreeUncountablyChromaticCard F κ' := by
  rcases h with ⟨κ₀, hκ₀⟩
  let B : Set Cardinal.{u} := fun κ => AtomFreeUncountablyChromaticCard F κ
  have hB : B.Nonempty := ⟨κ₀, hκ₀⟩
  let κ := Cardinal.lt_wf.min B hB
  refine ⟨κ, Cardinal.lt_wf.min_mem B hB, ?_⟩
  intro κ' hκ' hbad
  exact (Cardinal.lt_wf.not_lt_min B hbad) hκ'

/-- A triple system is locally countably chromatic below its vertex cardinal
when every restriction to a strictly smaller carrier has chromatic cardinal at
most `ℵ₀`. -/
def LocallyCountablyChromaticBelow {W : Type u} {D : Type v}
    (H : TripleSystem W D) : Prop :=
  ∀ S : Set W, Cardinal.mk S < Cardinal.mk W →
    (H.vertexRestriction S).chromaticCardinal ≤ ℵ₀

/-- Cardinal minimality of an uncountably chromatic atom-free triple system
makes every restriction to a strictly smaller carrier countably chromatic. -/
theorem locallyCountablyChromaticBelow_of_minimalBad
    {A : Type u} {E : Type v} (F : TripleSystem A E)
    {W : Type u} {D : Type v} (H : TripleSystem W D)
    {κ : Cardinal.{u}}
    (hcard : Cardinal.mk W = κ)
    (hfree : ¬ F.Appears H)
    (hmin : ∀ κ' : Cardinal.{u}, κ' < κ →
      ¬ AtomFreeUncountablyChromaticCard F κ') :
    LocallyCountablyChromaticBelow H := by
  intro S hS
  apply le_of_not_gt
  intro hunc
  apply hmin (Cardinal.mk S) (by simpa [hcard] using! hS)
  unfold AtomFreeUncountablyChromaticCard
  refine ⟨(S : Type u), H.RestrictedEdge S, H.vertexRestriction S, rfl, hunc, ?_⟩
  intro happ
  exact hfree (Appears.trans F happ
    (Nonempty.intro (H.vertexRestrictionEmbedding S)))

end TripleSystem

end Erdos593
