/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularRetargetedFixedPoint

/-!
# Registered master rows in the singular fixed-point construction

The unconditional two-pass construction first chooses a family of generator
rows, closes the singular source layers under their competitors, and only
then chooses master rows linking the closed layers.  A newly chosen master
row need not preserve the generator closure.

There is, however, one exact positive case: if every master path was already
registered in the union of the generator rows, then monotonicity of
`competitorClosure` transfers the first-pass closure certificate to the
master family.  This file packages that admissibility criterion and converts
such a registered two-pass family to the constant-row machine.

The existence of a registered selection is deliberately not asserted here.
It is the substantive simultaneous selection problem: choosing fresh master
rows and registering them only afterwards would change the closure again.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularRegisteredMasterRows

open SingularExtension SingularMatrix SingularClosedTargetRows
  SingularRetargetedFixedPoint

universe u

variable {V : Type u}
variable {G : DWeb V} {fixed : Set G.DPath}
variable {A₀ : Set V} {kappa : Cardinal.{u}}
variable {huncountable : aleph0 < kappa} {hsingular : kappa.IsSingular}
variable {hcard : #A₀ = kappa}

/-- A master family is registered when each of its paths already occurs in
one of the rows used to form the first-pass competitor closure. -/
def Registered
    (R : TwoPassRows G fixed A₀ kappa
      huncountable hsingular hcard) : Prop :=
  ∀ j, R.paths j ⊆ ⋃ i, R.generators i

namespace TwoPassRows

/-- Registered provenance makes the master family a subfamily of the
first-pass family, even after adjoining the fixed linkage. -/
theorem masterFamily_subset_generatorFamily
    (R : TwoPassRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (hregistered : Registered R) :
    fixed ∪ ⋃ j, R.paths j ⊆ fixed ∪ ⋃ i, R.generators i := by
  intro p hp
  rcases hp with hpFixed | hpMaster
  · exact Or.inl hpFixed
  · obtain ⟨j, hpj⟩ := Set.mem_iUnion.1 hpMaster
    exact Or.inr (hregistered j hpj)

/-- The first-pass omega closures are also closed under any registered
master family.  This is the precise monotonicity bridge missing for fresh
post-closure master rows. -/
theorem masterClosed_of_registered
    (R : TwoPassRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (hregistered : Registered R) (i : Index kappa) :
    G.competitorClosure (fixed ∪ ⋃ j, R.paths j) (R.sources i) ⊆
      R.sources i := by
  exact (G.competitorClosure_mono_paths
    (masterFamily_subset_generatorFamily R hregistered)).trans
      (R.generators_closed i)

/-- A registered two-pass family is a jointly competitor-closed family of
constant rows. -/
noncomputable def toClosedRows_of_registered
    (R : TwoPassRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (hregistered : Registered R) :
    ClosedRows G fixed A₀ kappa huncountable hsingular hcard :=
  R.toClosedRows (masterClosed_of_registered R hregistered)

/-- Repeating registered masters at every finite stage gives the target-row
matrix consumed by the singular extension argument. -/
noncomputable def toTargetRows_of_registered
    (R : TwoPassRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (hregistered : Registered R) :
    TargetRows G fixed A₀ kappa huncountable hsingular hcard :=
  (toClosedRows_of_registered R hregistered).toTargetRows

/-- With the usual fixed complementary linkage, registered master rows
already imply linkability of the ambient web. -/
theorem isLinkable_of_registered
    (R : TwoPassRows G fixed A₀ kappa
      huncountable hsingular hcard)
    (hregistered : Registered R)
    (hA₀ : A₀ ⊆ G.source)
    (hfixed : IsLinkageBetween G (G.source \ A₀) G.target fixed) :
    IsLinkable G := by
  exact SingularExtension.isLinkable_of_targetRows
    (toTargetRows_of_registered R hregistered) hA₀ hfixed

end TwoPassRows

#print axioms TwoPassRows.masterClosed_of_registered
#print axioms TwoPassRows.toTargetRows_of_registered
#print axioms TwoPassRows.isLinkable_of_registered

end SingularRegisteredMasterRows
end CardinalInduction
end Erdos599
