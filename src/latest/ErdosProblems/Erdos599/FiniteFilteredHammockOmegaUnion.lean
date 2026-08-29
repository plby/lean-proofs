/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FilteredNondegenerateHammockClosure

/-!
# Finite filtered hammock closure at an omega union

The two endpoints of a finite shortcut occur together at one stage of an
increasing omega sequence.  Consequently a filtered closure step which puts
its selected family into the next stage remains a filtered closure at the
union.  The path filter is fixed throughout the sequence.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {innerRoof outerRoof : Set V} {rho : Cardinal.{u}}
variable {P : AltPath Gamma.graph → Prop}

theorem finiteFilteredHammockClosedUpTo_iUnion_of_step
    (X : ℕ → Set V) (hmono : Monotone X)
    (hstep : ∀ n, FiniteFilteredHammockClosedUpTo Gamma Y (X (n + 1))
      (X n) innerRoof outerRoof P rho) :
    FiniteFilteredHammockClosedUpTo Gamma Y (⋃ n, X n) (⋃ n, X n)
      innerRoof outerRoof P rho := by
  intro u v hne heligible
  obtain ⟨nu, hu⟩ := Set.mem_iUnion.1 heligible.1.1
  obtain ⟨nv, hv⟩ := Set.mem_iUnion.1 heligible.2.1
  let n := max nu nv
  have hu' : u ∈ X n := hmono (Nat.le_max_left nu nv) hu
  have hv' : v ∈ X n := hmono (Nat.le_max_right nu nv) hv
  have hstage : HammockEligible (X n) innerRoof outerRoof u (.vertex v) :=
    ⟨⟨hu', heligible.1.2⟩, ⟨hv', heligible.2.2⟩⟩
  obtain ⟨H, hH, hcontained⟩ := hstep n u v hne hstage
  refine ⟨H, hH, ?_⟩
  intro x hx
  exact Set.mem_iUnion.2 ⟨n + 1, hcontained hx⟩

theorem finiteFilteredHammockClosedUpTo_iUnion_of_monotone
    (X : ℕ → Set V) (hmono : Monotone X)
    (hclosed : ∀ n, FiniteFilteredHammockClosedUpTo Gamma Y (X n) (X n)
      innerRoof outerRoof P rho) :
    FiniteFilteredHammockClosedUpTo Gamma Y (⋃ n, X n) (⋃ n, X n)
      innerRoof outerRoof P rho := by
  apply finiteFilteredHammockClosedUpTo_iUnion_of_step X hmono
  intro n u v hne heligible
  obtain ⟨H, hH, hcontained⟩ := hclosed n u v hne heligible
  refine ⟨H, hH, ?_⟩
  intro x hx
  exact hmono (Nat.le_succ n) (hcontained hx)

#print axioms finiteFilteredHammockClosedUpTo_iUnion_of_step
#print axioms finiteFilteredHammockClosedUpTo_iUnion_of_monotone

end Erdos599.Blueprint
