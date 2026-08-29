/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.NondegenerateHammockClosure

/-!
# Nondegenerate hammock closure at an omega union

For an increasing sequence of carriers, every finite eligible endpoint pair
already occurs together at one finite stage.  Thus a filtered hammock closure
step whose witnesses are put into the next carrier survives at the omega
union.  This is the form used by dynamic closure constructions: endpoint
pairs which become eligible later are not required to have been selected at
the initial stage.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {innerRoof outerRoof : Set V} {rho : Cardinal.{u}}

/-- A one-step filtered closure along an increasing omega sequence is a
filtered closure of its union.  In the step hypothesis the eligible pair is
read in `X n`, while the selected hammock is allowed to be placed in
`X (n + 1)`. -/
theorem nondegenerateHammockClosedUpTo_iUnion_of_step
    (X : ℕ → Set V) (hmono : Monotone X)
    (hstep : ∀ n, NondegenerateHammockClosedUpTo Gamma Y (X (n + 1))
      (X n) innerRoof outerRoof rho) :
    NondegenerateHammockClosedUpTo Gamma Y (⋃ n, X n) (⋃ n, X n)
      innerRoof outerRoof rho := by
  intro u e heligible
  obtain ⟨nu, hu⟩ := Set.mem_iUnion.1 heligible.1.1
  cases e with
  | infinity =>
      have hstage : HammockEligible (X nu) innerRoof outerRoof u .infinity :=
        ⟨⟨hu, heligible.1.2⟩, trivial⟩
      obtain ⟨H, hH, hcontained⟩ := hstep nu u .infinity hstage
      refine ⟨H, hH, ?_⟩
      intro x hx
      exact Set.mem_iUnion.2 ⟨nu + 1, hcontained hx⟩
  | vertex v =>
      obtain ⟨nv, hv⟩ := Set.mem_iUnion.1 heligible.2.1
      let n := max nu nv
      have hu' : u ∈ X n := hmono (Nat.le_max_left nu nv) hu
      have hv' : v ∈ X n := hmono (Nat.le_max_right nu nv) hv
      have hstage : HammockEligible (X n) innerRoof outerRoof u (.vertex v) :=
        ⟨⟨hu', heligible.1.2⟩, ⟨hv', heligible.2.2⟩⟩
      obtain ⟨H, hH, hcontained⟩ := hstep n u (.vertex v) hstage
      refine ⟨H, hH, ?_⟩
      intro x hx
      exact Set.mem_iUnion.2 ⟨n + 1, hcontained hx⟩

/-- In particular, filtered closure of every member of an increasing omega
sequence is preserved by its union. -/
theorem nondegenerateHammockClosedUpTo_iUnion_of_monotone
    (X : ℕ → Set V) (hmono : Monotone X)
    (hclosed : ∀ n, NondegenerateHammockClosedUpTo Gamma Y (X n) (X n)
      innerRoof outerRoof rho) :
    NondegenerateHammockClosedUpTo Gamma Y (⋃ n, X n) (⋃ n, X n)
      innerRoof outerRoof rho := by
  apply nondegenerateHammockClosedUpTo_iUnion_of_step X hmono
  intro n u e heligible
  obtain ⟨H, hH, hcontained⟩ := hclosed n u e heligible
  refine ⟨H, hH, ?_⟩
  intro x hx
  exact hmono (Nat.le_succ n) (hcontained hx)

#print axioms nondegenerateHammockClosedUpTo_iUnion_of_step
#print axioms nondegenerateHammockClosedUpTo_iUnion_of_monotone

end Erdos599.Blueprint
