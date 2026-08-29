/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.BoundarySimultaneousAssignment

/-!
# Ownership of cut contacts by assignment macro orbits

The boundary simultaneous-assignment proof chooses one alternating route in
each rooted macro orbit.  Its ordinary output remembers only injectivity of
finite terminals, but the literal Section 9 transaction needs the stronger
fact that two different rooted orbits cannot own the same contact with the
closing set.

For the outside-fragment family every contact with the closing set is an
endpoint of its fragment.  Boundary alignment then converts a mixed
fragment/reference contact into either a common initial pair or one genuine
macro step.  Warp disjointness consequently identifies the rooted orbits.
The theorem below isolates exactly this argument; no disjointness of the
chosen alternating paths is assumed.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V}
variable {Z Y : Set Gamma.DPath} {X : Set V}

/-- A path in a cut family meets the closing set only at one of its two
displayed endpoints.  Rays therefore can meet it only at their initial
vertex. -/
def CutEndpointPure (Z : Set Gamma.DPath) (X : Set V) : Prop :=
  ∀ p ∈ Z, ∀ x ∈ p.support, x ∈ X →
    p.initial = x ∨ Gamma.terminal? p = some x

/-- Two rooted macro orbits which contain the same forward-family member
have the same root. -/
theorem macroOrbit_roots_eq_of_common_forward
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    {p r : Z} (hpY : p.1.initial ∉ Gamma.vertexSet Y)
    (hrY : r.1.initial ∉ Gamma.vertexSet Y)
    {q s : Gamma.DPath}
    (hqp : q ∈ macroOrbit Z Y p) (hsr : s ∈ macroOrbit Z Y r)
    {x : V} (hxq : x ∈ q.support) (hxs : x ∈ s.support) : p = r := by
  have hqZ : q ∈ Z := macroOrbit_subset Z Y p hqp
  have hsZ : s ∈ Z := macroOrbit_subset Z Y r hsr
  have hqs : q = s :=
    DWeb.IsWarp.eq_of_mem_support hZ hqZ hsZ hxq hxs
  subst s
  exact macroOrbit_roots_eq_of_common hZ hY hpY hrY hqp hsr

/-- Two rooted macro orbits whose reference subwarps share a member have the
same root. -/
theorem macroOrbit_roots_eq_of_common_reference
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    {p r : Z} (hpY : p.1.initial ∉ Gamma.vertexSet Y)
    (hrY : r.1.initial ∉ Gamma.vertexSet Y)
    {q s : Gamma.DPath}
    (hqp : q ∈ macroReference Z Y p)
    (hsr : s ∈ macroReference Z Y r)
    {x : V} (hxq : x ∈ q.support) (hxs : x ∈ s.support) : p = r := by
  have hqs : q = s :=
    DWeb.IsWarp.eq_of_mem_support hY hqp.1 hsr.1 hxq hxs
  subst s
  obtain ⟨a, hap, hainit⟩ := hqp.2
  obtain ⟨b, hbr, hbinit⟩ := hsr.2
  have hab : a = b := by
    apply DWeb.IsWarp.eq_of_mem_support hZ
      (macroOrbit_subset Z Y p hap) (macroOrbit_subset Z Y r hbr)
    · exact a.initial_mem_support
    · have habinit : a.initial = b.initial := hainit.trans hbinit.symm
      exact habinit ▸ b.initial_mem_support
  subst b
  exact macroOrbit_roots_eq_of_common hZ hY hpY hrY hap hbr

/-- A forward member of one rooted orbit and a reference member of another
cannot meet at a cut vertex unless the roots agree. -/
theorem macroOrbit_roots_eq_of_forward_reference_cut_contact
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hboundary : BoundaryAligned Z Y)
    (hcut : CutEndpointPure Z X)
    {p r : Z} (hpY : p.1.initial ∉ Gamma.vertexSet Y)
    (hrY : r.1.initial ∉ Gamma.vertexSet Y)
    {q y : Gamma.DPath}
    (hqp : q ∈ macroOrbit Z Y p)
    (hyr : y ∈ macroReference Z Y r)
    {x : V} (hxq : x ∈ q.support) (hxy : x ∈ y.support)
    (hxX : x ∈ X) : p = r := by
  have hqZ : q ∈ Z := macroOrbit_subset Z Y p hqp
  rcases hcut q hqZ x hxq hxX with hqinitial | hqterminal
  · have hxY : x ∈ Gamma.vertexSet Y := ⟨y, hyr.1, hxy⟩
    obtain ⟨y', hy'Y, hy'initial⟩ :=
      hboundary.1 ⟨⟨q, hqZ, hqinitial⟩, hxY⟩
    have hy'eq : y' = y := by
      apply DWeb.IsWarp.eq_of_mem_support hY hy'Y hyr.1
      · exact hy'initial ▸ y'.initial_mem_support
      · exact hxy
    subst y'
    obtain ⟨s, hsr, hsinitial⟩ := hyr.2
    have hqs : q = s := by
      apply DWeb.IsWarp.eq_of_mem_support hZ hqZ
        (macroOrbit_subset Z Y r hsr)
      · exact hxq
      · have hsx : s.initial = x := hsinitial.trans hy'initial
        exact hsx ▸ s.initial_mem_support
    subst s
    exact macroOrbit_roots_eq_of_common hZ hY hpY hrY hqp hsr
  · have hxY : x ∈ Gamma.vertexSet Y := ⟨y, hyr.1, hxy⟩
    obtain ⟨y', hy'Y, hy'terminal⟩ :=
      hboundary.2 ⟨⟨q, hqZ, hqterminal⟩, hxY⟩
    have hy'eq : y' = y := by
      apply DWeb.IsWarp.eq_of_mem_support hY hy'Y hyr.1
      · exact Gamma.terminal_mem_support hy'terminal
      · exact hxy
    subst y'
    obtain ⟨s, hsr, hsinitial⟩ := hyr.2
    have hstep : AssignmentMacroStep Z Y ⟨q, hqZ⟩
        ⟨s, macroOrbit_subset Z Y r hsr⟩ := by
      exact ⟨⟨y, hyr.1⟩, x, hqterminal, hy'terminal, hsinitial.symm⟩
    have hsp : s ∈ macroOrbit Z Y p := by
      exact mem_macroOrbit_of_step (p := p) (r := ⟨q, hqZ⟩)
        (s := ⟨s, macroOrbit_subset Z Y r hsr⟩) hqp hstep
    exact macroOrbit_roots_eq_of_common hZ hY hpY hrY hsp hsr

/-- The symmetric mixed-contact case. -/
theorem macroOrbit_roots_eq_of_reference_forward_cut_contact
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hboundary : BoundaryAligned Z Y)
    (hcut : CutEndpointPure Z X)
    {p r : Z} (hpY : p.1.initial ∉ Gamma.vertexSet Y)
    (hrY : r.1.initial ∉ Gamma.vertexSet Y)
    {y q : Gamma.DPath}
    (hyp : y ∈ macroReference Z Y p)
    (hqr : q ∈ macroOrbit Z Y r)
    {x : V} (hxy : x ∈ y.support) (hxq : x ∈ q.support)
    (hxX : x ∈ X) : p = r := by
  exact (macroOrbit_roots_eq_of_forward_reference_cut_contact hZ hY
    hboundary hcut hrY hpY hqr hyp hxq hxy hxX).symm

/-- A cut contact determines the root even when each owner is known only to
be a forward macro member or a member of its reference subwarp. -/
theorem macroOrbit_roots_eq_of_cut_contact
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hboundary : BoundaryAligned Z Y)
    (hcut : CutEndpointPure Z X)
    {p r : Z} (hpY : p.1.initial ∉ Gamma.vertexSet Y)
    (hrY : r.1.initial ∉ Gamma.vertexSet Y)
    {a b : Gamma.DPath}
    (hap : a ∈ macroOrbit Z Y p ∨ a ∈ macroReference Z Y p)
    (hbr : b ∈ macroOrbit Z Y r ∨ b ∈ macroReference Z Y r)
    {x : V} (hxa : x ∈ a.support) (hxb : x ∈ b.support)
    (hxX : x ∈ X) : p = r := by
  rcases hap with hap | hap <;> rcases hbr with hbr | hbr
  · exact macroOrbit_roots_eq_of_common_forward hZ hY hpY hrY
      hap hbr hxa hxb
  · exact macroOrbit_roots_eq_of_forward_reference_cut_contact hZ hY
      hboundary hcut hpY hrY hap hbr hxa hxb hxX
  · exact macroOrbit_roots_eq_of_reference_forward_cut_contact hZ hY
      hboundary hcut hpY hrY hap hbr hxa hxb hxX
  · exact macroOrbit_roots_eq_of_common_reference hZ hY hpY hrY
      hap hbr hxa hxb

/-! ## Contact ownership for the selected simultaneous family -/

/-- The vertices at which one macro-owned selected route meets the closing
set.  Keeping this definition separate from the eventual path splitter makes
the ownership argument independent of whether the selected route is finite or
infinite. -/
def MacroOwnedBracketSimultaneousAssignment.contactSet
    (A : MacroOwnedBracketSimultaneousAssignment Z Y) (X : Set V)
    (z : {x : V // x ∈ Gamma.initialSet Z \ Gamma.initialSet Y}) : Set V :=
  (A.assigned z).vertexSet ∩ X

/-- Different rooted macro orbits cannot own the same closing-set contact.

This is the family-level form needed by the contact splitter.  It is stronger
than injectivity of the final endpoint map: the common vertex may occur
anywhere along either alternating route.  The proof first recovers one
forward-or-reference owner in each rooted macro orbit, applies
`macroOrbit_roots_eq_of_cut_contact`, and finally converts equality of the
distinguished root paths back to equality of the selected sources. -/
theorem MacroOwnedBracketSimultaneousAssignment.contactSet_pairwiseDisjoint
    (hZ : Gamma.IsWarp Z) (hY : Gamma.IsWarp Y)
    (hboundary : BoundaryAligned Z Y)
    (hcut : CutEndpointPure Z X)
    (A : MacroOwnedBracketSimultaneousAssignment Z Y) :
    ∀ s t, s ≠ t → Disjoint (A.contactSet X s) (A.contactSet X t) := by
  intro s t hst
  rw [Set.disjoint_left]
  intro x hxs hxt
  obtain ⟨q, hqOwner, hxq⟩ := A.vertex_owner s x hxs.1
  obtain ⟨r, hrOwner, hxr⟩ := A.vertex_owner t x hxt.1
  have hsOutside :
      (initialPath Z ⟨s.1, s.property.1⟩).1.initial ∉
        Gamma.vertexSet Y := by
    rw [initialPath_initial]
    exact hboundary.initial_outside s.property
  have htOutside :
      (initialPath Z ⟨t.1, t.property.1⟩).1.initial ∉
        Gamma.vertexSet Y := by
    rw [initialPath_initial]
    exact hboundary.initial_outside t.property
  have hroot := macroOrbit_roots_eq_of_cut_contact hZ hY hboundary hcut
    hsOutside htOutside hqOwner hrOwner hxq hxr hxs.2
  apply hst
  apply Subtype.ext
  calc
    s.1 = (initialPath Z ⟨s.1, s.property.1⟩).1.initial :=
      (initialPath_initial Z ⟨s.1, s.property.1⟩).symm
    _ = (initialPath Z ⟨t.1, t.property.1⟩).1.initial :=
      congrArg (fun p : Z ↦ p.1.initial) hroot
    _ = t.1 := initialPath_initial Z ⟨t.1, t.property.1⟩

end Alternating
end Erdos599
