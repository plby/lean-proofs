/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeReferenceTransportSemantics
import ErdosProblems.Erdos599.ColouredSafeHammockClosure

/-!
# Native hammock transport to the limiting reference

An actual local native hammock whose complete occurrence carriers lie in one
selected stage roof can be transported route-by-route to the limiting
reference.  The transport is injective and does not change a literal carrier,
so cardinality and pairwise-disjoint interiors are preserved exactly.

Validity depends only on the forward colour and is preserved definitionally.
Exposure at the limiting reference follows by reflecting any roofed limiting
contact to the selected stage.  For the finite nondegenerate filter, finite
switched reachability is reflected by the semantic transport theorem.
-/

noncomputable section

open Set

namespace Erdos599

open Cardinal DirectedPath Alternating Ladder Blueprint
open ColouredSafeReverseReachability

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}
variable {L : Gamma.KappaLadder kappa} {a : Stage kappa}

namespace ColouredSafeReverseReachability.CurrentSafeOccurrence

variable {current Y : Set Gamma.DPath} {s t : V}

/-- A displayed finite endpoint is one of the literal occurrence vertices. -/
theorem terminal_mem_vertexSet
    (A : CurrentSafeOccurrence current Y s)
    (hterminal : A.terminal? = some t) : t ∈ A.vertexSet := by
  cases A with
  | infinite Q hQ hfirst => simp at hterminal
  | finite u Q hQ hfirst hlast =>
      have hut : u = t := Option.some.inj hterminal
      exact ⟨Fin.last Q.length, hlast.trans hut⟩

end ColouredSafeReverseReachability.CurrentSafeOccurrence

namespace ColouredSafeAmbientOccurrence

open DWeb.KappaLadder.Deferred

variable {s : V}

/-- Intrinsic forward-warp validity is unaffected by reference retyping. -/
theorem Valid.retypeLimitReference
    (hL : HalfwayGeometry L)
    {A : Occurrence (L.warpAt a) s}
    (hA : Valid A) (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    Valid (retypeLimitReference hL ⟨A, hRoof⟩) := by
  obtain ⟨W, hW, hWfinite, hforward⟩ := hA
  refine ⟨W, hW, hWfinite, ?_⟩
  simpa only [ColouredSafeAmbientOccurrence.retypeLimitReference,
    ColouredSafeReverseReachability.CurrentSafeOccurrence.retypeLimitReference_forwardEdges]
      using hforward

end ColouredSafeAmbientOccurrence

namespace Blueprint.ColouredSafeHammock.ReferenceTransport

open DWeb.KappaLadder.Deferred
open ColouredSafeAmbientOccurrence ColouredSafeReferenceTransport

variable {s t : V} {e : Option V} {rho : Cardinal.{u}}

/-- The literal image of a local hammock under roof-supported reference
retyping.  Indexing by the actual subtype `H` avoids any choice of inverse. -/
def retypeFamily
    (hL : HalfwayGeometry L)
    (H : Set (Occurrence (L.warpAt a) s))
    (hRoof : ∀ A ∈ H, A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    Set (Occurrence L.limitWarp s) :=
  Set.range (fun A : H ↦
    ColouredSafeAmbientOccurrence.retypeLimitReference hL
      ⟨A.1, hRoof A.1 A.2⟩)

/-- The route map used by `retypeFamily` is injective. -/
theorem retypeMember_injective
    (hL : HalfwayGeometry L)
    (H : Set (Occurrence (L.warpAt a) s))
    (hRoof : ∀ A ∈ H, A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    Function.Injective (fun A : H ↦
      ColouredSafeAmbientOccurrence.retypeLimitReference hL
        ⟨A.1, hRoof A.1 A.2⟩) := by
  intro A B hAB
  have hroofed :=
    ColouredSafeAmbientOccurrence.retypeLimitReference_injective hL hAB
  have hvals : A.1 = B.1 := congrArg
    (fun C : ColouredSafeAmbientOccurrence.RoofSupportedAt L a s ↦ C.1)
    hroofed
  exact Subtype.ext hvals

/-- The transported family has exactly the same cardinality. -/
theorem mk_retypeFamily
    (hL : HalfwayGeometry L)
    (H : Set (Occurrence (L.warpAt a) s))
    (hRoof : ∀ A ∈ H, A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    #(retypeFamily hL H hRoof) = #H := by
  exact Cardinal.mk_range_eq _ (retypeMember_injective hL H hRoof)

/-- Literal carrier union of a native occurrence family. -/
def carrierUnion {Y : Set Gamma.DPath}
    (H : Set (Occurrence Y s)) : Set V :=
  ⋃ A : H, A.1.vertexSet

/-- Retyping preserves the complete union of literal occurrence carriers. -/
theorem carrierUnion_retypeFamily
    (hL : HalfwayGeometry L)
    (H : Set (Occurrence (L.warpAt a) s))
    (hRoof : ∀ A ∈ H, A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    carrierUnion (retypeFamily hL H hRoof) = carrierUnion H := by
  ext x
  constructor
  · intro hx
    obtain ⟨B, hxB⟩ := Set.mem_iUnion.1 hx
    obtain ⟨A, hBA⟩ := B.2
    rw [← hBA] at hxB
    exact Set.mem_iUnion.2 ⟨A, by
      simpa only [ColouredSafeAmbientOccurrence.retypeLimitReference_vertexSet]
        using hxB⟩
  · intro hx
    obtain ⟨A, hxA⟩ := Set.mem_iUnion.1 hx
    let B : retypeFamily hL H hRoof :=
      ⟨ColouredSafeAmbientOccurrence.retypeLimitReference hL
          ⟨A.1, hRoof A.1 A.2⟩,
        ⟨A, rfl⟩⟩
    exact Set.mem_iUnion.2 ⟨B, by
      change x ∈ ColouredSafeReverseReachability.CurrentSafeOccurrence.vertexSet
        (ColouredSafeAmbientOccurrence.retypeLimitReference hL
          ⟨A.1, hRoof A.1 A.2⟩)
      rw [ColouredSafeAmbientOccurrence.retypeLimitReference_vertexSet]
      exact hxA⟩

/-- A roof-supported locally good route remains good after retyping, provided
its additional filter is preserved. -/
theorem mem_goodRoutes_retypeLimitReference
    (hL : HalfwayGeometry L)
    {extraLocal : Occurrence (L.warpAt a) s → Prop}
    {extraGlobal : Occurrence L.limitWarp s → Prop}
    {A : Occurrence (L.warpAt a) s}
    (hRoof : A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hgood : A ∈ ColouredSafeHammock.goodRoutes
      (L.warpAt a) s e extraLocal)
    (hextra : extraGlobal
      (ColouredSafeAmbientOccurrence.retypeLimitReference hL ⟨A, hRoof⟩)) :
    ColouredSafeAmbientOccurrence.retypeLimitReference hL ⟨A, hRoof⟩ ∈
      ColouredSafeHammock.goodRoutes L.limitWarp s e extraGlobal := by
  rcases hgood with ⟨hvalid, hterminal, hsource, hendpoints, _hExtraLocal⟩
  refine ⟨hvalid.retypeLimitReference hL hRoof, ?_, ?_, ?_, hextra⟩
  · rw [ColouredSafeAmbientOccurrence.retypeLimitReference_terminal?]
    exact hterminal
  · intro hsLimit
    apply hsource
    exact limitWarp_inter_roof_subset_warpAt hL
      ⟨hsLimit, hRoof A.source_mem_vertexSet⟩
  · intro v hev hvLimit
    apply hendpoints v hev
    apply limitWarp_inter_roof_subset_warpAt hL
    refine ⟨hvLimit, hRoof ?_⟩
    exact A.terminal_mem_vertexSet (hterminal.trans hev)

/-- Generic transport of an actual native hammock once its route filter is
known to transport.  The ordinary and nondegenerate instances below provide
that proof without adding a provider assumption. -/
theorem hammock_retypeLimitReference
    (hL : HalfwayGeometry L)
    {extraLocal : Occurrence (L.warpAt a) s → Prop}
    {extraGlobal : Occurrence L.limitWarp s → Prop}
    {H : Set (Occurrence (L.warpAt a) s)}
    (hH : ColouredSafeHammock.Hammock
      (L.warpAt a) s e extraLocal H)
    (hRoof : ∀ A ∈ H, A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hExtra : ∀ A (hA : A ∈ H),
      A ∈ ColouredSafeHammock.goodRoutes (L.warpAt a) s e extraLocal →
      extraGlobal (ColouredSafeAmbientOccurrence.retypeLimitReference hL
        ⟨A, hRoof A hA⟩)) :
    ColouredSafeHammock.Hammock L.limitWarp s e extraGlobal
      (retypeFamily hL H hRoof) := by
  constructor
  · intro B hB
    obtain ⟨A, rfl⟩ := hB
    exact mem_goodRoutes_retypeLimitReference hL (hRoof A.1 A.2)
      (hH.1 A.2) (hExtra A.1 A.2 (hH.1 A.2))
  · intro B hB C hC hBC
    obtain ⟨A, rfl⟩ := hB
    obtain ⟨D, rfl⟩ := hC
    have hAD : A.1 ≠ D.1 := by
      intro hval
      apply hBC
      have hsub : A = D := Subtype.ext hval
      subst D
      rfl
    change Disjoint
      ((ColouredSafeAmbientOccurrence.retypeLimitReference hL
          ⟨A.1, hRoof A.1 A.2⟩).vertexSet \ ColouredSafeHammock.endpoints s e)
      ((ColouredSafeAmbientOccurrence.retypeLimitReference hL
          ⟨D.1, hRoof D.1 D.2⟩).vertexSet \ ColouredSafeHammock.endpoints s e)
    rw [ColouredSafeAmbientOccurrence.retypeLimitReference_vertexSet,
      ColouredSafeAmbientOccurrence.retypeLimitReference_vertexSet]
    exact hH.2 A.2 D.2 hAD

/-- Ordinary actual native hammocks transport unchanged to the limiting
reference. -/
theorem ordinary_hammock_retypeLimitReference
    (hL : HalfwayGeometry L)
    {H : Set (Occurrence (L.warpAt a) s)}
    (hH : ColouredSafeHammock.Hammock
      (L.warpAt a) s e (fun _ ↦ True) H)
    (hRoof : ∀ A ∈ H, A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    ColouredSafeHammock.Hammock L.limitWarp s e (fun _ ↦ True)
      (retypeFamily hL H hRoof) := by
  apply hammock_retypeLimitReference hL hH hRoof
  intro A hA hgood
  trivial

/-- A finite locally nondegenerate hammock remains nondegenerate against the
limiting reference.  The endpoint is roofed because it is a displayed literal
vertex of every member. -/
theorem nondegenerate_hammock_retypeLimitReference
    (hL : HalfwayGeometry L)
    {H : Set (Occurrence (L.warpAt a) s)}
    (hH : ColouredSafeHammock.Hammock (L.warpAt a) s (some t)
      (fun A ↦ ¬A.HasFiniteSwitchedPathTo t) H)
    (hRoof : ∀ A ∈ H, A.vertexSet ⊆ Gamma.roof (L.frontier a)) :
    ColouredSafeHammock.Hammock L.limitWarp s (some t)
      (fun A ↦ ¬A.HasFiniteSwitchedPathTo t)
      (retypeFamily hL H hRoof) := by
  apply hammock_retypeLimitReference hL hH hRoof
  intro A hA hgood
  have hterminal : A.terminal? = some t := hgood.2.1
  have htRoof : t ∈ Gamma.roof (L.frontier a) :=
    hRoof A hA (A.terminal_mem_vertexSet hterminal)
  intro hglobal
  exact hgood.2.2.2.2
    ((A.hasFiniteSwitchedPathTo_retypeLimitReference_iff
      hL (hRoof A hA) htRoof).mp hglobal)

/-- An ordinary roof-supported local hammock of cardinal `rho` yields a
limiting-reference native hammock of the same cardinal. -/
theorem hasCard_limitWarp_of_ordinary_hammock_warpAt
    (hL : HalfwayGeometry L)
    {H : Set (Occurrence (L.warpAt a) s)}
    (hH : ColouredSafeHammock.Hammock
      (L.warpAt a) s e (fun _ ↦ True) H)
    (hRoof : ∀ A ∈ H, A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hcard : #H = rho) :
    ColouredSafeHammock.HasCard L.limitWarp s e (fun _ ↦ True) rho :=
  ⟨retypeFamily hL H hRoof,
    ordinary_hammock_retypeLimitReference hL hH hRoof,
    (mk_retypeFamily hL H hRoof).trans hcard⟩

/-- The finite nondegenerate specialization transports the filtered native
cardinality witness exactly. -/
theorem hasCard_limitWarp_of_nondegenerate_hammock_warpAt
    (hL : HalfwayGeometry L)
    {H : Set (Occurrence (L.warpAt a) s)}
    (hH : ColouredSafeHammock.Hammock (L.warpAt a) s (some t)
      (fun A ↦ ¬A.HasFiniteSwitchedPathTo t) H)
    (hRoof : ∀ A ∈ H, A.vertexSet ⊆ Gamma.roof (L.frontier a))
    (hcard : #H = rho) :
    ColouredSafeHammock.HasCard L.limitWarp s (some t)
      (fun A ↦ ¬A.HasFiniteSwitchedPathTo t) rho :=
  ⟨retypeFamily hL H hRoof,
    nondegenerate_hammock_retypeLimitReference hL hH hRoof,
    (mk_retypeFamily hL H hRoof).trans hcard⟩

#print axioms carrierUnion_retypeFamily
#print axioms ordinary_hammock_retypeLimitReference
#print axioms nondegenerate_hammock_retypeLimitReference
#print axioms hasCard_limitWarp_of_ordinary_hammock_warpAt
#print axioms hasCard_limitWarp_of_nondegenerate_hammock_warpAt

end Blueprint.ColouredSafeHammock.ReferenceTransport

end Erdos599
