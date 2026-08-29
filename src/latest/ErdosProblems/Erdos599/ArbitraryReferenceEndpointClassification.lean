/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ArbitraryReferenceFracturedAssignment
import ErdosProblems.Erdos599.HalfwayEndpointCoveredClaim2

/-!
# Endpoint-covered Claim 2 after pruning a reference at a closed set

An assignment against `outsideReference Y X` need not be safe against the
full reference `Y`: a deleted reference member may cover one of the exposed
endpoints.  What does lift is *internal* safeness.  If, in addition, every
backward link avoids `X` and every forward link meets `X` only at its own
endpoints, alternation shows that the whole trace meets `X` only at its
prescribed endpoints.  The endpoint-covered version of Claim 2 then gives
the sound three-way/two-way classifications.

The forward-link hypothesis is deliberately explicit.  The public
`BracketFracturedAssignment` interface currently records forward provenance
only in the recombined `edgeWarp`; constructing this hypothesis from literal
post-closure holes requires the separate occurrence-provenance argument.
-/

noncomputable section

open Set

namespace Erdos599
namespace Blueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {U Y : Set Gamma.DPath} {X : Set V}

/-- The exact local incidence condition needed to turn linkwise avoidance
into endpoint-only contact of an alternating trace. -/
def LinkwiseEndpointAvoiding (Q : AltPath Gamma.graph) (X : Set V) : Prop :=
  (forall l, l ∈ Q.links -> l.direction = .backward ->
      Disjoint l.path.support X) ∧
    (forall l, l ∈ Q.links -> l.direction = .forward ->
      l.path.support ∩ X ⊆ {l.entry, l.exit})

/-- Bracket safeness against the outside reference supplies the backward
half of `LinkwiseEndpointAvoiding`; only literal forward provenance remains
as an input. -/
theorem LinkwiseEndpointAvoiding.of_bracketSafe_outsideReference
    {Q : AltPath Gamma.graph}
    (hQ : IsBracketSafe U (outsideReference Y X) Q)
    (hforward : forall l, l ∈ Q.links -> l.direction = .forward ->
      l.path.support ∩ X ⊆ {l.entry, l.exit}) :
    LinkwiseEndpointAvoiding Q X := by
  refine ⟨?_, hforward⟩
  intro l hl hbackward
  obtain ⟨p, hp, hlp⟩ := hQ.isAlternating.2.1 l hl hbackward
  rw [Set.disjoint_left]
  intro x hxl hxX
  exact Set.disjoint_left.1 hp.2 (hlp.1 hxl) hxX

/-- A finite alternating trace satisfying the linkwise condition meets the
cut only at its global initial and terminal vertices. -/
theorem LinkwiseEndpointAvoiding.finite_vertexSet_inter_subset
    (Q : FiniteTrace Gamma.graph)
    (hQ : LinkwiseEndpointAvoiding (.finite Q) X) :
    Q.vertexSet ∩ X ⊆ {Q.initial, Q.terminal} := by
  rintro x ⟨hxQ, hxX⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxQ
  have hmem : Q.link i ∈ (AltPath.finite Q).links := ⟨i, rfl⟩
  cases hdir : (Q.link i).direction with
  | backward =>
      exact False.elim (Set.disjoint_left.1
        (hQ.1 (Q.link i) hmem hdir) hxi hxX)
  | forward =>
      have hcontact := hQ.2 (Q.link i) hmem hdir ⟨hxi, hxX⟩
      rcases hcontact with hentry | hexit
      · by_cases hi0 : i.1 = 0
        · left
          have hieq : i = ⟨0, Nat.zero_lt_succ _⟩ := Fin.ext hi0
          rw [hieq] at hentry
          exact hentry
        · let k : Fin Q.lastIndex := ⟨i.1 - 1, by omega⟩
          have hsucc : k.succ = i := by
            apply Fin.ext
            dsimp [k]
            omega
          have hprevBackward : (Q.link k.castSucc).direction = .backward := by
            cases hprev : (Q.link k.castSucc).direction with
            | backward => rfl
            | forward =>
                exact False.elim (Q.alternates k (by
                  rw [hprev, hsucc, hdir]))
          have hxPrev : x ∈ (Q.link k.castSucc).path.support := by
            rw [hentry, ← hsucc, ← Q.joins k]
            exact (Q.link k.castSucc).exit_mem_support
          exact False.elim (Set.disjoint_left.1
            (hQ.1 (Q.link k.castSucc) ⟨k.castSucc, rfl⟩ hprevBackward)
            hxPrev hxX)
      · by_cases hilast : i.1 = Q.lastIndex
        · right
          have hieq : i = ⟨Q.lastIndex, Nat.lt_succ_self _⟩ := Fin.ext hilast
          rw [hieq] at hexit
          exact hexit
        · let k : Fin Q.lastIndex := ⟨i.1, by omega⟩
          have hcast : k.castSucc = i := by
            apply Fin.ext
            rfl
          have hnextBackward : (Q.link k.succ).direction = .backward := by
            cases hnext : (Q.link k.succ).direction with
            | backward => rfl
            | forward =>
                exact False.elim (Q.alternates k (by
                  rw [hcast, hdir, hnext]))
          have hxNext : x ∈ (Q.link k.succ).path.support := by
            rw [hexit, ← hcast, Q.joins k]
            exact (Q.link k.succ).entry_mem_support
          exact False.elim (Set.disjoint_left.1
            (hQ.1 (Q.link k.succ) ⟨k.succ, rfl⟩ hnextBackward)
            hxNext hxX)

/-- An infinite alternating trace satisfying the linkwise condition meets
the cut only at its global initial vertex. -/
theorem LinkwiseEndpointAvoiding.infinite_vertexSet_inter_subset
    (Q : InfiniteTrace Gamma.graph)
    (hQ : LinkwiseEndpointAvoiding (.infinite Q) X) :
    Q.vertexSet ∩ X ⊆ {Q.initial} := by
  rintro x ⟨hxQ, hxX⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.1 hxQ
  have hmem : Q.link i ∈ (AltPath.infinite Q).links := ⟨i, rfl⟩
  cases hdir : (Q.link i).direction with
  | backward =>
      exact False.elim (Set.disjoint_left.1
        (hQ.1 (Q.link i) hmem hdir) hxi hxX)
  | forward =>
      have hcontact := hQ.2 (Q.link i) hmem hdir ⟨hxi, hxX⟩
      rcases hcontact with hentry | hexit
      · by_cases hi0 : i = 0
        · subst i
          exact hentry
        · let k := i - 1
          have hsucc : k + 1 = i := by
            dsimp [k]
            omega
          have hprevBackward : (Q.link k).direction = .backward := by
            cases hprev : (Q.link k).direction with
            | backward => rfl
            | forward =>
                exact False.elim (Q.alternates k (by
                  rw [hprev, hsucc, hdir]))
          have hxPrev : x ∈ (Q.link k).path.support := by
            rw [hentry, ← hsucc, ← Q.joins k]
            exact (Q.link k).exit_mem_support
          exact False.elim (Set.disjoint_left.1
            (hQ.1 (Q.link k) ⟨k, rfl⟩ hprevBackward) hxPrev hxX)
      · have hnextBackward : (Q.link (i + 1)).direction = .backward := by
          cases hnext : (Q.link (i + 1)).direction with
          | backward => rfl
          | forward =>
              exact False.elim (Q.alternates i (by rw [hdir, hnext]))
        have hxNext : x ∈ (Q.link (i + 1)).path.support := by
          rw [hexit, Q.joins i]
          exact (Q.link (i + 1)).entry_mem_support
        exact False.elim (Set.disjoint_left.1
          (hQ.1 (Q.link (i + 1)) ⟨i + 1, rfl⟩ hnextBackward)
          hxNext hxX)

/-- Endpoint-only contact is exactly disjointness of the finite hammock
interior from the cut. -/
theorem LinkwiseEndpointAvoiding.finite_interior_disjoint
    (Q : FiniteTrace Gamma.graph)
    (hQ : LinkwiseEndpointAvoiding (.finite Q) X) :
    Disjoint (hammockInterior Q.initial (.vertex Q.terminal) (.finite Q)) X := by
  rw [Set.disjoint_left]
  rintro x hx hxX
  have hend := hQ.finite_vertexSet_inter_subset Q ⟨hx.1, hxX⟩
  exact hx.2 hend

/-- Endpoint-only contact is exactly disjointness of the infinite hammock
interior from the cut. -/
theorem LinkwiseEndpointAvoiding.infinite_interior_disjoint
    (Q : InfiniteTrace Gamma.graph)
    (hQ : LinkwiseEndpointAvoiding (.infinite Q) X) :
    Disjoint (hammockInterior Q.initial .infinity (.infinite Q)) X := by
  rw [Set.disjoint_left]
  rintro x hx hxX
  have hend := hQ.infinite_vertexSet_inter_subset Q ⟨hx.1, hxX⟩
  exact hx.2 hend

/-- Safety against the pruned reference always promotes to internal safety
against the full reference.  No whole-trace avoidance premise is required;
the only possible new failures are the exposed endpoint clauses. -/
theorem InternallySafe.of_safe_outsideReference
    {Q : AltPath Gamma.graph}
    (hY : Gamma.IsWarp Y)
    (hQ : IsSafe (outsideReference Y X) Q) :
    InternallySafe Y Q := by
  have hfamily : familyEdges (outsideReference Y X) ⊆ familyEdges Y :=
    familyEdges_outsideReference_subset
  refine ⟨hY, ?_, ?_, ?_, ?_⟩
  · intro l hl hbackward
    obtain ⟨p, hp, hlp⟩ := hQ.1.2.1 l hl hbackward
    exact ⟨p, hp.1, hlp⟩
  · intro p hpY
    by_cases hpout : p ∈ outsideReference Y X
    · exact hQ.2.1 p hpout
    · left
      ext e
      constructor
      · rintro ⟨heback, hep⟩
        simp only [AltPath.directionEdges, Set.mem_iUnion] at heback
        obtain ⟨l, hl, hbackward, hel⟩ := heback
        obtain ⟨q, hqout, hlq⟩ := hQ.1.2.1 l hl hbackward
        have hqp : q ≠ p := by
          intro hqp
          exact hpout (hqp ▸ hqout)
        have hdisjoint := hY hqout.1 hpY hqp
        have heq := hlq.2 hel
        have heqv := q.edgeSet_subset_support_prod heq
        have hepv := p.edgeSet_subset_support_prod hep
        exact False.elim (Set.disjoint_left.1 hdisjoint heqv.1 hepv.1)
      · simp
  · rintro ⟨R, hR⟩
    exact hQ.2.2.1 ⟨R, hR.trans (by
      intro e he
      exact ⟨he.1, fun heout => he.2 (hfamily heout)⟩)⟩
  · rintro ⟨C, hC⟩
    exact hQ.2.2.2 ⟨C, hC.trans (by
      intro e he
      exact ⟨he.1, fun heout => he.2 (hfamily heout)⟩)⟩

/-- Sound finite Claim-2 handoff for a trace produced against the outside
reference.  Covered exposed endpoints are returned as closed reference
owners rather than being incorrectly declared safe. -/
theorem classifyFinite_of_safeOutsideReference
    {kappa : Cardinal.{u}} {before innerRoof outerRoof : Set V}
    {u v : V} {Q : FiniteTrace Gamma.graph}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (hQsafe : IsSafe (outsideReference Y X) (.finite Q))
    (hQlinks : LinkwiseEndpointAvoiding (.finite Q) X)
    (heligible : u ∉ Gamma.vertexSet Y -> v ∉ Gamma.vertexSet Y ->
      HammockEligible before innerRoof outerRoof u (.vertex v))
    (hu : Q.initial = u) (hv : Q.terminal = v)
    (houtside : ¬ Q.vertexSet ⊆ X)
    (huX : u ∈ Gamma.vertexSet Y -> u ∈ X)
    (hvX : v ∈ Gamma.vertexSet Y -> v ∈ X) :
    Nonempty (FiniteSegmentClassification
      (Y := Y) (X := X) (kappa := kappa) (.finite Q) u v) := by
  apply classifyFinite hclosed hreferenceClosed heligible
      (fun _ _ => InternallySafe.of_safe_outsideReference hY hQsafe)
      hu (by simpa [AltPath.terminal?] using congrArg some hv)
      _ houtside huX hvX
  simpa [hu, hv] using hQlinks.finite_interior_disjoint Q

/-- Sound infinite Claim-2 handoff for a trace produced against the outside
reference. -/
theorem classifyInfinite_of_safeOutsideReference
    {kappa : Cardinal.{u}} {before innerRoof outerRoof persistent : Set V}
    {u : V} {Q : InfiniteTrace Gamma.graph}
    (hclosed : HammockClosedUpTo Gamma Y X before innerRoof outerRoof kappa)
    (hreferenceClosed : ClosedUnderPaths Gamma Y X)
    (hY : Gamma.IsWarp Y)
    (hQsafe : IsSafe (outsideReference Y X) (.infinite Q))
    (hQlinks : LinkwiseEndpointAvoiding (.infinite Q) X)
    (heligible : u ∉ Gamma.vertexSet Y ->
      HammockEligible before innerRoof outerRoof u .infinity)
    (hu : Q.initial = u)
    (houtside : ¬ Q.vertexSet ⊆ X)
    (huX : u ∈ Gamma.vertexSet Y -> u ∈ X) :
    Nonempty (InfiniteSegmentClassification
      (Y := Y) (X := X) (kappa := kappa) persistent (.infinite Q) u) := by
  apply classifyInfinite hclosed hreferenceClosed heligible
      (fun _ => InternallySafe.of_safe_outsideReference hY hQsafe)
      hu (by simp [AltPath.IsInfinite]) _ houtside huX
  simpa [hu] using hQlinks.infinite_interior_disjoint Q

#print axioms LinkwiseEndpointAvoiding.of_bracketSafe_outsideReference
#print axioms LinkwiseEndpointAvoiding.finite_interior_disjoint
#print axioms LinkwiseEndpointAvoiding.infinite_interior_disjoint
#print axioms InternallySafe.of_safe_outsideReference
#print axioms classifyFinite_of_safeOutsideReference
#print axioms classifyInfinite_of_safeOutsideReference

end Blueprint
end Erdos599
