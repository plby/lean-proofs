/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.Blueprint
import ErdosProblems.Erdos599.FamilyTools

/-!
# Seeded maximal hammocks and the large-hammock closure

This file isolates the Zorn and cardinal-selection part of Aharoni--Berger's
closing construction in Assertions 9.22--9.25.  The important point for
Assertion 9.30 is that a maximal hammock is chosen *above a prescribed
seed*.  Thus, whenever a hammock of cardinality `rho` exists, the selected
maximal-up-to-`rho` hammock has exactly that cardinality; its paths really
occur in the closing set and can later be thinned by a cardinal-avoidance
argument.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599
namespace Blueprint

open DirectedPath Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {ZBefore innerRoof roof : Set V}

private theorem image_subtype_subset {X : Type u} {K : Set X}
    (s : Set K) : Subtype.val '' s ⊆ K := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

private theorem mk_image_subtype_eq {X : Type u} {K : Set X}
    (s : Set K) : #(Subtype.val '' s : Set X) = #s :=
  Cardinal.mk_image_eq_of_injOn Subtype.val s Set.injOn_subtype_val

/-- A hammock can be extended to an inclusion-maximal hammock while
retaining every member of the seed.  This seeded form is essential in the
large-cardinal branch: an arbitrary maximal hammock need not contain the
given large witness. -/
theorem exists_maximal_hammock_superset (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (u : V) (e : AltEnd V)
    {K : Set (AltPath Gamma.graph)} (hK : Hammock Gamma Y u e K) :
    ∃ H : Set (AltPath Gamma.graph), K ⊆ H ∧
      Maximal (fun L ↦ Hammock Gamma Y u e L) H := by
  apply zorn_subset_nonempty
    {L : Set (AltPath Gamma.graph) | Hammock Gamma Y u e L}
  · intro c hcsub hc hcne
    exact ⟨⋃₀ c, hammock_sUnion_of_chain hcsub hc,
      fun L hLc ↦ Set.subset_sUnion_of_mem hLc⟩
  · exact hK

/-- Zorn plus cardinal thinning produces a maximal-up-to-`rho` hammock.
If an exact `rho`-sized hammock exists, the selected hammock has exactly
cardinality `rho`. -/
theorem exists_hammockMaximalUpTo_large (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (u : V) (e : AltEnd V)
    (rho : Cardinal.{u}) :
    ∃ H : Set (AltPath Gamma.graph),
      HammockMaximalUpTo Gamma Y u e rho H ∧
        (HasHammockCard Gamma Y u e rho → #H = rho) := by
  by_cases hlarge : ∃ K : Set (AltPath Gamma.graph),
      Hammock Gamma Y u e K ∧ succ rho ≤ #K
  · obtain ⟨K, hK, hlargeK⟩ := hlarge
    obtain ⟨s, hs⟩ := Cardinal.le_mk_iff_exists_set.mp
      ((le_succ rho).trans hlargeK)
    obtain ⟨t, ht⟩ := Cardinal.le_mk_iff_exists_set.mp hlargeK
    let H : Set (AltPath Gamma.graph) := Subtype.val '' s
    let L : Set (AltPath Gamma.graph) := Subtype.val '' t
    have hHK : H ⊆ K := image_subtype_subset s
    have hLK : L ⊆ K := image_subtype_subset t
    refine ⟨H, maximalUpTo_of_large (hK.subset hHK) ?_
      (hK.subset hLK) ?_, fun _ ↦ ?_⟩
    · exact (mk_image_subtype_eq s).trans hs
    · exact (mk_image_subtype_eq t).trans ht
    · exact (mk_image_subtype_eq s).trans hs
  · by_cases hrho : HasHammockCard Gamma Y u e rho
    · obtain ⟨K, hK, hKcard⟩ := hrho
      obtain ⟨M, hKM, hM⟩ :=
        exists_maximal_hammock_superset Gamma Y u e hK
      have hMcard : #M ≤ rho := by
        by_contra hnot
        exact hlarge ⟨M, hM.1, succ_le_of_lt (lt_of_not_ge hnot)⟩
      have hrhoM : rho ≤ #M := by
        rw [← hKcard]
        exact Cardinal.mk_subtype_mono hKM
      have hMeq : #M = rho := le_antisymm hMcard hrhoM
      exact ⟨M, maximalUpTo_of_maximal hM.1 hM hMcard,
        fun _ ↦ hMeq⟩
    · obtain ⟨M, hM⟩ := exists_maximal_hammock Gamma Y u e
      have hMcard : #M ≤ rho := by
        by_contra hnot
        exact hlarge ⟨M, hM.1, succ_le_of_lt (lt_of_not_ge hnot)⟩
      exact ⟨M, maximalUpTo_of_maximal hM.1 hM hMcard,
        fun h ↦ (hrho h).elim⟩

/-- The closure condition required in Assertion 9.30: for every eligible
endpoint pair, any exact `rho`-sized hammock has an exact `rho`-sized
hammock whose full vertex union is contained in the closing set. -/
def LargeHammockClosed (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (Z ZBefore innerRoof roof : Set V) (rho : Cardinal.{u}) : Prop :=
  ∀ u e, HammockEligible ZBefore innerRoof roof u e →
    HasHammockCard Gamma Y u e rho →
      ∃ H : Set (AltPath Gamma.graph),
        Hammock Gamma Y u e H ∧ #H = rho ∧ HammockContained H Z

abbrev EligiblePair (ZBefore innerRoof roof : Set V) :=
  {q : V × AltEnd V //
    HammockEligible ZBefore innerRoof roof q.1 q.2}

private def eligiblePairEmbedding (ZBefore innerRoof roof : Set V) :
    EligiblePair ZBefore innerRoof roof ↪ ZBefore × Option ZBefore where
  toFun q :=
    (⟨q.1.1, q.2.1.1⟩,
      match h : q.1.2 with
      | .vertex v => some ⟨v, by
          have hv : v ∈ ZBefore ∩ roof := by
            simpa [HammockEligible, h] using q.2.2
          exact hv.1⟩
      | .infinity => none)
  inj' := by
    rintro ⟨⟨u, e⟩, he⟩ ⟨⟨u', e'⟩, he'⟩ h
    apply Subtype.ext
    have hu : u = u' := congrArg (fun z => (z.1 : V)) h
    subst u'
    apply Prod.ext
    · rfl
    cases e with
    | infinity =>
        cases e' with
        | infinity => rfl
        | vertex v => simp at h
    | vertex v =>
        cases e' with
        | infinity => simp at h
        | vertex v' =>
            have hv : v = v' := by
              simpa using
                congrArg (fun z => Option.map Subtype.val z.2) h
            subst v'
            rfl

/-- There are at most `kappa` eligible endpoint pairs when `ZBefore` has
cardinality at most the infinite cardinal `kappa`. -/
theorem mk_eligiblePair_le {ZBefore innerRoof roof : Set V}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa) :
    #(EligiblePair ZBefore innerRoof roof) ≤ kappa := by
  refine (Cardinal.mk_le_of_injective
    (eligiblePairEmbedding ZBefore innerRoof roof).injective).trans ?_
  rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id,
    Cardinal.mk_option]
  apply Cardinal.mul_le_of_le hkappa hZBefore
  exact Cardinal.add_le_of_le hkappa hZBefore
    (Cardinal.one_le_aleph0.trans hkappa)

/-- The canonical maximal-up-to-`rho` hammock selected at an eligible pair. -/
noncomputable def chosenHammock (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (q : EligiblePair ZBefore innerRoof roof) :
    Set (AltPath Gamma.graph) :=
  Classical.choose
    (exists_hammockMaximalUpTo_large Gamma Y q.1.1 q.1.2 rho)

theorem chosenHammock_spec (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (q : EligiblePair ZBefore innerRoof roof) :
    HammockMaximalUpTo Gamma Y q.1.1 q.1.2 rho
      (chosenHammock Gamma Y rho q) :=
  (Classical.choose_spec
    (exists_hammockMaximalUpTo_large Gamma Y q.1.1 q.1.2 rho)).1

theorem chosenHammock_card_eq_of_hasHammockCard
    (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (q : EligiblePair ZBefore innerRoof roof)
    (hlarge : HasHammockCard Gamma Y q.1.1 q.1.2 rho) :
    #(chosenHammock Gamma Y rho q) = rho :=
  (Classical.choose_spec
    (exists_hammockMaximalUpTo_large Gamma Y q.1.1 q.1.2 rho)).2 hlarge

def chosenHammockVertices (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (q : EligiblePair ZBefore innerRoof roof) : Set V :=
  ⋃ Q : chosenHammock Gamma Y rho q, Q.1.vertexSet

/-- The union of all chosen eligible hammocks. -/
def allHammockVertices (Gamma : DWeb V) (Y : Set Gamma.DPath)
    (rho : Cardinal.{u}) (ZBefore innerRoof roof : Set V) : Set V :=
  ⋃ q : EligiblePair ZBefore innerRoof roof,
    chosenHammockVertices Gamma Y rho q

theorem chosenHammock_contained_all (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (q : EligiblePair ZBefore innerRoof roof) :
    HammockContained (chosenHammock Gamma Y rho q)
      (allHammockVertices Gamma Y rho ZBefore innerRoof roof) := by
  intro x hx
  simp only [hammockVertexSet, allHammockVertices,
    chosenHammockVertices, Set.mem_iUnion] at hx ⊢
  obtain ⟨Q, hQ, hxQ⟩ := hx
  exact ⟨q, ⟨Q, hQ⟩, hxQ⟩

/-- The selected union really is closed under every eligible exact-size
hammock requirement. -/
theorem allHammockVertices_largeHammockClosed (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (ZBefore innerRoof roof : Set V) :
    LargeHammockClosed Gamma Y
      (allHammockVertices Gamma Y rho ZBefore innerRoof roof)
      ZBefore innerRoof roof rho := by
  intro u e helig hlarge
  let q : EligiblePair ZBefore innerRoof roof := ⟨(u, e), helig⟩
  exact ⟨chosenHammock Gamma Y rho q,
    (chosenHammock_spec Gamma Y rho q).isHammock,
    chosenHammock_card_eq_of_hasHammockCard Gamma Y rho q hlarge,
    chosenHammock_contained_all Gamma Y rho q⟩

theorem finiteTrace_vertexSet_countable {D : Digraph V}
    (Q : FiniteTrace D) : Q.vertexSet.Countable := by
  exact Set.countable_iUnion fun i => (Q.link i).path.support_countable

theorem infiniteTrace_vertexSet_countable {D : Digraph V}
    (Q : InfiniteTrace D) : Q.vertexSet.Countable := by
  exact Set.countable_iUnion fun i => (Q.link i).path.support_countable

theorem altPath_vertexSet_countable {D : Digraph V} (Q : AltPath D) :
    Q.vertexSet.Countable := by
  cases Q with
  | trivial v => simp [AltPath.vertexSet]
  | finite Q => exact finiteTrace_vertexSet_countable Q
  | infinite Q => exact infiniteTrace_vertexSet_countable Q

private theorem mk_iUnion_le_of_le {I X : Type u} {f : I → Set X}
    {kappa : Cardinal.{u}} (hkappa : aleph0 ≤ kappa)
    (hI : #I ≤ kappa) (hf : ∀ i, #(f i) ≤ kappa) :
    #(⋃ i, f i) ≤ kappa := by
  refine (Cardinal.mk_iUnion_le f).trans ?_
  exact Cardinal.mul_le_of_le hkappa hI (ciSup_le' hf)

theorem mk_chosenHammockVertices_le (Gamma : DWeb V)
    (Y : Set Gamma.DPath) {rho kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (q : EligiblePair ZBefore innerRoof roof) :
    #(chosenHammockVertices Gamma Y rho q) ≤ kappa := by
  apply mk_iUnion_le_of_le hkappa
  · exact (chosenHammock_spec Gamma Y rho q).card_le.trans hrho
  · intro Q
    exact (altPath_vertexSet_countable Q.1).le_aleph0.trans hkappa

/-- The whole selected closure remains `kappa`-small. -/
theorem mk_allHammockVertices_le (Gamma : DWeb V)
    (Y : Set Gamma.DPath) {rho kappa : Cardinal.{u}}
    (hkappa : aleph0 ≤ kappa) (hrho : rho ≤ kappa)
    (hZBefore : #ZBefore ≤ kappa) :
    #(allHammockVertices Gamma Y rho ZBefore innerRoof roof) ≤ kappa := by
  apply mk_iUnion_le_of_le hkappa
  · exact mk_eligiblePair_le hkappa hZBefore
  · exact mk_chosenHammockVertices_le Gamma Y hkappa hrho

theorem allHammockVertices_subset_roof (Gamma : DWeb V)
    (Y : Set Gamma.DPath) (rho : Cardinal.{u})
    (hSafeRoof : ∀ Q : AltPath Gamma.graph, IsSafe Y Q → Q.vertexSet ⊆ roof) :
    allHammockVertices Gamma Y rho ZBefore innerRoof roof ⊆ roof := by
  intro x hx
  obtain ⟨q, hx⟩ := Set.mem_iUnion.1 hx
  obtain ⟨Q, hxQ⟩ := Set.mem_iUnion.1 hx
  exact hSafeRoof Q.1
    ((chosenHammock_spec Gamma Y rho q).isHammock.1 Q.1 Q.2).1 hxQ

/-- In an explicit `kappa`-successor-sized hammock, one member's interior
avoids every set of cardinality at most `kappa`.  Membership in the given
hammock is retained so that a `HammockContained H Z` hypothesis can be used
after the selection. -/
theorem exists_mem_hammock_disjoint_of_mk_eq
    {u : V} {e : AltEnd V} {kappa : Cardinal.{u}} {X : Set V}
    {H : Set (AltPath Gamma.graph)}
    (hH : Hammock Gamma Y u e H) (hcard : #H = succ kappa)
    (hX : #X ≤ kappa) :
    ∃ Q : AltPath Gamma.graph, Q ∈ H ∧
      IsSafe Y Q ∧ Q.initial = u ∧ HasEnd Q e ∧
        Disjoint (hammockInterior u e Q) X := by
  have hexists : ∃ Q ∈ H, Disjoint (hammockInterior u e Q) X := by
    by_contra hnone
    push Not at hnone
    have hmeet : ∀ Q ∈ H, ∃ x ∈ X, x ∈ hammockInterior u e Q := by
      intro Q hQ
      rcases Set.not_disjoint_iff.mp (hnone Q hQ) with ⟨x, hxQ, hxX⟩
      exact ⟨x, hxX, hxQ⟩
    have hle : #H ≤ #X :=
      Erdos599.FamilyTools.mk_le_of_pairwiseDisjoint_of_meets hH.2 hmeet
    have hsucc_le : succ kappa ≤ kappa := by
      calc
        succ kappa = #H := hcard.symm
        _ ≤ #X := hle
        _ ≤ kappa := hX
    exact (not_le_of_gt (Order.lt_succ kappa)) hsucc_le
  rcases hexists with ⟨Q, hQH, hQdisjoint⟩
  exact ⟨Q, hQH, (hH.1 Q hQH).1, (hH.1 Q hQH).2.1,
    (hH.1 Q hQH).2.2, hQdisjoint⟩

/-- The containment-aware form of the explicit-family selector. -/
theorem exists_mem_hammock_subset_disjoint_of_mk_eq
    {u : V} {e : AltEnd V} {kappa : Cardinal.{u}} {X Z : Set V}
    {H : Set (AltPath Gamma.graph)}
    (hH : Hammock Gamma Y u e H) (hcard : #H = succ kappa)
    (hHZ : HammockContained H Z) (hX : #X ≤ kappa) :
    ∃ Q : AltPath Gamma.graph, Q ∈ H ∧ Q.vertexSet ⊆ Z ∧
      IsSafe Y Q ∧ Q.initial = u ∧ HasEnd Q e ∧
        Disjoint (hammockInterior u e Q) X := by
  obtain ⟨Q, hQH, hsafe, hinitial, hend, hdisjoint⟩ :=
    exists_mem_hammock_disjoint_of_mk_eq hH hcard hX
  have hQZ : Q.vertexSet ⊆ Z := by
    intro x hx
    apply hHZ
    simp only [hammockVertexSet, Set.mem_iUnion]
    exact ⟨Q, hQH, hx⟩
  exact ⟨Q, hQH, hQZ, hsafe, hinitial, hend, hdisjoint⟩

/-- Existential-hammock convenience wrapper for the explicit selector. -/
theorem exists_hammock_path_disjoint_of_mk_le
    {u : V} {e : AltEnd V} {kappa : Cardinal.{u}} {X : Set V}
    (hhammock : HasHammockCard Gamma Y u e (succ kappa))
    (hX : #X ≤ kappa) :
    ∃ Q : AltPath Gamma.graph,
      IsSafe Y Q ∧ Q.initial = u ∧ HasEnd Q e ∧
        Disjoint (hammockInterior u e Q) X := by
  rcases hhammock with ⟨H, hH, hcard⟩
  obtain ⟨Q, _hQH, hsafe, hinitial, hend, hdisjoint⟩ :=
    exists_mem_hammock_disjoint_of_mk_eq hH hcard hX
  exact ⟨Q, hsafe, hinitial, hend, hdisjoint⟩

/-- A strong hammock has a selected avoiding member which remains
nondegenerate. -/
theorem exists_mem_nondegenerateHammock_disjoint_of_mk_eq
    {u v : V} {kappa : Cardinal.{u}} {X : Set V}
    {H : Set (AltPath Gamma.graph)}
    (hH : NondegenerateHammock Gamma Y u (.vertex v) H)
    (hcard : #H = succ kappa) (hX : #X ≤ kappa) :
    ∃ Q : AltPath Gamma.graph, Q ∈ H ∧
      IsSafe Y Q ∧ Q.initial = u ∧ HasEnd Q (.vertex v) ∧
        ¬IsDegenerate Y Q (.vertex v) ∧
        Disjoint (hammockInterior u (.vertex v) Q) X := by
  obtain ⟨Q, hQH, hsafe, hinitial, hend, hdisjoint⟩ :=
    exists_mem_hammock_disjoint_of_mk_eq hH.1 hcard hX
  exact ⟨Q, hQH, hsafe, hinitial, hend, hH.2 Q hQH, hdisjoint⟩

/-- Existential strong-hammock form of the nondegenerate selector. -/
theorem exists_nondegenerate_hammock_path_disjoint_of_mk_le
    {u v : V} {kappa : Cardinal.{u}} {X : Set V}
    (hhammock :
      HasNondegenerateHammockCard Gamma Y u (.vertex v) (succ kappa))
    (hX : #X ≤ kappa) :
    ∃ H : Set (AltPath Gamma.graph), ∃ Q : AltPath Gamma.graph,
      NondegenerateHammock Gamma Y u (.vertex v) H ∧
      #H = succ kappa ∧ Q ∈ H ∧
      IsSafe Y Q ∧ Q.initial = u ∧ HasEnd Q (.vertex v) ∧
        ¬IsDegenerate Y Q (.vertex v) ∧
        Disjoint (hammockInterior u (.vertex v) Q) X := by
  rcases hhammock with ⟨H, hH, hcard⟩
  obtain ⟨Q, hQH, hsafe, hinitial, hend, hnondeg, hdisjoint⟩ :=
    exists_mem_nondegenerateHammock_disjoint_of_mk_eq hH hcard hX
  exact ⟨H, Q, hH, hcard, hQH, hsafe, hinitial, hend, hnondeg, hdisjoint⟩

/-- Infinity-endpoint form used in Assertion 9.30: only the common initial
vertex `u` is exempt from avoidance. -/
theorem exists_safe_infinite_hammock_path_avoiding
    {u : V} {kappa : Cardinal.{u}} {X : Set V}
    (hhammock : HasHammockCard Gamma Y u .infinity (succ kappa))
    (hX : #X ≤ kappa) :
    ∃ Q : AltPath Gamma.graph,
      IsSafe Y Q ∧ Q.initial = u ∧ Q.IsInfinite ∧
        Disjoint (Q.vertexSet \ {u}) X := by
  simpa [HasEnd, hammockInterior, hammockEndpoints] using
    (exists_hammock_path_disjoint_of_mk_le hhammock hX)

end Blueprint
end Erdos599
