/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceTheorem66Case3
import ErdosProblems.Erdos916.AHTWatkinsMesner

/-!
# The three-by-three splitter branch in AHT Theorem 6.6

This file formalizes the unconditional local graph theory in the first
branch of claim (8) in the proof of Theorem 6.6 of
Aboulker--Havet--Trotignon.  The source has splitter sets `A,B`, both of
cardinality three.  Apart from the three distinguished terminal components,
condition (vii) of the Watkins--Mesner splitter says that a component has
boundary in `A`, in `B`, or in one of the three matched two-sets.  The
two-set alternatives contradict three-connectivity.

We also formalize the union `C_A` of all `A`-side components, the elementary
triangle-free/minimum-degree argument giving `2 ≤ |C_A|`, and the exact
three-boundary fragment certificate used against the earlier large-fragment
claim.  No splitter-existence or minimal-counterexample principle is assumed:
all inputs below are finite sets and concrete adjacency facts.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

private theorem aht_card_pair_le {W : Type*} [DecidableEq W] (a b : W) :
    ({a, b} : Finset W).card ≤ 2 := by
  calc
    ({a, b} : Finset W).card ≤ ({b} : Finset W).card + 1 :=
      Finset.card_insert_le _ _
    _ = 2 := by simp

/-! ## A small external boundary contradicts three-connectivity -/

/-- The separation naturally associated to a set `C` whose external
neighbours all lie in `T`. -/
def ahtExternalBoundarySeparation
    (G : SimpleGraph V) (C T : Finset V)
    (hCT : Disjoint C T) (hboundary : HasExternalBoundaryIn G C T) :
    AHTSeparation G where
  left := C ∪ T
  right := Finset.univ \ C
  cover := by
    ext z
    by_cases hz : z ∈ C <;> simp [hz]
  not_adj := by
    intro p q hpL hpR hqR hqL hpq
    have hpC : p ∈ C := by
      by_contra hpC
      exact hpR (by simp [hpC])
    have hqC : q ∉ C := by simpa using hqR
    have hqT : q ∈ T := hboundary p hpC q hpq hqC
    exact hqL (Finset.mem_union_right _ hqT)

/-- The separator of the external-boundary separation is exactly `T`. -/
theorem ahtExternalBoundarySeparation_separator
    (C T : Finset V) (hCT : Disjoint C T)
    (hboundary : HasExternalBoundaryIn G C T) :
    (ahtExternalBoundarySeparation G C T hCT hboundary).separator = T := by
  ext z
  have hdisj := Finset.disjoint_left.mp hCT
  by_cases hzT : z ∈ T
  · have hzC : z ∉ C := fun hzC ↦ hdisj hzC hzT
    simp [AHTSeparation.separator, ahtExternalBoundarySeparation, hzT, hzC]
  · simp [AHTSeparation.separator, ahtExternalBoundarySeparation, hzT]

/-- If both strict sides are inhabited, the external-boundary separation is
proper. -/
theorem ahtExternalBoundarySeparation_proper
    (C T : Finset V) (hCT : Disjoint C T)
    (hboundary : HasExternalBoundaryIn G C T)
    (hC : C.Nonempty) (hout : ∃ w : V, w ∉ C ∪ T) :
    (ahtExternalBoundarySeparation G C T hCT hboundary).Proper := by
  obtain ⟨c, hc⟩ := hC
  obtain ⟨w, hw⟩ := hout
  constructor
  · refine ⟨c, Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hc, ?_⟩⟩
    simp [ahtExternalBoundarySeparation, hc]
  · refine ⟨w, Finset.mem_sdiff.mpr ⟨?_, hw⟩⟩
    simp only [ahtExternalBoundarySeparation, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    exact fun hwC ↦ hw (Finset.mem_union_left _ hwC)

/-- In a three-connected graph, every nontrivial external boundary has at
least three vertices. -/
theorem three_le_card_of_externalBoundary
    (hthree : IsThreeConnected G) (C T : Finset V)
    (hCT : Disjoint C T) (hboundary : HasExternalBoundaryIn G C T)
    (hC : C.Nonempty) (hout : ∃ w : V, w ∉ C ∪ T) :
    3 ≤ T.card := by
  have hproper := ahtExternalBoundarySeparation_proper
    (G := G) C T hCT hboundary hC hout
  have horder := hthree.2
    (ahtExternalBoundarySeparation G C T hCT hboundary) hproper
  rw [AHTSeparation.order,
    ahtExternalBoundarySeparation_separator C T hCT hboundary] at horder
  exact horder

/-- If a three-element set contains the external boundary, then every one
of its vertices is actually met.  This is the exact `N(C)=A` strengthening
used when turning a component union into a fragment. -/
theorem externalBoundary_tight_of_card_three
    (hthree : IsThreeConnected G) (C A : Finset V) {w : V}
    (hCA : Disjoint C A) (hboundary : HasExternalBoundaryIn G C A)
    (hC : C.Nonempty) (hA : A.card = 3)
    (hwC : w ∉ C) (hwA : w ∉ A) :
    ∀ a ∈ A, ∃ c ∈ C, G.Adj c a := by
  intro a haA
  by_contra h
  push Not at h
  have hsmall : HasExternalBoundaryIn G C (A.erase a) := by
    intro c hc q hcq hqC
    have hqA := hboundary c hc q hcq hqC
    exact Finset.mem_erase.mpr ⟨fun hqa ↦ by
      subst q
      exact h c hc hcq, hqA⟩
  have hdisj : Disjoint C (A.erase a) :=
    hCA.mono_right (Finset.erase_subset a A)
  have hout : ∃ z : V, z ∉ C ∪ A.erase a := by
    refine ⟨w, ?_⟩
    simp only [Finset.mem_union, not_or]
    exact ⟨hwC, fun hw ↦ hwA (Finset.mem_of_mem_erase hw)⟩
  have hthreeBoundary := three_le_card_of_externalBoundary
    hthree C (A.erase a) hdisj hsmall hC hout
  rw [Finset.card_erase_of_mem haA, hA] at hthreeBoundary
  omega

/-! ## The component-boundary dichotomy -/

/-- In the `|A|=|B|=3` branch, the three matched-pair alternatives in
Watkins--Mesner condition (vii) are impossible for any component not meeting
`v`.  Thus its entire external boundary lies on one side. -/
theorem component_boundary_in_left_or_right_of_both_triples
    (hthree : IsThreeConnected G)
    (A B D : Finset V) (v : V)
    {xA yA zA xB yB zB : V}
    (hD : IsComponentAfterDeleting G (A ∪ B ∪ {v}) D)
    (hvAB : v ∉ A ∪ B)
    (hxA : xA ∈ A) (hyA : yA ∈ A) (hzA : zA ∈ A)
    (hxB : xB ∈ B) (hyB : yB ∈ B) (hzB : zB ∈ B)
    (hoptions :
      HasExternalBoundaryIn G D A ∨ HasExternalBoundaryIn G D B ∨
        HasExternalBoundaryIn G D {xA, xB} ∨
        HasExternalBoundaryIn G D {yA, yB} ∨
        HasExternalBoundaryIn G D {zA, zB}) :
    HasExternalBoundaryIn G D A ∨ HasExternalBoundaryIn G D B := by
  rcases hoptions with hA | hB | hx | hy | hz
  · exact Or.inl hA
  · exact Or.inr hB
  · exfalso
    have hsub : ({xA, xB} : Finset V) ⊆ A ∪ B := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_union_left _ hxA
      · exact Finset.mem_union_right _ hxB
    have hDdisj : Disjoint D (A ∪ B ∪ {v}) := hD.2.1
    have hDP : Disjoint D ({xA, xB} : Finset V) :=
      hDdisj.mono_right (hsub.trans Finset.subset_union_left)
    have hvD : v ∉ D := fun hvD ↦
      Finset.disjoint_left.mp hDdisj hvD (by simp)
    have hvP : v ∉ ({xA, xB} : Finset V) := by
      intro hvP
      exact hvAB (hsub hvP)
    have hcard := three_le_card_of_externalBoundary hthree D {xA, xB}
      hDP hx hD.1 ⟨v, by
        simp only [Finset.mem_union, not_or]
        exact ⟨hvD, hvP⟩⟩
    have hpair : ({xA, xB} : Finset V).card ≤ 2 := aht_card_pair_le _ _
    omega
  · exfalso
    have hsub : ({yA, yB} : Finset V) ⊆ A ∪ B := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_union_left _ hyA
      · exact Finset.mem_union_right _ hyB
    have hDdisj : Disjoint D (A ∪ B ∪ {v}) := hD.2.1
    have hDP : Disjoint D ({yA, yB} : Finset V) :=
      hDdisj.mono_right (hsub.trans Finset.subset_union_left)
    have hvD : v ∉ D := fun hvD ↦
      Finset.disjoint_left.mp hDdisj hvD (by simp)
    have hvP : v ∉ ({yA, yB} : Finset V) := by
      intro hvP
      exact hvAB (hsub hvP)
    have hcard := three_le_card_of_externalBoundary hthree D {yA, yB}
      hDP hy hD.1 ⟨v, by
        simp only [Finset.mem_union, not_or]
        exact ⟨hvD, hvP⟩⟩
    have hpair : ({yA, yB} : Finset V).card ≤ 2 := aht_card_pair_le _ _
    omega
  · exfalso
    have hsub : ({zA, zB} : Finset V) ⊆ A ∪ B := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_union_left _ hzA
      · exact Finset.mem_union_right _ hzB
    have hDdisj : Disjoint D (A ∪ B ∪ {v}) := hD.2.1
    have hDP : Disjoint D ({zA, zB} : Finset V) :=
      hDdisj.mono_right (hsub.trans Finset.subset_union_left)
    have hvD : v ∉ D := fun hvD ↦
      Finset.disjoint_left.mp hDdisj hvD (by simp)
    have hvP : v ∉ ({zA, zB} : Finset V) := by
      intro hvP
      exact hvAB (hsub hvP)
    have hcard := three_le_card_of_externalBoundary hthree D {zA, zB}
      hDP hz hD.1 ⟨v, by
        simp only [Finset.mem_union, not_or]
        exact ⟨hvD, hvP⟩⟩
    have hpair : ({zA, zB} : Finset V).card ≤ 2 := aht_card_pair_le _ _
    omega

/-! ## Unions of same-side components -/

/-- The finite union denoted `C_A` (or `C_B`) in the paper. -/
def ahtComponentSideUnion (components : Finset (Finset V)) : Finset V :=
  components.biUnion id

/-- A union of sets whose external boundaries lie in `A` again has external
boundary in `A`. -/
theorem componentSideUnion_externalBoundary
    (components : Finset (Finset V)) (A : Finset V)
    (hboundary : ∀ D ∈ components, HasExternalBoundaryIn G D A) :
    HasExternalBoundaryIn G (ahtComponentSideUnion components) A := by
  intro p hp q hpq hq
  obtain ⟨D, hD, hpD⟩ := Finset.mem_biUnion.mp hp
  apply hboundary D hD p hpD q hpq
  intro hqD
  exact hq (Finset.mem_biUnion.mpr ⟨D, hD, hqD⟩)

/-- Disjointness from the boundary is preserved by the component union. -/
theorem componentSideUnion_disjoint
    (components : Finset (Finset V)) (A : Finset V)
    (hdisj : ∀ D ∈ components, Disjoint D A) :
    Disjoint (ahtComponentSideUnion components) A := by
  apply Finset.disjoint_left.mpr
  intro p hp hpA
  obtain ⟨D, hD, hpD⟩ := Finset.mem_biUnion.mp hp
  exact Finset.disjoint_left.mp (hdisj D hD) hpD hpA

/-- A nonempty family of nonempty components has nonempty union. -/
theorem componentSideUnion_nonempty
    (components : Finset (Finset V))
    (hcomponents : components.Nonempty)
    (hnonempty : ∀ D ∈ components, D.Nonempty) :
    (ahtComponentSideUnion components).Nonempty := by
  obtain ⟨D, hD⟩ := hcomponents
  obtain ⟨p, hp⟩ := hnonempty D hD
  exact ⟨p, Finset.mem_biUnion.mpr ⟨D, hD, hp⟩⟩

/-! ## The two-vertex lower bound on a relevant side -/

/-- Exact local data used for one of the two boundary vertices `y_A,z_A`
in the proof that `C_A` cannot have cardinality zero or one.

If the side union were a singleton `d`, minimum degree at `d` would make it
adjacent to every vertex of the three-set `boundary`.  Triangle-freeness then
forbids all boundary-boundary edges.  It also forbids the possible matched
edge from `anchor` because `terminal` is adjacent to both ends.  The displayed
location condition would leave `anchor` with at most the two neighbours
`d,terminal`, contradicting minimum degree three. -/
structure AHTRelevantTripleSideLocal (G : SimpleGraph V) where
  carrier : Finset V
  boundary : Finset V
  anchor : V
  terminal : V
  matched : V
  carrier_nonempty : carrier.Nonempty
  carrier_disjoint_boundary : Disjoint carrier boundary
  boundary_card : boundary.card = 3
  external_boundary : HasExternalBoundaryIn G carrier boundary
  anchor_mem : anchor ∈ boundary
  anchor_adj_terminal : G.Adj anchor terminal
  terminal_adj_matched : G.Adj terminal matched
  anchor_neighbor_location :
    ∀ ⦃q : V⦄, G.Adj anchor q →
      q ∈ carrier ∨ q = terminal ∨ q ∈ boundary ∨ q = matched

/-- Triangle-freeness and minimum degree three force at least two vertices
in each relevant same-side component union. -/
theorem AHTRelevantTripleSideLocal.two_le_card
    (S : AHTRelevantTripleSideLocal G)
    (htri : AHTTriangleFree G) (hmin : ∀ p : V, 3 ≤ G.degree p) :
    2 ≤ S.carrier.card := by
  by_contra hcard
  have hle : S.carrier.card ≤ 1 := by omega
  obtain ⟨d, hd⟩ := S.carrier_nonempty
  have hcarrier : S.carrier = {d} := by
    have hpos : 0 < S.carrier.card := Finset.card_pos.mpr S.carrier_nonempty
    have hone : S.carrier.card = 1 := by omega
    obtain ⟨e, he⟩ := Finset.card_eq_one.mp hone
    have hde : d = e := by simpa [he] using hd
    simpa [hde] using he
  have hdNsub : G.neighborFinset d ⊆ S.boundary := by
    intro q hq
    have hdq : G.Adj d q := by simpa using hq
    apply S.external_boundary d hd q hdq
    rw [hcarrier]
    simp only [Finset.mem_singleton]
    exact hdq.ne.symm
  have hNcard : 3 ≤ (G.neighborFinset d).card := by
    simpa only [G.card_neighborFinset_eq_degree] using hmin d
  have hneighbors : G.neighborFinset d = S.boundary := by
    apply Finset.eq_of_subset_of_card_le hdNsub
    rw [S.boundary_card]
    exact hNcard
  have hboundarySub : S.boundary ⊆ G.neighborFinset d := by
    rw [hneighbors]
  have hda : G.Adj d S.anchor := by
    exact (by simpa using hboundarySub S.anchor_mem)
  have hanchorSub : G.neighborFinset S.anchor ⊆ {d, S.terminal} := by
    intro q hq
    have haq : G.Adj S.anchor q := by simpa using hq
    rcases S.anchor_neighbor_location haq with hqC | rfl | hqA | rfl
    · have : q = d := by simpa [hcarrier] using hqC
      simp [this]
    · simp
    · by_cases hqa : q = S.anchor
      · subst q
        exact False.elim (G.loopless.irrefl S.anchor haq)
      · have hdq : G.Adj d q := by
          exact (by simpa using hboundarySub hqA)
        exact False.elim (htri hda.symm hdq haq.symm)
    · exact False.elim
        (htri S.anchor_adj_terminal S.terminal_adj_matched haq.symm)
  have hdegreeLe : G.degree S.anchor ≤ 2 := by
    rw [← G.card_neighborFinset_eq_degree]
    exact (Finset.card_le_card hanchorSub).trans (aht_card_pair_le _ _)
  have hdegreeGe := hmin S.anchor
  exact (by omega : False)

/-! ## The source three-boundary fragment certificate -/

/-- The concrete forbidden-fragment package used against claim (5) (the
first numbered claim in the source proof of Theorem 6.6).  It records both
strict sides, their common three-vertex boundary, and the twin pair on the
large side. -/
structure AHTClaimOneFragmentCertificate
    (G : SimpleGraph V) [DecidableRel G.Adj] where
  fragment : Finset V
  opposite : Finset V
  boundary : Finset V
  partition : fragment ∪ boundary ∪ opposite = Finset.univ
  fragment_disjoint_boundary : Disjoint fragment boundary
  opposite_disjoint_boundary : Disjoint opposite boundary
  fragment_disjoint_opposite : Disjoint fragment opposite
  fragment_boundary : HasExternalBoundaryIn G fragment boundary
  opposite_boundary : HasExternalBoundaryIn G opposite boundary
  fragment_meets_boundary :
    ∀ a ∈ boundary, ∃ f ∈ fragment, G.Adj f a
  opposite_meets_boundary :
    ∀ a ∈ boundary, ∃ c ∈ opposite, G.Adj c a
  boundary_card : boundary.card = 3
  six_le_fragment : 6 ≤ fragment.card
  two_le_opposite : 2 ≤ opposite.card
  twinLeft : V
  twinRight : V
  twins : AHTTwinPair G twinLeft twinRight
  twinLeft_mem : twinLeft ∈ fragment
  twinRight_mem : twinRight ∈ fragment

/-- Given the `A`-side union `C_A`, its set-theoretic complement away from
`A` has the same external boundary. -/
theorem externalBoundary_complement_away
    (C A : Finset V) (hCA : Disjoint C A)
    (hboundary : HasExternalBoundaryIn G C A) :
    HasExternalBoundaryIn G (Finset.univ \ (C ∪ A)) A := by
  intro p hp q hpq hqF
  have hqOutside : q ∈ C ∪ A := by
    by_contra hq
    exact hqF (by simpa [hq])
  rcases Finset.mem_union.mp hqOutside with hqC | hqA
  · have hpC : p ∉ C := by
      have hp' := Finset.mem_sdiff.mp hp
      exact fun hpC ↦ hp'.2 (Finset.mem_union_left _ hpC)
    have hpA : p ∈ A := hboundary q hqC p hpq.symm hpC
    have hp' := Finset.mem_sdiff.mp hp
    exact False.elim (hp'.2 (Finset.mem_union_right _ hpA))
  · exact hqA

/-- Package the first branch of source claim (8) as the precise
three-boundary fragment certificate.  The nontrivial estimate
`2 ≤ |C_A|` is supplied by `AHTRelevantTripleSideLocal.two_le_card`; the
large-side and twin facts are the direct splitter membership bookkeeping. -/
theorem ahtClaimOneFragmentCertificate_of_threeBoundarySide
    (C A : Finset V) {p q : V}
    (hthree : IsThreeConnected G)
    (hCA : Disjoint C A)
    (hboundary : HasExternalBoundaryIn G C A)
    (hAcard : A.card = 3)
    (hCcard : 2 ≤ C.card)
    (hpq : AHTTwinPair G p q)
    (hp : p ∈ Finset.univ \ (C ∪ A))
    (hq : q ∈ Finset.univ \ (C ∪ A))
    (hlarge : 6 ≤ (Finset.univ \ (C ∪ A)).card) :
    Nonempty (AHTClaimOneFragmentCertificate G) := by
  let F := Finset.univ \ (C ∪ A)
  have hFC : Disjoint F C := by
    apply Finset.disjoint_left.mpr
    intro z hzF hzC
    exact (Finset.mem_sdiff.mp hzF).2 (Finset.mem_union_left _ hzC)
  have hFA : Disjoint F A := by
    apply Finset.disjoint_left.mpr
    intro z hzF hzA
    exact (Finset.mem_sdiff.mp hzF).2 (Finset.mem_union_right _ hzA)
  have hpartition : F ∪ A ∪ C = Finset.univ := by
    ext z
    by_cases hzC : z ∈ C <;> by_cases hzA : z ∈ A <;>
      simp [F, hzC, hzA]
  have hFboundary : HasExternalBoundaryIn G F A :=
    externalBoundary_complement_away C A hCA hboundary
  have hCnonempty : C.Nonempty := Finset.card_pos.mp (by omega)
  have hFcard : 6 ≤ F.card := by
    simpa only [F] using hlarge
  have hFnonempty : F.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨c, hcC⟩ := hCnonempty
  have hcA : c ∉ A := fun hcA ↦
    Finset.disjoint_left.mp hCA hcC hcA
  have hcF : c ∉ F := fun hcF ↦
    Finset.disjoint_left.mp hFC hcF hcC
  have hpC : p ∉ C := by
    have hp' := Finset.mem_sdiff.mp hp
    exact fun hpC ↦ hp'.2 (Finset.mem_union_left _ hpC)
  have hpA : p ∉ A := by
    have hp' := Finset.mem_sdiff.mp hp
    exact fun hpA ↦ hp'.2 (Finset.mem_union_right _ hpA)
  have hFtight := externalBoundary_tight_of_card_three
    hthree F A hFA hFboundary hFnonempty hAcard hcF hcA
  have hCtight := externalBoundary_tight_of_card_three
    hthree C A hCA hboundary ⟨c, hcC⟩ hAcard hpC hpA
  exact ⟨{
    fragment := F
    opposite := C
    boundary := A
    partition := hpartition
    fragment_disjoint_boundary := hFA
    opposite_disjoint_boundary := hCA
    fragment_disjoint_opposite := hFC
    fragment_boundary := hFboundary
    opposite_boundary := hboundary
    fragment_meets_boundary := hFtight
    opposite_meets_boundary := hCtight
    boundary_card := hAcard
    six_le_fragment := hlarge
    two_le_opposite := hCcard
    twinLeft := p
    twinRight := q
    twins := hpq
    twinLeft_mem := hp
    twinRight_mem := hq }⟩

/-- End-to-end local form of the `|A|=|B|=3` branch: the relevant-side
data, triangle-freeness, and minimum degree supply the two-vertex opposite
side automatically, after which the complement is packaged as the exact
large three-boundary fragment from claim (5). -/
theorem ahtClaimOneFragmentCertificate_of_relevantTripleSide
    (S : AHTRelevantTripleSideLocal G) {p q : V}
    (hthree : IsThreeConnected G)
    (htri : AHTTriangleFree G) (hmin : ∀ z : V, 3 ≤ G.degree z)
    (hpq : AHTTwinPair G p q)
    (hp : p ∈ Finset.univ \ (S.carrier ∪ S.boundary))
    (hq : q ∈ Finset.univ \ (S.carrier ∪ S.boundary))
    (hlarge : 6 ≤
      (Finset.univ \ (S.carrier ∪ S.boundary)).card) :
    Nonempty (AHTClaimOneFragmentCertificate G) := by
  exact ahtClaimOneFragmentCertificate_of_threeBoundarySide
    S.carrier S.boundary hthree S.carrier_disjoint_boundary
    S.external_boundary S.boundary_card (S.two_le_card htri hmin)
    hpq hp hq hlarge

end Erdos916
