/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceLemma64
import ErdosProblems.Erdos916.AHTSourceLemma65

/-!
# The replacement-pair step in AHT Theorem 6.6

This file formalizes the unconditional graph-theoretic core of claim (7) in
the proof of Theorem 6.6 of Aboulker--Havet--Trotignon.  The proof replaces a
fragment `X` by a graph containing a deliberately added pair of degree-three
false twins.  Minimality supplies two disjoint twin pairs in that replacement.
The first result below shows, without making any assumption about which pairs
minimality selected, that some degree-three twin pair consists entirely of old
vertices.

The only exceptional old pair in the source construction is the pair of
boundary vertices.  In that case both boundaries have the same third
neighbour `x'` in `X`; the construction makes `{x',v}` a two-vertex gate
between `X \ {x'}` and a boundary vertex.  The second part of this file
constructs that separation explicitly and proves that three-connectivity
forces `X = {x'}`.  These lemmas contain no minimality principle: the global
minimal-counterexample and splitter arguments only have to supply their
displayed concrete replacement and gate hypotheses.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Extracting an old pair from the double-pin replacement -/

/-- If two disjoint twin pairs both meet a fixed twin pair, their opposite
endpoints form another twin pair, disjoint from the fixed one. -/
private theorem cross_pairs_give_pair_away
    {a p b q : V}
    (hap : AreFalseTwins G a p) (hbq : AreFalseTwins G b q)
    (hab : AreFalseTwins G a b)
    (hdisj : Disjoint ({a, p} : Finset V) {b, q})
    (hdegp : G.degree p = 3) :
    ∃ r s : V, AHTTwinPair G r s ∧
      r ≠ a ∧ r ≠ b ∧ s ≠ a ∧ s ≠ b := by
  have hd := Finset.disjoint_left.mp hdisj
  have hpa : p ≠ a := hap.1.symm
  have hpb : p ≠ b := by
    intro h
    exact hd (a := p) (by simp) (by simpa [h])
  have hqa : q ≠ a := by
    intro h
    exact hd (a := q) (by simpa [h]) (by simp)
  have hqb : q ≠ b := hbq.1.symm
  have hpq : p ≠ q := by
    intro h
    exact hd (a := p) (by simp) (by simpa [h])
  have htwins : AreFalseTwins G p q := by
    refine ⟨hpq, ?_⟩
    exact hap.2.symm.trans (hab.2.trans hbq.2)
  exact ⟨p, q, ⟨htwins, hdegp⟩, hpa, hpb, hqa, hqb⟩

/-- Resolve the case in which each of two disjoint pairs has a chosen
endpoint in the fixed pair. -/
private theorem resolve_pair_hits
    {n₀ n₁ a p b q : V}
    (hn : AreFalseTwins G n₀ n₁)
    (ha : a ∈ ({n₀, n₁} : Finset V))
    (hb : b ∈ ({n₀, n₁} : Finset V))
    (hap : AreFalseTwins G a p) (hbq : AreFalseTwins G b q)
    (hdegp : G.degree p = 3)
    (hd : Disjoint ({a, p} : Finset V) {b, q}) :
    ∃ r s : V, AHTTwinPair G r s ∧
      r ∉ ({n₀, n₁} : Finset V) ∧ s ∉ ({n₀, n₁} : Finset V) := by
  have habne : a ≠ b := by
    intro hab
    subst b
    have hdl := Finset.disjoint_left.mp hd
    exact hdl (a := a) (Finset.mem_insert_self a {p})
      (Finset.mem_insert_self a {q})
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact False.elim (habne rfl)
    · obtain ⟨r, s, hrs, hr₀, hr₁, hs₀, hs₁⟩ :=
        cross_pairs_give_pair_away hap hbq hn hd hdegp
      exact ⟨r, s, hrs, by simpa only [Finset.mem_insert,
        Finset.mem_singleton, not_or] using And.intro hr₀ hr₁,
        by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or]
          using And.intro hs₀ hs₁⟩
  · rcases hb with rfl | rfl
    · obtain ⟨r, s, hrs, hr₁, hr₀, hs₁, hs₀⟩ :=
        cross_pairs_give_pair_away hap hbq hn.symm hd hdegp
      exact ⟨r, s, hrs, by simpa only [Finset.mem_insert,
        Finset.mem_singleton, not_or] using And.intro hr₀ hr₁,
        by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or]
          using And.intro hs₀ hs₁⟩
    · exact False.elim (habne rfl)

/-- A graph containing a fixed false-twin pair and two further disjoint
degree-three false-twin pairs contains a degree-three false-twin pair avoiding
both fixed vertices.  This also covers the apparently awkward case in which
each of the two supplied pairs uses one fixed vertex. -/
theorem exists_ahtTwinPair_away_of_twoDisjointPairs
    {n₀ n₁ : V} (hn : AreFalseTwins G n₀ n₁)
    (T : TwoDisjointDegreeThreeFalseTwinPairs G) :
    ∃ p q : V, AHTTwinPair G p q ∧
      p ∉ ({n₀, n₁} : Finset V) ∧ q ∉ ({n₀, n₁} : Finset V) := by
  classical
  by_cases huv : Disjoint ({T.u, T.v} : Finset V) {n₀, n₁}
  · refine ⟨T.u, T.v, ⟨T.twin_uv, T.degree_u⟩, ?_, ?_⟩
    · exact fun h ↦ (Finset.disjoint_left.mp huv (by simp) h)
    · exact fun h ↦ (Finset.disjoint_left.mp huv (by simp) h)
  by_cases hxy : Disjoint ({T.x, T.y} : Finset V) {n₀, n₁}
  · refine ⟨T.x, T.y, ⟨T.twin_xy, T.degree_x⟩, ?_, ?_⟩
    · exact fun h ↦ (Finset.disjoint_left.mp hxy (by simp) h)
    · exact fun h ↦ (Finset.disjoint_left.mp hxy (by simp) h)
  have huv' : ∃ z, z ∈ ({T.u, T.v} : Finset V) ∧
      z ∈ ({n₀, n₁} : Finset V) := by
    exact Finset.not_disjoint_iff.mp huv
  have hxy' : ∃ z, z ∈ ({T.x, T.y} : Finset V) ∧
      z ∈ ({n₀, n₁} : Finset V) := by
    exact Finset.not_disjoint_iff.mp hxy
  obtain ⟨z, hzuv, hzn⟩ := huv'
  obtain ⟨w, hwxy, hwn⟩ := hxy'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzuv hwxy
  rcases hzuv with rfl | rfl
  · rcases hwxy with rfl | rfl
    · exact resolve_pair_hits hn hzn hwn T.twin_uv T.twin_xy
        T.degree_v T.disjoint
    · have hd : Disjoint ({T.u, T.v} : Finset V) {T.y, T.x} := by
        rw [show ({T.y, T.x} : Finset V) = {T.x, T.y} by
          ext r; simp [or_comm]]
        exact T.disjoint
      exact resolve_pair_hits hn hzn hwn T.twin_uv T.twin_xy.symm
        T.degree_v hd
  · rcases hwxy with rfl | rfl
    · have hd : Disjoint ({T.v, T.u} : Finset V) {T.x, T.y} := by
        rw [show ({T.v, T.u} : Finset V) = {T.u, T.v} by
          ext r; simp [or_comm]]
        exact T.disjoint
      exact resolve_pair_hits hn hzn hwn T.twin_uv.symm T.twin_xy
        T.degree_u hd
    · have hd : Disjoint ({T.v, T.u} : Finset V) {T.y, T.x} := by
        rw [show ({T.v, T.u} : Finset V) = {T.u, T.v} by
          ext r; simp [or_comm]]
        rw [show ({T.y, T.x} : Finset V) = {T.x, T.y} by
          ext r; simp [or_comm]]
        exact T.disjoint
      exact resolve_pair_hits hn hzn hwn T.twin_uv.symm T.twin_xy.symm
        T.degree_u hd

/-- Specialization to the AHT double-pin replacement: from any two disjoint
degree-three twin pairs in the replacement, one can extract a pair consisting
of two old torso vertices. -/
theorem ahtDoublePinReplacement_exists_old_twinPair
    {H : SimpleGraph V} [DecidableRel H.Adj] {a b c : V}
    (T : TwoDisjointDegreeThreeFalseTwinPairs
      (ahtDoublePinReplacement H a b c)) :
    ∃ p q : V, AHTTwinPair (ahtDoublePinReplacement H a b c)
      (.inl p) (.inl q) := by
  obtain ⟨p, q, hpq, hp, hq⟩ :=
    exists_ahtTwinPair_away_of_twoDisjointPairs
      (ahtDoublePinReplacement.new_vertices_areFalseTwins
        (H := H) (a := a) (b := b) (c := c)) T
  rcases p with p | i
  · rcases q with q | j
    · exact ⟨p, q, hpq⟩
    · fin_cases j <;> simp at hq
  · fin_cases i <;> simp at hp

/-- Equality of neighbourhoods for an old pair in the replacement restricts
to equality of neighbourhoods in the prepared torso. -/
theorem ahtDoublePinReplacement_old_falseTwins
    {H : SimpleGraph V} [DecidableRel H.Adj] {a b c p q : V}
    (h : AreFalseTwins (ahtDoublePinReplacement H a b c)
      (.inl p) (.inl q)) :
    AreFalseTwins H p q := by
  refine ⟨fun hpq ↦ h.1 (congrArg Sum.inl hpq), ?_⟩
  ext r
  have hadj := h.adj_iff (.inl r)
  simpa using hadj

/-! ## The exceptional boundary pair gives an order-two separation -/

/-- The explicit separation through the two gate vertices `x` and `v`.
Its left side is `X ∪ {v}` and its right side is the complement of `X`
together with the two gates. -/
def ahtTwoVertexGateSeparation
    (G : SimpleGraph V) (X : Finset V) (x v : V)
    (hx : x ∈ X)
    (hgate : ∀ ⦃p q : V⦄, p ∈ X → p ≠ x →
      q ∉ X → q ≠ v → ¬G.Adj p q) :
    AHTSeparation G where
  left := X ∪ {v}
  right := (Finset.univ \ X) ∪ {x, v}
  cover := by
    ext z
    by_cases hz : z ∈ X <;> simp [hz]
  not_adj := by
    intro p q hpL hpR hqR hqL
    have hpX : p ∈ X := by
      rcases Finset.mem_union.mp hpL with hpX | hpv
      · exact hpX
      · have hpv' : p = v := by simpa using hpv
        subst p
        exact False.elim (hpR (by simp))
    have hpx : p ≠ x := by
      intro h
      subst p
      exact hpR (by simp)
    have hqX : q ∉ X := by
      intro hqX
      exact hqL (Finset.mem_union_left _ hqX)
    have hqv : q ≠ v := by
      intro h
      subst q
      exact hqL (by simp)
    exact hgate hpX hpx hqX hqv

/-- The separator of the gate separation is exactly `{x,v}`. -/
theorem ahtTwoVertexGateSeparation_separator
    (X : Finset V) {x v : V} (hx : x ∈ X) (hv : v ∉ X)
    (hgate : ∀ ⦃p q : V⦄, p ∈ X → p ≠ x →
      q ∉ X → q ≠ v → ¬G.Adj p q) :
    (ahtTwoVertexGateSeparation G X x v hx hgate).separator = {x, v} := by
  ext z
  by_cases hzx : z = x
  · subst z
    simp [AHTSeparation.separator, ahtTwoVertexGateSeparation, hx]
  by_cases hzv : z = v
  · subst z
    simp [AHTSeparation.separator, ahtTwoVertexGateSeparation, hv]
  · simp [AHTSeparation.separator, ahtTwoVertexGateSeparation, hzx, hzv]

/-- If `X` has a vertex besides `x` and the other side has a vertex besides
`v`, the gate separation is proper. -/
theorem ahtTwoVertexGateSeparation_proper
    (X : Finset V) {x v y q : V}
    (hx : x ∈ X) (hv : v ∉ X)
    (hy : y ∉ X) (hyv : y ≠ v)
    (hq : q ∈ X) (hqx : q ≠ x)
    (hgate : ∀ ⦃p r : V⦄, p ∈ X → p ≠ x →
      r ∉ X → r ≠ v → ¬G.Adj p r) :
    (ahtTwoVertexGateSeparation G X x v hx hgate).Proper := by
  constructor
  · refine ⟨q, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_union_left _ hq
    · have hqv : q ≠ v := fun h ↦ hv (h ▸ hq)
      simp [ahtTwoVertexGateSeparation, hq, hqx, hqv]
  · refine ⟨y, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_union_left _ (by simp [hy])
    · simp [ahtTwoVertexGateSeparation, hy, hyv]

/-- The exceptional boundary-pair branch of AHT claim (7): in a
three-connected replacement, a fragment separated from a surviving boundary
vertex by the two gates `x,v` has no vertex other than `x`. -/
theorem card_eq_one_of_threeConnected_of_twoVertexGate
    (X : Finset V) {x v y : V}
    (hthree : IsThreeConnected G)
    (hx : x ∈ X) (hv : v ∉ X)
    (hy : y ∉ X) (hyv : y ≠ v)
    (hgate : ∀ ⦃p q : V⦄, p ∈ X → p ≠ x →
      q ∉ X → q ≠ v → ¬G.Adj p q) :
    X.card = 1 := by
  have hall : ∀ q ∈ X, q = x := by
    intro q hq
    by_contra hqx
    have hproper := ahtTwoVertexGateSeparation_proper
      (G := G) X hx hv hy hyv hq hqx hgate
    have horder := hthree.2
      (ahtTwoVertexGateSeparation G X x v hx hgate) hproper
    rw [AHTSeparation.order,
      ahtTwoVertexGateSeparation_separator X hx hv hgate] at horder
    have hxv : x ≠ v := fun h ↦ hv (h ▸ hx)
    simp [hxv] at horder
  have hX : X = {x} := by
    apply Finset.Subset.antisymm
    · intro q hq
      simpa [hall q hq]
    · intro q hq
      have hqx : q = x := by simpa only [Finset.mem_singleton] using hq
      subst q
      exact hx
  simp [hX]

/-- Source-shaped combination of the two unconditional branches of claim
(7).  Upstream replacement/minimality supplies the displayed concrete
alternative: either the old replacement pair already lies in `X` and lifts
to `G`, or the exceptional boundary pair exposes the two-vertex gate. -/
theorem aht_theorem66_claim7_of_replacement_alternative
    (X : Finset V)
    (hbranch :
      (∃ p ∈ X, ∃ q ∈ X, AHTTwinPair G p q) ∨
      ∃ x v y : V,
        IsThreeConnected G ∧ x ∈ X ∧ v ∉ X ∧ y ∉ X ∧ y ≠ v ∧
        ∀ ⦃p q : V⦄, p ∈ X → p ≠ x →
          q ∉ X → q ≠ v → ¬G.Adj p q) :
    X.card = 1 ∨ ∃ p ∈ X, ∃ q ∈ X, AHTTwinPair G p q := by
  rcases hbranch with hpair | ⟨x, v, y, hthree, hx, hv, hy, hyv, hgate⟩
  · exact Or.inr hpair
  · exact Or.inl <|
      card_eq_one_of_threeConnected_of_twoVertexGate
        X hthree hx hv hy hyv hgate

/-- Claim (7) connected directly to the concrete double-pin replacement.
The hypothesis `hclassify` is the local adjacency calculation for the
prepared torso: it says that the old pair extracted from the replacement is
either an ambient twin pair inside `X`, or the exceptional boundary pair,
in which case it returns the actual two-gate separation data.  In
particular, this theorem takes a concrete two-pair certificate rather than a
principle asserting that such certificates exist. -/
theorem aht_theorem66_claim7_of_doublePinReplacement_classification
    {H : SimpleGraph V} [DecidableRel H.Adj] {a b c : V}
    (X : Finset V)
    (T : TwoDisjointDegreeThreeFalseTwinPairs
      (ahtDoublePinReplacement H a b c))
    (hclassify : ∀ p q : V,
      AHTTwinPair (ahtDoublePinReplacement H a b c) (.inl p) (.inl q) →
        (∃ r ∈ X, ∃ s ∈ X, AHTTwinPair G r s) ∨
        ∃ x v y : V ⊕ Fin 2,
          IsThreeConnected (ahtDoublePinReplacement H a b c) ∧
          x ∈ X.map ahtDoublePinReplacement.oldVertexEmbedding ∧
          v ∉ X.map ahtDoublePinReplacement.oldVertexEmbedding ∧
          y ∉ X.map ahtDoublePinReplacement.oldVertexEmbedding ∧ y ≠ v ∧
          ∀ ⦃r s : V ⊕ Fin 2⦄,
            r ∈ X.map ahtDoublePinReplacement.oldVertexEmbedding → r ≠ x →
            s ∉ X.map ahtDoublePinReplacement.oldVertexEmbedding → s ≠ v →
            ¬(ahtDoublePinReplacement H a b c).Adj r s) :
    X.card = 1 ∨ ∃ r ∈ X, ∃ s ∈ X, AHTTwinPair G r s := by
  obtain ⟨p, q, hpq⟩ :=
    ahtDoublePinReplacement_exists_old_twinPair (T := T)
  rcases hclassify p q hpq with hpair |
      ⟨x, v, y, hthree, hx, hv, hy, hyv, hgate⟩
  · exact Or.inr hpair
  · left
    have hcard := card_eq_one_of_threeConnected_of_twoVertexGate
      (X.map ahtDoublePinReplacement.oldVertexEmbedding)
      hthree hx hv hy hyv hgate
    simpa using hcard

end Erdos916
