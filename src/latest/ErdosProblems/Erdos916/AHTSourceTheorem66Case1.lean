/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.AHTSourceTheorem66Case3

/-!
# The large-complement fragment claim in AHT Theorem 6.6

This file isolates the unconditional replacement calculation in claim (1)
of Theorem 6.6 of Aboulker--Havet--Trotignon.  Two disjoint twin pairs in
the double-pin replacement yield an old pair.  Such an old pair is either a
pair of non-pins, in which case it is already a degree-three twin pair in the
prepared torso, or a pair of pins, each of old-torso degree one.

In the exceptional pin-pair branch, the two pins must be identified with
their original boundary vertices.  Their common old neighbour and the
original boundary vertex underlying the third pin form an order-two gate.
Three-connectivity of the replacement then forces the retained fragment to
consist only of that common neighbour.  This is the contradiction with the
hypothesis that the fragment has at least two vertices in source claim (1).

The construction of the prepared torso from an ambient fragment, and the
cardinality comparison which makes its replacement smaller, belong to the
full Lemma 6.4 API.  The results below make the exact concrete output needed
from that API explicit; they do not assume a replacement or minimality
principle.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
variable {a b c : V}

private abbrev IsDoublePin (a b c p : V) : Prop :=
  p = a ∨ p = b ∨ p = c

/-! ## Old vertices in the double-pin replacement -/

/-- A non-pin old vertex gains no neighbour in the double-pin operation. -/
theorem ahtDoublePinReplacement_neighborFinset_old_nonpin
    {p : V} (hp : ¬IsDoublePin a b c p) :
    (ahtDoublePinReplacement H a b c).neighborFinset (.inl p) =
      (H.neighborFinset p).map
        ahtDoublePinReplacement.oldVertexEmbedding := by
  ext z
  rcases z with q | i
  · simp [SimpleGraph.mem_neighborFinset,
      ahtDoublePinReplacement.oldVertexEmbedding]
  · constructor
    · intro h
      rw [SimpleGraph.mem_neighborFinset] at h
      exact (hp (ahtDoublePinReplacement.adj_old_new_iff.mp h)).elim
    · intro h
      obtain ⟨q, -, hq⟩ := Finset.mem_map.mp h
      change (Sum.inl q : V ⊕ Fin 2) = Sum.inr i at hq
      exact (Sum.inl_ne_inr hq).elim

/-- Consequently the degree of a non-pin old vertex is unchanged. -/
theorem ahtDoublePinReplacement_degree_old_nonpin
    {p : V} (hp : ¬IsDoublePin a b c p) :
    (ahtDoublePinReplacement H a b c).degree (.inl p) = H.degree p := by
  rw [← (ahtDoublePinReplacement H a b c).card_neighborFinset_eq_degree,
    ahtDoublePinReplacement_neighborFinset_old_nonpin hp,
    Finset.card_map, H.card_neighborFinset_eq_degree]

/-- False twins among old replacement vertices are simultaneously pins or
simultaneously non-pins: adjacency to either newly adjoined vertex detects
exactly the pins. -/
theorem ahtDoublePinReplacement_isDoublePin_iff_of_old_falseTwins
    {p q : V}
    (hpq : AreFalseTwins (ahtDoublePinReplacement H a b c)
      (.inl p) (.inl q)) :
    IsDoublePin a b c p ↔ IsDoublePin a b c q := by
  have h := hpq.adj_iff (.inr (0 : Fin 2))
  simpa only [ahtDoublePinReplacement.adj_old_new_iff] using h

/-- Complete classification of a degree-three old pair in the double-pin
replacement.  Away from the pins the pair lifts verbatim to the old torso;
at the pins, both old-torso degrees are one. -/
theorem ahtDoublePinReplacement_old_twinPair_classification
    {p q : V}
    (hpq : AHTTwinPair (ahtDoublePinReplacement H a b c)
      (.inl p) (.inl q)) :
    (¬IsDoublePin a b c p ∧ ¬IsDoublePin a b c q ∧
        AHTTwinPair H p q) ∨
      (IsDoublePin a b c p ∧ IsDoublePin a b c q ∧
        AreFalseTwins H p q ∧ H.degree p = 1 ∧ H.degree q = 1) := by
  have hpPinIff : IsDoublePin a b c p ↔ IsDoublePin a b c q :=
    ahtDoublePinReplacement_isDoublePin_iff_of_old_falseTwins hpq.falseTwins
  have hpqH : AreFalseTwins H p q :=
    ahtDoublePinReplacement_old_falseTwins hpq.falseTwins
  by_cases hpPin : IsDoublePin a b c p
  · right
    have hqPin : IsDoublePin a b c q := hpPinIff.mp hpPin
    have hpDegree := hpq.degree_left
    have hqDegree := hpq.degree_right
    rw [ahtDoublePinReplacement.degree_old_pin hpPin] at hpDegree
    rw [ahtDoublePinReplacement.degree_old_pin hqPin] at hqDegree
    exact ⟨hpPin, hqPin, hpqH, by omega, by omega⟩
  · left
    have hqPin : ¬IsDoublePin a b c q := by
      exact fun hq ↦ hpPin (hpPinIff.mpr hq)
    have hpDegree := hpq.degree_left
    rw [ahtDoublePinReplacement_degree_old_nonpin hpPin] at hpDegree
    exact ⟨hpPin, hqPin, hpqH, hpDegree⟩

/-- From the two disjoint pairs supplied by minimality in a double-pin
replacement one extracts an old pair together with its complete pin/non-pin
classification. -/
theorem ahtDoublePinReplacement_twoPairs_classification
    (T : TwoDisjointDegreeThreeFalseTwinPairs
      (ahtDoublePinReplacement H a b c)) :
    ∃ p q : V,
      AHTTwinPair (ahtDoublePinReplacement H a b c) (.inl p) (.inl q) ∧
      ((¬IsDoublePin a b c p ∧ ¬IsDoublePin a b c q ∧
          AHTTwinPair H p q) ∨
        (IsDoublePin a b c p ∧ IsDoublePin a b c q ∧
          AreFalseTwins H p q ∧ H.degree p = 1 ∧ H.degree q = 1)) := by
  obtain ⟨p, q, hpq⟩ :=
    ahtDoublePinReplacement_exists_old_twinPair (T := T)
  exact ⟨p, q, hpq,
    ahtDoublePinReplacement_old_twinPair_classification hpq⟩

/-- Two distinct members of the three-pin set have a unique remaining pin,
recorded here in the set form used by the gate argument. -/
theorem exists_third_doublePin
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {p q : V} (hpq : p ≠ q)
    (hp : IsDoublePin a b c p) (hq : IsDoublePin a b c q) :
    ∃ r : V, p ≠ r ∧ q ≠ r ∧
      ({p, q, r} : Finset V) = {a, b, c} := by
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl
  · exact (hpq rfl).elim
  · refine ⟨c, hac, hbc, ?_⟩
    rfl
  · refine ⟨b, hab, hbc.symm, ?_⟩
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · refine ⟨c, hbc, hac, ?_⟩
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exact (hpq rfl).elim
  · refine ⟨a, hab.symm, hac.symm, ?_⟩
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · refine ⟨b, hbc.symm, hab, ?_⟩
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · refine ⟨a, hac.symm, hab.symm, ?_⟩
    ext z
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto
  · exact (hpq rfl).elim

/-- Concrete lift of the non-pin branch to an ambient graph.  The two
displayed neighbourhood equalities are exactly what the fragment
construction supplies for vertices wholly in the retained interior. -/
theorem ahtDoublePinReplacement_old_nonpin_twinPair_lift
    {p q : V}
    (hpq : AHTTwinPair (ahtDoublePinReplacement H a b c)
      (.inl p) (.inl q))
    (hp : ¬IsDoublePin a b c p)
    (hNp : G.neighborFinset p = H.neighborFinset p)
    (hNq : G.neighborFinset q = H.neighborFinset q) :
    AHTTwinPair G p q := by
  rcases ahtDoublePinReplacement_old_twinPair_classification hpq with
      ⟨-, -, hpqH⟩ | ⟨hpPin, -⟩
  · have hfin : G.neighborFinset p = G.neighborFinset q :=
      hNp.trans (hpqH.falseTwins.neighborFinset_eq.trans hNq.symm)
    have hfalse : AreFalseTwins G p q := by
      refine ⟨hpqH.falseTwins.1, ?_⟩
      ext z
      have hz := Finset.ext_iff.mp hfin z
      simpa only [SimpleGraph.mem_neighborSet,
        ← SimpleGraph.mem_neighborFinset] using hz
    have hdegree : G.degree p = 3 := by
      rw [← G.card_neighborFinset_eq_degree, hNp,
        H.card_neighborFinset_eq_degree, hpqH.degree_left]
    exact ⟨hfalse, hdegree⟩
  · exact (hp hpPin).elim

/-! ## Combining a retained and a complementary pair -/

/-- A twin pair contained in a fragment and another twin pair contained in
its complement form the forbidden two-pair certificate. -/
theorem twoDisjointPairs_of_mem_and_not_mem
    (F : Finset V) {p q r s : V}
    (hpq : AHTTwinPair G p q) (hp : p ∈ F) (hq : q ∈ F)
    (hrs : AHTTwinPair G r s) (hr : r ∉ F) (hs : s ∉ F) :
    Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G) := by
  refine ⟨{
    u := p
    v := q
    x := r
    y := s
    twin_uv := hpq.falseTwins
    twin_xy := hrs.falseTwins
    degree_u := hpq.degree_left
    degree_x := hrs.degree_left
    disjoint := ?_ }⟩
  apply Finset.disjoint_left.mpr
  intro z hzF hzC
  simp only [Finset.mem_insert, Finset.mem_singleton] at hzF hzC
  rcases hzF with rfl | rfl
  · rcases hzC with h | h
    · exact hr (h ▸ hp)
    · exact hs (h ▸ hp)
  · rcases hzC with h | h
    · exact hr (h ▸ hq)
    · exact hs (h ▸ hq)

/-- In a counterexample with no two disjoint pairs, a pair in the
complement rules out every pair contained in the retained fragment. -/
theorem no_twinPair_inside_of_complement_pair_of_no_twoDisjointPairs
    (F : Finset V)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    {r s : V} (hrs : AHTTwinPair G r s) (hr : r ∉ F) (hs : s ∉ F) :
    ¬∃ p ∈ F, ∃ q ∈ F, AHTTwinPair G p q := by
  rintro ⟨p, hp, q, hq, hpq⟩
  exact hno (twoDisjointPairs_of_mem_and_not_mem F hpq hp hq hrs hr hs)

/-! ## The exceptional boundary pair -/

/-- A degree-one vertex with a displayed neighbour has exactly that
singleton neighbourhood. -/
theorem neighborFinset_eq_singleton_of_degree_eq_one_of_adj
    {p x : V} (hdegree : H.degree p = 1) (hpx : H.Adj p x) :
    H.neighborFinset p = {x} := by
  have hcard : (H.neighborFinset p).card = 1 := by
    simpa only [H.card_neighborFinset_eq_degree] using hdegree
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard
  have hx : x ∈ H.neighborFinset p := by simpa using hpx
  have hxy : x = y := by simpa [hy] using hx
  simpa [hxy] using hy

/-- The source boundary calculation in the exceptional branch of claim
(1).  The retained set `F` has boundary among the three pins.  If two pins
are twins in the replacement and have a common neighbour `x ∈ F`, then the
third pin and `x` are a two-vertex gate.  Three-connectivity of the
replacement forces `F = {x}`. -/
theorem card_eq_one_of_doublePin_boundary_twinPair
    {p q r x : V} (F : Finset V)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hpins : ({p, q, r} : Finset V) = {a, b, c})
    (hpF : p ∉ F) (hqF : q ∉ F) (hrF : r ∉ F)
    (hxF : x ∈ F) (hpx : H.Adj p x)
    (hboundary : ∀ ⦃z w : V⦄, z ∈ F → w ∉ F → H.Adj z w →
      w = p ∨ w = q ∨ w = r)
    (htwin : AHTTwinPair (ahtDoublePinReplacement H a b c)
      (.inl p) (.inl q))
    (hthree : IsThreeConnected (ahtDoublePinReplacement H a b c)) :
    F.card = 1 := by
  let R := ahtDoublePinReplacement H a b c
  let e : V ↪ V ⊕ Fin 2 := ahtDoublePinReplacement.oldVertexEmbedding
  let X : Finset (V ⊕ Fin 2) := F.map e
  have hpPin : IsDoublePin a b c p := by
    have : p ∈ ({a, b, c} : Finset V) := by
      rw [← hpins]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hqPin : IsDoublePin a b c q := by
    have : q ∈ ({a, b, c} : Finset V) := by
      rw [← hpins]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hrPin : IsDoublePin a b c r := by
    have : r ∈ ({a, b, c} : Finset V) := by
      rw [← hpins]
      simp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using this
  have hdegreeP : H.degree p = 1 := by
    have h := htwin.degree_left
    rw [ahtDoublePinReplacement.degree_old_pin hpPin] at h
    omega
  have hdegreeQ : H.degree q = 1 := by
    have h := htwin.degree_right
    rw [ahtDoublePinReplacement.degree_old_pin hqPin] at h
    omega
  have hNp : H.neighborFinset p = {x} :=
    neighborFinset_eq_singleton_of_degree_eq_one_of_adj hdegreeP hpx
  have hqx : H.Adj q x := by
    have hfalseH := ahtDoublePinReplacement_old_falseTwins htwin.falseTwins
    exact (hfalseH.adj_iff x).mp hpx
  have hNq : H.neighborFinset q = {x} :=
    neighborFinset_eq_singleton_of_degree_eq_one_of_adj hdegreeQ hqx
  have hxX : (.inl x : V ⊕ Fin 2) ∈ X := by
    exact Finset.mem_map.mpr ⟨x, hxF, rfl⟩
  have hrX : (.inl r : V ⊕ Fin 2) ∉ X := by
    intro h
    obtain ⟨z, hzF, hz⟩ := Finset.mem_map.mp h
    exact hrF (Sum.inl.inj hz.symm ▸ hzF)
  have hpX : (.inl p : V ⊕ Fin 2) ∉ X := by
    intro h
    obtain ⟨z, hzF, hz⟩ := Finset.mem_map.mp h
    exact hpF (Sum.inl.inj hz.symm ▸ hzF)
  have hpr' : (.inl p : V ⊕ Fin 2) ≠ .inl r := by
    exact fun h ↦ hpr (Sum.inl.inj h)
  have hgate : ∀ ⦃z w : V ⊕ Fin 2⦄,
      z ∈ X → z ≠ .inl x → w ∉ X → w ≠ .inl r → ¬R.Adj z w := by
    intro z w hzX hzx hwX hwr hzw
    obtain ⟨z0, hz0F, rfl⟩ := Finset.mem_map.mp hzX
    have hz0x : z0 ≠ x := fun h ↦ hzx (congrArg Sum.inl h)
    rcases w with w0 | i
    · have hw0F : w0 ∉ F := by
        intro hw0F
        exact hwX (Finset.mem_map.mpr ⟨w0, hw0F, rfl⟩)
      have hw0r : w0 ≠ r := fun h ↦ hwr (congrArg Sum.inl h)
      have hzwH : H.Adj z0 w0 := hzw
      rcases hboundary hz0F hw0F hzwH with hwp | hwq | hwr0
      · have hz0N : z0 ∈ H.neighborFinset p := by
          simpa [hwp] using hzwH.symm
        rw [hNp] at hz0N
        exact hz0x (by simpa using hz0N)
      · have hz0N : z0 ∈ H.neighborFinset q := by
          simpa [hwq] using hzwH.symm
        rw [hNq] at hz0N
        exact hz0x (by simpa using hz0N)
      · exact hw0r hwr0
    · have hz0Pin : IsDoublePin a b c z0 :=
        ahtDoublePinReplacement.adj_old_new_iff.mp hzw
      have hz0Mem : z0 ∈ ({p, q, r} : Finset V) := by
        rw [hpins]
        simpa only [Finset.mem_insert, Finset.mem_singleton] using hz0Pin
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz0Mem
      rcases hz0Mem with rfl | rfl | rfl
      · exact hpF hz0F
      · exact hqF hz0F
      · exact hrF hz0F
  have hXcard := card_eq_one_of_threeConnected_of_twoVertexGate
    X hthree hxX hrX hpX hpr' hgate
  simpa [X, e] using hXcard

/-! ## Specialization to the source-exact three-fragment construction -/

namespace AHTThreeFragment

variable (F : Erdos916.AHTThreeFragment G)

/-- The original fragment, embedded as old base vertices of the double-pin
replacement. -/
def fragmentEmbedding : {x : V // x ∈ F.verts} ↪
    (F.PreparedVertex ⊕ Fin 2) where
  toFun x := .inl (.inl ⟨x.1, Finset.mem_union_left _ x.2⟩)
  inj' x y h := by
    have h₁ := Sum.inl.inj h
    have h₂ := Sum.inl.inj h₁
    exact Subtype.ext (congrArg (fun q : F.BaseVertex => q.1) h₂)

/-- The finset image of the original fragment in the replacement graph. -/
def replacementFragment : Finset (F.PreparedVertex ⊕ Fin 2) :=
  Finset.univ.map F.fragmentEmbedding

@[simp] theorem card_replacementFragment :
    F.replacementFragment.card = F.verts.card := by
  simp [replacementFragment, fragmentEmbedding, Fintype.card_coe]

@[simp] theorem mem_replacementFragment_iff
    {z : F.PreparedVertex ⊕ Fin 2} :
    z ∈ F.replacementFragment ↔
      ∃ x : V, ∃ hx : x ∈ F.verts,
        z = (.inl (.inl
          ⟨x, Finset.mem_union_left _ hx⟩) : F.PreparedVertex ⊕ Fin 2) := by
  constructor
  · intro hz
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.mp hz
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact Finset.mem_map.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩

/-- The retained old base vertex corresponding to a displayed boundary
vertex. -/
def boundaryBase (i : Fin 3) : F.BaseVertex :=
  ⟨F.boundaryVertex i, F.boundary_mem_base i⟩

/-- Every old prepared vertex which is not one of the three distinguished
pins is a base vertex rather than a fresh vertex. -/
theorem exists_base_of_not_doublePin
    {p : F.PreparedVertex}
    (hp : ¬IsDoublePin (F.pin 0) (F.pin 1) (F.pin 2) p) :
    ∃ q : F.BaseVertex, p = .inl q := by
  rcases p with q | l
  · exact ⟨q, rfl⟩
  · exfalso
    apply hp
    rcases l with ⟨l, hl⟩
    have hpPin :
        (Sum.inr ⟨l, hl⟩ : F.PreparedVertex) = F.pin l := by
      simp [AHTThreeFragment.pin, hl]
    fin_cases l
    · exact Or.inl hpPin
    · exact Or.inr (Or.inl hpPin)
    · exact Or.inr (Or.inr hpPin)

/-- An interior base vertex has exactly the same degree in the ambient graph
and in the prepared graph.  The fragment boundary equation is used in the
forward direction to show that every ambient neighbour is retained. -/
theorem degree_prepared_interior
    (p : F.BaseVertex) (hpF : p.1 ∈ F.verts) :
    G.degree p.1 = F.preparedGraph.degree (.inl p) := by
  have neighbor_mem_base {z : V} (hpz : G.Adj p.1 z) :
      z ∈ F.verts ∪ ({F.a, F.b, F.c} : Finset V) := by
    by_cases hzF : z ∈ F.verts
    · exact Finset.mem_union_left _ hzF
    · apply Finset.mem_union_right
      simpa using (F.boundary_exact z hzF).1 ⟨p.1, hpF, hpz.symm⟩
  rw [← G.card_neighborFinset_eq_degree,
    ← F.preparedGraph.card_neighborFinset_eq_degree]
  apply Finset.card_bij
    (fun z hz ↦
      (.inl ⟨z, neighbor_mem_base (by
        simpa [SimpleGraph.mem_neighborFinset] using hz)⟩ :
        F.PreparedVertex))
  · intro z hz
    rw [SimpleGraph.mem_neighborFinset]
    have hpz : G.Adj p.1 z := by
      simpa [SimpleGraph.mem_neighborFinset] using hz
    exact ⟨hpz, fun hbad ↦
      Finset.disjoint_left.mp F.boundary_disjoint hpF hbad.1⟩
  · intro z₁ hz₁ z₂ hz₂ heq
    have heq' := Sum.inl.inj heq
    exact congrArg Subtype.val heq'
  · intro z hz
    rw [SimpleGraph.mem_neighborFinset] at hz
    rcases z with q | l
    · refine ⟨q.1, ?_, ?_⟩
      · simpa [SimpleGraph.mem_neighborFinset] using hz.1
      · exact congrArg Sum.inl (Subtype.ext rfl)
    · have hpboundary : p.1 = F.boundaryVertex l.1 := by
        simpa using hz
      exact (F.boundary_not_mem l.1 (hpboundary ▸ hpF)).elim

/-- In a false-twin pair of non-pin old prepared vertices, both vertices lie
in the original fragment.  A boundary base vertex either is its distinguished
pin or is adjacent to its own fresh pin, and the latter adjacency distinguishes
it from every other vertex. -/
theorem base_mem_verts_of_nonpin_falseTwins
    {p q : F.BaseVertex}
    (hp : ¬IsDoublePin (F.pin 0) (F.pin 1) (F.pin 2)
      (.inl p : F.PreparedVertex))
    (hq : ¬IsDoublePin (F.pin 0) (F.pin 1) (F.pin 2)
      (.inl q : F.PreparedVertex))
    (hpq : AreFalseTwins F.preparedGraph
      (.inl p : F.PreparedVertex) (.inl q : F.PreparedVertex)) :
    p.1 ∈ F.verts ∧ q.1 ∈ F.verts := by
  have left_mem {p q : F.BaseVertex}
      (hp : ¬IsDoublePin (F.pin 0) (F.pin 1) (F.pin 2)
        (.inl p : F.PreparedVertex))
      (hpq : AreFalseTwins F.preparedGraph
        (.inl p : F.PreparedVertex) (.inl q : F.PreparedVertex)) :
      p.1 ∈ F.verts := by
    rcases Finset.mem_union.mp p.2 with hpF | hpBoundary
    · exact hpF
    · exfalso
      have not_boundary (l : Fin 3) : p.1 ≠ F.boundaryVertex l := by
        intro hpl
        have hpBase : p = F.boundaryBase l := Subtype.ext hpl
        by_cases hl : F.NeedsFreshPin l
        · let fl : F.FreshPin := ⟨l, hl⟩
          have hpAdj : F.preparedGraph.Adj
              (.inl p : F.PreparedVertex) (.inr fl) := by
            simp [hpBase, boundaryBase, fl]
          have hqAdj : F.preparedGraph.Adj
              (.inl q : F.PreparedVertex) (.inr fl) :=
            (hpq.adj_iff (.inr fl)).mp hpAdj
          have hql : q.1 = F.boundaryVertex l := by
            simpa [fl] using hqAdj
          apply hpq.1
          apply congrArg Sum.inl
          exact Subtype.ext (hpl.trans hql.symm)
        · apply hp
          have hpPin :
              (.inl p : F.PreparedVertex) = F.pin l := by
            rw [hpBase]
            simp [AHTThreeFragment.pin, hl, boundaryBase]
          fin_cases l
          · exact Or.inl hpPin
          · exact Or.inr (Or.inl hpPin)
          · exact Or.inr (Or.inr hpPin)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hpBoundary
      rcases hpBoundary with ha | hb | hc
      · exact not_boundary 0 ha
      · exact not_boundary 1 hb
      · exact not_boundary 2 hc
  exact ⟨left_mem hp hpq, left_mem hq hpq.symm⟩

/-- The non-pin branch extracted from the double-pin replacement is already
an ambient twin pair contained in the original fragment. -/
theorem exists_ambient_twinPair_of_replacement_old_nonpin
    {p q : F.PreparedVertex}
    (hpq : AHTTwinPair F.replacementGraph (.inl p) (.inl q))
    (hp : ¬IsDoublePin (F.pin 0) (F.pin 1) (F.pin 2) p)
    (hq : ¬IsDoublePin (F.pin 0) (F.pin 1) (F.pin 2) q) :
    ∃ x ∈ F.verts, ∃ y ∈ F.verts, AHTTwinPair G x y := by
  obtain ⟨p0, rfl⟩ := F.exists_base_of_not_doublePin hp
  obtain ⟨q0, rfl⟩ := F.exists_base_of_not_doublePin hq
  have hpqPrepared : AHTTwinPair F.preparedGraph (.inl p0) (.inl q0) := by
    rcases ahtDoublePinReplacement_old_twinPair_classification hpq with
      hnonpin | hpin
    · exact hnonpin.2.2
    · exact (hp hpin.1).elim
  obtain ⟨hp0F, hq0F⟩ :=
    F.base_mem_verts_of_nonpin_falseTwins hp hq hpqPrepared.falseTwins
  have hpqAmbient : AreFalseTwins G p0.1 q0.1 := by
    refine ⟨fun heq ↦ hpqPrepared.falseTwins.1 (congrArg Sum.inl
      (Subtype.ext heq)), ?_⟩
    ext z
    change G.Adj p0.1 z ↔ G.Adj q0.1 z
    constructor
    · intro hpz
      have hzBase : z ∈ F.verts ∪ ({F.a, F.b, F.c} : Finset V) := by
        by_cases hzF : z ∈ F.verts
        · exact Finset.mem_union_left _ hzF
        · apply Finset.mem_union_right
          simpa using (F.boundary_exact z hzF).1 ⟨p0.1, hp0F, hpz.symm⟩
      let qz : F.BaseVertex := ⟨z, hzBase⟩
      have hpzPrepared : F.preparedGraph.Adj (.inl p0) (.inl qz) :=
        ⟨hpz, fun hbad ↦
          Finset.disjoint_left.mp F.boundary_disjoint hp0F hbad.1⟩
      exact ((hpqPrepared.falseTwins.adj_iff (.inl qz)).mp hpzPrepared).1
    · intro hqz
      have hzBase : z ∈ F.verts ∪ ({F.a, F.b, F.c} : Finset V) := by
        by_cases hzF : z ∈ F.verts
        · exact Finset.mem_union_left _ hzF
        · apply Finset.mem_union_right
          simpa using (F.boundary_exact z hzF).1 ⟨q0.1, hq0F, hqz.symm⟩
      let qz : F.BaseVertex := ⟨z, hzBase⟩
      have hqzPrepared : F.preparedGraph.Adj (.inl q0) (.inl qz) :=
        ⟨hqz, fun hbad ↦
          Finset.disjoint_left.mp F.boundary_disjoint hq0F hbad.1⟩
      exact ((hpqPrepared.falseTwins.adj_iff (.inl qz)).mpr hqzPrepared).1
  have hp0Degree : G.degree p0.1 = 3 := by
    rw [F.degree_prepared_interior p0 hp0F]
    exact hpqPrepared.degree_left
  exact ⟨p0.1, hp0F, q0.1, hq0F, hpqAmbient, hp0Degree⟩

/-- The elementary size comparison in AHT Theorem 6.6, claim (1).  The
prepared replacement retains `F`, the three boundary vertices, at most
three fresh pins, and the two double-pin vertices.  Hence an opposite side
of cardinality at least six makes the replacement strictly smaller. -/
theorem replacement_card_lt_of_six_le_outside
    (hout : 6 ≤
      (Finset.univ \ (F.verts ∪ ({F.a, F.b, F.c} : Finset V))).card) :
    Fintype.card (F.PreparedVertex ⊕ Fin 2) < Fintype.card V := by
  let B : Finset V := F.verts ∪ ({F.a, F.b, F.c} : Finset V)
  have hboundary : ({F.a, F.b, F.c} : Finset V).card = 3 := by
    simp [F.ab, F.ac, F.bc]
  have hbase : Fintype.card F.BaseVertex = F.verts.card + 3 := by
    rw [Fintype.card_coe, Finset.card_union_of_disjoint F.boundary_disjoint,
      hboundary]
  have hfresh : Fintype.card F.FreshPin ≤ 3 := by
    calc
      Fintype.card F.FreshPin ≤ Fintype.card (Fin 3) :=
        Fintype.card_subtype_le _
      _ = 3 := by simp
  have hsplit :
      (Finset.univ \ B).card + B.card = Fintype.card V := by
    simpa [Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ B)
  have hBcard : B.card = F.verts.card + 3 := by
    simpa [B, Fintype.card_coe] using hbase
  simp only [Fintype.card_sum, Fintype.card_fin]
  rw [hbase]
  rw [hBcard] at hsplit
  change 6 ≤ (Finset.univ \ B).card at hout
  omega

/-- Two distinct distinguished pins that are false twins in the prepared
graph cannot involve a fresh pin.  Thus both are the original boundary
vertices.  This is the small point needed before the source's two-cut is
formed with the *original* third boundary vertex rather than, in general,
the third distinguished pin. -/
theorem not_needsFreshPin_of_pin_falseTwins
    {i j : Fin 3} (hij : i ≠ j)
    (hijTwin : AreFalseTwins F.preparedGraph (F.pin i) (F.pin j)) :
    ¬F.NeedsFreshPin i := by
  intro hi
  let qi : F.BaseVertex :=
    ⟨F.boundaryVertex i, F.boundary_mem_base i⟩
  have hiAdj : F.preparedGraph.Adj (F.pin i) (.inl qi) := by
    simp [AHTThreeFragment.pin, hi, qi]
  have hjAdj : F.preparedGraph.Adj (F.pin j) (.inl qi) :=
    (hijTwin.adj_iff (.inl qi)).mp hiAdj
  by_cases hj : F.NeedsFreshPin j
  · have hboundary : F.boundaryVertex i = F.boundaryVertex j := by
      simpa [AHTThreeFragment.pin, hj, qi] using hjAdj
    exact hij (F.boundaryVertex_injective hboundary)
  · rw [show F.pin j = (.inl (F.boundaryBase j) : F.PreparedVertex) by
      simp [AHTThreeFragment.pin, hj, boundaryBase]] at hjAdj
    exact hjAdj.2 ⟨by
      fin_cases j <;> simp [boundaryBase], by
      fin_cases i <;> simp [qi]⟩

/-- Symmetric form of `not_needsFreshPin_of_pin_falseTwins`. -/
theorem not_needsFreshPin_right_of_pin_falseTwins
    {i j : Fin 3} (hij : i ≠ j)
    (hijTwin : AreFalseTwins F.preparedGraph (F.pin i) (F.pin j)) :
    ¬F.NeedsFreshPin j := by
  exact F.not_needsFreshPin_of_pin_falseTwins hij.symm hijTwin.symm

/-- A false-twin pair of distinct distinguished pins has a common neighbour
in the retained fragment.  Both pins have already been shown to be
identified boundary vertices, so the displayed ambient adjacencies are the
literal two edges used in AHT claim (1). -/
theorem exists_common_insideNeighbor_of_pin_falseTwins
    {i j : Fin 3} (hij : i ≠ j)
    (hijTwin : AreFalseTwins F.preparedGraph (F.pin i) (F.pin j)) :
    ∃ x ∈ F.verts,
      G.Adj (F.boundaryVertex i) x ∧
      G.Adj (F.boundaryVertex j) x := by
  have hi : ¬F.NeedsFreshPin i :=
    F.not_needsFreshPin_of_pin_falseTwins hij hijTwin
  have hj : ¬F.NeedsFreshPin j :=
    F.not_needsFreshPin_right_of_pin_falseTwins hij hijTwin
  obtain ⟨x, hx⟩ := F.insideNeighborFinset_nonempty i
  have hxAdj : G.Adj (F.boundaryVertex i) x := by
    simpa [AHTThreeFragment.insideNeighborFinset,
      SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hx).1
  have hxF : x ∈ F.verts := (Finset.mem_inter.mp hx).2
  let qx : F.BaseVertex :=
    ⟨x, Finset.mem_union_left _ hxF⟩
  have hiPrepared : F.preparedGraph.Adj (F.pin i) (.inl qx) := by
    rw [show F.pin i =
      (.inl ⟨F.boundaryVertex i, F.boundary_mem_base i⟩ :
        F.PreparedVertex) by
      simp [AHTThreeFragment.pin, hi]]
    exact ⟨hxAdj, fun hbad ↦
      Finset.disjoint_left.mp F.boundary_disjoint hxF hbad.2⟩
  have hjPrepared : F.preparedGraph.Adj (F.pin j) (.inl qx) :=
    (hijTwin.adj_iff (.inl qx)).mp hiPrepared
  have hjAdj : G.Adj (F.boundaryVertex j) x := by
    rw [show F.pin j =
      (.inl ⟨F.boundaryVertex j, F.boundary_mem_base j⟩ :
        F.PreparedVertex) by
      simp [AHTThreeFragment.pin, hj]] at hjPrepared
    exact hjPrepared.1
  exact ⟨x, hxF, hxAdj, hjAdj⟩

/-- The source-exact exceptional branch of claim (1).  If two of the three
distinguished pins form a twin pair in the double-pin replacement, then the
fragment has one vertex.  Notice that the second gate vertex below is the
original boundary vertex indexed by `k`; this remains correct when the third
distinguished pin itself is fresh. -/
theorem verts_card_eq_one_of_pin_twinPair
    {i j k : Fin 3} (hij : i ≠ j)
    (hindices : ({i, j, k} : Finset (Fin 3)) = Finset.univ)
    (hijTwin : AHTTwinPair F.replacementGraph
      (.inl (F.pin i)) (.inl (F.pin j)))
    (hthree : IsThreeConnected F.replacementGraph) :
    F.verts.card = 1 := by
  have hijPrepared :
      AreFalseTwins F.preparedGraph (F.pin i) (F.pin j) :=
    ahtDoublePinReplacement_old_falseTwins hijTwin.falseTwins
  have hi : ¬F.NeedsFreshPin i :=
    F.not_needsFreshPin_of_pin_falseTwins hij hijPrepared
  have hj : ¬F.NeedsFreshPin j :=
    F.not_needsFreshPin_right_of_pin_falseTwins hij hijPrepared
  obtain ⟨x, hxF, hixG, hjxG⟩ :=
    F.exists_common_insideNeighbor_of_pin_falseTwins hij hijPrepared
  let qx : F.BaseVertex :=
    ⟨x, Finset.mem_union_left _ hxF⟩
  let xP : F.PreparedVertex := .inl qx
  let xR : F.PreparedVertex ⊕ Fin 2 := .inl xP
  let vR : F.PreparedVertex ⊕ Fin 2 := .inl (.inl (F.boundaryBase k))
  let yR : F.PreparedVertex ⊕ Fin 2 := .inr 0
  let X := F.replacementFragment
  have hpinI : F.pin i = .inl (F.boundaryBase i) := by
    simp [AHTThreeFragment.pin, hi, boundaryBase]
  have hpinJ : F.pin j = .inl (F.boundaryBase j) := by
    simp [AHTThreeFragment.pin, hj, boundaryBase]
  have hixPrepared : F.preparedGraph.Adj (F.pin i) xP := by
    rw [hpinI]
    exact ⟨hixG, fun hbad ↦
      Finset.disjoint_left.mp F.boundary_disjoint hxF hbad.2⟩
  have hjxPrepared : F.preparedGraph.Adj (F.pin j) xP := by
    rw [hpinJ]
    exact ⟨hjxG, fun hbad ↦
      Finset.disjoint_left.mp F.boundary_disjoint hxF hbad.2⟩
  have hNi : F.preparedGraph.neighborFinset (F.pin i) = {xP} :=
    neighborFinset_eq_singleton_of_degree_eq_one_of_adj
      (F.degree_pin i) hixPrepared
  have hNj : F.preparedGraph.neighborFinset (F.pin j) = {xP} :=
    neighborFinset_eq_singleton_of_degree_eq_one_of_adj
      (F.degree_pin j) hjxPrepared
  have hxX : xR ∈ X := by
    rw [AHTThreeFragment.mem_replacementFragment_iff]
    exact ⟨x, hxF, rfl⟩
  have hvX : vR ∉ X := by
    intro hv
    rw [AHTThreeFragment.mem_replacementFragment_iff] at hv
    obtain ⟨z, hzF, hz⟩ := hv
    have hz₁ := Sum.inl.inj hz.symm
    have hz₂ := Sum.inl.inj hz₁
    have hzval : z = F.boundaryVertex k :=
      congrArg Subtype.val hz₂
    exact F.boundary_not_mem k (hzval ▸ hzF)
  have hyX : yR ∉ X := by
    intro hy
    rw [AHTThreeFragment.mem_replacementFragment_iff] at hy
    obtain ⟨z, hzF, hz⟩ := hy
    exact Sum.inr_ne_inl hz
  have hyv : yR ≠ vR := Sum.inr_ne_inl
  have hgate : ∀ ⦃z w : F.PreparedVertex ⊕ Fin 2⦄,
      z ∈ X → z ≠ xR → w ∉ X → w ≠ vR →
        ¬F.replacementGraph.Adj z w := by
    intro z w hzX hzx hwX hwv hzw
    rw [AHTThreeFragment.mem_replacementFragment_iff] at hzX
    obtain ⟨z0, hz0F, rfl⟩ := hzX
    let qz : F.BaseVertex :=
      ⟨z0, Finset.mem_union_left _ hz0F⟩
    have hzNotPin (l : Fin 3) :
        (Sum.inl qz : F.PreparedVertex) ≠ F.pin l := by
      by_cases hl : F.NeedsFreshPin l
      · simp [AHTThreeFragment.pin, hl]
      · intro heq
        have heq0 : (Sum.inl qz : F.PreparedVertex) =
            .inl (F.boundaryBase l) := by
          simpa [AHTThreeFragment.pin, hl, boundaryBase] using heq
        have heq' : qz = F.boundaryBase l := by
          exact Sum.inl.inj heq0
        have hzboundary : z0 = F.boundaryVertex l :=
          congrArg Subtype.val heq'
        exact F.boundary_not_mem l (hzboundary ▸ hz0F)
    rcases w with w | t
    · have hzwPrepared :
          F.preparedGraph.Adj (.inl qz) w := hzw
      rcases w with qw | l
      · by_cases hqwF : qw.1 ∈ F.verts
        · apply hwX
          rw [AHTThreeFragment.mem_replacementFragment_iff]
          exact ⟨qw.1, hqwF, by
            apply congrArg Sum.inl
            apply congrArg Sum.inl
            exact Subtype.ext rfl⟩
        · have hqwBoundary :
              qw.1 = F.a ∨ qw.1 = F.b ∨ qw.1 = F.c :=
            (F.boundary_exact qw.1 hqwF).1
              ⟨z0, hz0F, hzwPrepared.1.symm⟩
          obtain ⟨l, hqwl⟩ :
              ∃ l : Fin 3, qw.1 = F.boundaryVertex l := by
            rcases hqwBoundary with ha | hb | hc
            · exact ⟨0, ha⟩
            · exact ⟨1, hb⟩
            · exact ⟨2, hc⟩
          have hl : l ∈ ({i, j, k} : Finset (Fin 3)) := by
            rw [hindices]
            simp
          simp only [Finset.mem_insert, Finset.mem_singleton] at hl
          have hqwBase : qw = F.boundaryBase l :=
            Subtype.ext hqwl
          rcases hl with rfl | rfl | rfl
          · have hzNi : (.inl qz : F.PreparedVertex) ∈
                F.preparedGraph.neighborFinset (F.pin l) := by
              rw [SimpleGraph.mem_neighborFinset, hpinI]
              simpa [hqwBase] using hzwPrepared.symm
            rw [hNi] at hzNi
            have hzqx : (Sum.inl qz : F.PreparedVertex) = xP := by
              simpa using hzNi
            exact hzx (congrArg Sum.inl hzqx)
          · have hzNj : (.inl qz : F.PreparedVertex) ∈
                F.preparedGraph.neighborFinset (F.pin l) := by
              rw [SimpleGraph.mem_neighborFinset, hpinJ]
              simpa [hqwBase] using hzwPrepared.symm
            rw [hNj] at hzNj
            have hzqx : (Sum.inl qz : F.PreparedVertex) = xP := by
              simpa using hzNj
            exact hzx (congrArg Sum.inl hzqx)
          · apply hwv
            apply congrArg Sum.inl
            apply congrArg Sum.inl
            exact hqwBase
      · have hzboundary : z0 = F.boundaryVertex l.1 := by
          simpa [qz] using hzwPrepared
        exact F.boundary_not_mem l.1 (hzboundary ▸ hz0F)
    · have hzPin :
          (Sum.inl qz : F.PreparedVertex) = F.pin 0 ∨
          (Sum.inl qz : F.PreparedVertex) = F.pin 1 ∨
          (Sum.inl qz : F.PreparedVertex) = F.pin 2 :=
        ahtDoublePinReplacement.adj_old_new_iff.mp hzw
      rcases hzPin with hzPin | hzPin | hzPin
      · exact hzNotPin 0 hzPin
      · exact hzNotPin 1 hzPin
      · exact hzNotPin 2 hzPin
  have hcard := card_eq_one_of_threeConnected_of_twoVertexGate
    X hthree hxX hvX hyX hyv hgate
  simpa [X] using hcard

/-- The complete unconditional replacement endgame of AHT Theorem 6.6,
claim (1).  A complementary ambient twin pair rules out the non-pin branch;
the remaining pin branch forces the retained fragment to be a singleton. -/
theorem verts_card_eq_one_of_replacement_twoPairs
    (T : TwoDisjointDegreeThreeFalseTwinPairs F.replacementGraph)
    (hthree : IsThreeConnected F.replacementGraph)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    {r s : V} (hrs : AHTTwinPair G r s)
    (hr : r ∉ F.verts) (hs : s ∉ F.verts) :
    F.verts.card = 1 := by
  obtain ⟨p, q, hpq, hclass⟩ :=
    ahtDoublePinReplacement_twoPairs_classification (T := T)
  rcases hclass with hnonpin | hpin
  · obtain ⟨x, hxF, y, hyF, hxy⟩ :=
      F.exists_ambient_twinPair_of_replacement_old_nonpin
        hpq hnonpin.1 hnonpin.2.1
    exact (hno (twoDisjointPairs_of_mem_and_not_mem
      F.verts hxy hxF hyF hrs hr hs)).elim
  · have hpqNe : p ≠ q := fun heq ↦ hpq.falseTwins.1
      (congrArg Sum.inl heq)
    rcases hpin.1 with rfl | rfl | rfl <;>
      rcases hpin.2.1 with rfl | rfl | rfl
    · exact (hpqNe rfl).elim
    · exact F.verts_card_eq_one_of_pin_twinPair
        (k := (2 : Fin 3)) (by decide) (by decide) hpq hthree
    · exact F.verts_card_eq_one_of_pin_twinPair
        (k := (1 : Fin 3)) (by decide) (by decide) hpq hthree
    · exact F.verts_card_eq_one_of_pin_twinPair
        (k := (2 : Fin 3)) (by decide) (by decide) hpq hthree
    · exact (hpqNe rfl).elim
    · exact F.verts_card_eq_one_of_pin_twinPair
        (k := (0 : Fin 3)) (by decide) (by decide) hpq hthree
    · exact F.verts_card_eq_one_of_pin_twinPair
        (k := (1 : Fin 3)) (by decide) (by decide) hpq hthree
    · exact F.verts_card_eq_one_of_pin_twinPair
        (k := (0 : Fin 3)) (by decide) (by decide) hpq hthree
    · exact (hpqNe rfl).elim

/-- Contradiction form used verbatim in source claim (1): a fragment of at
least two vertices cannot coexist with the concrete replacement and
complementary-pair certificates. -/
theorem not_two_le_card_of_replacement_twoPairs
    (T : TwoDisjointDegreeThreeFalseTwinPairs F.replacementGraph)
    (hthree : IsThreeConnected F.replacementGraph)
    (hno : ¬Nonempty (TwoDisjointDegreeThreeFalseTwinPairs G))
    {r s : V} (hrs : AHTTwinPair G r s)
    (hr : r ∉ F.verts) (hs : s ∉ F.verts) :
    ¬2 ≤ F.verts.card := by
  intro htwo
  have hone := F.verts_card_eq_one_of_replacement_twoPairs
    T hthree hno hrs hr hs
  omega

end AHTThreeFragment

end Erdos916
