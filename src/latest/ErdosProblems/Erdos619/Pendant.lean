/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- No license was supplied with the original proof repository.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 619.
Informal proof: Claude Fable 5.
Formal proof: GPT-5.5 with Codex, following a formalization sketch and guidance
from Claude Fable 5. Human contributor and publisher: Nick (Nikolas) Kuhn.
Source: https://www.erdosproblems.com/619#post-6986
https://github.com/nick-kuhn/erdos-619/tree/7f65718b8c1019ecc24e6c9a6b04ec4c66a4e26f
Original Lean/Mathlib version: 4.28.0.
Original Mathlib revision: 8f9d9cff6bd728b17a24e163c9402775d9e6a365.
-/
import ErdosProblems.Erdos619.Host

open SimpleGraph
open scoped BigOperators

set_option linter.mathlibStandardSet false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Erdos619

/-- A feasible `h_r` supergraph for the challenge definition. -/
def FeasibleSupergraph {n : ℕ} (r : ℕ) (G H : SimpleGraph (Fin n)) : Prop :=
  G ≤ H ∧ H.CliqueFree 3 ∧ H.ediam ≤ (r : ℕ∞)

/-- On a finite vertex type, any nonempty feasible set has a least added-edge count, hence an
`IsHR` witness. -/
theorem exists_isHR_of_exists_feasible {n r : ℕ} {G : SimpleGraph (Fin n)}
    (hfeas : ∃ H : SimpleGraph (Fin n), FeasibleSupergraph r G H) :
    ∃ m : ℕ, IsHR r G m := by
  classical
  let P : ℕ → Prop := fun m =>
    ∃ H : SimpleGraph (Fin n),
      FeasibleSupergraph r G H ∧ addedEdgeCount G H = m
  have hP : ∃ m, P m := by
    rcases hfeas with ⟨H, hH⟩
    exact ⟨addedEdgeCount G H, H, hH, rfl⟩
  let m := Nat.find hP
  have hm : P m := Nat.find_spec hP
  rcases hm with ⟨H, hH, hcount⟩
  refine ⟨m, H, hH.1, hH.2.1, hH.2.2, hcount, ?_⟩
  intro K hGK hKtf hKdiam
  exact Nat.find_min' hP ⟨K, ⟨hGK, hKtf, hKdiam⟩, rfl⟩

/-- If every feasible supergraph has at least `L` new edges, then the `h_r` value has at least
`L` new edges. -/
theorem exists_isHR_with_real_lower_bound {n r : ℕ} {G : SimpleGraph (Fin n)} {L : ℝ}
    (hfeas : ∃ H : SimpleGraph (Fin n), FeasibleSupergraph r G H)
    (hlower : ∀ H : SimpleGraph (Fin n), FeasibleSupergraph r G H →
      L ≤ (addedEdgeCount G H : ℝ)) :
    ∃ m : ℕ, IsHR r G m ∧ L ≤ (m : ℝ) := by
  rcases exists_isHR_of_exists_feasible (r := r) (G := G) hfeas with ⟨m, hm⟩
  rcases hm with ⟨H, hGH, hHtf, hHdiam, hcount, hmin⟩
  refine ⟨m, ⟨H, hGH, hHtf, hHdiam, hcount, hmin⟩, ?_⟩
  simpa [hcount] using hlower H ⟨hGH, hHtf, hHdiam⟩

/-- It is enough to bound explicit walks between all ordered pairs to bound extended diameter. -/
lemma ediam_le_of_forall_exists_walk_le {V : Type} (G : SimpleGraph V) {r : ℕ}
    (h : ∀ u v : V, ∃ p : G.Walk u v, p.length ≤ r) : G.ediam ≤ (r : ℕ∞) := by
  rw [SimpleGraph.ediam_le_iff]
  intro u v
  rcases h u v with ⟨p, hp⟩
  exact (SimpleGraph.edist_le p).trans (by exact_mod_cast hp)

/-- Extract a concrete bounded walk from a finite extended-distance bound. -/
lemma exists_walk_length_le_of_edist_le {V : Type} {G : SimpleGraph V} {u v : V} {r : ℕ}
    (h : G.edist u v ≤ (r : ℕ∞)) :
    ∃ p : G.Walk u v, p.length ≤ r := by
  have hne : G.edist u v ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top r) h
  rcases SimpleGraph.exists_walk_of_edist_ne_top hne with ⟨p, hp⟩
  refine ⟨p, ?_⟩
  have hp_le : (p.length : ℕ∞) ≤ (r : ℕ∞) := by
    rw [hp]
    exact h
  exact ENat.natCast_le_natCast.mp hp_le

/-- Transporting a supergraph relation across the canonical `Fin` copy preserves inclusion. -/
lemma overFin_mono {V : Type} [Fintype V] {n : ℕ} {G K : SimpleGraph V}
    (hc : Fintype.card V = n) (hGK : G ≤ K) :
    G.overFin hc ≤ K.overFin hc := by
  intro x y hxy
  exact hGK hxy

/-- A walk-by-walk diameter bound survives transport to the canonical `Fin` copy. -/
lemma overFin_ediam_le_of_forall_exists_walk_le {V : Type} [Fintype V] {n r : ℕ}
    (G : SimpleGraph V) (hc : Fintype.card V = n)
    (h : ∀ u v : V, ∃ p : G.Walk u v, p.length ≤ r) :
    (G.overFin hc).ediam ≤ (r : ℕ∞) := by
  apply ediam_le_of_forall_exists_walk_le
  intro x y
  let e := SimpleGraph.overFinIso (G := G) hc
  rcases h (e.symm x) (e.symm y) with ⟨p, hp⟩
  have hx : e (e.symm x) = x := by simp
  have hy : e (e.symm y) = y := by simp
  rw [← hx, ← hy]
  exact ⟨p.map e.toHom, by simpa [Walk.length_map] using hp⟩

/-- Distinct connected components have disjoint supports, in pointwise form. -/
lemma connectedComponent_not_mem_supp_of_ne {V : Type} {G : SimpleGraph V}
    {X Y : G.ConnectedComponent} (hXY : X ≠ Y) {v : V} (hv : v ∈ X.supp) :
    v ∉ Y.supp := by
  intro hvY
  exact hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hv hvY)

/-- Component-local form of the standard connected graph edge lower bound. -/
lemma connectedComponent_supp_ncard_le_edgeSet_add_one {V : Type} (G : SimpleGraph V)
    (C : G.ConnectedComponent) :
    C.supp.ncard ≤ Nat.card C.toSimpleGraph.edgeSet + 1 := by
  have h := C.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  exact h

lemma connectedComponent_edgeSigma_card_le_edgeSet {V : Type} [Fintype V]
    (G : SimpleGraph V) :
    Nat.card (Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) ≤ Nat.card G.edgeSet := by
  classical
  let edgeMap : (Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) → G.edgeSet := fun z =>
    match z with
    | ⟨C, e⟩ =>
        ⟨Sym2.map Subtype.val e.1, by
          refine Sym2.ind ?_ e.1 e.2
          intro u v huv
          have hG : G.Adj u.1 v.1 := by
            simpa [SimpleGraph.mem_edgeSet, SimpleGraph.ConnectedComponent.toSimpleGraph] using huv
          simpa [SimpleGraph.mem_edgeSet, Sym2.map_mk] using hG⟩
  have hinj : Function.Injective edgeMap := by
    rintro ⟨X, e⟩ ⟨Y, f⟩ h
    have hval : Sym2.map Subtype.val e.1 = Sym2.map Subtype.val f.1 := by
      simpa [edgeMap] using congrArg Subtype.val h
    refine Sym2.ind ?_ e.1 e.2 f.2 hval
    intro u v huv hf hmap
    refine Sym2.ind ?_ f.1 hf hmap
    intro u' v' huv' hmap'
    have hpair : s((u : V), (v : V)) = s((u' : V), (v' : V)) := by
      simpa [Sym2.map_mk] using hmap'
    have hXY : X = Y := by
      rw [Sym2.eq_iff] at hpair
      rcases hpair with ⟨huu, _⟩ | ⟨huv', _⟩
      · have huY : (u : V) ∈ Y := by
          rw [huu]
          exact u'.2
        exact SimpleGraph.ConnectedComponent.eq_of_common_vertex u.2 huY
      · have huY : (u : V) ∈ Y := by
          rw [huv']
          exact v'.2
        exact SimpleGraph.ConnectedComponent.eq_of_common_vertex u.2 huY
    subst Y
    have hef : e = f := by
      apply Subtype.ext
      exact Sym2.map.injective Subtype.val_injective hval
    cases hef
    rfl
  exact Nat.card_le_card_of_injective edgeMap hinj

lemma card_vertex_le_edgeSet_add_connectedComponents {V : Type} [Fintype V]
    (G : SimpleGraph V) :
    Nat.card V ≤ Nat.card G.edgeSet + Nat.card G.ConnectedComponent := by
  classical
  have hverts : Nat.card V = ∑ C : G.ConnectedComponent, C.supp.ncard := by
    rw [Nat.card_eq_fintype_card]
    simp only [← (set_fintype_card_eq_univ_iff _).mpr G.iUnion_connectedComponentSupp,
      ← Set.toFinset_card, Set.toFinset_iUnion SimpleGraph.ConnectedComponent.supp]
    rw [Finset.card_biUnion
      (fun x _ y _ hxy => Set.disjoint_toFinset.mpr
        (SimpleGraph.pairwise_disjoint_supp_connectedComponent _ hxy))]
    simp [Set.ncard_eq_toFinset_card']
  rw [hverts]
  calc
    (∑ C : G.ConnectedComponent, C.supp.ncard) ≤
        ∑ C : G.ConnectedComponent, (Nat.card C.toSimpleGraph.edgeSet + 1) := by
      exact Finset.sum_le_sum fun C _ => connectedComponent_supp_ncard_le_edgeSet_add_one G C
    _ = (∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) +
        Nat.card G.ConnectedComponent := by
      simp [Finset.sum_add_distrib, Nat.card_eq_fintype_card]
    _ ≤ Nat.card G.edgeSet + Nat.card G.ConnectedComponent := by
      have hEdgeSum : (∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet) ≤
          Nat.card G.edgeSet := by
        have h := connectedComponent_edgeSigma_card_le_edgeSet G
        have hsigma : Nat.card (Σ C : G.ConnectedComponent, C.toSimpleGraph.edgeSet) =
            ∑ C : G.ConnectedComponent, Nat.card C.toSimpleGraph.edgeSet := by
          rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
          simp [Nat.card_eq_fintype_card]
        exact le_of_eq_of_le hsigma.symm h
      exact Nat.add_le_add_right hEdgeSum _

/-- A core graph with a family of pendant vertices attached by `root`.  This sum-type version keeps
all graph-theoretic arguments independent of the later `Fin n` encoding arithmetic. -/
def PendantCoreGraphSum {C P : Type} (H : SimpleGraph C) (root : P → C) :
    SimpleGraph (C ⊕ P) where
  Adj x y :=
    match x, y with
    | Sum.inl a, Sum.inl b => H.Adj a b
    | Sum.inl a, Sum.inr p => root p = a
    | Sum.inr p, Sum.inl a => root p = a
    | Sum.inr _, Sum.inr _ => False
  symm := by
    constructor
    rintro (a | p) (b | q) h
    · exact h.symm
    · simpa using h
    · simpa using h
    · exact False.elim h
  loopless := ⟨by
    intro x
    cases x with
    | inl a => exact H.irrefl
    | inr p => exact id⟩

@[simp] lemma pendantCoreGraphSum_adj_core_core {C P : Type} {H : SimpleGraph C} {root : P → C}
    {a b : C} :
    (PendantCoreGraphSum H root).Adj (Sum.inl a) (Sum.inl b) ↔ H.Adj a b := Iff.rfl

@[simp] lemma pendantCoreGraphSum_adj_core_pendant {C P : Type} {H : SimpleGraph C} {root : P → C}
    {a : C} {p : P} :
    (PendantCoreGraphSum H root).Adj (Sum.inl a) (Sum.inr p) ↔ root p = a := Iff.rfl

@[simp] lemma pendantCoreGraphSum_adj_pendant_core {C P : Type} {H : SimpleGraph C} {root : P → C}
    {p : P} {a : C} :
    (PendantCoreGraphSum H root).Adj (Sum.inr p) (Sum.inl a) ↔ root p = a := Iff.rfl

@[simp] lemma pendantCoreGraphSum_not_adj_pendant_pendant {C P : Type} {H : SimpleGraph C}
    {root : P → C} {p q : P} :
    ¬ (PendantCoreGraphSum H root).Adj (Sum.inr p) (Sum.inr q) := by
  simp [PendantCoreGraphSum]

@[simp] lemma pendantCoreGraphSum_adj_pendant_iff {C P : Type} {H : SimpleGraph C} {root : P → C}
    {p : P} {x : C ⊕ P} :
    (PendantCoreGraphSum H root).Adj (Sum.inr p) x ↔ x = Sum.inl (root p) := by
  cases x with
  | inl a =>
      change root p = a ↔ Sum.inl a = Sum.inl (root p)
      simp [eq_comm]
  | inr q => simp

@[simp] lemma pendantCoreGraphSum_adj_iff_pendant {C P : Type} {H : SimpleGraph C} {root : P → C}
    {x : C ⊕ P} {p : P} :
    (PendantCoreGraphSum H root).Adj x (Sum.inr p) ↔ x = Sum.inl (root p) := by
  rw [adj_comm, pendantCoreGraphSum_adj_pendant_iff]

/-- The graph on pendants whose edges are the pendant-pendant edges of a supergraph.  Since the
base pendant-core graph has no pendant-pendant edges, these are exactly the new edges of this
type in any supergraph of the base graph. -/
def PendantPairGraph {C P : Type} (K : SimpleGraph (C ⊕ P)) : SimpleGraph P where
  Adj p q := K.Adj (Sum.inr p) (Sum.inr q)
  symm := by
    constructor
    intro p q h
    exact h.symm
  loopless := ⟨by
    intro p
    exact K.irrefl⟩

@[simp] lemma pendantPairGraph_adj {C P : Type} {K : SimpleGraph (C ⊕ P)} {p q : P} :
    (PendantPairGraph K).Adj p q ↔ K.Adj (Sum.inr p) (Sum.inr q) := Iff.rfl

/-- The core vertices adjacent to a given vertex in a graph on `C ⊕ P`. -/
noncomputable def CoreNeighborFinset {C P : Type} [Fintype C] (K : SimpleGraph (C ⊕ P))
    (w : C ⊕ P) : Finset C := by
  classical
  exact Finset.univ.filter fun c : C => K.Adj w (Sum.inl c)

@[simp] lemma mem_coreNeighborFinset {C P : Type} [Fintype C]
    {K : SimpleGraph (C ⊕ P)} {w : C ⊕ P} {c : C} :
    c ∈ CoreNeighborFinset K w ↔ K.Adj w (Sum.inl c) := by
  classical
  simp [CoreNeighborFinset]

lemma coreNeighborFinset_isIndepSet_of_triangleFree {C P : Type} [Fintype C]
    {H : SimpleGraph C} {K : SimpleGraph (C ⊕ P)}
    (hKtf : K.CliqueFree 3)
    (hcore : ∀ a b : C, H.Adj a b → K.Adj (Sum.inl a) (Sum.inl b))
    (w : C ⊕ P) : H.IsIndepSet (CoreNeighborFinset K w : Set C) := by
  rw [SimpleGraph.isIndepSet_iff]
  intro a ha b hb hab_ne hab
  have hKind := K.isIndepSet_neighborSet_of_triangleFree hKtf w
  have hwa : Sum.inl a ∈ K.neighborSet w := by simpa using ha
  have hwb : Sum.inl b ∈ K.neighborSet w := by simpa using hb
  exact hKind hwa hwb (by simpa using hab_ne) (hcore a b hab)

lemma coreNeighborFinset_card_le_indepNum_of_triangleFree {C P : Type} [Fintype C]
    {H : SimpleGraph C} {K : SimpleGraph (C ⊕ P)}
    (hKtf : K.CliqueFree 3)
    (hcore : ∀ a b : C, H.Adj a b → K.Adj (Sum.inl a) (Sum.inl b))
    (w : C ⊕ P) :
    (CoreNeighborFinset K w).card ≤ H.indepNum := by
  exact SimpleGraph.IsIndepSet.card_le_indepNum
    (coreNeighborFinset_isIndepSet_of_triangleFree (H := H) hKtf hcore w)

lemma coreNeighborFinset_card_le_indepNum_of_pendantCore_le {C P : Type} [Fintype C]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)}
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) (w : C ⊕ P) :
    (CoreNeighborFinset K w).card ≤ H.indepNum := by
  apply coreNeighborFinset_card_le_indepNum_of_triangleFree (H := H) hKtf
  intro a b hab
  exact hGK (by simpa using hab)

/-- A component of the pendant-pair graph is core-free if its pendants have no new edge to the
core. Equivalently, every core neighbor in the supergraph is still the original root. -/
def PendantComponentCoreFree {C P : Type} (K : SimpleGraph (C ⊕ P)) (root : P → C)
    (X : (PendantPairGraph K).ConnectedComponent) : Prop :=
  ∀ p : P, p ∈ X.supp → ∀ c : C, K.Adj (Sum.inr p) (Sum.inl c) → c = root p

/-- A component is core-touching if it is not core-free. -/
def PendantComponentCoreTouching {C P : Type} (K : SimpleGraph (C ⊕ P)) (root : P → C)
    (X : (PendantPairGraph K).ConnectedComponent) : Prop :=
  ¬ PendantComponentCoreFree K root X

lemma not_coreFree_iff_exists_new_core_edge {C P : Type} {K : SimpleGraph (C ⊕ P)}
    {root : P → C} {X : (PendantPairGraph K).ConnectedComponent} :
    ¬ PendantComponentCoreFree K root X ↔
      ∃ p : P, p ∈ X.supp ∧ ∃ c : C, K.Adj (Sum.inr p) (Sum.inl c) ∧ c ≠ root p := by
  simp [PendantComponentCoreFree]

lemma coreFree_edge_from_pendant {C P : Type} {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent}
    (hfree : PendantComponentCoreFree K root X) {p : P} (hp : p ∈ X.supp)
    {x : C ⊕ P} (hpx : K.Adj (Sum.inr p) x) :
    x = Sum.inl (root p) ∨ ∃ q : P, q ∈ X.supp ∧ x = Sum.inr q := by
  cases x with
  | inl c =>
      left
      exact congrArg Sum.inl (hfree p hp c hpx)
  | inr q =>
      right
      refine ⟨q, ?_, rfl⟩
      exact X.mem_supp_of_adj_mem_supp hp hpx

lemma coreFree_edge_to_pendant {C P : Type} {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent}
    (hfree : PendantComponentCoreFree K root X) {p : P} (hp : p ∈ X.supp)
    {x : C ⊕ P} (hxp : K.Adj x (Sum.inr p)) :
    x = Sum.inl (root p) ∨ ∃ q : P, q ∈ X.supp ∧ x = Sum.inr q := by
  simpa [eq_comm] using coreFree_edge_from_pendant (K := K) (root := root) hfree hp hxp.symm

lemma coreFree_edge_from_pendant_eq_root_of_not_in_component {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent}
    (hfree : PendantComponentCoreFree K root X) {p : P} (hp : p ∈ X.supp)
    {x : C ⊕ P} (hpx : K.Adj (Sum.inr p) x)
    (hx : ¬ ∃ q : P, q ∈ X.supp ∧ x = Sum.inr q) :
    x = Sum.inl (root p) := by
  rcases coreFree_edge_from_pendant (K := K) (root := root) hfree hp hpx with hroot | hpend
  · exact hroot
  · exact False.elim (hx hpend)

lemma coreFree_edge_to_pendant_eq_root_of_not_in_component {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent}
    (hfree : PendantComponentCoreFree K root X) {p : P} (hp : p ∈ X.supp)
    {x : C ⊕ P} (hxp : K.Adj x (Sum.inr p))
    (hx : ¬ ∃ q : P, q ∈ X.supp ∧ x = Sum.inr q) :
    x = Sum.inl (root p) := by
  rcases coreFree_edge_to_pendant (K := K) (root := root) hfree hp hxp with hroot | hpend
  · exact hroot
  · exact False.elim (hx hpend)

lemma pendantPairGraph_not_adj_of_mem_distinct_components {C P : Type}
    {K : SimpleGraph (C ⊕ P)}
    {X Y : (PendantPairGraph K).ConnectedComponent} (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp) :
    ¬ K.Adj (Sum.inr p) (Sum.inr q) := by
  intro hpq
  have hqX : q ∈ X.supp := X.mem_supp_of_adj_mem_supp hp hpq
  exact hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hqX hq)

lemma pendantPairGraph_vertices_ne_of_mem_distinct_components {C P : Type}
    {K : SimpleGraph (C ⊕ P)}
    {X Y : (PendantPairGraph K).ConnectedComponent} (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp) :
    p ≠ q := by
  intro hpq
  subst q
  exact hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hp hq)

/-- Core vertices are close if there is a walk of length at most two between their core copies. -/
def CoreClose {C P : Type} (K : SimpleGraph (C ⊕ P)) (a b : C) : Prop :=
  ∃ p : K.Walk (Sum.inl a) (Sum.inl b), p.length ≤ 2

lemma CoreClose.refl {C P : Type} {K : SimpleGraph (C ⊕ P)} (a : C) :
    CoreClose K a a := by
  exact ⟨Walk.nil, by simp⟩

lemma CoreClose.symm {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    (h : CoreClose K a b) : CoreClose K b a := by
  rcases h with ⟨p, hp⟩
  exact ⟨p.reverse, by simpa [Walk.length_reverse] using hp⟩

lemma CoreClose.of_adj {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    (hab : K.Adj (Sum.inl a) (Sum.inl b)) : CoreClose K a b := by
  exact ⟨hab.toWalk, by simp⟩

lemma CoreClose.of_two_step {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    {z : C ⊕ P} (haz : K.Adj (Sum.inl a) z) (hzb : K.Adj z (Sum.inl b)) :
    CoreClose K a b := by
  exact ⟨Walk.cons haz hzb.toWalk, by simp⟩

lemma CoreClose.eq_or_adj_or_two_step {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    (h : CoreClose K a b) :
    a = b ∨ K.Adj (Sum.inl a) (Sum.inl b) ∨
      ∃ z : C ⊕ P, K.Adj (Sum.inl a) z ∧ K.Adj z (Sum.inl b) := by
  rcases h with ⟨w, hw⟩
  cases w with
  | nil => exact Or.inl rfl
  | cons h01 w₁ =>
      cases w₁ with
      | nil => exact Or.inr (Or.inl h01)
      | cons h12 w₂ =>
          cases w₂ with
          | nil => exact Or.inr (Or.inr ⟨_, h01, h12⟩)
          | cons h23 w₃ =>
              simp at hw

lemma CoreClose.adj_or_two_step_of_ne {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    (h : CoreClose K a b) (hab : a ≠ b) :
    K.Adj (Sum.inl a) (Sum.inl b) ∨
      ∃ z : C ⊕ P, K.Adj (Sum.inl a) z ∧ K.Adj z (Sum.inl b) := by
  rcases h.eq_or_adj_or_two_step with hEq | hAdj | hTwo
  · exact False.elim (hab hEq)
  · exact Or.inl hAdj
  · exact Or.inr hTwo

lemma CoreClose.two_step_of_ne_of_not_adj {C P : Type} {K : SimpleGraph (C ⊕ P)} {a b : C}
    (h : CoreClose K a b) (hab : a ≠ b) (hnadj : ¬ K.Adj (Sum.inl a) (Sum.inl b)) :
    ∃ z : C ⊕ P, K.Adj (Sum.inl a) z ∧ K.Adj z (Sum.inl b) := by
  rcases h.adj_or_two_step_of_ne hab with hAdj | hTwo
  · exact False.elim (hnadj hAdj)
  · exact hTwo

/-- The unordered distinct core pairs whose core copies are at graph distance at most two. -/
noncomputable def CoreClosePairFinset {C P : Type} [Fintype C] (K : SimpleGraph (C ⊕ P)) : Finset (Sym2 C) := by
  classical
  exact Finset.univ.filter fun e : Sym2 C => ¬ e.IsDiag ∧ ∃ a b : C, e = s(a, b) ∧ CoreClose K a b

lemma mem_coreClosePairFinset_mk {C P : Type} [Fintype C] {K : SimpleGraph (C ⊕ P)}
    {a b : C} :
    s(a, b) ∈ CoreClosePairFinset K ↔ a ≠ b ∧ CoreClose K a b := by
  classical
  constructor
  · intro h
    rcases (by simpa [CoreClosePairFinset] using h) with ⟨hdiag, c, d, hcd, hclose⟩
    have hab : a ≠ b := by
      intro h
      exact hdiag (by simpa [Sym2.mk_isDiag_iff] using h)
    rcases hcd with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hab, by simpa [hac, hbd] using hclose⟩
    · have hba : CoreClose K b a := by simpa [hbc, had] using hclose
      exact ⟨hab, hba.symm⟩
  · rintro ⟨hab, hclose⟩
    simp [CoreClosePairFinset, hab]
    exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, hclose⟩

/-- Core pairs with a common old core neighbor in the host graph. -/
noncomputable def CoreOldTwoStepPairFinset {C : Type} [Fintype C] (H : SimpleGraph C) : Finset (Sym2 C) := by
  classical
  exact Finset.univ.filter fun e : Sym2 C =>
    ¬ e.IsDiag ∧ ∃ a : C, ∃ b : C, ∃ w : C, e = s(a, b) ∧ H.Adj w a ∧ H.Adj w b

lemma mem_coreOldTwoStepPairFinset_mk {C : Type} [Fintype C] {H : SimpleGraph C}
    {a b : C} :
    s(a, b) ∈ CoreOldTwoStepPairFinset H ↔
      a ≠ b ∧ ∃ w : C, H.Adj w a ∧ H.Adj w b := by
  classical
  constructor
  · intro h
    rcases (by simpa [CoreOldTwoStepPairFinset] using h) with
      ⟨hdiag, c, d, hcd, w, hwc, hwd⟩
    have hab : a ≠ b := by
      intro h
      exact hdiag (by simpa [Sym2.mk_isDiag_iff] using h)
    rcases hcd with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hab, w, by simpa [hac] using hwc, by simpa [hbd] using hwd⟩
    · exact ⟨hab, w, by simpa [had] using hwd, by simpa [hbc] using hwc⟩
  · rintro ⟨hab, w, hwa, hwb⟩
    simp [CoreOldTwoStepPairFinset, hab]
    exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, w, hwa, hwb⟩

/-- The image of all ordered pairs of old neighbors of a common core vertex. -/
noncomputable def NeighborPairImageFinset {C : Type} [Fintype C] (H : SimpleGraph C) : Finset (Sym2 C) := by
  classical
  exact Finset.univ.biUnion fun w : C =>
    (((H.neighborSet w).toFinset.product (H.neighborSet w).toFinset).image fun p : C × C => s(p.1, p.2))

lemma coreOldTwoStepPair_subset_neighborPairImage {C : Type} [Fintype C] {H : SimpleGraph C} :
    CoreOldTwoStepPairFinset H ⊆ NeighborPairImageFinset H := by
  classical
  intro e he
  rcases (by simpa [CoreOldTwoStepPairFinset] using he) with
    ⟨_hdiag, a, b, hpair, w, hwa, hwb⟩
  rw [hpair]
  rw [NeighborPairImageFinset]
  apply Finset.mem_biUnion.mpr
  refine ⟨w, by simp, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨(a, b), ?_, rfl⟩
  simpa [SimpleGraph.mem_neighborSet] using ⟨hwa, hwb⟩

lemma neighborPairImage_card_le_sum_neighbor_ncard {C : Type} [Fintype C] (H : SimpleGraph C) :
    (NeighborPairImageFinset H).card ≤
      ∑ w : C, (H.neighborSet w).ncard * (H.neighborSet w).ncard := by
  classical
  let imageAt := fun w : C =>
    (((H.neighborSet w).toFinset.product (H.neighborSet w).toFinset).image fun p : C × C => s(p.1, p.2))
  have hcard : (NeighborPairImageFinset H).card ≤ ∑ w : C, (imageAt w).card := by
    simpa [NeighborPairImageFinset, imageAt] using
      (Finset.card_biUnion_le (s := (Finset.univ : Finset C)) (t := imageAt))
  have hsum : (∑ w : C, (imageAt w).card) ≤
      ∑ w : C, (H.neighborSet w).ncard * (H.neighborSet w).ncard := by
    refine Finset.sum_le_sum ?_
    intro w _
    have himage : (imageAt w).card ≤ ((H.neighborSet w).toFinset.product (H.neighborSet w).toFinset).card :=
      Finset.card_image_le
    have hprod : ((H.neighborSet w).toFinset.product (H.neighborSet w).toFinset).card =
        (H.neighborSet w).ncard * (H.neighborSet w).ncard := by
      simp [Finset.product_eq_sprod, Finset.card_product, Set.ncard_eq_toFinset_card']
    exact himage.trans_eq hprod
  exact hcard.trans hsum

lemma coreOldTwoStepPair_card_le_card_mul_sq {m d : ℕ} {H : SimpleGraph (Fin m)}
    (hdeg : MaxDegreeAtMost H d) :
    (CoreOldTwoStepPairFinset H).card ≤ m * d * d := by
  classical
  calc
    (CoreOldTwoStepPairFinset H).card ≤ (NeighborPairImageFinset H).card :=
      Finset.card_le_card coreOldTwoStepPair_subset_neighborPairImage
    _ ≤ ∑ w : Fin m, (H.neighborSet w).ncard * (H.neighborSet w).ncard :=
      neighborPairImage_card_le_sum_neighbor_ncard H
    _ ≤ ∑ _w : Fin m, d * d := by
      refine Finset.sum_le_sum ?_
      intro w _
      exact Nat.mul_le_mul (hdeg w) (hdeg w)
    _ = m * d * d := by
      simp [Fintype.card_fin]
      ring

/-- Distinct core pairs adjacent in a supergraph on `C ⊕ P`. -/
noncomputable def CoreAdjPairFinset {C P : Type} [Fintype C] (K : SimpleGraph (C ⊕ P)) : Finset (Sym2 C) := by
  classical
  exact Finset.univ.filter fun e : Sym2 C =>
    ¬ e.IsDiag ∧ ∃ a : C, ∃ b : C, e = s(a, b) ∧ K.Adj (Sum.inl a) (Sum.inl b)

lemma mem_coreAdjPairFinset_mk {C P : Type} [Fintype C] {K : SimpleGraph (C ⊕ P)}
    {a b : C} :
    s(a, b) ∈ CoreAdjPairFinset K ↔ a ≠ b ∧ K.Adj (Sum.inl a) (Sum.inl b) := by
  classical
  constructor
  · intro h
    rcases (by simpa [CoreAdjPairFinset] using h) with ⟨hdiag, c, d, hcd, hKcd⟩
    have hab : a ≠ b := by
      intro h
      exact hdiag (by simpa [Sym2.mk_isDiag_iff] using h)
    rcases hcd with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hab, by simpa [hac, hbd] using hKcd⟩
    · exact ⟨hab, by simpa [had, hbc] using hKcd.symm⟩
  · rintro ⟨hab, hK⟩
    simp [CoreAdjPairFinset, hab]
    exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, hK⟩

/-- Core-core adjacencies in `K` that were not old host edges. -/
noncomputable def CoreNewAdjPairFinset {C P : Type} [Fintype C] (H : SimpleGraph C)
    (K : SimpleGraph (C ⊕ P)) : Finset (Sym2 C) := by
  classical
  exact Finset.univ.filter fun e : Sym2 C =>
    ¬ e.IsDiag ∧ ∃ a : C, ∃ b : C,
      e = s(a, b) ∧ K.Adj (Sum.inl a) (Sum.inl b) ∧ ¬ H.Adj a b

lemma mem_coreNewAdjPairFinset_mk {C P : Type} [Fintype C] {H : SimpleGraph C}
    {K : SimpleGraph (C ⊕ P)} {a b : C} :
    s(a, b) ∈ CoreNewAdjPairFinset H K ↔
      a ≠ b ∧ K.Adj (Sum.inl a) (Sum.inl b) ∧ ¬ H.Adj a b := by
  classical
  constructor
  · intro h
    rcases (by simpa [CoreNewAdjPairFinset] using h) with ⟨hdiag, c, d, hcd, hKcd, hHcd⟩
    have hab : a ≠ b := by
      intro h
      exact hdiag (by simpa [Sym2.mk_isDiag_iff] using h)
    rcases hcd with ⟨hac, hbd⟩ | ⟨had, hbc⟩
    · exact ⟨hab, by simpa [hac, hbd] using hKcd, by simpa [hac, hbd] using hHcd⟩
    · exact ⟨hab, by simpa [had, hbc] using hKcd.symm,
        by simpa [had, hbc, adj_comm] using hHcd⟩
  · rintro ⟨hab, hK, hH⟩
    simp [CoreNewAdjPairFinset, hab]
    exact ⟨a, b, Or.inl ⟨rfl, rfl⟩, hK, hH⟩

lemma coreFree_components_coreClose_of_two_step {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X Y : (PendantPairGraph K).ConnectedComponent}
    (hXfree : PendantComponentCoreFree K root X)
    (hYfree : PendantComponentCoreFree K root Y) (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp)
    {z : C ⊕ P} (hpz : K.Adj (Sum.inr p) z) (hzq : K.Adj z (Sum.inr q)) :
    CoreClose K (root p) (root q) := by
  cases z with
  | inl c =>
      have hpc : c = root p := hXfree p hp c hpz
      have hqc : c = root q := hYfree q hq c hzq.symm
      have hroot : root p = root q := hpc.symm.trans hqc
      simpa [hroot] using CoreClose.refl (K := K) (root p)
  | inr r =>
      have hrX : r ∈ X.supp := X.mem_supp_of_adj_mem_supp hp hpz
      have hrY : r ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq hzq.symm
      exact False.elim (hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hrX hrY))

lemma coreFree_components_exists_coreClose_of_three_step {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X Y : (PendantPairGraph K).ConnectedComponent}
    (hXfree : PendantComponentCoreFree K root X)
    (hYfree : PendantComponentCoreFree K root Y) (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp)
    {z₁ z₂ : C ⊕ P} (h01 : K.Adj (Sum.inr p) z₁)
    (h12 : K.Adj z₁ z₂) (h23 : K.Adj z₂ (Sum.inr q)) :
    ∃ u : P, u ∈ X.supp ∧ ∃ v : P, v ∈ Y.supp ∧ CoreClose K (root u) (root v) := by
  cases z₁ with
  | inl c₁ =>
      cases z₂ with
      | inl c₂ =>
          refine ⟨p, hp, q, hq, ?_⟩
          have hc₁ : c₁ = root p := hXfree p hp c₁ h01
          have hc₂ : c₂ = root q := hYfree q hq c₂ h23.symm
          exact CoreClose.of_adj (by simpa [hc₁, hc₂] using h12)
      | inr r₂ =>
          have hc₁p : c₁ = root p := hXfree p hp c₁ h01
          have hr₂Y : r₂ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h23.symm
          have hc₁r₂ : c₁ = root r₂ := hYfree r₂ hr₂Y c₁ h12.symm
          refine ⟨p, hp, r₂, hr₂Y, ?_⟩
          have hroot : root p = root r₂ := hc₁p.symm.trans hc₁r₂
          simpa [hroot] using CoreClose.refl (K := K) (root p)
  | inr r₁ =>
      cases z₂ with
      | inl c₂ =>
          have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
          have hc₂r₁ : c₂ = root r₁ := hXfree r₁ hr₁X c₂ h12
          have hc₂q : c₂ = root q := hYfree q hq c₂ h23.symm
          refine ⟨r₁, hr₁X, q, hq, ?_⟩
          have hroot : root r₁ = root q := hc₂r₁.symm.trans hc₂q
          simpa [hroot] using CoreClose.refl (K := K) (root r₁)
      | inr r₂ =>
          have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
          have hr₂X : r₂ ∈ X.supp := X.mem_supp_of_adj_mem_supp hr₁X h12
          have hr₂Y : r₂ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h23.symm
          exact False.elim (hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hr₂X hr₂Y))

lemma coreFree_components_exists_coreClose_of_four_step {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X Y : (PendantPairGraph K).ConnectedComponent}
    (hXfree : PendantComponentCoreFree K root X)
    (hYfree : PendantComponentCoreFree K root Y) (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp)
    {z₁ z₂ z₃ : C ⊕ P} (h01 : K.Adj (Sum.inr p) z₁)
    (h12 : K.Adj z₁ z₂) (h23 : K.Adj z₂ z₃)
    (h34 : K.Adj z₃ (Sum.inr q)) :
    ∃ u : P, u ∈ X.supp ∧ ∃ v : P, v ∈ Y.supp ∧ CoreClose K (root u) (root v) := by
  cases z₁ with
  | inl c₁ =>
      cases z₂ with
      | inl c₂ =>
          cases z₃ with
          | inl c₃ =>
              refine ⟨p, hp, q, hq, ?_⟩
              have hc₁ : c₁ = root p := hXfree p hp c₁ h01
              have hc₃ : c₃ = root q := hYfree q hq c₃ h34.symm
              exact CoreClose.of_two_step (by simpa [hc₁] using h12) (by simpa [hc₃] using h23)
          | inr r₃ =>
              have hc₁ : c₁ = root p := hXfree p hp c₁ h01
              have hr₃Y : r₃ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h34.symm
              have hc₂r₃ : c₂ = root r₃ := hYfree r₃ hr₃Y c₂ h23.symm
              refine ⟨p, hp, r₃, hr₃Y, ?_⟩
              exact CoreClose.of_adj (by simpa [hc₁, hc₂r₃] using h12)
      | inr r₂ =>
          cases z₃ with
          | inl c₃ =>
              refine ⟨p, hp, q, hq, ?_⟩
              have hc₁p : c₁ = root p := hXfree p hp c₁ h01
              have hc₃q : c₃ = root q := hYfree q hq c₃ h34.symm
              exact CoreClose.of_two_step (by simpa [hc₁p] using h12) (by simpa [hc₃q] using h23)
          | inr r₃ =>
              have hc₁p : c₁ = root p := hXfree p hp c₁ h01
              have hr₃Y : r₃ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h34.symm
              have hr₂Y : r₂ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hr₃Y h23.symm
              have hc₁r₂ : c₁ = root r₂ := hYfree r₂ hr₂Y c₁ h12.symm
              refine ⟨p, hp, r₂, hr₂Y, ?_⟩
              have hroot : root p = root r₂ := hc₁p.symm.trans hc₁r₂
              simpa [hroot] using CoreClose.refl (K := K) (root p)
  | inr r₁ =>
      cases z₂ with
      | inl c₂ =>
          cases z₃ with
          | inl c₃ =>
              have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
              have hc₂r₁ : c₂ = root r₁ := hXfree r₁ hr₁X c₂ h12
              have hc₃q : c₃ = root q := hYfree q hq c₃ h34.symm
              refine ⟨r₁, hr₁X, q, hq, ?_⟩
              exact CoreClose.of_adj (by simpa [hc₂r₁, hc₃q] using h23)
          | inr r₃ =>
              have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
              have hc₂r₁ : c₂ = root r₁ := hXfree r₁ hr₁X c₂ h12
              have hr₃Y : r₃ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h34.symm
              have hc₂r₃ : c₂ = root r₃ := hYfree r₃ hr₃Y c₂ h23.symm
              refine ⟨r₁, hr₁X, r₃, hr₃Y, ?_⟩
              have hroot : root r₁ = root r₃ := hc₂r₁.symm.trans hc₂r₃
              simpa [hroot] using CoreClose.refl (K := K) (root r₁)
      | inr r₂ =>
          cases z₃ with
          | inl c₃ =>
              have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
              have hr₂X : r₂ ∈ X.supp := X.mem_supp_of_adj_mem_supp hr₁X h12
              have hc₃r₂ : c₃ = root r₂ := hXfree r₂ hr₂X c₃ h23
              have hc₃q : c₃ = root q := hYfree q hq c₃ h34.symm
              refine ⟨r₂, hr₂X, q, hq, ?_⟩
              have hroot : root r₂ = root q := hc₃r₂.symm.trans hc₃q
              simpa [hroot] using CoreClose.refl (K := K) (root r₂)
          | inr r₃ =>
              have hr₁X : r₁ ∈ X.supp := X.mem_supp_of_adj_mem_supp hp h01
              have hr₂X : r₂ ∈ X.supp := X.mem_supp_of_adj_mem_supp hr₁X h12
              have hr₃X : r₃ ∈ X.supp := X.mem_supp_of_adj_mem_supp hr₂X h23
              have hr₃Y : r₃ ∈ Y.supp := Y.mem_supp_of_adj_mem_supp hq h34.symm
              exact False.elim (hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hr₃X hr₃Y))

lemma coreFree_components_exists_coreClose_of_walk_le_four {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X Y : (PendantPairGraph K).ConnectedComponent}
    (hXfree : PendantComponentCoreFree K root X)
    (hYfree : PendantComponentCoreFree K root Y) (hXY : X ≠ Y)
    {p q : P} (hp : p ∈ X.supp) (hq : q ∈ Y.supp)
    (w : K.Walk (Sum.inr p) (Sum.inr q)) (hw : w.length ≤ 4) :
    ∃ u : P, u ∈ X.supp ∧ ∃ v : P, v ∈ Y.supp ∧ CoreClose K (root u) (root v) := by
  cases w with
  | nil =>
      exact False.elim (hXY (SimpleGraph.ConnectedComponent.eq_of_common_vertex hp hq))
  | cons h01 w₁ =>
      cases w₁ with
      | nil =>
          exact False.elim ((pendantPairGraph_not_adj_of_mem_distinct_components hXY hp hq) h01)
      | cons h12 w₂ =>
          cases w₂ with
          | nil =>
              exact ⟨p, hp, q, hq,
                coreFree_components_coreClose_of_two_step hXfree hYfree hXY hp hq h01 h12⟩
          | cons h23 w₃ =>
              cases w₃ with
              | nil =>
                  exact coreFree_components_exists_coreClose_of_three_step
                    hXfree hYfree hXY hp hq h01 h12 h23
              | cons h34 w₄ =>
                  cases w₄ with
                  | nil =>
                      exact coreFree_components_exists_coreClose_of_four_step
                        hXfree hYfree hXY hp hq h01 h12 h23 h34
                  | cons h45 w₅ =>
                      simp at hw
                      omega

/-- Lemma 1 from the write-up, in the form needed for counting: distinct core-free
pendant-pair components force a pair of roots to be within two steps in the supergraph. -/
lemma coreFree_components_exists_coreClose_of_ediam_le_four {C P : Type}
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X Y : (PendantPairGraph K).ConnectedComponent}
    (hKdiam : K.ediam ≤ (4 : ℕ∞))
    (hXfree : PendantComponentCoreFree K root X)
    (hYfree : PendantComponentCoreFree K root Y) (hXY : X ≠ Y) :
    ∃ u : P, u ∈ X.supp ∧ ∃ v : P, v ∈ Y.supp ∧ CoreClose K (root u) (root v) := by
  rcases X.nonempty_supp with ⟨p, hp⟩
  rcases Y.nonempty_supp with ⟨q, hq⟩
  have hed : K.edist (Sum.inr p) (Sum.inr q) ≤ (4 : ℕ∞) :=
    (SimpleGraph.ediam_le_iff.mp hKdiam) (Sum.inr p) (Sum.inr q)
  rcases exists_walk_length_le_of_edist_le hed with ⟨w, hw⟩
  exact coreFree_components_exists_coreClose_of_walk_le_four hXfree hYfree hXY hp hq w hw

/-- The new edges of `K` over a base graph `G`, as a finset matching `addedEdgeCount`. -/
noncomputable def AddedEdgeFinset {V : Type} [Fintype V] (G K : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact K.edgeFinset \ G.edgeFinset

@[simp] lemma mem_addedEdgeFinset {V : Type} [Fintype V] {G K : SimpleGraph V}
    {e : Sym2 V} :
    e ∈ AddedEdgeFinset G K ↔ e ∈ K.edgeSet ∧ e ∉ G.edgeSet := by
  classical
  simp [AddedEdgeFinset]

@[simp] lemma addedEdgeCount_eq_addedEdgeFinset {n : ℕ} (G K : SimpleGraph (Fin n)) :
    addedEdgeCount G K = (AddedEdgeFinset G K).card := by
  classical
  unfold addedEdgeCount AddedEdgeFinset
  congr 1
  ext e
  simp

lemma coreNewAdjPair_card_le_addedEdgeFinset {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    (CoreNewAdjPairFinset H K).card ≤
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  let cinl : C ↪ C ⊕ P := Function.Embedding.inl
  let f : {e : Sym2 C // e ∈ CoreNewAdjPairFinset H K} →
      {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K} := fun e =>
    ⟨cinl.sym2Map e.1, by
      refine Sym2.ind ?_ e.1 e.2
      intro a b heab
      rcases (mem_coreNewAdjPairFinset_mk (H := H) (K := K)).mp heab with
        ⟨_hab, hK, hH⟩
      rw [mem_addedEdgeFinset]
      constructor
      · simpa [cinl, Function.Embedding.sym2Map_apply, Sym2.map_mk, SimpleGraph.mem_edgeSet] using hK
      · intro hbase
        apply hH
        simpa [cinl, Function.Embedding.sym2Map_apply, Sym2.map_mk, SimpleGraph.mem_edgeSet] using hbase⟩
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    apply Subtype.ext
    have hval : cinl.sym2Map e₁.1 = cinl.sym2Map e₂.1 := by
      simpa [f] using congrArg Subtype.val h
    exact cinl.sym2Map.injective hval
  have hcard := Nat.card_le_card_of_injective f hf
  have hdom : Nat.card {e : Sym2 C // e ∈ CoreNewAdjPairFinset H K} =
      (CoreNewAdjPairFinset H K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcod : Nat.card {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K} =
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hdom, hcod] at hcard
  exact hcard

lemma coreAdjPair_card_le_host_edges_add_added {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    (CoreAdjPairFinset K).card ≤
      Nat.card H.edgeSet + (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  have hsubset : CoreAdjPairFinset K ⊆ H.edgeFinset ∪ CoreNewAdjPairFinset H K := by
    intro e he
    rcases (by simpa [CoreAdjPairFinset] using he) with ⟨hdiag, a, b, hpair, hK⟩
    by_cases hH : H.Adj a b
    · apply Finset.mem_union.mpr
      left
      rw [hpair]
      simpa [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hH
    · apply Finset.mem_union.mpr
      right
      rw [CoreNewAdjPairFinset]
      simp [hdiag]
      exact ⟨a, b, hpair, hK, hH⟩
  have hcard_union : (CoreAdjPairFinset K).card ≤
      (H.edgeFinset ∪ CoreNewAdjPairFinset H K).card := Finset.card_le_card hsubset
  have hunion : (H.edgeFinset ∪ CoreNewAdjPairFinset H K).card ≤
      H.edgeFinset.card + (CoreNewAdjPairFinset H K).card := Finset.card_union_le _ _
  have hnew := coreNewAdjPair_card_le_addedEdgeFinset (H := H) (root := root) (K := K)
  have hedge : H.edgeFinset.card = Nat.card H.edgeSet := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
  omega

/-- Oriented new edges whose terminal endpoint is a core vertex.  These are the charges used for
non-old distance-two close pairs. -/
noncomputable def CoreIncidentNewOrientationFinset {C P : Type} [Fintype C] [Fintype P]
    (H : SimpleGraph C) (root : P → C) (K : SimpleGraph (C ⊕ P)) : Finset ((C ⊕ P) × C) := by
  classical
  exact Finset.univ.filter fun oa : (C ⊕ P) × C =>
    K.Adj oa.1 (Sum.inl oa.2) ∧
      s(oa.1, Sum.inl oa.2) ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K

@[simp] lemma mem_coreIncidentNewOrientationFinset {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} {z : C ⊕ P} {a : C} :
    (z, a) ∈ CoreIncidentNewOrientationFinset H root K ↔
      K.Adj z (Sum.inl a) ∧
        s(z, Sum.inl a) ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K := by
  classical
  simp [CoreIncidentNewOrientationFinset]

/-- The overcounting set of charged close core pairs. -/
noncomputable def CoreChargedPairFinset {C P : Type} [Fintype C] [Fintype P]
    (H : SimpleGraph C) (root : P → C) (K : SimpleGraph (C ⊕ P)) : Finset (Sym2 C) := by
  classical
  exact (CoreIncidentNewOrientationFinset H root K).biUnion fun oa =>
    (CoreNeighborFinset K oa.1).image fun b : C => s(oa.2, b)

lemma mem_coreChargedPairFinset_of_orientation {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)}
    {z : C ⊕ P} {a b : C}
    (hnew : (z, a) ∈ CoreIncidentNewOrientationFinset H root K)
    (hzb : K.Adj z (Sum.inl b)) :
    s(a, b) ∈ CoreChargedPairFinset H root K := by
  classical
  rw [CoreChargedPairFinset]
  apply Finset.mem_biUnion.mpr
  refine ⟨(z, a), hnew, ?_⟩
  apply Finset.mem_image.mpr
  exact ⟨b, by simpa using hzb, rfl⟩

lemma base_core_two_step_of_base_neighbors {C P : Type} {H : SimpleGraph C} {root : P → C}
    {z : C ⊕ P} {a b : C} (hab : a ≠ b)
    (hza : (PendantCoreGraphSum H root).Adj z (Sum.inl a))
    (hzb : (PendantCoreGraphSum H root).Adj z (Sum.inl b)) :
    ∃ w : C, H.Adj w a ∧ H.Adj w b := by
  cases z with
  | inl w =>
      exact ⟨w, by simpa using hza, by simpa using hzb⟩
  | inr p =>
      have ha : a = root p := by simpa using hza
      have hb : b = root p := by simpa using hzb
      exact False.elim (hab (ha.trans hb.symm))

lemma coreClosePair_subset_adj_old_charged {C P : Type} [Fintype C] [Fintype P] [DecidableEq C]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    CoreClosePairFinset K ⊆
      (CoreAdjPairFinset K ∪ CoreOldTwoStepPairFinset H) ∪ CoreChargedPairFinset H root K := by
  classical
  intro e he
  refine Sym2.ind ?_ e he
  intro a b heab
  rcases (mem_coreClosePairFinset_mk (K := K)).mp heab with ⟨hab, hclose⟩
  rcases hclose.adj_or_two_step_of_ne hab with hAdj | hTwo
  · apply Finset.mem_union.mpr
    left
    apply Finset.mem_union.mpr
    left
    exact (mem_coreAdjPairFinset_mk (K := K)).mpr ⟨hab, hAdj⟩
  · rcases hTwo with ⟨z, haz, hzb⟩
    have hza : K.Adj z (Sum.inl a) := haz.symm
    by_cases hbaseza : (PendantCoreGraphSum H root).Adj z (Sum.inl a)
    · by_cases hbasezb : (PendantCoreGraphSum H root).Adj z (Sum.inl b)
      · rcases base_core_two_step_of_base_neighbors (H := H) (root := root) hab hbaseza hbasezb with
          ⟨w, hwa, hwb⟩
        apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        exact (mem_coreOldTwoStepPairFinset_mk (H := H)).mpr ⟨hab, w, hwa, hwb⟩
      · have hadded : s(z, Sum.inl b) ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K := by
          rw [mem_addedEdgeFinset]
          constructor
          · simpa [SimpleGraph.mem_edgeSet] using hzb
          · intro hbaseEdge
            exact hbasezb (by simpa [SimpleGraph.mem_edgeSet] using hbaseEdge)
        have horient : (z, b) ∈ CoreIncidentNewOrientationFinset H root K := by
          exact (mem_coreIncidentNewOrientationFinset (H := H) (root := root) (K := K)).mpr ⟨hzb, hadded⟩
        apply Finset.mem_union.mpr
        right
        simpa [Sym2.eq_swap] using mem_coreChargedPairFinset_of_orientation (H := H)
          (root := root) (K := K) horient hza
    · have hadded : s(z, Sum.inl a) ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K := by
        rw [mem_addedEdgeFinset]
        constructor
        · simpa [SimpleGraph.mem_edgeSet] using hza
        · intro hbaseEdge
          exact hbaseza (by simpa [SimpleGraph.mem_edgeSet] using hbaseEdge)
      have horient : (z, a) ∈ CoreIncidentNewOrientationFinset H root K := by
        exact (mem_coreIncidentNewOrientationFinset (H := H) (root := root) (K := K)).mpr ⟨hza, hadded⟩
      apply Finset.mem_union.mpr
      right
      exact mem_coreChargedPairFinset_of_orientation (H := H) (root := root) (K := K) horient hzb

lemma coreChargedPair_card_le_orientation_mul_indepNum {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)}
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    (CoreChargedPairFinset H root K).card ≤
      (CoreIncidentNewOrientationFinset H root K).card * H.indepNum := by
  classical
  let orient := CoreIncidentNewOrientationFinset H root K
  let imageAt := fun oa : (C ⊕ P) × C => (CoreNeighborFinset K oa.1).image fun b : C => s(oa.2, b)
  have hcard : (CoreChargedPairFinset H root K).card ≤ ∑ oa ∈ orient, (imageAt oa).card := by
    simpa [CoreChargedPairFinset, orient, imageAt] using (Finset.card_biUnion_le (s := orient) (t := imageAt))
  have hsum : (∑ oa ∈ orient, (imageAt oa).card) ≤ ∑ _oa ∈ orient, H.indepNum := by
    refine Finset.sum_le_sum ?_
    intro oa _
    exact (Finset.card_image_le.trans (coreNeighborFinset_card_le_indepNum_of_pendantCore_le hGK hKtf oa.1))
  calc
    (CoreChargedPairFinset H root K).card ≤ ∑ oa ∈ orient, (imageAt oa).card := hcard
    _ ≤ ∑ _oa ∈ orient, H.indepNum := hsum
    _ = orient.card * H.indepNum := by simp [Finset.sum_const]

/-- Endpoints of a finset of unordered pairs, counted with the pair they belong to. -/
noncomputable def Sym2EndpointFinset {V : Type} (E : Finset (Sym2 V)) : Finset (Sym2 V × V) := by
  classical
  exact E.biUnion fun e => e.toFinset.image fun v => (e, v)

@[simp] lemma mem_sym2EndpointFinset {V : Type} {E : Finset (Sym2 V)} {e : Sym2 V} {v : V} :
    (e, v) ∈ Sym2EndpointFinset E ↔ e ∈ E ∧ v ∈ e := by
  classical
  constructor
  · intro h
    rw [Sym2EndpointFinset] at h
    rcases Finset.mem_biUnion.mp h with ⟨e', he', hv⟩
    rcases Finset.mem_image.mp hv with ⟨v', hv', hpair⟩
    cases hpair
    exact ⟨he', by simpa [Sym2.mem_toFinset] using hv'⟩
  · rintro ⟨he, hv⟩
    rw [Sym2EndpointFinset]
    apply Finset.mem_biUnion.mpr
    refine ⟨e, he, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨v, by simpa [Sym2.mem_toFinset] using hv, rfl⟩

lemma sym2EndpointFinset_card_le_two_mul {V : Type} (E : Finset (Sym2 V)) :
    (Sym2EndpointFinset E).card ≤ 2 * E.card := by
  classical
  let endpoints := fun e : Sym2 V => e.toFinset.image fun v => (e, v)
  have hcard : (Sym2EndpointFinset E).card ≤ ∑ e ∈ E, (endpoints e).card := by
    simpa [Sym2EndpointFinset, endpoints] using
      (Finset.card_biUnion_le (s := E) (t := endpoints))
  have hsum : (∑ e ∈ E, (endpoints e).card) ≤ ∑ _e ∈ E, 2 := by
    refine Finset.sum_le_sum ?_
    intro e _
    have himage : (endpoints e).card ≤ e.toFinset.card := by
      simpa [endpoints] using (Finset.card_image_le (s := e.toFinset) (f := fun v => (e, v)))
    have hto : e.toFinset.card ≤ 2 := by
      rw [Sym2.card_toFinset]
      split <;> omega
    exact himage.trans hto
  calc
    (Sym2EndpointFinset E).card ≤ ∑ e ∈ E, (endpoints e).card := hcard
    _ ≤ ∑ _e ∈ E, 2 := hsum
    _ = E.card * 2 := by simp [Finset.sum_const]
    _ = 2 * E.card := by rw [Nat.mul_comm]

/-- Ordered distinct core pairs whose unordered pair is close. -/
noncomputable def CoreCloseOrderedPairFinset {C P : Type} [Fintype C]
    (K : SimpleGraph (C ⊕ P)) : Finset (C × C) := by
  classical
  exact Finset.univ.filter fun ab : C × C => ab.1 ≠ ab.2 ∧ s(ab.1, ab.2) ∈ CoreClosePairFinset K

@[simp] lemma mem_coreCloseOrderedPairFinset {C P : Type} [Fintype C]
    {K : SimpleGraph (C ⊕ P)} {a b : C} :
    (a, b) ∈ CoreCloseOrderedPairFinset K ↔ a ≠ b ∧ s(a, b) ∈ CoreClosePairFinset K := by
  classical
  simp [CoreCloseOrderedPairFinset]

lemma coreCloseOrderedPair_card_le_two_mul {C P : Type} [Fintype C]
    {K : SimpleGraph (C ⊕ P)} :
    (CoreCloseOrderedPairFinset K).card ≤ 2 * (CoreClosePairFinset K).card := by
  classical
  let endpoints := Sym2EndpointFinset (CoreClosePairFinset K)
  let f : {ab : C × C // ab ∈ CoreCloseOrderedPairFinset K} →
      {ev : Sym2 C × C // ev ∈ endpoints} := fun ab =>
    ⟨(s(ab.1.1, ab.1.2), ab.1.1), by
      change (s(ab.1.1, ab.1.2), ab.1.1) ∈ Sym2EndpointFinset (CoreClosePairFinset K)
      rw [mem_sym2EndpointFinset]
      exact ⟨(mem_coreCloseOrderedPairFinset (K := K)).mp ab.2 |>.2,
        Sym2.mem_mk_left _ _⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨a₁, b₁⟩, h₁⟩ ⟨⟨a₂, b₂⟩, h₂⟩ h
    apply Subtype.ext
    have hpair : (s(a₁, b₁), a₁) = (s(a₂, b₂), a₂) := by
      simpa [f] using congrArg Subtype.val h
    have ha : a₁ = a₂ := congrArg Prod.snd hpair
    have hedge : s(a₁, b₁) = s(a₂, b₂) := congrArg Prod.fst hpair
    have hb : b₁ = b₂ := by
      have hedge' : s(a₁, b₁) = s(a₁, b₂) := by
        simpa [ha] using hedge
      exact Sym2.congr_right.mp hedge'
    simp [ha, hb]
  have hcard := Nat.card_le_card_of_injective f hf
  have hdom : Nat.card {ab : C × C // ab ∈ CoreCloseOrderedPairFinset K} =
      (CoreCloseOrderedPairFinset K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcod : Nat.card {ev : Sym2 C × C // ev ∈ endpoints} = endpoints.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hdom, hcod] at hcard
  exact hcard.trans (sym2EndpointFinset_card_le_two_mul (CoreClosePairFinset K))

/-- Endpoints of new edges, counted with the edge they belong to. -/
noncomputable def AddedEdgeEndpointFinset {V : Type} [Fintype V]
    (G K : SimpleGraph V) : Finset (Sym2 V × V) := by
  classical
  exact (AddedEdgeFinset G K).biUnion fun e => e.toFinset.image fun v => (e, v)

@[simp] lemma mem_addedEdgeEndpointFinset {V : Type} [Fintype V]
    {G K : SimpleGraph V} {e : Sym2 V} {v : V} :
    (e, v) ∈ AddedEdgeEndpointFinset G K ↔ e ∈ AddedEdgeFinset G K ∧ v ∈ e := by
  classical
  constructor
  · intro h
    rw [AddedEdgeEndpointFinset] at h
    rcases Finset.mem_biUnion.mp h with ⟨e', he', hv⟩
    rcases Finset.mem_image.mp hv with ⟨v', hv', hpair⟩
    cases hpair
    exact ⟨he', by simpa [Sym2.mem_toFinset] using hv'⟩
  · rintro ⟨he, hv⟩
    rw [AddedEdgeEndpointFinset]
    apply Finset.mem_biUnion.mpr
    refine ⟨e, he, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨v, by simpa [Sym2.mem_toFinset] using hv, rfl⟩

lemma addedEdgeEndpointFinset_card_le_two_mul {V : Type} [Fintype V]
    (G K : SimpleGraph V) :
    (AddedEdgeEndpointFinset G K).card ≤ 2 * (AddedEdgeFinset G K).card := by
  classical
  let endpoints := fun e : Sym2 V => e.toFinset.image fun v => (e, v)
  have hcard : (AddedEdgeEndpointFinset G K).card ≤
      ∑ e ∈ AddedEdgeFinset G K, (endpoints e).card := by
    simpa [AddedEdgeEndpointFinset, endpoints] using
      (Finset.card_biUnion_le (s := AddedEdgeFinset G K) (t := endpoints))
  have hsum : (∑ e ∈ AddedEdgeFinset G K, (endpoints e).card) ≤
      ∑ _e ∈ AddedEdgeFinset G K, 2 := by
    refine Finset.sum_le_sum ?_
    intro e _
    have himage : (endpoints e).card ≤ e.toFinset.card := by
      simpa [endpoints] using (Finset.card_image_le (s := e.toFinset) (f := fun v => (e, v)))
    have hto : e.toFinset.card ≤ 2 := by
      rw [Sym2.card_toFinset]
      split <;> omega
    exact himage.trans hto
  calc
    (AddedEdgeEndpointFinset G K).card ≤
        ∑ e ∈ AddedEdgeFinset G K, (endpoints e).card := hcard
    _ ≤ ∑ _e ∈ AddedEdgeFinset G K, 2 := hsum
    _ = (AddedEdgeFinset G K).card * 2 := by simp [Finset.sum_const]
    _ = 2 * (AddedEdgeFinset G K).card := by rw [Nat.mul_comm]

lemma coreIncidentNewOrientation_card_le_two_mul_added {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    (CoreIncidentNewOrientationFinset H root K).card ≤
      2 * (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  let endpointSet := AddedEdgeEndpointFinset (PendantCoreGraphSum H root) K
  let f : {oa : (C ⊕ P) × C // oa ∈ CoreIncidentNewOrientationFinset H root K} →
      {ev : Sym2 (C ⊕ P) × (C ⊕ P) // ev ∈ endpointSet} := fun oa =>
    ⟨(s(oa.1.1, Sum.inl oa.1.2), Sum.inl oa.1.2), by
      change (s(oa.1.1, Sum.inl oa.1.2), Sum.inl oa.1.2) ∈
        AddedEdgeEndpointFinset (PendantCoreGraphSum H root) K
      rw [mem_addedEdgeEndpointFinset]
      exact ⟨(mem_coreIncidentNewOrientationFinset (H := H) (root := root) (K := K)).mp oa.2 |>.2,
        Sym2.mem_mk_right _ _⟩⟩
  have hf : Function.Injective f := by
    rintro ⟨⟨z₁, a₁⟩, h₁⟩ ⟨⟨z₂, a₂⟩, h₂⟩ h
    apply Subtype.ext
    have hpair : (s(z₁, (Sum.inl a₁ : C ⊕ P)), (Sum.inl a₁ : C ⊕ P)) =
        (s(z₂, (Sum.inl a₂ : C ⊕ P)), (Sum.inl a₂ : C ⊕ P)) := by
      simpa [f] using congrArg Subtype.val h
    have ha : a₁ = a₂ := Sum.inl.inj (congrArg Prod.snd hpair)
    have hedge : s(z₁, (Sum.inl a₁ : C ⊕ P)) = s(z₂, (Sum.inl a₂ : C ⊕ P)) :=
      congrArg Prod.fst hpair
    have hz : z₁ = z₂ := by
      have hedge' : s(z₁, (Sum.inl a₁ : C ⊕ P)) = s(z₂, (Sum.inl a₁ : C ⊕ P)) := by
        simpa [ha] using hedge
      exact Sym2.congr_left.mp hedge'
    simp [hz, ha]
  have hcard := Nat.card_le_card_of_injective f hf
  have hdom : Nat.card {oa : (C ⊕ P) × C // oa ∈ CoreIncidentNewOrientationFinset H root K} =
      (CoreIncidentNewOrientationFinset H root K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcod : Nat.card {ev : Sym2 (C ⊕ P) × (C ⊕ P) // ev ∈ endpointSet} =
      endpointSet.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hdom, hcod] at hcard
  exact hcard.trans (addedEdgeEndpointFinset_card_le_two_mul (PendantCoreGraphSum H root) K)

lemma coreChargedPair_card_le_two_mul_added_mul_indepNum {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)}
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    (CoreChargedPairFinset H root K).card ≤
      2 * (AddedEdgeFinset (PendantCoreGraphSum H root) K).card * H.indepNum := by
  have hcharged := coreChargedPair_card_le_orientation_mul_indepNum (H := H) (root := root)
    (K := K) hGK hKtf
  have horient := coreIncidentNewOrientation_card_le_two_mul_added (H := H) (root := root) (K := K)
  exact hcharged.trans (Nat.mul_le_mul_right H.indepNum horient)

lemma coreClosePair_card_le_adj_old_charged {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    (CoreClosePairFinset K).card ≤
      (CoreAdjPairFinset K).card + (CoreOldTwoStepPairFinset H).card +
        (CoreChargedPairFinset H root K).card := by
  classical
  have hsubset := coreClosePair_subset_adj_old_charged (C := C) (P := P)
    (H := H) (root := root) (K := K)
  have hcard : (CoreClosePairFinset K).card ≤
      ((CoreAdjPairFinset K ∪ CoreOldTwoStepPairFinset H) ∪
        CoreChargedPairFinset H root K).card := Finset.card_le_card hsubset
  have houter : ((CoreAdjPairFinset K ∪ CoreOldTwoStepPairFinset H) ∪
        CoreChargedPairFinset H root K).card ≤
      (CoreAdjPairFinset K ∪ CoreOldTwoStepPairFinset H).card +
        (CoreChargedPairFinset H root K).card := Finset.card_union_le _ _
  have hinner : (CoreAdjPairFinset K ∪ CoreOldTwoStepPairFinset H).card ≤
      (CoreAdjPairFinset K).card + (CoreOldTwoStepPairFinset H).card := Finset.card_union_le _ _
  omega

lemma coreClosePair_card_le_host_raw {d m : ℕ} {P : Type} [Fintype P]
    {H : SimpleGraph (Fin m)} {root : P → Fin m} {K : SimpleGraph (Fin m ⊕ P)}
    (hHost : HostGraph d m H)
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    (CoreClosePairFinset K).card ≤
      (m * d + (AddedEdgeFinset (PendantCoreGraphSum H root) K).card) +
        m * d * d +
          2 * (AddedEdgeFinset (PendantCoreGraphSum H root) K).card * H.indepNum := by
  classical
  have hclose := coreClosePair_card_le_adj_old_charged (H := H) (root := root) (K := K)
  have hadj := coreAdjPair_card_le_host_edges_add_added (H := H) (root := root) (K := K)
  have hedge := HostGraph.edgeSet_nat_card_le_card_mul hHost
  have hold := coreOldTwoStepPair_card_le_card_mul_sq (m := m) (d := d) (H := H) hHost.maxDegreeAtMost
  have hcharged := coreChargedPair_card_le_two_mul_added_mul_indepNum (H := H) (root := root)
    (K := K) hGK hKtf
  omega

lemma coreClosePair_card_le_host {d m : ℕ} {P : Type} [Fintype P]
    {H : SimpleGraph (Fin m)} {root : P → Fin m} {K : SimpleGraph (Fin m ⊕ P)}
    (hHost : HostGraph d m H)
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    (CoreClosePairFinset K).card ≤
      m * d + m * d * d +
        (AddedEdgeFinset (PendantCoreGraphSum H root) K).card * (1 + 2 * H.indepNum) := by
  have hraw := coreClosePair_card_le_host_raw (d := d) (m := m) (H := H) (root := root)
    (K := K) hHost hGK hKtf
  nlinarith [hraw]

lemma coreClosePair_card_real_le_host {d m : ℕ} {P : Type} [Fintype P]
    {H : SimpleGraph (Fin m)} {root : P → Fin m} {K : SimpleGraph (Fin m ⊕ P)}
    (hHost : HostGraph d m H)
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    ((CoreClosePairFinset K).card : ℝ) ≤
      (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
        ((AddedEdgeFinset (PendantCoreGraphSum H root) K).card : ℝ) *
          (1 + 2 * (H.indepNum : ℝ)) := by
  have hnat := coreClosePair_card_le_host (d := d) (m := m) (H := H) (root := root)
    (K := K) hHost hGK hKtf
  exact_mod_cast hnat

lemma coreClosePair_card_real_le_host_log {d m : ℕ} {P : Type} [Fintype P]
    {H : SimpleGraph (Fin m)} {root : P → Fin m} {K : SimpleGraph (Fin m ⊕ P)}
    (hHost : HostGraph d m H)
    (hGK : PendantCoreGraphSum H root ≤ K) (hKtf : K.CliqueFree 3) :
    ((CoreClosePairFinset K).card : ℝ) ≤
      (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
        ((AddedEdgeFinset (PendantCoreGraphSum H root) K).card : ℝ) *
          (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ))) := by
  have hbase := coreClosePair_card_real_le_host (d := d) (m := m) (H := H) (root := root)
    (K := K) hHost hGK hKtf
  have hfac : 1 + 2 * (H.indepNum : ℝ) ≤
      1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)) := by
    nlinarith [HostGraph.indepNum_le hHost]
  have hmul := mul_le_mul_of_nonneg_left hfac
    (show 0 ≤ ((AddedEdgeFinset (PendantCoreGraphSum H root) K).card : ℝ) by positivity)
  nlinarith

lemma sym2_map_mem_edgeSet_comap_iff {V W : Type} (e : V ≃ W)
    (G : SimpleGraph W) (x : Sym2 V) :
    x.map e ∈ G.edgeSet ↔ x ∈ (G.comap e).edgeSet := by
  refine Sym2.ind ?_ x
  intro a b
  simp [SimpleGraph.mem_edgeSet]

noncomputable def sym2EquivOfEquiv {V W : Type} (e : V ≃ W) : Sym2 V ≃ Sym2 W where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv := by
    intro x
    rw [Sym2.map_map]
    refine Sym2.ind ?_ x
    intro a b
    simp [Sym2.map_mk]
  right_inv := by
    intro x
    rw [Sym2.map_map]
    refine Sym2.ind ?_ x
    intro a b
    simp [Sym2.map_mk]

@[simp] lemma sym2EquivOfEquiv_apply {V W : Type} (e : V ≃ W) (x : Sym2 V) :
    sym2EquivOfEquiv e x = x.map e := rfl

@[simp] lemma sym2EquivOfEquiv_symm_apply {V W : Type} (e : V ≃ W) (x : Sym2 W) :
    (sym2EquivOfEquiv e).symm x = x.map e.symm := rfl

lemma addedEdgeFinset_map_sym2Equiv_comap {V W : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (G K : SimpleGraph W) :
    (AddedEdgeFinset (G.comap e) (K.comap e)).map (sym2EquivOfEquiv e).toEmbedding =
      AddedEdgeFinset G K := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_map.mp hz with ⟨x, hx, hxz⟩
    rw [mem_addedEdgeFinset] at hx ⊢
    rw [← hxz]
    exact ⟨(sym2_map_mem_edgeSet_comap_iff e K x).2 hx.1,
      fun hG => hx.2 ((sym2_map_mem_edgeSet_comap_iff e G x).1 hG)⟩
  · intro hz
    rw [mem_addedEdgeFinset] at hz
    refine Finset.mem_map.mpr ⟨z.map e.symm, ?_, ?_⟩
    · rw [mem_addedEdgeFinset]
      have hKpre : z.map e.symm ∈ (K.comap e).edgeSet := by
        rw [← sym2_map_mem_edgeSet_comap_iff e K (z.map e.symm)]
        simpa [Sym2.map_map] using hz.1
      have hGpre : z.map e.symm ∉ (G.comap e).edgeSet := by
        intro hG
        apply hz.2
        have hGmap := (sym2_map_mem_edgeSet_comap_iff e G (z.map e.symm)).2 hG
        simpa [Sym2.map_map] using hGmap
      exact ⟨hKpre, hGpre⟩
    · simp [sym2EquivOfEquiv, Sym2.map_map]

lemma addedEdgeFinset_card_comap_equiv {V W : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (G K : SimpleGraph W) :
    (AddedEdgeFinset (G.comap e) (K.comap e)).card = (AddedEdgeFinset G K).card := by
  classical
  rw [← addedEdgeFinset_map_sym2Equiv_comap e G K, Finset.card_map]

lemma ediam_comap_equiv_le {V W : Type} (e : V ≃ W) {G : SimpleGraph W} {r : ℕ}
    (h : G.ediam ≤ (r : ℕ∞)) : (G.comap e).ediam ≤ (r : ℕ∞) := by
  apply ediam_le_of_forall_exists_walk_le
  intro u v
  have hed : G.edist (e u) (e v) ≤ (r : ℕ∞) :=
    (SimpleGraph.ediam_le_iff.mp h) (e u) (e v)
  rcases exists_walk_length_le_of_edist_le hed with ⟨p, hp⟩
  let iso := SimpleGraph.Iso.comap e G
  have hu : iso.symm (e u) = u := by
    change e.symm (e u) = u
    simp
  have hv : iso.symm (e v) = v := by
    change e.symm (e v) = v
    simp
  rw [← hu, ← hv]
  exact ⟨p.map iso.symm.toHom, by simpa [Walk.length_map] using hp⟩

lemma overFin_comap_equiv_eq {V : Type} [Fintype V] {n : ℕ} (G : SimpleGraph V)
    (hc : Fintype.card V = n) :
    (G.overFin hc).comap (Fintype.equivFinOfCardEq hc) = G := by
  ext u v
  simp [SimpleGraph.overFin]

lemma overFin_le_comap_of_le {V : Type} [Fintype V] {n : ℕ}
    {G : SimpleGraph V} {K : SimpleGraph (Fin n)} (hc : Fintype.card V = n)
    (hGK : G.overFin hc ≤ K) :
    G ≤ K.comap (Fintype.equivFinOfCardEq hc) := by
  classical
  let e := Fintype.equivFinOfCardEq hc
  intro u v huv
  have hfin : (G.overFin hc).Adj (e u) (e v) := by
    simpa [e, SimpleGraph.overFin] using huv
  exact hGK hfin

lemma cliqueFree_comap_equiv {V W : Type} (e : V ≃ W) {G : SimpleGraph W} {r : ℕ}
    (h : G.CliqueFree r) : (G.comap e).CliqueFree r := by
  exact SimpleGraph.CliqueFree.comap (SimpleGraph.Iso.comap e G).isContained h

lemma addedEdgeCount_overFin_eq_addedEdgeFinset_comap {V : Type} [Fintype V] {n : ℕ}
    (G : SimpleGraph V) (K : SimpleGraph (Fin n)) (hc : Fintype.card V = n) :
    addedEdgeCount (G.overFin hc) K =
      (AddedEdgeFinset G (K.comap (Fintype.equivFinOfCardEq hc))).card := by
  classical
  let e := Fintype.equivFinOfCardEq hc
  have hG : (G.overFin hc).comap e = G := by
    simpa [e] using overFin_comap_equiv_eq G hc
  calc
    addedEdgeCount (G.overFin hc) K = (AddedEdgeFinset (G.overFin hc) K).card := by
      rw [addedEdgeCount_eq_addedEdgeFinset]
    _ = (AddedEdgeFinset ((G.overFin hc).comap e) (K.comap e)).card := by
      exact (addedEdgeFinset_card_comap_equiv e (G.overFin hc) K).symm
    _ = (AddedEdgeFinset G (K.comap e)).card := by
      rw [hG]

/-- The finite set of pendant-pair components with no new edge to the core. -/
noncomputable def CoreFreeComponentFinset {C P : Type} [Fintype P]
    (K : SimpleGraph (C ⊕ P)) (root : P → C) :
    Finset (PendantPairGraph K).ConnectedComponent := by
  classical
  exact Finset.univ.filter fun X => PendantComponentCoreFree K root X

@[simp] lemma mem_coreFreeComponentFinset {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent} :
    X ∈ CoreFreeComponentFinset K root ↔ PendantComponentCoreFree K root X := by
  classical
  simp [CoreFreeComponentFinset]

/-- The finite set of pendant-pair components that have a new edge to the core. -/
noncomputable def CoreTouchingComponentFinset {C P : Type} [Fintype P]
    (K : SimpleGraph (C ⊕ P)) (root : P → C) :
    Finset (PendantPairGraph K).ConnectedComponent := by
  classical
  exact Finset.univ.filter fun X => PendantComponentCoreTouching K root X

@[simp] lemma mem_coreTouchingComponentFinset {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    {X : (PendantPairGraph K).ConnectedComponent} :
    X ∈ CoreTouchingComponentFinset K root ↔ PendantComponentCoreTouching K root X := by
  classical
  simp [CoreTouchingComponentFinset]

/-- A chosen new pendant-core edge witnessing that a component is core-touching. -/
noncomputable def touchingComponentWitness {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C}
    (X : {X : (PendantPairGraph K).ConnectedComponent //
      X ∈ CoreTouchingComponentFinset K root}) :
    {pc : P × C //
      pc.1 ∈ X.1.supp ∧ K.Adj (Sum.inr pc.1) (Sum.inl pc.2) ∧ pc.2 ≠ root pc.1} := by
  classical
  have htouch : PendantComponentCoreTouching K root X.1 :=
    (mem_coreTouchingComponentFinset (K := K) (root := root)).mp X.2
  let h := not_coreFree_iff_exists_new_core_edge.mp htouch
  let p : P := Classical.choose h
  have hp_spec : p ∈ X.1.supp ∧
      ∃ c : C, K.Adj (Sum.inr p) (Sum.inl c) ∧ c ≠ root p := Classical.choose_spec h
  let hc_exists := hp_spec.2
  let c : C := Classical.choose hc_exists
  have hc_spec : K.Adj (Sum.inr p) (Sum.inl c) ∧ c ≠ root p :=
    Classical.choose_spec hc_exists
  exact ⟨(p, c), hp_spec.1, hc_spec.1, hc_spec.2⟩

lemma sym2_inr_inr_ne_inr_inl {C P : Type} {p q r : P} {c : C} :
    s((Sum.inr p : C ⊕ P), Sum.inr q) ≠ s(Sum.inr r, Sum.inl c) := by
  intro h
  rw [Sym2.eq_iff] at h
  rcases h with ⟨_, hbad⟩ | ⟨hbad, _⟩ <;> cases hbad

lemma sym2Map_inr_ne_inr_inl {C P : Type} {e : Sym2 P} {p : P} {c : C} :
    ((Function.Embedding.inr : P ↪ C ⊕ P).sym2Map e) ≠
      s((Sum.inr p : C ⊕ P), Sum.inl c) := by
  intro h
  refine Sym2.ind ?_ e h
  intro a b hab
  have hshape : s((Sum.inr a : C ⊕ P), Sum.inr b) = s((Sum.inr p : C ⊕ P), Sum.inl c) := by
    simp [Function.Embedding.sym2Map_apply, Sym2.map_mk] at hab
  exact sym2_inr_inr_ne_inr_inl hshape

lemma sym2_inr_inl_eq_inr_inl {C P : Type} {p q : P} {a b : C}
    (h : s((Sum.inr p : C ⊕ P), Sum.inl a) = s(Sum.inr q, Sum.inl b)) :
    p = q ∧ a = b := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨hp, ha⟩ | ⟨hbad, _⟩
  · exact ⟨Sum.inr.inj hp, Sum.inl.inj ha⟩
  · cases hbad

lemma pendantPair_edges_add_touchingComponents_le_addedEdgeFinset {C P : Type}
    [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    Nat.card (PendantPairGraph K).edgeSet + (CoreTouchingComponentFinset K root).card ≤
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  let touch := CoreTouchingComponentFinset K root
  let pinr : P ↪ C ⊕ P := Function.Embedding.inr
  let charge : (PendantPairGraph K).edgeSet ⊕ {X : (PendantPairGraph K).ConnectedComponent // X ∈ touch} →
      {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K}
    | Sum.inl e =>
        ⟨pinr.sym2Map e.1, by
          refine Sym2.ind ?_ e.1 e.2
          intro p q hpq
          have hpq' : K.Adj (Sum.inr p) (Sum.inr q) := by
            simpa [SimpleGraph.mem_edgeSet] using hpq
          simp [pinr, mem_addedEdgeFinset, Function.Embedding.sym2Map_apply, Sym2.map_mk,
            hpq']⟩
    | Sum.inr X =>
        let w := touchingComponentWitness (K := K) (root := root) X
        ⟨s((Sum.inr w.1.1 : C ⊕ P), Sum.inl w.1.2), by
          have hK : K.Adj (Sum.inr w.1.1) (Sum.inl w.1.2) := w.2.2.1
          have hnew : w.1.2 ≠ root w.1.1 := w.2.2.2
          rw [mem_addedEdgeFinset]
          refine ⟨?_, ?_⟩
          · simpa [SimpleGraph.mem_edgeSet] using hK
          · intro hbase
            have hroot : w.1.2 = root w.1.1 := by
              simpa [SimpleGraph.mem_edgeSet] using hbase
            exact hnew hroot⟩
  have hcharge : Function.Injective charge := by
    intro x y hxy
    cases x with
    | inl e =>
        cases y with
        | inl e' =>
            apply congrArg Sum.inl
            apply Subtype.ext
            have hval : pinr.sym2Map e.1 = pinr.sym2Map e'.1 := by
              simpa [charge] using congrArg Subtype.val hxy
            exact pinr.sym2Map.injective hval
        | inr X =>
            exfalso
            let w := touchingComponentWitness (K := K) (root := root) X
            have hval : pinr.sym2Map e.1 = s((Sum.inr w.1.1 : C ⊕ P), Sum.inl w.1.2) := by
              simpa [charge, w] using congrArg Subtype.val hxy
            exact sym2Map_inr_ne_inr_inl (C := C) (P := P) hval
    | inr X =>
        cases y with
        | inl e =>
            exfalso
            let w := touchingComponentWitness (K := K) (root := root) X
            have hval : s((Sum.inr w.1.1 : C ⊕ P), Sum.inl w.1.2) = pinr.sym2Map e.1 := by
              simpa [charge, w] using congrArg Subtype.val hxy
            exact sym2Map_inr_ne_inr_inl (C := C) (P := P) hval.symm
        | inr Y =>
            apply congrArg Sum.inr
            apply Subtype.ext
            let wx := touchingComponentWitness (K := K) (root := root) X
            let wy := touchingComponentWitness (K := K) (root := root) Y
            have hval : s((Sum.inr wx.1.1 : C ⊕ P), Sum.inl wx.1.2) =
                s((Sum.inr wy.1.1 : C ⊕ P), Sum.inl wy.1.2) := by
              simpa [charge, wx, wy] using congrArg Subtype.val hxy
            have hp : wx.1.1 = wy.1.1 := (sym2_inr_inl_eq_inr_inl hval).1
            exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
              (by simpa [hp] using wx.2.1) wy.2.1
  have hcard := Nat.card_le_card_of_injective charge hcharge
  have htouchCard : Nat.card {X : (PendantPairGraph K).ConnectedComponent // X ∈ touch} =
      touch.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  have hcod : Nat.card
      {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K} =
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [Nat.card_sum, htouchCard, hcod] at hcard
  simpa [touch] using hcard

lemma coreFreeComponent_card_add_touchingComponent_card {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} :
    (CoreFreeComponentFinset K root).card + (CoreTouchingComponentFinset K root).card =
      Nat.card (PendantPairGraph K).ConnectedComponent := by
  classical
  rw [Nat.card_eq_fintype_card]
  simp [CoreFreeComponentFinset, CoreTouchingComponentFinset, PendantComponentCoreTouching,
    Finset.card_filter_add_card_filter_not]

/-- Core-free pendant-pair components containing a pendant with a specified root. -/
noncomputable def CoreFreeComponentsAtRootFinset {C P : Type} [Fintype P]
    (K : SimpleGraph (C ⊕ P)) (root : P → C) (c : C) :
    Finset (PendantPairGraph K).ConnectedComponent := by
  classical
  exact (CoreFreeComponentFinset K root).filter fun X => ∃ p : P, p ∈ X.supp ∧ root p = c

@[simp] lemma mem_coreFreeComponentsAtRootFinset {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} {c : C}
    {X : (PendantPairGraph K).ConnectedComponent} :
    X ∈ CoreFreeComponentsAtRootFinset K root c ↔
      PendantComponentCoreFree K root X ∧ ∃ p : P, p ∈ X.supp ∧ root p = c := by
  classical
  simp [CoreFreeComponentsAtRootFinset]

noncomputable def coreFreeComponentAtRootWitness {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} {c : C}
    (X : {X : (PendantPairGraph K).ConnectedComponent //
      X ∈ CoreFreeComponentsAtRootFinset K root c}) :
    {p : P // p ∈ X.1.supp ∧ root p = c} := by
  classical
  have hx : ∃ p : P, p ∈ X.1.supp ∧ root p = c :=
    (mem_coreFreeComponentsAtRootFinset (K := K) (root := root) (c := c)).mp X.2 |>.2
  let p : P := Classical.choose hx
  exact ⟨p, Classical.choose_spec hx⟩

lemma coreFreeComponentsAtRoot_card_le_rootFiber {C P : Type} [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} (c : C) :
    (CoreFreeComponentsAtRootFinset K root c).card ≤ Nat.card {p : P // root p = c} := by
  classical
  let A := CoreFreeComponentsAtRootFinset K root c
  let f : {X : (PendantPairGraph K).ConnectedComponent // X ∈ A} → {p : P // root p = c} :=
    fun X =>
      let w := coreFreeComponentAtRootWitness (K := K) (root := root) (c := c) X
      ⟨w.1, w.2.2⟩
  have hf : Function.Injective f := by
    intro X Y hXY
    apply Subtype.ext
    let wx := coreFreeComponentAtRootWitness (K := K) (root := root) (c := c) X
    let wy := coreFreeComponentAtRootWitness (K := K) (root := root) (c := c) Y
    have hp : wx.1 = wy.1 := by
      simpa [f, wx, wy] using congrArg Subtype.val hXY
    exact SimpleGraph.ConnectedComponent.eq_of_common_vertex
      (by simpa [hp] using wx.2.1) wy.2.1
  have hcard := Nat.card_le_card_of_injective f hf
  have hA : Nat.card {X : (PendantPairGraph K).ConnectedComponent // X ∈ A} = A.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact le_of_eq_of_le hA.symm hcard

lemma coreFreeComponent_card_le_sum_roots {C P : Type} [Fintype C] [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} :
    (CoreFreeComponentFinset K root).card ≤
      ∑ c : C, (CoreFreeComponentsAtRootFinset K root c).card := by
  classical
  let free := CoreFreeComponentFinset K root
  let atRoot := fun c : C => CoreFreeComponentsAtRootFinset K root c
  have hsubset : free ⊆ Finset.univ.biUnion atRoot := by
    intro X hX
    rcases X.nonempty_supp with ⟨p, hp⟩
    have hXfree : PendantComponentCoreFree K root X := by simpa [free] using hX
    have hXat : X ∈ atRoot (root p) := by
      simpa [atRoot] using ⟨hXfree, p, hp, rfl⟩
    exact Finset.mem_biUnion.mpr ⟨root p, by simp, hXat⟩
  calc
    free.card ≤ (Finset.univ.biUnion atRoot).card := Finset.card_le_card hsubset
    _ ≤ ∑ c ∈ (Finset.univ : Finset C), (atRoot c).card := Finset.card_biUnion_le
    _ = ∑ c : C, (CoreFreeComponentsAtRootFinset K root c).card := by simp [atRoot]

/-- Ordered pairs of distinct core-free components are controlled by same-root collisions and close
ordered root pairs.  This is the finite combinatorial core of Lemma 3. -/
lemma coreFreeComponent_offDiag_card_le_root_close {C P : Type} [Fintype C] [Fintype P]
    {K : SimpleGraph (C ⊕ P)} {root : P → C} {S : ℕ}
    (hKdiam : K.ediam ≤ (4 : ℕ∞))
    (hS : ∀ c : C, (CoreFreeComponentsAtRootFinset K root c).card ≤ S) :
    ((CoreFreeComponentFinset K root).offDiag).card ≤
      Fintype.card C * S * S + 2 * (CoreClosePairFinset K).card * S * S := by
  classical
  let free := CoreFreeComponentFinset K root
  let atRoot := fun c : C => CoreFreeComponentsAtRootFinset K root c
  let samePairs : Finset ((PendantPairGraph K).ConnectedComponent ×
      (PendantPairGraph K).ConnectedComponent) :=
    (Finset.univ : Finset C).biUnion fun c => (atRoot c).product (atRoot c)
  let closePairs : Finset ((PendantPairGraph K).ConnectedComponent ×
      (PendantPairGraph K).ConnectedComponent) :=
    (CoreCloseOrderedPairFinset K).biUnion fun ab => (atRoot ab.1).product (atRoot ab.2)
  have hsubset : free.offDiag ⊆ samePairs ∪ closePairs := by
    intro XY hXY
    rcases (Finset.mem_offDiag.mp hXY) with ⟨hXfree_mem, hYfree_mem, hXYne⟩
    have hXfree : PendantComponentCoreFree K root XY.1 := by simpa [free] using hXfree_mem
    have hYfree : PendantComponentCoreFree K root XY.2 := by simpa [free] using hYfree_mem
    rcases coreFree_components_exists_coreClose_of_ediam_le_four
        (K := K) (root := root) hKdiam hXfree hYfree hXYne with
      ⟨u, huX, v, hvY, hclose⟩
    have hXat : XY.1 ∈ atRoot (root u) := by
      exact (mem_coreFreeComponentsAtRootFinset (K := K) (root := root) (c := root u)).mpr
        ⟨hXfree, u, huX, rfl⟩
    by_cases hroot : root u = root v
    · have hYat : XY.2 ∈ atRoot (root u) := by
        exact (mem_coreFreeComponentsAtRootFinset (K := K) (root := root) (c := root u)).mpr
          ⟨hYfree, v, hvY, hroot.symm⟩
      apply Finset.mem_union.mpr
      left
      change XY ∈ (Finset.univ : Finset C).biUnion fun c => (atRoot c).product (atRoot c)
      apply Finset.mem_biUnion.mpr
      refine ⟨root u, by simp, ?_⟩
      exact Finset.mem_product.mpr ⟨hXat, hYat⟩
    · have hYat : XY.2 ∈ atRoot (root v) := by
        exact (mem_coreFreeComponentsAtRootFinset (K := K) (root := root) (c := root v)).mpr
          ⟨hYfree, v, hvY, rfl⟩
      have hordered : (root u, root v) ∈ CoreCloseOrderedPairFinset K := by
        exact (mem_coreCloseOrderedPairFinset (K := K)).mpr
          ⟨hroot, (mem_coreClosePairFinset_mk (K := K)).mpr ⟨hroot, hclose⟩⟩
      apply Finset.mem_union.mpr
      right
      change XY ∈ (CoreCloseOrderedPairFinset K).biUnion fun ab => (atRoot ab.1).product (atRoot ab.2)
      apply Finset.mem_biUnion.mpr
      refine ⟨(root u, root v), hordered, ?_⟩
      exact Finset.mem_product.mpr ⟨hXat, hYat⟩
  have hpairCard : free.offDiag.card ≤ samePairs.card + closePairs.card := by
    exact (Finset.card_le_card hsubset).trans (Finset.card_union_le samePairs closePairs)
  have hsameCard : samePairs.card ≤ ∑ c : C, (atRoot c).card * (atRoot c).card := by
    calc
      samePairs.card ≤ ∑ c ∈ (Finset.univ : Finset C), ((atRoot c).product (atRoot c)).card := by
        simpa [samePairs] using
          (Finset.card_biUnion_le (s := (Finset.univ : Finset C))
            (t := fun c : C => (atRoot c).product (atRoot c)))
      _ = ∑ c : C, (atRoot c).card * (atRoot c).card := by
        simp [Finset.card_product]
  have hsameBound : samePairs.card ≤ Fintype.card C * S * S := by
    calc
      samePairs.card ≤ ∑ c : C, (atRoot c).card * (atRoot c).card := hsameCard
      _ ≤ ∑ _c : C, S * S := by
        refine Finset.sum_le_sum ?_
        intro c _
        exact Nat.mul_le_mul (hS c) (hS c)
      _ = Fintype.card C * S * S := by
        simp [Nat.mul_assoc]
  have hcloseCard : closePairs.card ≤
      ∑ ab ∈ CoreCloseOrderedPairFinset K, (atRoot ab.1).card * (atRoot ab.2).card := by
    calc
      closePairs.card ≤
          ∑ ab ∈ CoreCloseOrderedPairFinset K, ((atRoot ab.1).product (atRoot ab.2)).card := by
        simpa [closePairs] using
          (Finset.card_biUnion_le (s := CoreCloseOrderedPairFinset K)
            (t := fun ab : C × C => (atRoot ab.1).product (atRoot ab.2)))
      _ = ∑ ab ∈ CoreCloseOrderedPairFinset K, (atRoot ab.1).card * (atRoot ab.2).card := by
        simp [Finset.card_product]
  have hcloseBound : closePairs.card ≤ 2 * (CoreClosePairFinset K).card * S * S := by
    calc
      closePairs.card ≤
          ∑ ab ∈ CoreCloseOrderedPairFinset K, (atRoot ab.1).card * (atRoot ab.2).card := hcloseCard
      _ ≤ ∑ _ab ∈ CoreCloseOrderedPairFinset K, S * S := by
        refine Finset.sum_le_sum ?_
        intro ab _
        exact Nat.mul_le_mul (hS ab.1) (hS ab.2)
      _ = (CoreCloseOrderedPairFinset K).card * (S * S) := by simp [Finset.sum_const]
      _ ≤ (2 * (CoreClosePairFinset K).card) * (S * S) := by
        exact Nat.mul_le_mul_right (S * S) (coreCloseOrderedPair_card_le_two_mul (K := K))
      _ = 2 * (CoreClosePairFinset K).card * S * S := by ring
  exact hpairCard.trans (Nat.add_le_add hsameBound hcloseBound)

lemma pendant_component_accounting {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    Nat.card P - (CoreFreeComponentFinset K root).card ≤
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  let F : SimpleGraph P := PendantPairGraph K
  let free := CoreFreeComponentFinset K root
  let touch := CoreTouchingComponentFinset K root
  have hvertices : Nat.card P ≤ Nat.card F.edgeSet + Nat.card F.ConnectedComponent :=
    card_vertex_le_edgeSet_add_connectedComponents F
  have hcomponents : free.card + touch.card = Nat.card F.ConnectedComponent := by
    simpa [F, free, touch] using
      (coreFreeComponent_card_add_touchingComponent_card (K := K) (root := root))
  have hcharge : Nat.card F.edgeSet + touch.card ≤
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
    simpa [F, touch] using
      (pendantPair_edges_add_touchingComponents_le_addedEdgeFinset (H := H) (root := root) (K := K))
  have hmid : Nat.card P - free.card ≤ Nat.card F.edgeSet + touch.card := by
    omega
  exact hmid.trans hcharge

lemma pendantPair_edgeSet_card_le_addedEdgeFinset {C P : Type} [Fintype C] [Fintype P]
    {H : SimpleGraph C} {root : P → C} {K : SimpleGraph (C ⊕ P)} :
    Nat.card (PendantPairGraph K).edgeSet ≤
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
  classical
  let pinr : P ↪ C ⊕ P := Function.Embedding.inr
  let f : (PendantPairGraph K).edgeSet →
      {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K} := fun e =>
    ⟨pinr.sym2Map e.1, by
      refine Sym2.ind ?_ e.1 e.2
      intro p q hpq
      have hpq' : K.Adj (Sum.inr p) (Sum.inr q) := by
        simpa [SimpleGraph.mem_edgeSet] using hpq
      simp [pinr, mem_addedEdgeFinset, Function.Embedding.sym2Map_apply, Sym2.map_mk, hpq']⟩
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    apply Subtype.ext
    have hval : pinr.sym2Map e₁.1 = pinr.sym2Map e₂.1 := by
      simpa [f] using congrArg Subtype.val h
    exact pinr.sym2Map.injective hval
  have hcard := Nat.card_le_card_of_injective f hf
  have hcod : Nat.card
      {e : Sym2 (C ⊕ P) // e ∈ AddedEdgeFinset (PendantCoreGraphSum H root) K} =
      (AddedEdgeFinset (PendantCoreGraphSum H root) K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [hcod] at hcard
  exact hcard

/-- The explicit hub supergraph used only to show that the feasible set in `IsHR` is nonempty.
It adds a star from one chosen pendant `hub` to every pendant over a different root. -/
def PendantHubSupergraphSum {C P : Type} (H : SimpleGraph C) (root : P → C) (hub : P) :
    SimpleGraph (C ⊕ P) where
  Adj x y :=
    (PendantCoreGraphSum H root).Adj x y ∨
      ∃ p : P, root p ≠ root hub ∧
        ((x = Sum.inr hub ∧ y = Sum.inr p) ∨ (x = Sum.inr p ∧ y = Sum.inr hub))
  symm := by
    constructor
    intro x y h
    rcases h with hbase | ⟨p, hp, hnew⟩
    · exact Or.inl hbase.symm
    · rcases hnew with ⟨hxhub, hyp⟩ | ⟨hxp, hyhub⟩
      · exact Or.inr ⟨p, hp, Or.inr ⟨hyp, hxhub⟩⟩
      · exact Or.inr ⟨p, hp, Or.inl ⟨hyhub, hxp⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with hbase | ⟨p, hp, hnew⟩
    · exact (PendantCoreGraphSum H root).irrefl hbase
    · rcases hnew with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · have : p = hub := by simpa using h₂.symm.trans h₁
        exact hp (by rw [this])
      · have : p = hub := by simpa using h₁.symm.trans h₂
        exact hp (by rw [this])⟩

lemma pendantCoreGraphSum_le_hubSupergraph {C P : Type} (H : SimpleGraph C) (root : P → C)
    (hub : P) :
    PendantCoreGraphSum H root ≤ PendantHubSupergraphSum H root hub := by
  intro x y hxy
  exact Or.inl hxy

@[simp] lemma pendantHubSupergraphSum_adj_core_core {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub : P} {a b : C} :
    (PendantHubSupergraphSum H root hub).Adj (Sum.inl a) (Sum.inl b) ↔ H.Adj a b := by
  constructor
  · intro h
    rcases h with hbase | ⟨p, hp, hnew⟩
    · exact hbase
    · rcases hnew with ⟨h₁, _⟩ | ⟨h₁, _⟩ <;> cases h₁
  · intro h
    exact Or.inl h

@[simp] lemma pendantHubSupergraphSum_adj_hub_pendant {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub p : P} (hp : root p ≠ root hub) :
    (PendantHubSupergraphSum H root hub).Adj (Sum.inr hub) (Sum.inr p) := by
  exact Or.inr ⟨p, hp, Or.inl ⟨rfl, rfl⟩⟩

@[simp] lemma pendantHubSupergraphSum_adj_core_pendant {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub : P} {a : C} {p : P} :
    (PendantHubSupergraphSum H root hub).Adj (Sum.inl a) (Sum.inr p) ↔ root p = a := by
  constructor
  · intro h
    rcases h with hbase | ⟨q, _, hnew⟩
    · exact hbase.symm
    · rcases hnew with ⟨hcore, _⟩ | ⟨hcore, _⟩ <;> cases hcore
  · intro h
    exact Or.inl (by simpa [eq_comm] using h)

@[simp] lemma pendantHubSupergraphSum_adj_pendant_core {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub : P} {p : P} {a : C} :
    (PendantHubSupergraphSum H root hub).Adj (Sum.inr p) (Sum.inl a) ↔ root p = a := by
  rw [adj_comm, pendantHubSupergraphSum_adj_core_pendant]

@[simp] lemma pendantHubSupergraphSum_adj_pendant_pendant {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub p q : P} :
    (PendantHubSupergraphSum H root hub).Adj (Sum.inr p) (Sum.inr q) ↔
      (p = hub ∧ root q ≠ root hub) ∨ (q = hub ∧ root p ≠ root hub) := by
  constructor
  · intro h
    rcases h with hbase | ⟨r, hr, hnew⟩
    · exact False.elim hbase
    · rcases hnew with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · left
        refine ⟨?_, ?_⟩
        · simpa using hp
        · have hqr : q = r := by simpa using hq
          simpa [hqr] using hr
      · right
        refine ⟨?_, ?_⟩
        · simpa using hq
        · have hpr : p = r := by simpa using hp
          simpa [hpr] using hr
  · intro h
    rcases h with ⟨hp, hqroot⟩ | ⟨hq, hproot⟩
    · subst p
      exact Or.inr ⟨q, hqroot, Or.inl ⟨rfl, rfl⟩⟩
    · subst q
      exact Or.inr ⟨p, hproot, Or.inr ⟨rfl, rfl⟩⟩

lemma pendantHubSupergraphSum_walk_to_hub_le_two {C P : Type} (H : SimpleGraph C)
    (root : P → C) (hub : P)
    (hcover : ∀ c : C, c ≠ root hub → ∃ p : P, root p = c) :
    ∀ x : C ⊕ P, ∃ p : (PendantHubSupergraphSum H root hub).Walk x (Sum.inr hub),
      p.length ≤ 2 := by
  intro x
  cases x with
  | inl a =>
      by_cases ha : a = root hub
      · have hbase : (PendantHubSupergraphSum H root hub).Adj (Sum.inl a) (Sum.inr hub) := by
          exact Or.inl (by simp [ha])
        exact ⟨hbase.toWalk, by simp⟩
      · rcases hcover a ha with ⟨p, hp⟩
        have hbase : (PendantHubSupergraphSum H root hub).Adj (Sum.inl a) (Sum.inr p) := by
          exact Or.inl (by simp [hp])
        have hp_ne : root p ≠ root hub := by
          intro h
          exact ha (hp.symm.trans h)
        have hnew : (PendantHubSupergraphSum H root hub).Adj (Sum.inr p) (Sum.inr hub) := by
          exact Or.inr ⟨p, hp_ne, Or.inr ⟨rfl, rfl⟩⟩
        exact ⟨Walk.cons hbase hnew.toWalk, by simp⟩
  | inr p =>
      by_cases hp : root p = root hub
      · have hbase₁ : (PendantHubSupergraphSum H root hub).Adj
            (Sum.inr p) (Sum.inl (root p)) := by
          exact Or.inl (by simp)
        have hbase₂ : (PendantHubSupergraphSum H root hub).Adj
            (Sum.inl (root p)) (Sum.inr hub) := by
          exact Or.inl (by simp [hp])
        exact ⟨Walk.cons hbase₁ hbase₂.toWalk, by simp⟩
      · have hnew : (PendantHubSupergraphSum H root hub).Adj (Sum.inr p) (Sum.inr hub) := by
          exact Or.inr ⟨p, hp, Or.inr ⟨rfl, rfl⟩⟩
        exact ⟨hnew.toWalk, by simp⟩

lemma pendantHubSupergraphSum_walk_le_four {C P : Type} (H : SimpleGraph C)
    (root : P → C) (hub : P)
    (hcover : ∀ c : C, c ≠ root hub → ∃ p : P, root p = c) :
    ∀ x y : C ⊕ P, ∃ p : (PendantHubSupergraphSum H root hub).Walk x y,
      p.length ≤ 4 := by
  intro x y
  rcases pendantHubSupergraphSum_walk_to_hub_le_two H root hub hcover x with ⟨px, hpx⟩
  rcases pendantHubSupergraphSum_walk_to_hub_le_two H root hub hcover y with ⟨py, hpy⟩
  refine ⟨px.append py.reverse, ?_⟩
  rw [Walk.length_append, Walk.length_reverse]
  simpa using Nat.add_le_add hpx hpy

lemma pendantHubSupergraphSum_ediam_le_four {C P : Type} (H : SimpleGraph C)
    (root : P → C) (hub : P)
    (hcover : ∀ c : C, c ≠ root hub → ∃ p : P, root p = c) :
    (PendantHubSupergraphSum H root hub).ediam ≤ (4 : ℕ∞) := by
  apply ediam_le_of_forall_exists_walk_le
  intro x y
  rcases pendantHubSupergraphSum_walk_to_hub_le_two H root hub hcover x with ⟨px, hpx⟩
  rcases pendantHubSupergraphSum_walk_to_hub_le_two H root hub hcover y with ⟨py, hpy⟩
  refine ⟨px.append py.reverse, ?_⟩
  rw [Walk.length_append, Walk.length_reverse]
  simpa using Nat.add_le_add hpx hpy

/-- In a complete-graph embedding into a pendant-core graph, if one source vertex lands on a
pendant, every other source vertex lands on that pendant's root. -/
theorem embedding_eq_root_of_maps_to_pendant {C P : Type} {H : SimpleGraph C} {root : P → C}
    {k : ℕ} (f : completeGraph (Fin k) ↪g PendantCoreGraphSum H root)
    {i : Fin k} {p : P} (hi : f i = Sum.inr p) {j : Fin k} (hij : j ≠ i) :
    f j = Sum.inl (root p) := by
  have hadjSrc : (completeGraph (Fin k)).Adj i j := by simpa [top_adj] using hij.symm
  have hadj : (PendantCoreGraphSum H root).Adj (f i) (f j) :=
    (RelEmbedding.map_rel_iff f).2 hadjSrc
  rw [hi] at hadj
  exact pendantCoreGraphSum_adj_pendant_iff.mp hadj

/-- No embedding of a triangle into a pendant-core graph can send any source vertex to a pendant. -/
theorem not_exists_triangle_embedding_maps_to_pendant {C P : Type} {H : SimpleGraph C} {root : P → C}
    (f : completeGraph (Fin 3) ↪g PendantCoreGraphSum H root) :
    ¬ ∃ (i : Fin 3) (p : P), f i = Sum.inr p := by
  rintro ⟨i, p, hi⟩
  fin_cases i
  · have h1 := embedding_eq_root_of_maps_to_pendant f hi (j := (1 : Fin 3)) (by decide)
    have h2 := embedding_eq_root_of_maps_to_pendant f hi (j := (2 : Fin 3)) (by decide)
    have heq : f (1 : Fin 3) = f (2 : Fin 3) := h1.trans h2.symm
    exact (by decide : (1 : Fin 3) ≠ 2) (RelEmbedding.injective f heq)
  · have h0 := embedding_eq_root_of_maps_to_pendant f hi (j := (0 : Fin 3)) (by decide)
    have h2 := embedding_eq_root_of_maps_to_pendant f hi (j := (2 : Fin 3)) (by decide)
    have heq : f (0 : Fin 3) = f (2 : Fin 3) := h0.trans h2.symm
    exact (by decide : (0 : Fin 3) ≠ 2) (RelEmbedding.injective f heq)
  · have h0 := embedding_eq_root_of_maps_to_pendant f hi (j := (0 : Fin 3)) (by decide)
    have h1 := embedding_eq_root_of_maps_to_pendant f hi (j := (1 : Fin 3)) (by decide)
    have heq : f (0 : Fin 3) = f (1 : Fin 3) := h0.trans h1.symm
    exact (by decide : (0 : Fin 3) ≠ 1) (RelEmbedding.injective f heq)

/-- If a triangle embedding into a pendant-core graph uses no pendant vertices, it induces a triangle
embedding into the core. -/
theorem false_of_triangle_embedding_all_core {C P : Type} {H : SimpleGraph C} {root : P → C}
    (hH : H.CliqueFree 3)
    (f : completeGraph (Fin 3) ↪g PendantCoreGraphSum H root)
    (hno : ¬ ∃ (i : Fin 3) (p : P), f i = Sum.inr p) : False := by
  obtain ⟨c0, h0⟩ : ∃ c : C, f (0 : Fin 3) = Sum.inl c := by
    cases h : f (0 : Fin 3) with
    | inl c => exact ⟨c, rfl⟩
    | inr p => exact False.elim (hno ⟨0, p, h⟩)
  obtain ⟨c1, h1⟩ : ∃ c : C, f (1 : Fin 3) = Sum.inl c := by
    cases h : f (1 : Fin 3) with
    | inl c => exact ⟨c, rfl⟩
    | inr p => exact False.elim (hno ⟨1, p, h⟩)
  obtain ⟨c2, h2⟩ : ∃ c : C, f (2 : Fin 3) = Sum.inl c := by
    cases h : f (2 : Fin 3) with
    | inl c => exact ⟨c, rfl⟩
    | inr p => exact False.elim (hno ⟨2, p, h⟩)
  have h01 : H.Adj c0 c1 := by
    have hs : (completeGraph (Fin 3)).Adj (0 : Fin 3) 1 := by simp [top_adj]
    have ht := (RelEmbedding.map_rel_iff f).2 hs
    simpa [h0, h1] using ht
  have h02 : H.Adj c0 c2 := by
    have hs : (completeGraph (Fin 3)).Adj (0 : Fin 3) 2 := by simp [top_adj]
    have ht := (RelEmbedding.map_rel_iff f).2 hs
    simpa [h0, h2] using ht
  have h12 : H.Adj c1 c2 := by
    have hs : (completeGraph (Fin 3)).Adj (1 : Fin 3) 2 := by simp [top_adj]
    have ht := (RelEmbedding.map_rel_iff f).2 hs
    simpa [h1, h2] using ht
  have hc01 : c0 ≠ c1 := by
    intro hc
    apply (by decide : (0 : Fin 3) ≠ 1)
    apply RelEmbedding.injective f
    rw [h0, h1, hc]
  have hc02 : c0 ≠ c2 := by
    intro hc
    apply (by decide : (0 : Fin 3) ≠ 2)
    apply RelEmbedding.injective f
    rw [h0, h2, hc]
  have hc12 : c1 ≠ c2 := by
    intro hc
    apply (by decide : (1 : Fin 3) ≠ 2)
    apply RelEmbedding.injective f
    rw [h1, h2, hc]
  let g : Fin 3 → C := fun i =>
    match i with
    | 0 => c0
    | 1 => c1
    | 2 => c2
  have ginj : Function.Injective g := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [g] at hab ⊢
    · exact False.elim (hc01 hab)
    · exact False.elim (hc02 hab)
    · exact False.elim (hc01 hab.symm)
    · exact False.elim (hc12 hab)
    · exact False.elim (hc02 hab.symm)
    · exact False.elim (hc12 hab.symm)
  let emb : completeGraph (Fin 3) ↪g H :=
    { toEmbedding := ⟨g, ginj⟩
      map_rel_iff' := by
        intro a b
        constructor
        · intro hab
          have hne : a ≠ b := by
            intro heq
            subst b
            exact H.irrefl hab
          simpa [top_adj] using hne
        · intro hab
          fin_cases a <;> fin_cases b <;> simp [g, top_adj] at hab ⊢
          · exact h01
          · exact h02
          · exact h01.symm
          · exact h12
          · exact h02.symm
          · exact h12.symm }
  exact (SimpleGraph.cliqueFree_iff.mp hH).false emb.toCopy

/-- Attaching pendant leaves to a triangle-free core preserves triangle-freeness. -/
theorem pendantCoreGraphSum_cliqueFree_three {C P : Type} {H : SimpleGraph C} {root : P → C}
    (hH : H.CliqueFree 3) : (PendantCoreGraphSum H root).CliqueFree 3 := by
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  by_cases hpend : ∃ (i : Fin 3) (p : P), f i = Sum.inr p
  · exact not_exists_triangle_embedding_maps_to_pendant f hpend
  · exact false_of_triangle_embedding_all_core hH f hpend

lemma false_of_three_core_adj_of_cliqueFree_three {C : Type} {H : SimpleGraph C}
    (hH : H.CliqueFree 3) {a b c : C}
    (hab : H.Adj a b) (hac : H.Adj a c) (hbc : H.Adj b c)
    (hab_ne : a ≠ b) (hac_ne : a ≠ c) (hbc_ne : b ≠ c) : False := by
  let g : Fin 3 → C := fun i =>
    match i with
    | 0 => a
    | 1 => b
    | 2 => c
  have ginj : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [g] at hij ⊢
    · exact False.elim (hab_ne hij)
    · exact False.elim (hac_ne hij)
    · exact False.elim (hab_ne hij.symm)
    · exact False.elim (hbc_ne hij)
    · exact False.elim (hac_ne hij.symm)
    · exact False.elim (hbc_ne hij.symm)
  let emb : completeGraph (Fin 3) ↪g H :=
    { toEmbedding := ⟨g, ginj⟩
      map_rel_iff' := by
        intro i j
        constructor
        · intro hij
          have hne : i ≠ j := by
            intro heq
            subst j
            exact H.irrefl hij
          simpa [top_adj] using hne
        · intro hij
          fin_cases i <;> fin_cases j <;> simp [g, top_adj] at hij ⊢
          · exact hab
          · exact hac
          · exact hab.symm
          · exact hbc
          · exact hac.symm
          · exact hbc.symm }
  exact (SimpleGraph.cliqueFree_iff.mp hH).false emb.toCopy

/-- The hub supergraph used for feasibility is triangle-free when the core is triangle-free. -/
theorem pendantHubSupergraphSum_cliqueFree_three {C P : Type} {H : SimpleGraph C}
    {root : P → C} {hub : P} (hH : H.CliqueFree 3) :
    (PendantHubSupergraphSum H root hub).CliqueFree 3 := by
  by_contra h
  let f := SimpleGraph.topEmbeddingOfNotCliqueFree h
  have h01 : (PendantHubSupergraphSum H root hub).Adj (f (0 : Fin 3)) (f 1) := by
    exact (RelEmbedding.map_rel_iff f).2 (by simp [top_adj])
  have h02 : (PendantHubSupergraphSum H root hub).Adj (f (0 : Fin 3)) (f 2) := by
    exact (RelEmbedding.map_rel_iff f).2 (by simp [top_adj])
  have h12 : (PendantHubSupergraphSum H root hub).Adj (f (1 : Fin 3)) (f 2) := by
    exact (RelEmbedding.map_rel_iff f).2 (by simp [top_adj])
  have hne01 : f (0 : Fin 3) ≠ f 1 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 1) (RelEmbedding.injective f h)
  have hne02 : f (0 : Fin 3) ≠ f 2 := by
    intro h
    exact (by decide : (0 : Fin 3) ≠ 2) (RelEmbedding.injective f h)
  have hne12 : f (1 : Fin 3) ≠ f 2 := by
    intro h
    exact (by decide : (1 : Fin 3) ≠ 2) (RelEmbedding.injective f h)
  cases h0 : f (0 : Fin 3) with
  | inl c0 =>
      cases h1 : f (1 : Fin 3) with
      | inl c1 =>
          cases h2 : f (2 : Fin 3) with
          | inl c2 =>
              have hc01 : H.Adj c0 c1 := by simpa [h0, h1] using h01
              have hc02 : H.Adj c0 c2 := by simpa [h0, h2] using h02
              have hc12 : H.Adj c1 c2 := by simpa [h1, h2] using h12
              have hnc01 : c0 ≠ c1 := by
                intro hc
                exact hne01 (by rw [h0, h1, hc])
              have hnc02 : c0 ≠ c2 := by
                intro hc
                exact hne02 (by rw [h0, h2, hc])
              have hnc12 : c1 ≠ c2 := by
                intro hc
                exact hne12 (by rw [h1, h2, hc])
              exact false_of_three_core_adj_of_cliqueFree_three hH hc01 hc02 hc12 hnc01 hnc02 hnc12
          | inr p2 =>
              have hr20 : root p2 = c0 := by simpa [h0, h2] using h02
              have hr21 : root p2 = c1 := by simpa [h1, h2] using h12
              have hnc01 : c0 ≠ c1 := by
                intro hc
                exact hne01 (by rw [h0, h1, hc])
              exact hnc01 (hr20.symm.trans hr21)
      | inr p1 =>
          cases h2 : f (2 : Fin 3) with
          | inl c2 =>
              have hr10 : root p1 = c0 := by simpa [h0, h1] using h01
              have hr12 : root p1 = c2 := by simpa [h1, h2] using h12
              have hnc02 : c0 ≠ c2 := by
                intro hc
                exact hne02 (by rw [h0, h2, hc])
              exact hnc02 (hr10.symm.trans hr12)
          | inr p2 =>
              have hr10 : root p1 = c0 := by simpa [h0, h1] using h01
              have hr20 : root p2 = c0 := by simpa [h0, h2] using h02
              have hp12 : (p1 = hub ∧ root p2 ≠ root hub) ∨
                  (p2 = hub ∧ root p1 ≠ root hub) := by
                simpa [h1, h2] using h12
              rcases hp12 with ⟨hp1, hroot⟩ | ⟨hp2, hroot⟩
              · subst p1
                exact hroot (hr20.trans hr10.symm)
              · subst p2
                exact hroot (hr10.trans hr20.symm)
  | inr p0 =>
      cases h1 : f (1 : Fin 3) with
      | inl c1 =>
          cases h2 : f (2 : Fin 3) with
          | inl c2 =>
              have hr01 : root p0 = c1 := by simpa [h0, h1] using h01
              have hr02 : root p0 = c2 := by simpa [h0, h2] using h02
              have hnc12 : c1 ≠ c2 := by
                intro hc
                exact hne12 (by rw [h1, h2, hc])
              exact hnc12 (hr01.symm.trans hr02)
          | inr p2 =>
              have hr01 : root p0 = c1 := by simpa [h0, h1] using h01
              have hr21 : root p2 = c1 := by simpa [h1, h2] using h12
              have hp02 : (p0 = hub ∧ root p2 ≠ root hub) ∨
                  (p2 = hub ∧ root p0 ≠ root hub) := by
                simpa [h0, h2] using h02
              rcases hp02 with ⟨hp0, hroot⟩ | ⟨hp2, hroot⟩
              · subst p0
                exact hroot (hr21.trans hr01.symm)
              · subst p2
                exact hroot (hr01.trans hr21.symm)
      | inr p1 =>
          cases h2 : f (2 : Fin 3) with
          | inl c2 =>
              have hr02 : root p0 = c2 := by simpa [h0, h2] using h02
              have hr12 : root p1 = c2 := by simpa [h1, h2] using h12
              have hp01 : (p0 = hub ∧ root p1 ≠ root hub) ∨
                  (p1 = hub ∧ root p0 ≠ root hub) := by
                simpa [h0, h1] using h01
              rcases hp01 with ⟨hp0, hroot⟩ | ⟨hp1, hroot⟩
              · subst p0
                exact hroot (hr12.trans hr02.symm)
              · subst p1
                exact hroot (hr02.trans hr12.symm)
          | inr p2 =>
              have hpne01 : p0 ≠ p1 := by
                intro hp
                exact hne01 (by rw [h0, h1, hp])
              have hpne02 : p0 ≠ p2 := by
                intro hp
                exact hne02 (by rw [h0, h2, hp])
              have hpne12 : p1 ≠ p2 := by
                intro hp
                exact hne12 (by rw [h1, h2, hp])
              have hp01 : (p0 = hub ∧ root p1 ≠ root hub) ∨
                  (p1 = hub ∧ root p0 ≠ root hub) := by
                simpa [h0, h1] using h01
              have hp02 : (p0 = hub ∧ root p2 ≠ root hub) ∨
                  (p2 = hub ∧ root p0 ≠ root hub) := by
                simpa [h0, h2] using h02
              have hp12 : (p1 = hub ∧ root p2 ≠ root hub) ∨
                  (p2 = hub ∧ root p1 ≠ root hub) := by
                simpa [h1, h2] using h12
              rcases hp01 with ⟨hp0, _⟩ | ⟨hp1, _⟩
              · rcases hp12 with ⟨hp1, _⟩ | ⟨hp2, _⟩
                · exact hpne01 (hp0.trans hp1.symm)
                · exact hpne02 (hp0.trans hp2.symm)
              · rcases hp02 with ⟨hp0, _⟩ | ⟨hp2, _⟩
                · exact hpne01 (hp0.trans hp1.symm)
                · exact hpne12 (hp1.trans hp2.symm)

/-- The core embeds into the sum-type pendant-core graph. -/
def pendantCoreGraphSumCoreHom {C P : Type} (H : SimpleGraph C) (root : P → C) :
    H →g PendantCoreGraphSum H root where
  toFun := Sum.inl
  map_rel' := by
    intro a b h
    exact h

/-- Adding pendant leaves to a connected core keeps the graph connected. -/
theorem pendantCoreGraphSum_connected {C P : Type} {H : SimpleGraph C} {root : P → C}
    (hH : H.Connected) : (PendantCoreGraphSum H root).Connected := by
  let : Nonempty (C ⊕ P) := hH.nonempty.map Sum.inl
  refine ⟨?_⟩
  intro x y
  cases x with
  | inl a =>
      cases y with
      | inl b => exact (hH.preconnected a b).map (pendantCoreGraphSumCoreHom H root)
      | inr q =>
          exact ((hH.preconnected a (root q)).map (pendantCoreGraphSumCoreHom H root)).trans
            (Adj.reachable (by exact rfl)).symm
  | inr p =>
      cases y with
      | inl b =>
          exact (Adj.reachable (by exact rfl)).trans
            ((hH.preconnected (root p) b).map (pendantCoreGraphSumCoreHom H root))
      | inr q =>
          exact (Adj.reachable (by exact rfl)).trans
            (((hH.preconnected (root p) (root q)).map (pendantCoreGraphSumCoreHom H root)).trans
              (Adj.reachable (by exact rfl)).symm)

/-- The pendant vertices before transport: `s` indexed leaves over every core vertex, plus `q`
extra leaves.  The extras are attached to the first `q` core vertices when `q ≤ m`. -/
abbrev PendantCorePendant (s m q : ℕ) := (Fin m × Fin s) ⊕ Fin q

/-- The finite vertex type used before transporting the pendant-core graph to `Fin n`. -/
abbrev PendantCoreVertex (s m q : ℕ) := Fin m ⊕ PendantCorePendant s m q

/-- The root of a pendant in the faithful product/sum encoding. -/
def pendantCoreRoot {s m q : ℕ} (hq : q ≤ m) : PendantCorePendant s m q → Fin m
  | Sum.inl p => p.1
  | Sum.inr j => Fin.castLE hq j

/-- Pendants with a fixed root. -/
abbrev PendantRootFiber {s m q : ℕ} (hq : q ≤ m) (c : Fin m) :=
  {p : PendantCorePendant s m q // pendantCoreRoot hq p = c}

/-- A fiber code proving that each core supports at most `s + 1` pendants. -/
def pendantRootFiberCode {s m q : ℕ} {hq : q ≤ m} {c : Fin m} :
    PendantRootFiber (s := s) hq c → Fin s ⊕ Unit
  | ⟨Sum.inl p, _⟩ => Sum.inl p.2
  | ⟨Sum.inr _, _⟩ => Sum.inr ()

lemma pendantRootFiberCode_injective {s m q : ℕ} {hq : q ≤ m} {c : Fin m} :
    Function.Injective (pendantRootFiberCode (s := s) (hq := hq) (c := c)) := by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ hcode
  cases p with
  | inl p0 =>
      cases p' with
      | inl p1 =>
          simp [pendantRootFiberCode] at hcode
          have hroot0 : p0.1 = c := by simpa [pendantCoreRoot] using hp
          have hroot1 : p1.1 = c := by simpa [pendantCoreRoot] using hp'
          apply Subtype.ext
          exact congrArg Sum.inl (Prod.ext (hroot0.trans hroot1.symm) hcode)
      | inr j =>
          simp [pendantRootFiberCode] at hcode
  | inr j =>
      cases p' with
      | inl p1 =>
          simp [pendantRootFiberCode] at hcode
      | inr j' =>
          have hj : Fin.castLE hq j = c := by simpa [pendantCoreRoot] using hp
          have hj' : Fin.castLE hq j' = c := by simpa [pendantCoreRoot] using hp'
          have hcast : Fin.castLE hq j = Fin.castLE hq j' := hj.trans hj'.symm
          have hidx : j = j' := Fin.castLE_injective hq hcast
          apply Subtype.ext
          simp [hidx]

lemma pendantRootFiber_card_le {s m q : ℕ} (hq : q ≤ m) (c : Fin m) :
    Fintype.card (PendantRootFiber (s := s) hq c) ≤ s + 1 := by
  calc
    Fintype.card (PendantRootFiber (s := s) hq c) ≤ Fintype.card (Fin s ⊕ Unit) :=
      Fintype.card_le_of_injective
        (pendantRootFiberCode (s := s) (hq := hq) (c := c))
        (pendantRootFiberCode_injective (s := s) (hq := hq) (c := c))
    _ = s + 1 := by simp

lemma coreFreeComponentsAtRoot_card_le_typed {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)} (c : Fin m) :
    (CoreFreeComponentsAtRootFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq) c).card ≤
      s + 1 := by
  have h := coreFreeComponentsAtRoot_card_le_rootFiber
    (K := K) (root := pendantCoreRoot (s := s) (m := m) (q := q) hq) c
  have hfiber : Nat.card (PendantRootFiber (s := s) hq c) =
      Fintype.card (PendantRootFiber (s := s) hq c) := by
    rw [Nat.card_eq_fintype_card]
  exact h.trans (by simpa [PendantRootFiber, hfiber] using pendantRootFiber_card_le hq c)

lemma coreFreeComponent_card_le_typed_root_bound {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)} :
    (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card ≤
      m * (s + 1) := by
  calc
    (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card
        ≤ ∑ c : Fin m,
          (CoreFreeComponentsAtRootFinset K
            (pendantCoreRoot (s := s) (m := m) (q := q) hq) c).card :=
      coreFreeComponent_card_le_sum_roots
    _ ≤ ∑ _c : Fin m, (s + 1) := by
      exact Finset.sum_le_sum fun c _ => coreFreeComponentsAtRoot_card_le_typed (K := K) hq c
    _ = m * (s + 1) := by simp [Fintype.card_fin]

lemma pendantCorePendant_nat_card (s m q : ℕ) :
    Nat.card (PendantCorePendant s m q) = m * s + q := by
  rw [Nat.card_eq_fintype_card]
  dsimp [PendantCorePendant]
  simp [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]

lemma real_sub_le_of_nat_sub_le {a b c : ℕ} {x y : ℝ}
    (hx : x ≤ (a : ℝ)) (hy : (b : ℝ) ≤ y) (h : a - b ≤ c) :
    x - y ≤ (c : ℝ) := by
  by_cases hba : b ≤ a
  · have hc : (a : ℝ) - (b : ℝ) ≤ (c : ℝ) := by
      have hcast : ((a - b : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast h
      rwa [Nat.cast_sub hba] at hcast
    nlinarith
  · have hab : (a : ℝ) < (b : ℝ) := by exact_mod_cast Nat.lt_of_not_ge hba
    have hxy : x - y ≤ 0 := by nlinarith
    have hc0 : 0 ≤ (c : ℝ) := by positivity
    linarith

lemma coreFreeComponent_offDiag_card_le_typed {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)}
    (hKdiam : K.ediam ≤ (4 : ℕ∞)) :
    ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).offDiag).card ≤
      m * (s + 1) * (s + 1) + 2 * (CoreClosePairFinset K).card * (s + 1) * (s + 1) := by
  classical
  have h := coreFreeComponent_offDiag_card_le_root_close
    (C := Fin m) (P := PendantCorePendant s m q) (K := K)
    (root := pendantCoreRoot (s := s) (m := m) (q := q) hq) (S := s + 1)
    hKdiam (fun c => coreFreeComponentsAtRoot_card_le_typed (s := s) (m := m) (q := q)
      (K := K) hq c)
  simpa [Fintype.card_fin, Nat.mul_assoc] using h

lemma coreFreeComponent_sq_sub_card_le_typed {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)}
    (hKdiam : K.ediam ≤ (4 : ℕ∞)) :
    (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card *
        (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card -
      (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card ≤
        m * (s + 1) * (s + 1) + 2 * (CoreClosePairFinset K).card * (s + 1) * (s + 1) := by
  simpa [Finset.offDiag_card] using coreFreeComponent_offDiag_card_le_typed (s := s) (m := m)
    (q := q) (K := K) hq hKdiam

lemma nat_le_mul_self (n : ℕ) : n ≤ n * n := by
  cases n with
  | zero => simp
  | succ n => exact Nat.le_mul_of_pos_right _ (Nat.succ_pos n)

lemma coreFreeComponent_sq_sub_real_le_typed {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)}
    (hKdiam : K.ediam ≤ (4 : ℕ∞)) :
    let N := (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card
    (N : ℝ) * (N : ℝ) - (N : ℝ) ≤
      (m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
        2 * ((CoreClosePairFinset K).card : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) := by
  intro N
  have hnat := coreFreeComponent_sq_sub_card_le_typed (s := s) (m := m) (q := q)
    (K := K) hq hKdiam
  have hcast : (((N * N - N : ℕ) : ℝ)) ≤
      (m * (s + 1) * (s + 1) + 2 * (CoreClosePairFinset K).card * (s + 1) * (s + 1) : ℕ) := by
    exact_mod_cast hnat
  have hle : N ≤ N * N := nat_le_mul_self N
  rw [Nat.cast_sub hle] at hcast
  norm_num at hcast ⊢
  nlinarith

lemma real_le_one_add_sqrt_of_sq_sub_le {x B : ℝ}
    (h : x * x - x ≤ B) :
    x ≤ 1 + Real.sqrt B := by
  by_cases hx1 : x ≤ 1
  · have hs : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
    linarith
  · have hxge : 1 ≤ x := le_of_not_ge hx1
    have hsq : (x - 1) ^ 2 ≤ B := by nlinarith
    have hs : x - 1 ≤ Real.sqrt B := Real.le_sqrt_of_sq_le hsq
    linarith

lemma coreFreeComponent_card_real_le_one_add_sqrt_of_close_bound {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)} {B : ℝ}
    (hKdiam : K.ediam ≤ (4 : ℕ∞))
    (hclose : ((CoreClosePairFinset K).card : ℝ) ≤ B) :
    let N := (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card
    (N : ℝ) ≤
      1 + Real.sqrt
        ((m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
          2 * B * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) := by
  intro N
  have hquad := coreFreeComponent_sq_sub_real_le_typed (s := s) (m := m) (q := q)
    (K := K) hq hKdiam
  have hroot := real_le_one_add_sqrt_of_sq_sub_le (x := (N : ℝ)) hquad
  refine hroot.trans ?_
  have hsqrt :
      Real.sqrt
          ((m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
            2 * ((CoreClosePairFinset K).card : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) ≤
        Real.sqrt
          ((m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
            2 * B * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) := by
    apply Real.sqrt_le_sqrt
    have hSsq : 0 ≤ ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  linarith

lemma coreFreeComponent_card_real_le_one_add_of_close_bound_sq {s m q : ℕ} (hq : q ≤ m)
    {K : SimpleGraph (PendantCoreVertex s m q)} {B R : ℝ}
    (hKdiam : K.ediam ≤ (4 : ℕ∞))
    (hclose : ((CoreClosePairFinset K).card : ℝ) ≤ B)
    (hR : 0 ≤ R)
    (hbound :
      (m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
          2 * B * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) ≤ R ^ 2) :
    let N := (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card
    (N : ℝ) ≤ 1 + R := by
  intro N
  have hN := coreFreeComponent_card_real_le_one_add_sqrt_of_close_bound (s := s) (m := m)
    (q := q) (K := K) hq hKdiam hclose
  have hsqrt :
      Real.sqrt
        ((m : ℝ) * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ) +
          2 * B * ((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) ≤ R := by
    rw [Real.sqrt_le_iff]
    exact ⟨hR, hbound⟩
  linarith

lemma coreFreeComponent_card_real_le_one_add_sqrt_host {s d m q : ℕ} (hq : q ≤ m)
    {H : SimpleGraph (Fin m)} {K : SimpleGraph (PendantCoreVertex s m q)}
    (hHost : HostGraph d m H)
    (hGK : PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq) ≤ K)
    (hKtf : K.CliqueFree 3) (hKdiam : K.ediam ≤ (4 : ℕ∞)) :
    let A := (AddedEdgeFinset (PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)) K).card
    let S : ℝ := ((s + 1 : ℕ) : ℝ)
    let B : ℝ :=
      (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
        (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
    let N := (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card
    (N : ℝ) ≤ 1 + Real.sqrt ((m : ℝ) * S * S + 2 * B * S * S) := by
  intro A S B N
  exact coreFreeComponent_card_real_le_one_add_sqrt_of_close_bound (s := s) (m := m)
    (q := q) (K := K) (B := B) hq hKdiam
    (by
      simpa [A, B] using
        (coreClosePair_card_real_le_host_log (d := d) (m := m)
          (P := PendantCorePendant s m q) (H := H)
          (root := pendantCoreRoot (s := s) (m := m) (q := q) hq) (K := K)
          hHost hGK hKtf))

lemma pendant_core_typed_added_edges_lower_of_coreFree_bound {s m q : ℕ} (hq : q ≤ m)
    {H : SimpleGraph (Fin m)} {K : SimpleGraph (PendantCoreVertex s m q)} {B : ℝ}
    (hfree : ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤ B) :
    ((m * s : ℕ) : ℝ) - B ≤
      ((AddedEdgeFinset (PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)) K).card : ℝ) := by
  have hpend : ((m * s : ℕ) : ℝ) ≤
      (Nat.card (PendantCorePendant s m q) : ℝ) := by
    rw [pendantCorePendant_nat_card]
    exact_mod_cast Nat.le_add_right (m * s) q
  have hacc : Nat.card (PendantCorePendant s m q) -
      (CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card ≤
        (AddedEdgeFinset (PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)) K).card := by
    simpa using
      (pendant_component_accounting (C := Fin m) (P := PendantCorePendant s m q)
        (H := H) (root := pendantCoreRoot (s := s) (m := m) (q := q) hq) (K := K))
  exact real_sub_le_of_nat_sub_le hpend hfree hacc

lemma pendant_core_typed_added_edges_lower_of_coreFree_eta {s m q : ℕ} (hq : q ≤ m)
    {H : SimpleGraph (Fin m)} {K : SimpleGraph (PendantCoreVertex s m q)} {η : ℝ}
    (hfree : ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
      η / 4 * ((m * s : ℕ) : ℝ) + 1) :
    (1 - η / 4) * ((m * s : ℕ) : ℝ) - 1 ≤
      ((AddedEdgeFinset (PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)) K).card : ℝ) := by
  have h := pendant_core_typed_added_edges_lower_of_coreFree_bound (s := s) (m := m) (q := q)
    (H := H) (K := K) hq hfree
  nlinarith

/-- A canonical base pendant over a core vertex, available when `s > 0`. -/
def basePendant {s m q : ℕ} (hs : 0 < s) (c : Fin m) : PendantCorePendant s m q :=
  Sum.inl (c, ⟨0, hs⟩)

@[simp] lemma pendantCoreRoot_basePendant {s m q : ℕ} (hq : q ≤ m)
    (hs : 0 < s) (c : Fin m) :
    pendantCoreRoot (s := s) (m := m) (q := q) hq (basePendant hs c) = c := rfl

lemma pendantCoreRoot_cover_of_pos_s {s m q : ℕ} (hq : q ≤ m) (hs : 0 < s) :
    ∀ c : Fin m, ∃ p : PendantCorePendant s m q, pendantCoreRoot hq p = c := by
  intro c
  exact ⟨basePendant hs c, rfl⟩

lemma pendantHubTyped_ediam_le_four {s m q : ℕ} (hq : q ≤ m) (hm : 0 < m)
    (hs : 0 < s) (H : SimpleGraph (Fin m)) :
    (PendantHubSupergraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)
      (basePendant hs ⟨0, hm⟩)).ediam ≤ (4 : ℕ∞) := by
  apply pendantHubSupergraphSum_ediam_le_four
  intro c _
  exact pendantCoreRoot_cover_of_pos_s hq hs c

/-- The pendant-core graph on its natural sum-type vertex set. -/
def PendantCoreGraphTyped (s m q : ℕ) (hq : q ≤ m) (H : SimpleGraph (Fin m)) :
    SimpleGraph (PendantCoreVertex s m q) :=
  PendantCoreGraphSum H (pendantCoreRoot (s := s) (m := m) (q := q) hq)

lemma pendantCoreVertex_card (s m q : ℕ) :
    Fintype.card (PendantCoreVertex s m q) = m * (s + 1) + q := by
  dsimp [PendantCoreVertex, PendantCorePendant]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  rw [Nat.mul_succ]
  omega

/-- The pendant-core construction used in the write-up, transported to the challenge's `Fin n`
vertex type when the cardinal arithmetic matches.  Outside the intended arithmetic and `q ≤ m`
range it is defined as `⊥`, which is irrelevant for the eventual construction. -/
noncomputable def PendantCoreGraph (s n m q : ℕ) (H : SimpleGraph (Fin m)) : SimpleGraph (Fin n) :=
  if hq : q ≤ m then
    if hn : m * (s + 1) + q = n then
      (PendantCoreGraphTyped s m q hq H).overFin (by
        rw [pendantCoreVertex_card, hn])
    else
      ⊥
  else
    ⊥

lemma pendantCoreGraph_eq_overFin {s n m q : ℕ} {H : SimpleGraph (Fin m)}
    (hq : q ≤ m) (hn : m * (s + 1) + q = n) :
    PendantCoreGraph s n m q H =
      (PendantCoreGraphTyped s m q hq H).overFin (by rw [pendantCoreVertex_card, hn]) := by
  simp [PendantCoreGraph, hq, hn]

lemma pendantCoreGraph_connected {s n m q : ℕ} {H : SimpleGraph (Fin m)}
    (hq : q ≤ m) (hn : m * (s + 1) + q = n) (hH : H.Connected) :
    (PendantCoreGraph s n m q H).Connected := by
  rw [pendantCoreGraph_eq_overFin hq hn]
  exact (SimpleGraph.Iso.connected_iff
    (SimpleGraph.overFinIso (G := PendantCoreGraphTyped s m q hq H)
      (by rw [pendantCoreVertex_card, hn]))).1
    (pendantCoreGraphSum_connected hH)

lemma pendantCoreGraph_cliqueFree_three {s n m q : ℕ} {H : SimpleGraph (Fin m)}
    (hq : q ≤ m) (hn : m * (s + 1) + q = n) (hH : H.CliqueFree 3) :
    (PendantCoreGraph s n m q H).CliqueFree 3 := by
  rw [pendantCoreGraph_eq_overFin hq hn]
  exact SimpleGraph.CliqueFree.comap
    (SimpleGraph.overFinIso (G := PendantCoreGraphTyped s m q hq H)
      (by rw [pendantCoreVertex_card, hn])).symm.isContained
    (pendantCoreGraphSum_cliqueFree_three hH)

lemma pendantCoreGraph_feasible {s n m q : ℕ} {H : SimpleGraph (Fin m)}
    (hq : q ≤ m) (hn : m * (s + 1) + q = n) (hm : 0 < m) (hs : 0 < s)
    (hH : H.CliqueFree 3) :
    ∃ K : SimpleGraph (Fin n), FeasibleSupergraph 4 (PendantCoreGraph s n m q H) K := by
  classical
  let root : PendantCorePendant s m q → Fin m :=
    pendantCoreRoot (s := s) (m := m) (q := q) hq
  let hub : PendantCorePendant s m q := basePendant hs ⟨0, hm⟩
  let Ksum : SimpleGraph (PendantCoreVertex s m q) := PendantHubSupergraphSum H root hub
  have hcard : Fintype.card (PendantCoreVertex s m q) = n := by
    rw [pendantCoreVertex_card, hn]
  refine ⟨Ksum.overFin hcard, ?_, ?_, ?_⟩
  · rw [pendantCoreGraph_eq_overFin hq hn]
    exact overFin_mono hcard (pendantCoreGraphSum_le_hubSupergraph H root hub)
  · exact SimpleGraph.CliqueFree.comap
      (SimpleGraph.overFinIso (G := Ksum) hcard).symm.isContained
      (pendantHubSupergraphSum_cliqueFree_three (H := H) (root := root) (hub := hub) hH)
  · have hcover : ∀ c : Fin m, c ≠ root hub →
        ∃ p : PendantCorePendant s m q, root p = c := by
      intro c _
      simpa [root] using pendantCoreRoot_cover_of_pos_s hq hs c
    exact overFin_ediam_le_of_forall_exists_walk_le Ksum hcard
      (pendantHubSupergraphSum_walk_le_four H root hub hcover)

/-- Specification for `PendantCoreGraph`: connected, triangle-free, and built from a host core with
`s` or `s + 1` leaves on each core vertex. -/
def PendantCoreSpec (s d n m q : ℕ) (H : SimpleGraph (Fin m)) : Prop :=
  n = m * (s + 1) + q ∧ q ≤ s ∧ HostGraph d m H

lemma PendantCoreSpec.order {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) : n = m * (s + 1) + q := h.1

lemma PendantCoreSpec.remainder_le {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) : q ≤ s := h.2.1

lemma PendantCoreSpec.host {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) : HostGraph d m H := h.2.2

lemma PendantCoreSpec.graph_connected {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) (hq : q ≤ m) :
    (PendantCoreGraph s n m q H).Connected :=
  pendantCoreGraph_connected hq h.order.symm h.host.connected

lemma PendantCoreSpec.graph_cliqueFree_three {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) (hq : q ≤ m) :
    (PendantCoreGraph s n m q H).CliqueFree 3 :=
  pendantCoreGraph_cliqueFree_three hq h.order.symm h.host.cliqueFree_three

lemma PendantCoreSpec.graph_feasible {s d n m q : ℕ} {H : SimpleGraph (Fin m)}
    (h : PendantCoreSpec s d n m q H) (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s) :
    ∃ K : SimpleGraph (Fin n), FeasibleSupergraph 4 (PendantCoreGraph s n m q H) K :=
  pendantCoreGraph_feasible hq h.order.symm hm hs h.host.cliqueFree_three

/-- Pull the typed component-count estimate through the canonical `Fin n` transport to bound any
feasible `Fin n` supergraph of a pendant-core graph. -/
theorem pendantCoreGraph_addedEdgeCount_lower_of_coreFree_eta {s n m q : ℕ}
    {H : SimpleGraph (Fin m)} (hq : q ≤ m) (hn : m * (s + 1) + q = n) {η : ℝ}
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1)
    (Kfin : SimpleGraph (Fin n))
    (hK : FeasibleSupergraph 4 (PendantCoreGraph s n m q H) Kfin) :
    (1 - η / 4) * ((m * s : ℕ) : ℝ) - 1 ≤
      (addedEdgeCount (PendantCoreGraph s n m q H) Kfin : ℝ) := by
  classical
  let Gt : SimpleGraph (PendantCoreVertex s m q) := PendantCoreGraphTyped s m q hq H
  have hc : Fintype.card (PendantCoreVertex s m q) = n := by
    rw [pendantCoreVertex_card, hn]
  let e := Fintype.equivFinOfCardEq hc
  let Kt : SimpleGraph (PendantCoreVertex s m q) := Kfin.comap e
  have hgraph : PendantCoreGraph s n m q H = Gt.overFin hc := by
    simpa [Gt] using pendantCoreGraph_eq_overFin (s := s) (n := n) (m := m) (q := q)
      (H := H) hq hn
  have hGKfin : Gt.overFin hc ≤ Kfin := by
    rw [← hgraph]
    exact hK.1
  have hGtKt : Gt ≤ Kt := by
    simpa [Gt, Kt, e] using overFin_le_comap_of_le (G := Gt) (K := Kfin) hc hGKfin
  have hKttf : Kt.CliqueFree 3 := by
    simpa [Kt, e] using cliqueFree_comap_equiv e hK.2.1
  have hKtdiam : Kt.ediam ≤ (4 : ℕ∞) := by
    simpa [Kt, e] using ediam_comap_equiv_le e hK.2.2
  have hfreeKt := hfree Kt hGtKt hKttf hKtdiam
  have htyped := pendant_core_typed_added_edges_lower_of_coreFree_eta
    (s := s) (m := m) (q := q) (H := H) (K := Kt) hq hfreeKt
  have hcount : addedEdgeCount (PendantCoreGraph s n m q H) Kfin =
      (AddedEdgeFinset Gt Kt).card := by
    rw [hgraph]
    simpa [Gt, Kt, e] using addedEdgeCount_overFin_eq_addedEdgeFinset_comap Gt Kfin hc
  rw [hcount]
  simpa [Gt, Kt, PendantCoreGraphTyped] using htyped

/-- Under the typed core-free-component estimate, the actual `h_4` value for the transported
pendant-core graph has the same lower bound. -/
theorem PendantCoreSpec.exists_isHR_lower_of_coreFree_eta {s d n m q : ℕ}
    {H : SimpleGraph (Fin m)} (h : PendantCoreSpec s d n m q H)
    (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s) {η : ℝ}
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1) :
    ∃ mhr : ℕ, IsHR 4 (PendantCoreGraph s n m q H) mhr ∧
      (1 - η / 4) * ((m * s : ℕ) : ℝ) - 1 ≤ (mhr : ℝ) := by
  refine exists_isHR_with_real_lower_bound
    (r := 4) (G := PendantCoreGraph s n m q H)
    (L := (1 - η / 4) * ((m * s : ℕ) : ℝ) - 1)
    (h.graph_feasible hq hm hs) ?_
  intro K hK
  exact pendantCoreGraph_addedEdgeCount_lower_of_coreFree_eta hq h.order.symm hfree K hK

/-- The same fixed-parameter statement after the final numerical absorption step. -/
theorem PendantCoreSpec.exists_isHR_final_of_coreFree_eta {s d n m q : ℕ}
    {H : SimpleGraph (Fin m)} (h : PendantCoreSpec s d n m q H)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s)
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1)
    (hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ))
    (hbig : 1 ≤ η / 4 * (n : ℝ)) :
    ∃ mhr : ℕ, IsHR 4 (PendantCoreGraph s n m q H) mhr ∧
      (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  rcases h.exists_isHR_lower_of_coreFree_eta hq hm hs hfree with ⟨mhr, hhr, hlower⟩
  refine ⟨mhr, hhr, ?_⟩
  have hcoef : 0 ≤ 1 - η / 4 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsmn hcoef
  nlinarith

/-- Fixed-parameter counterexample package, after all graph-counting and numeric hypotheses have
been supplied. -/
theorem PendantCoreSpec.counterexample_of_coreFree_eta {s d n m q : ℕ}
    {H : SimpleGraph (Fin m)} (h : PendantCoreSpec s d n m q H)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s)
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1)
    (hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ))
    (hbig : 1 ≤ η / 4 * (n : ℝ)) :
    ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
      G.Connected ∧ G.CliqueFree 3 ∧ IsHR 4 G mhr ∧ (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  rcases h.exists_isHR_final_of_coreFree_eta hη0 hη1 hq hm hs hfree hsmn hbig with
    ⟨mhr, hhr, hlower⟩
  exact ⟨PendantCoreGraph s n m q H, mhr, h.graph_connected hq, h.graph_cliqueFree_three hq,
    hhr, hlower⟩

/-- The elementary size comparison used after writing `n = m(s+1)+q` with `q ≤ s`. -/
lemma sm_lower_bound_of_order_le_mul_s_add_two {η : ℝ} {s m n : ℕ}
    (hη0 : 0 < η) (hη1 : η < 1)
    (hs : 4 ≤ η * ((s : ℝ) + 2))
    (hn : (n : ℝ) ≤ (m : ℝ) * ((s : ℝ) + 2)) :
    (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ) := by
  have hcoef_nonneg : 0 ≤ 1 - η / 2 := by nlinarith
  have hstep₁ := mul_le_mul_of_nonneg_left hn hcoef_nonneg
  have hcoef : (1 - η / 2) * ((s : ℝ) + 2) ≤ (s : ℝ) := by nlinarith
  have hmnonneg : 0 ≤ (m : ℝ) := by positivity
  have hstep₂ : (1 - η / 2) * ((m : ℝ) * ((s : ℝ) + 2)) ≤ (m : ℝ) * (s : ℝ) := by
    have := mul_le_mul_of_nonneg_left hcoef hmnonneg
    nlinarith
  norm_num at hstep₁ hstep₂ ⊢
  nlinarith

lemma exists_nat_pos_eta_mul_add_two_ge_four {η : ℝ} (hη0 : 0 < η) :
    ∃ s : ℕ, 0 < s ∧ 4 ≤ η * ((s : ℝ) + 2) := by
  let s : ℕ := Nat.ceil (4 / η)
  have hsceil : (4 / η : ℝ) ≤ (s : ℝ) := Nat.le_ceil _
  have hspos : 0 < s := by
    have hsone : 1 ≤ s := by
      rw [Nat.one_le_ceil_iff]
      positivity
    exact Nat.succ_le_iff.mp hsone
  refine ⟨s, hspos, ?_⟩
  have hmul : η * (4 / η) ≤ η * (s : ℝ) := mul_le_mul_of_nonneg_left hsceil hη0.le
  have hηne : η ≠ 0 := ne_of_gt hη0
  have hmul_eq : η * (4 / η) = 4 := by
    field_simp [hηne]
  nlinarith [hmul, hmul_eq]

lemma eventually_atTop_div_succ {s : ℕ} {P : ℕ → Prop}
    (hP : ∀ᶠ m : ℕ in Filter.atTop, P m) :
    ∀ᶠ n : ℕ in Filter.atTop, P (n / (s + 1)) := by
  rcases Filter.eventually_atTop.1 hP with ⟨M, hM⟩
  refine Filter.eventually_atTop.2 ⟨(s + 1) * M, ?_⟩
  intro n hn
  apply hM
  change M ≤ n / (s + 1)
  rw [Nat.le_div_iff_mul_le (Nat.succ_pos s)]
  simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn

lemma eventually_mod_succ_le_div_succ (s : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, n % (s + 1) ≤ n / (s + 1) := by
  refine Filter.eventually_atTop.2 ⟨(s + 1) * s, ?_⟩
  intro n hn
  have hmod : n % (s + 1) ≤ s := Nat.lt_succ_iff.mp (Nat.mod_lt n (Nat.succ_pos s))
  have hdiv : s ≤ n / (s + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos s)]
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hn
  exact hmod.trans hdiv

lemma eventually_pos_div_succ (s : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, 0 < n / (s + 1) := by
  refine Filter.eventually_atTop.2 ⟨s + 1, ?_⟩
  intro n hn
  exact Nat.div_pos hn (Nat.succ_pos s)

lemma eventually_one_le_eta_four_mul_nat {η : ℝ} (hη0 : 0 < η) :
    ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ η / 4 * (n : ℝ) := by
  have hcoef : 0 < η / 4 := by positivity
  have ht : Filter.Tendsto (fun n : ℕ => η / 4 * (n : ℝ)) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop hcoef tendsto_natCast_atTop_atTop
  exact ht.eventually_ge_atTop 1

/-- Convert the component accounting inequality `t ≥ |I| - N` and the component bound on `N`
into the lower bound used in the final assembly. -/
theorem accounting_to_sm_lower_bound {η sm I N t : ℝ}
    (hacc : I - N ≤ t) (hI : sm ≤ I) (hN : N ≤ η / 4 * sm + 1) :
    (1 - η / 4) * sm - 1 ≤ t := by
  nlinarith

/-- The final real-arithmetic assembly from the write-up.  Once the component accounting gives
`t ≥ (1 - η/4) sm - 1`, it is enough that `sm` is at least `(1 - η/2)n` and `n` is large enough
to absorb the final `-1`. -/
theorem final_numeric_assembly {η sm n t : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (ht : (1 - η / 4) * sm - 1 ≤ t)
    (hsmn : (1 - η / 2) * n ≤ sm)
    (hbig : 1 ≤ η / 4 * n) :
    (1 - η) * n ≤ t := by
  have hcoef : 0 ≤ 1 - η / 4 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsmn hcoef
  nlinarith

/-- A combined version of the last two deterministic arithmetic steps. -/
theorem final_assembly_from_accounting {η sm I N n t : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hacc : I - N ≤ t) (hI : sm ≤ I) (hN : N ≤ η / 4 * sm + 1)
    (hsmn : (1 - η / 2) * n ≤ sm) (hbig : 1 ≤ η / 4 * n) :
    (1 - η) * n ≤ t := by
  exact final_numeric_assembly hη0 hη1 (accounting_to_sm_lower_bound hacc hI hN) hsmn hbig

/-- Conditional fixed-parameter lower bound matching the corrected Lemma 3 argument: if the
supergraph already adds at least `n` edges, the final lower bound is immediate; otherwise the
core-free-component estimate is invoked. -/
theorem pendantCoreGraph_addedEdgeCount_final_lower_of_cond_coreFree_eta {s n m q : ℕ}
    {H : SimpleGraph (Fin m)} (hq : q ≤ m) (hn : m * (s + 1) + q = n)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((AddedEdgeFinset (PendantCoreGraphTyped s m q hq H) K).card : ℝ) < (n : ℝ) →
          ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
            η / 4 * ((m * s : ℕ) : ℝ) + 1)
    (hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ))
    (hbig : 1 ≤ η / 4 * (n : ℝ))
    (Kfin : SimpleGraph (Fin n))
    (hK : FeasibleSupergraph 4 (PendantCoreGraph s n m q H) Kfin) :
    (1 - η) * (n : ℝ) ≤ (addedEdgeCount (PendantCoreGraph s n m q H) Kfin : ℝ) := by
  classical
  let Gt : SimpleGraph (PendantCoreVertex s m q) := PendantCoreGraphTyped s m q hq H
  have hc : Fintype.card (PendantCoreVertex s m q) = n := by
    rw [pendantCoreVertex_card, hn]
  let e := Fintype.equivFinOfCardEq hc
  let Kt : SimpleGraph (PendantCoreVertex s m q) := Kfin.comap e
  have hgraph : PendantCoreGraph s n m q H = Gt.overFin hc := by
    simpa [Gt] using pendantCoreGraph_eq_overFin (s := s) (n := n) (m := m) (q := q)
      (H := H) hq hn
  have hGKfin : Gt.overFin hc ≤ Kfin := by
    rw [← hgraph]
    exact hK.1
  have hGtKt : Gt ≤ Kt := by
    simpa [Gt, Kt, e] using overFin_le_comap_of_le (G := Gt) (K := Kfin) hc hGKfin
  have hKttf : Kt.CliqueFree 3 := by
    simpa [Kt, e] using cliqueFree_comap_equiv e hK.2.1
  have hKtdiam : Kt.ediam ≤ (4 : ℕ∞) := by
    simpa [Kt, e] using ediam_comap_equiv_le e hK.2.2
  have hcount : addedEdgeCount (PendantCoreGraph s n m q H) Kfin =
      (AddedEdgeFinset Gt Kt).card := by
    rw [hgraph]
    simpa [Gt, Kt, e] using addedEdgeCount_overFin_eq_addedEdgeFinset_comap Gt Kfin hc
  by_cases hsmall : ((AddedEdgeFinset Gt Kt).card : ℝ) < (n : ℝ)
  · have hfreeKt :
        ((CoreFreeComponentFinset Kt (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
          η / 4 * ((m * s : ℕ) : ℝ) + 1 := by
      exact hfree Kt (by simpa [Gt] using hGtKt) hKttf hKtdiam (by simpa [Gt] using hsmall)
    have htyped := pendant_core_typed_added_edges_lower_of_coreFree_eta
      (s := s) (m := m) (q := q) (H := H) (K := Kt) hq hfreeKt
    have hfinal := final_numeric_assembly hη0 hη1 htyped hsmn hbig
    rw [hcount]
    simpa [Gt, Kt, PendantCoreGraphTyped] using hfinal
  · have hlarge : (n : ℝ) ≤ ((AddedEdgeFinset Gt Kt).card : ℝ) := le_of_not_gt hsmall
    have hcoef : (1 - η) * (n : ℝ) ≤ (n : ℝ) := by
      have hnnonneg : 0 ≤ (n : ℝ) := by positivity
      nlinarith
    have hfinal : (1 - η) * (n : ℝ) ≤ ((AddedEdgeFinset Gt Kt).card : ℝ) := hcoef.trans hlarge
    rw [hcount]
    simpa [Gt, Kt, PendantCoreGraphTyped] using hfinal

/-- Fixed-parameter counterexample package with the corrected conditional Lemma 3 hypothesis. -/
theorem PendantCoreSpec.counterexample_of_cond_coreFree_eta {s d n m q : ℕ}
    {H : SimpleGraph (Fin m)} (h : PendantCoreSpec s d n m q H)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s)
    (hfree : ∀ K : SimpleGraph (PendantCoreVertex s m q),
      PendantCoreGraphTyped s m q hq H ≤ K → K.CliqueFree 3 → K.ediam ≤ (4 : ℕ∞) →
        ((AddedEdgeFinset (PendantCoreGraphTyped s m q hq H) K).card : ℝ) < (n : ℝ) →
          ((CoreFreeComponentFinset K (pendantCoreRoot (s := s) (m := m) (q := q) hq)).card : ℝ) ≤
            η / 4 * ((m * s : ℕ) : ℝ) + 1)
    (hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ))
    (hbig : 1 ≤ η / 4 * (n : ℝ)) :
    ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
      G.Connected ∧ G.CliqueFree 3 ∧ IsHR 4 G mhr ∧ (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  have hlowerAll : ∀ K : SimpleGraph (Fin n), FeasibleSupergraph 4 (PendantCoreGraph s n m q H) K →
      (1 - η) * (n : ℝ) ≤ (addedEdgeCount (PendantCoreGraph s n m q H) K : ℝ) := by
    intro K hK
    exact pendantCoreGraph_addedEdgeCount_final_lower_of_cond_coreFree_eta
      (s := s) (n := n) (m := m) (q := q) (H := H) hq h.order.symm hη0 hη1
      hfree hsmn hbig K hK
  rcases exists_isHR_with_real_lower_bound
      (r := 4) (G := PendantCoreGraph s n m q H) (L := (1 - η) * (n : ℝ))
      (h.graph_feasible hq hm hs) hlowerAll with
    ⟨mhr, hhr, hlower⟩
  exact ⟨PendantCoreGraph s n m q H, mhr, h.graph_connected hq, h.graph_cliqueFree_three hq,
    hhr, hlower⟩

/-- Fixed-parameter counterexample package where Lemma 3 has been reduced to a single explicit
radicand inequality.  This is the deterministic interface for the remaining asymptotic estimates. -/
theorem PendantCoreSpec.counterexample_of_numeric_coreFree {s d n m q : ℕ}
    {H : SimpleGraph (Fin m)} (h : PendantCoreSpec s d n m q H)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hq : q ≤ m) (hm : 0 < m) (hs : 0 < s)
    (hrad : ∀ A : ℕ, (A : ℝ) < (n : ℝ) →
      let S : ℝ := ((s + 1 : ℕ) : ℝ)
      let B : ℝ :=
        (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
          (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
      (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2)
    (hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ))
    (hbig : 1 ≤ η / 4 * (n : ℝ)) :
    ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
      G.Connected ∧ G.CliqueFree 3 ∧ IsHR 4 G mhr ∧ (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  refine h.counterexample_of_cond_coreFree_eta hη0 hη1 hq hm hs ?_ hsmn hbig
  intro K hGK hKtf hKdiam hsmall
  let A := (AddedEdgeFinset (PendantCoreGraphTyped s m q hq H) K).card
  let S : ℝ := ((s + 1 : ℕ) : ℝ)
  let B : ℝ :=
    (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
      (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
  have hclose : ((CoreClosePairFinset K).card : ℝ) ≤ B := by
    simpa [A, B, PendantCoreGraphTyped] using
      (coreClosePair_card_real_le_host_log (d := d) (m := m)
        (P := PendantCorePendant s m q) (H := H)
        (root := pendantCoreRoot (s := s) (m := m) (q := q) hq) (K := K)
        h.host (by simpa [PendantCoreGraphTyped] using hGK) hKtf)
  have hR : 0 ≤ η / 4 * ((m * s : ℕ) : ℝ) := by positivity
  have hradA :
      (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2 := by
    simpa [A, S, B] using hrad A hsmall
  have hN := coreFreeComponent_card_real_le_one_add_of_close_bound_sq
    (s := s) (m := m) (q := q) (K := K) (B := B)
    (R := η / 4 * ((m * s : ℕ) : ℝ)) hq hKdiam hclose hR hradA
  nlinarith

/-- Build the eventual finite pendant-core specifications from fixed `s,d`, eventual host graphs at
that `d`, and the explicit radicand estimate along `m = n / (s + 1)`. -/
theorem eventual_pendant_specs_of_fixed_d {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {s d : ℕ} (hs : 0 < s) (hsη : 4 ≤ η * ((s : ℝ) + 2))
    (hHost : ∀ᶠ m : ℕ in Filter.atTop, ∃ H : SimpleGraph (Fin m), HostGraph d m H)
    (hrad : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ A : ℕ, (A : ℝ) < (n : ℝ) →
        let m := n / (s + 1)
        let S : ℝ := ((s + 1 : ℕ) : ℝ)
        let B : ℝ :=
          (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
            (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
        (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (s' d' m q : ℕ) (H : SimpleGraph (Fin m)),
        PendantCoreSpec s' d' n m q H ∧ q ≤ m ∧ 0 < m ∧ 0 < s' ∧
          (∀ A : ℕ, (A : ℝ) < (n : ℝ) →
            let S : ℝ := ((s' + 1 : ℕ) : ℝ)
            let B : ℝ :=
              (m : ℝ) * (d' : ℝ) + (m : ℝ) * (d' : ℝ) * (d' : ℝ) +
                (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d' : ℝ) / (d' : ℝ)))
            (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s' : ℕ) : ℝ)) ^ 2) ∧
          (1 - η / 2) * (n : ℝ) ≤ ((m * s' : ℕ) : ℝ) ∧
          1 ≤ η / 4 * (n : ℝ) := by
  filter_upwards [eventually_atTop_div_succ (s := s) hHost, hrad,
    eventually_mod_succ_le_div_succ s, eventually_pos_div_succ s,
    eventually_one_le_eta_four_mul_nat hη0] with n hHostn hradn hqle hmpos hbig
  let m := n / (s + 1)
  let q := n % (s + 1)
  rcases hHostn with ⟨H, hH⟩
  have hqles : q ≤ s := by
    exact Nat.lt_succ_iff.mp (Nat.mod_lt n (Nat.succ_pos s))
  have hn : n = m * (s + 1) + q := by
    simpa [m, q, Nat.mul_comm] using (Nat.div_add_mod n (s + 1)).symm
  have hnle_nat : n ≤ m * (s + 2) := by
    calc
      n = m * (s + 1) + q := hn
      _ ≤ m * (s + 1) + m := Nat.add_le_add_left hqle _
      _ = m * (s + 2) := by ring
  have hnle : (n : ℝ) ≤ (m : ℝ) * ((s : ℝ) + 2) := by
    exact_mod_cast hnle_nat
  have hsmn : (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ) :=
    sm_lower_bound_of_order_le_mul_s_add_two hη0 hη1 hsη hnle
  refine ⟨s, d, m, q, H, ?_, hqle, hmpos, hs, ?_, hsmn, hbig⟩
  · exact ⟨hn, hqles, hH⟩
  · intro A hA
    simpa [m] using hradn A hA

/-- Eventual counterexample family from eventual finite pendant-core specifications.  This isolates
what remains of the asymptotic parameter-selection proof after the deterministic graph counting. -/
theorem counterexample_family_from_eventual_pendant_specs {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hSpecs : ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (s d m q : ℕ) (H : SimpleGraph (Fin m)),
        PendantCoreSpec s d n m q H ∧ q ≤ m ∧ 0 < m ∧ 0 < s ∧
          (∀ A : ℕ, (A : ℝ) < (n : ℝ) →
            let S : ℝ := ((s + 1 : ℕ) : ℝ)
            let B : ℝ :=
              (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
                (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
            (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2) ∧
          (1 - η / 2) * (n : ℝ) ≤ ((m * s : ℕ) : ℝ) ∧
          1 ≤ η / 4 * (n : ℝ)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
        G.Connected ∧ G.CliqueFree 3 ∧ IsHR 4 G mhr ∧ (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  filter_upwards [hSpecs] with n hn
  rcases hn with ⟨s, d, m, q, H, hspec, hq, hm, hs, hrad, hsmn, hbig⟩
  exact hspec.counterexample_of_numeric_coreFree hη0 hη1 hq hm hs hrad hsmn hbig

/-- Counterexample family from fixed `s,d` data: eventual host graphs at `d` and the eventual
radicand estimate along the Euclidean decomposition of `n`. -/
theorem counterexample_family_from_fixed_d_data {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    {s d : ℕ} (hs : 0 < s) (hsη : 4 ≤ η * ((s : ℝ) + 2))
    (hHost : ∀ᶠ m : ℕ in Filter.atTop, ∃ H : SimpleGraph (Fin m), HostGraph d m H)
    (hrad : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ A : ℕ, (A : ℝ) < (n : ℝ) →
        let m := n / (s + 1)
        let S : ℝ := ((s + 1 : ℕ) : ℝ)
        let B : ℝ :=
          (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
            (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
        (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
        G.Connected ∧ G.CliqueFree 3 ∧ IsHR 4 G mhr ∧ (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  exact counterexample_family_from_eventual_pendant_specs hη0 hη1
    (eventual_pendant_specs_of_fixed_d hη0 hη1 hs hsη hHost hrad)

lemma eventually_log_div_nat_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in Filter.atTop, Real.log (d : ℝ) / (d : ℝ) ≤ ε := by
  have hlo : (fun x : ℝ => Real.log x) =o[Filter.atTop] (fun x : ℝ => x) :=
    Real.isLittleO_log_id_atTop
  have hlo_nat :
      (fun d : ℕ => Real.log (d : ℝ)) =o[Filter.atTop] (fun d : ℕ => (d : ℝ)) :=
    hlo.comp_tendsto tendsto_natCast_atTop_atTop
  have h := hlo_nat.def hε
  filter_upwards [h, Filter.eventually_ge_atTop 1] with d hd hd1
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  have hlog : Real.log (d : ℝ) ≤ ε * (d : ℝ) := by
    have habs := hd
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at habs
    have hdabs : |(d : ℝ)| = (d : ℝ) := abs_of_nonneg (Nat.cast_nonneg d)
    rw [hdabs] at habs
    exact (le_abs_self _).trans habs
  exact (div_le_iff₀ hdpos).mpr hlog

lemma radicand_bound_real {η m n A S s d L : ℝ}
    (hm0 : 0 ≤ m) (hL0 : 0 ≤ L)
    (hA : A ≤ n) (hn : n ≤ m * (s + 2))
    (hlin : S * S * (m + 2 * m * d + 2 * m * d * d + 2 * m * (s + 2)) ≤
      η ^ 2 / 32 * m ^ 2 * s ^ 2)
    (hquad : 4 * hostC * S * S * (s + 2) * L ≤ η ^ 2 / 32 * s ^ 2) :
    m * S * S + 2 * (m * d + m * d * d + A * (1 + 2 * (hostC * m * L))) * S * S ≤
      (η / 4 * (m * s)) ^ 2 := by
  have hhost0 : 0 ≤ hostC := by norm_num [hostC]
  have hAle : A ≤ m * (s + 2) := hA.trans hn
  have hprod1 : 0 ≤ hostC * m := mul_nonneg hhost0 hm0
  have hprod : 0 ≤ hostC * m * L := mul_nonneg hprod1 hL0
  have hfac : 0 ≤ 1 + 2 * (hostC * m * L) := by nlinarith
  have hAterm : A * (1 + 2 * (hostC * m * L)) ≤
      (m * (s + 2)) * (1 + 2 * (hostC * m * L)) :=
    mul_le_mul_of_nonneg_right hAle hfac
  have hm2nonneg : 0 ≤ m ^ 2 := sq_nonneg m
  have hquad_m := mul_le_mul_of_nonneg_left hquad hm2nonneg
  nlinarith [hlin, hquad_m, hAterm]

lemma eventually_fixed_d_radicand {η : ℝ} (hη0 : 0 < η)
    {s d : ℕ} (hs : 0 < s)
    (hL0 : 0 ≤ Real.log (d : ℝ) / (d : ℝ))
    (hquad :
      4 * hostC * (((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) * ((s : ℝ) + 2) *
          (Real.log (d : ℝ) / (d : ℝ)) ≤
        η ^ 2 / 32 * (s : ℝ) ^ 2) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ∀ A : ℕ, (A : ℝ) < (n : ℝ) →
        let m := n / (s + 1)
        let S : ℝ := ((s + 1 : ℕ) : ℝ)
        let B : ℝ :=
          (m : ℝ) * (d : ℝ) + (m : ℝ) * (d : ℝ) * (d : ℝ) +
            (A : ℝ) * (1 + 2 * (hostC * (m : ℝ) * Real.log (d : ℝ) / (d : ℝ)))
        (m : ℝ) * S * S + 2 * B * S * S ≤ (η / 4 * ((m * s : ℕ) : ℝ)) ^ 2 := by
  let S : ℝ := ((s + 1 : ℕ) : ℝ)
  let C : ℝ := S * S * (1 + 2 * (d : ℝ) + 2 * (d : ℝ) * (d : ℝ) + 2 * ((s : ℝ) + 2))
  let den : ℝ := η ^ 2 / 32 * (s : ℝ) ^ 2
  have hden_pos : 0 < den := by
    dsimp [den]
    positivity
  let M : ℕ := Nat.ceil (C / den)
  have hMceil : C / den ≤ (M : ℝ) := by
    dsimp [M]
    exact Nat.le_ceil _
  have hCleM : C ≤ den * (M : ℝ) := by
    have htmp := (div_le_iff₀ hden_pos).mp hMceil
    nlinarith
  filter_upwards [eventually_atTop_div_succ (s := s) (P := fun m => M ≤ m)
      (Filter.eventually_ge_atTop M), eventually_mod_succ_le_div_succ s] with n hmM hqle
  intro A hA
  let m := n / (s + 1)
  let q := n % (s + 1)
  let L : ℝ := Real.log (d : ℝ) / (d : ℝ)
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hMle_real : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmM
  have hCle : C ≤ den * (m : ℝ) := by
    exact hCleM.trans (mul_le_mul_of_nonneg_left hMle_real hden_pos.le)
  have hlin0 : C * (m : ℝ) ≤ den * (m : ℝ) ^ 2 := by
    have := mul_le_mul_of_nonneg_right hCle hm0
    nlinarith
  have hlin : S * S * ((m : ℝ) + 2 * (m : ℝ) * (d : ℝ) +
      2 * (m : ℝ) * (d : ℝ) * (d : ℝ) + 2 * (m : ℝ) * ((s : ℝ) + 2)) ≤
      η ^ 2 / 32 * (m : ℝ) ^ 2 * (s : ℝ) ^ 2 := by
    have hleft : S * S * ((m : ℝ) + 2 * (m : ℝ) * (d : ℝ) +
        2 * (m : ℝ) * (d : ℝ) * (d : ℝ) + 2 * (m : ℝ) * ((s : ℝ) + 2)) =
        C * (m : ℝ) := by
      dsimp [C]
      ring
    have hright : den * (m : ℝ) ^ 2 = η ^ 2 / 32 * (m : ℝ) ^ 2 * (s : ℝ) ^ 2 := by
      dsimp [den]
      ring
    rw [hleft, ← hright]
    exact hlin0
  have hn : n = m * (s + 1) + q := by
    simpa [m, q, Nat.mul_comm] using (Nat.div_add_mod n (s + 1)).symm
  have hnle_nat : n ≤ m * (s + 2) := by
    calc
      n = m * (s + 1) + q := hn
      _ ≤ m * (s + 1) + m := Nat.add_le_add_left hqle _
      _ = m * (s + 2) := by ring
  have hnle : (n : ℝ) ≤ (m : ℝ) * ((s : ℝ) + 2) := by exact_mod_cast hnle_nat
  have hA_le : (A : ℝ) ≤ (n : ℝ) := le_of_lt hA
  have hmain := radicand_bound_real (η := η) (m := (m : ℝ)) (n := (n : ℝ))
    (A := (A : ℝ)) (S := S) (s := (s : ℝ)) (d := (d : ℝ)) (L := L)
    hm0 hL0 hA_le hnle hlin
    (by simpa [S, L, mul_assoc, mul_left_comm, mul_comm] using hquad)
  simpa [m, S, L, Nat.cast_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    using hmain

/-- The pendant-component accounting theorem.

This packages the pendant construction, Lemmas 1-3, and the final numerical assembly from the
write-up.  Its only graph-existence input is Lemma E's eventual host-graph family. -/
theorem pendant_core_counterexamples_from_hosts
    (hHosts : ∀ᶠ d : ℕ in Filter.atTop,
      ∀ᶠ m : ℕ in Filter.atTop,
        ∃ H : SimpleGraph (Fin m), HostGraph d m H) :
    ∀ {η : ℝ}, 0 < η → η < 1 →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
          G.Connected ∧
            G.CliqueFree 3 ∧
              IsHR 4 G mhr ∧
                (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  intro η hη0 hη1
  rcases exists_nat_pos_eta_mul_add_two_ge_four hη0 with ⟨s, hs, hsη⟩
  let S : ℝ := ((s + 1 : ℕ) : ℝ)
  let target : ℝ := η ^ 2 / 32 * (s : ℝ) ^ 2
  let denom : ℝ := 4 * hostC * (S * S) * ((s : ℝ) + 2)
  have htarget_pos : 0 < target := by
    dsimp [target]
    positivity
  have hdenom_pos : 0 < denom := by
    dsimp [denom, S, hostC]
    positivity
  let ε : ℝ := target / denom
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hD : ∀ᶠ d : ℕ in Filter.atTop,
      (∀ᶠ m : ℕ in Filter.atTop, ∃ H : SimpleGraph (Fin m), HostGraph d m H) ∧
        Real.log (d : ℝ) / (d : ℝ) ≤ ε ∧ 1 ≤ d := by
    filter_upwards [hHosts, eventually_log_div_nat_le hε, Filter.eventually_ge_atTop 1] with
      d hHostD hlogD hd1
    exact ⟨hHostD, hlogD, hd1⟩
  rcases Filter.eventually_atTop.1 hD with ⟨D, hDtail⟩
  let d := D
  rcases hDtail d le_rfl with ⟨hHostD, hlogD, hd1⟩
  have hL0 : 0 ≤ Real.log (d : ℝ) / (d : ℝ) := by
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
    have hlog0 : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg (by exact_mod_cast hd1)
    exact div_nonneg hlog0 hdpos.le
  have hdenom_eps : denom * ε = target := by
    dsimp [ε]
    field_simp [hdenom_pos.ne']
  have hquad :
      4 * hostC * (((s + 1 : ℕ) : ℝ) * ((s + 1 : ℕ) : ℝ)) * ((s : ℝ) + 2) *
          (Real.log (d : ℝ) / (d : ℝ)) ≤
        η ^ 2 / 32 * (s : ℝ) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hlogD hdenom_pos.le
    have hmul' : denom * (Real.log (d : ℝ) / (d : ℝ)) ≤ target := by
      nlinarith [hmul, hdenom_eps]
    simpa [denom, S, target, mul_assoc, mul_left_comm, mul_comm] using hmul'
  exact counterexample_family_from_fixed_d_data hη0 hη1 hs hsη hHostD
    (eventually_fixed_d_radicand hη0 hs hL0 hquad)

/-- The asymptotic counterexample family extracted from Lemma E and pendant-core accounting. -/
theorem counterexample_family :
    ∀ {η : ℝ}, 0 < η → η < 1 →
      ∀ᶠ n : ℕ in Filter.atTop,
        ∃ (G : SimpleGraph (Fin n)) (mhr : ℕ),
          G.Connected ∧
            G.CliqueFree 3 ∧
              IsHR 4 G mhr ∧
                (1 - η) * (n : ℝ) ≤ (mhr : ℝ) := by
  exact pendant_core_counterexamples_from_hosts lemmaE_host_graphs

/-- Convert the asymptotic lower-bound family into the formal negation of the conjecture. -/
theorem erdos_619_solution : Erdos619.erdos_619 := by
  intro hconj
  rcases hconj with ⟨c, hcpos, hc⟩
  set η : ℝ := c / 2
  have hη0 : 0 < η := by positivity
  by_cases hη1 : η < 1
  · rcases (Filter.eventually_atTop.1 (counterexample_family hη0 hη1)) with ⟨n0, hn0⟩
    let n := max n0 1
    rcases hn0 n (le_max_left _ _) with ⟨G, mhr, hGconn, hGtf, hhr, hlower⟩
    have hupper := hc n G mhr hGconn hGtf hhr
    have hηc : 1 - c = 1 - η - η := by ring
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_one) (le_max_right n0 1))
    have hgap : (1 - c) * (n : ℝ) < (1 - η) * (n : ℝ) := by
      rw [hηc]
      nlinarith [mul_pos hη0 hnpos]
    linarith
  · have hcge : 2 ≤ c := by
      dsimp [η] at hη1
      linarith
    rcases (Filter.eventually_atTop.1 (counterexample_family (show (0 : ℝ) < 1 / 2 by norm_num)
        (show (1 / 2 : ℝ) < 1 by norm_num))) with ⟨n0, hn0⟩
    let n := max n0 1
    rcases hn0 n (le_max_left _ _) with ⟨G, mhr, hGconn, hGtf, hhr, _⟩
    have hupper := hc n G mhr hGconn hGtf hhr
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_one) (le_max_right n0 1))
    have : (1 - c) * (n : ℝ) < 0 := by nlinarith
    have hmhr_nonneg : 0 ≤ (mhr : ℝ) := by positivity
    linarith

end Erdos619
