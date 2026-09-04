-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.E5StarDecomposition
import ErdosProblems.Erdos1177.E5FiniteBound

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite colourings of the edge-intersection graph

This module relates finite colourings of a linear triple system's
edge-intersection graph to weak vertex colourings of the triple system.  A
proper colouring of the intersection graph partitions the hyperedges into
matchings.  Mark one vertex in every hyperedge; for each matching class, record
whether a vertex is marked by an edge in that class.  The resulting Boolean
signature is nonconstant on every hyperedge.
-/

open Cardinal

namespace Erdos1177

universe u v

variable {W : Type u}

/-- A colouring of the edge-intersection graph, stated without committing to a
particular graph-colouring API. -/
def EdgeIntersectionColoring (H : Hypergraph W) (C : Type v) (c : H.edges → C) : Prop :=
  ∀ ⦃e f : H.edges⦄, (edgeIntersectionGraph H).Adj e f → c e ≠ c f

/-- The edge-intersection graph is colourable by `C`. -/
def EdgeIntersectionColorable (H : Hypergraph W) (C : Type v) : Prop :=
  ∃ c : H.edges → C, EdgeIntersectionColoring H C c

/-
Edges receiving the same colour in a proper intersection-graph colouring
are disjoint.
-/
theorem disjoint_of_edgeIntersectionColoring_same
    (H : Hypergraph W) {C : Type v} {c : H.edges → C}
    (hc : EdgeIntersectionColoring H C c) {e f : H.edges}
    (hcol : c e = c f) (hne : e ≠ f) : Disjoint (e : Set W) (f : Set W) := by
  exact Set.disjoint_left.mpr fun x hex hfx => by have := hc ( show ( edgeIntersectionGraph H ).Adj e f from by
                                                                exact edgeIntersectionGraph_adj_of_common_vertex H hne hex hfx ) ; simp_all +decide [ Set.disjoint_left ] ;

/-- A chosen marked vertex of each edge of a triple system. -/
noncomputable def edgeMark (H : Hypergraph W) (htri : H.IsTripleSystem) : H.edges → W :=
  fun e => Classical.choose (Set.nonempty_of_ncard_ne_zero (by
    rw [htri e.1 e.2]
    norm_num))

/-
The marked vertex belongs to its edge.
-/
theorem edgeMark_mem (H : Hypergraph W) (htri : H.IsTripleSystem) (e : H.edges) :
    edgeMark H htri e ∈ e.1 := by
  exact Classical.choose_spec ( Set.nonempty_of_ncard_ne_zero ( by rw [ htri e.1 e.2 ] ; norm_num ) )

/-
A proper `q`-colouring of the edge-intersection graph gives a weak
vertex-colouring of the triple system by Boolean `q`-signatures.
-/
theorem properColoring_of_edgeIntersectionColoring
    (H : Hypergraph W) (htri : H.IsTripleSystem) (q : ℕ)
    (c : H.edges → Fin q) (hc : EdgeIntersectionColoring H (Fin q) c) :
    ∃ d : W → (Fin q → Bool), H.ProperColoring d := by
  -- Define d(v)(i) to be true iff there exists an edge e of colour i whose chosen mark is v.
  set d : W → Fin q → Prop := fun v i => ∃ e : H.edges, c e = i ∧ edgeMark H htri e = v;
  refine' ⟨ _, _ ⟩;
  convert! fun v i => decide ( d v i ) using 1;
  exact fun v i => Classical.propDecidable _;
  intro e he;
  -- Since e is a triple, there exists a vertex v in e such that v ≠ edgeMark H htri ⟨e, he⟩.
  obtain ⟨v, hv⟩ : ∃ v ∈ e, v ≠ edgeMark H htri ⟨e, he⟩ := by
    have := htri e he;
    exact Set.exists_ne_of_one_lt_ncard ( by linarith ) _;
  refine' ⟨ edgeMark H htri ⟨ e, he ⟩, _, v, _, _ ⟩ <;> simp_all +decide only [eq_mpr_eq_cast, cast_eq, ne_eq];
  · exact edgeMark_mem H htri ⟨ e, he ⟩;
  · use c ⟨ e, he ⟩ ; simp_all +decide [ d ] ;
    push_neg;
    refine' Or.inl ⟨ ⟨ e, he, rfl, rfl ⟩, _ ⟩;
    intro a ha hca hva; have := hc ( show ( edgeIntersectionGraph H ).Adj ⟨ a, ha ⟩ ⟨ e, he ⟩ from by
                                      exact edgeIntersectionGraph_adj_of_common_vertex H ( by aesop ) ( edgeMark_mem H htri ⟨ a, ha ⟩ ) ( by aesop ) ) ; simp_all +decide [ Set.disjoint_left ] ;

/-
Cardinal-valued form of the Boolean-signature construction.
-/
theorem colorableBy_of_edgeIntersectionColorable_fin
    (H : Hypergraph W) (htri : H.IsTripleSystem) (q : ℕ)
    (hc : EdgeIntersectionColorable H (Fin q)) :
    H.ColorableBy (Cardinal.mk (ULift.{u} (Fin q → Bool))) := by
  have := properColoring_of_edgeIntersectionColoring H htri q hc.choose hc.choose_spec;
  convert! this using 1;
  constructor <;> intro h <;> cases' h with d hd;
  · convert! this using 1;
  · refine' ⟨ _, _ ⟩;
    exact fun w => Classical.choice ( Cardinal.eq.1 ( by simp +decide [ Cardinal.mk_fintype ] ) ) ( ULift.up ( d w ) );
    intro e he; specialize hd e he; aesop;

/-
If a triple system has no proper colouring by Boolean `q`-signatures, then
its edge-intersection graph has no proper `q`-colouring.
-/
theorem not_edgeIntersectionColorable_of_not_signatureColorable
    (H : Hypergraph W) (htri : H.IsTripleSystem) (q : ℕ)
    (hno : ¬ ∃ d : W → (Fin q → Bool), H.ProperColoring d) :
    ¬ EdgeIntersectionColorable H (Fin q) := by
  contrapose! hno; have := properColoring_of_edgeIntersectionColoring H htri q hno.choose hno.choose_spec; aesop;

/-
Unbounded finite weak chromatic number forces unbounded finite chromatic
number of the edge-intersection graph.
-/
theorem edgeIntersection_not_finitely_colorable_of_unbounded
    (H : Hypergraph W) (htri : H.IsTripleSystem)
    (hunbounded : ∀ k : ℕ, 0 < k →
      ¬ ∃ d : W → Fin k, H.ProperColoring d) :
    ∀ q : ℕ, 0 < q → ¬ EdgeIntersectionColorable H (Fin q) := by
  intro q hq_pos hq_colorable
  obtain ⟨c, hc⟩ := hq_colorable;
  obtain ⟨d, hd⟩ := properColoring_of_edgeIntersectionColoring H htri q c hc;
  exact hunbounded ( Fintype.card ( Fin q → Bool ) ) ( Fintype.card_pos_iff.mpr ⟨ fun _ => Bool.true ⟩ ) ⟨ fun w => Fintype.equivFin _ ( d w ), by
    intro e he; specialize hd e he; aesop; ⟩

/-
In particular, every countable core occurring in the E5 reduction has an
edge-intersection graph of unbounded finite chromatic number.
-/
theorem countableCore_edgeIntersection_unbounded
    (H : Hypergraph W) (A : Set (Set W))
    (htri : H.IsTripleSystem) (hA : A ⊆ H.edges)
    (hunbounded : ∀ k : ℕ, 0 < k →
      ¬ ∃ d : W → Fin k, (⟨A⟩ : Hypergraph W).ProperColoring d) :
    ∀ q : ℕ, 0 < q →
      ¬ EdgeIntersectionColorable (⟨A⟩ : Hypergraph W) (Fin q) := by
  exact fun q hq =>
    edgeIntersection_not_finitely_colorable_of_unbounded
      (⟨A⟩ : Hypergraph W) (fun e he => htri e (hA he)) hunbounded q hq

end Erdos1177
