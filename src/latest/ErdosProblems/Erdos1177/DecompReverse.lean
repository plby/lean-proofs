-- Modified for this repository: Lean 4.33.0 port and Erdos1177 namespace.
import ErdosProblems.Erdos1177.DecompExpansion

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Finite bridge decomposition (§5): the reverse direction

This file proves the reverse direction of `prop:finite-decomposition`: a finite
triple system that is linear, has every hyperedge-node incident with a bridge,
and every Berge cycle of even length, is a member of the class `B`.

The heart of the argument is the reconstruction of `F` from its expansion pieces
(`decomp_step`): every such `F` with at least one edge is, up to isomorphism,
either a single bipartite expansion, a disjoint union of two smaller such
systems, or a one-point amalgamation of two smaller such systems.  A strong
induction on the number of edges then places `F` in `B`.
-/

open Cardinal

namespace Erdos1177

open Classical

universe u

/-! ### Isomorphism of finite triple systems is an equivalence -/

/-- Reflexivity of `FTS.Iso`. -/
theorem FTS.Iso.refl (F : FTS) : FTS.Iso F F :=
  ⟨Equiv.refl _, by intro e; simp⟩

/-- Symmetry of `FTS.Iso`. -/
theorem FTS.Iso.symm {F G : FTS} (h : FTS.Iso F G) : FTS.Iso G F := by
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.symm, ?_⟩
  intro e
  rw [hφ (e.map φ.symm.toEmbedding)]
  simp [Finset.map_map]

/-! ### The reconstruction step (geometric core) -/

/-- **The reconstruction step.**  A finite triple system with no isolated
vertices, at least one edge, that is linear, bridge-incident and has only even
Berge cycles, is — up to isomorphism — a single bipartite expansion, a disjoint
union of two strictly smaller `ReconOK` systems, or a one-point amalgamation of
two strictly smaller `ReconOK` systems. -/
theorem decomp_step (F : FTS) (h : ReconOK F) :
    (∃ (VJ : Type) (_ : Fintype VJ) (_ : DecidableEq VJ) (J : SimpleGraph VJ)
        (_ : DecidableRel J.Adj), J.Colorable 2 ∧ FTS.Iso F (graphExpansion J)) ∨
    (∃ F₁ F₂ : FTS, F₁.edges.card < F.edges.card ∧ F₂.edges.card < F.edges.card ∧
        ReconOK F₁ ∧ ReconOK F₂ ∧ FTS.Iso F (F₁.disjUnion F₂)) ∨
    (∃ (F₁ F₂ : FTS) (x : F₁.V) (y : F₂.V),
        F₁.edges.card < F.edges.card ∧ F₂.edges.card < F.edges.card ∧
        ReconOK F₁ ∧ ReconOK F₂ ∧ FTS.Iso F (F₁.amalgamate F₂ x y)) := by
  obtain ⟨hlin, hno_iso, hbr, hev⟩ := h
  by_cases hA : ∃ (ed : {e : Finset F.V // e ∈ F.edges}) (w : F.V),
      IsBridgeInc F w ed ∧ ∃ f : {e : Finset F.V // e ∈ F.edges}, f ≠ ed ∧ w ∈ f.1
  · -- Amalgamation case.
    obtain ⟨ed, w, hbrid, f, hfne, hwf⟩ := hA
    exact Or.inr (Or.inr
      (decomp_amalg ⟨hlin, hno_iso, hbr, hev⟩ ed w hbrid f hfne hwf))
  · -- Expansion case: every edge has a private vertex.
    push_neg at hA
    refine Or.inl (exists_expansion_of_private hlin ?_ hev)
    intro ed
    obtain ⟨w, hw_mem, hw_bridge⟩ := hbr ed
    refine ⟨w, hw_mem, ?_⟩
    intro g hg hwg
    by_contra hgne
    exact hA ed w hw_bridge ⟨g, hg⟩ (fun hcontra => hgne (congrArg Subtype.val hcontra)) hwg

/-! ### The induction -/

/-- **Reverse direction, no-isolated-vertices case.**  A `ReconOK` finite triple
system is in the class `B`. -/
theorem bclass_of_reconOK (F : FTS) (h : ReconOK F) : Bclass F := by
  -- strong induction on the number of edges
  generalize hn : F.edges.card = n
  induction n using Nat.strong_induction_on generalizing F with
  | _ n ih =>
    rcases F.edges.eq_empty_or_nonempty with hE | -
    · exact Bclass.edgeless F hE
    · rcases decomp_step F h with
        ⟨VJ, _, _, J, _, hJ, hiso⟩ | ⟨F₁, F₂, h1, h2, hr1, hr2, hiso⟩ |
        ⟨F₁, F₂, x, y, h1, h2, hr1, hr2, hiso⟩
      · exact Bclass.iso hiso.symm (Bclass.expansion J hJ)
      · subst hn
        exact Bclass.iso hiso.symm
          (Bclass.union (ih _ h1 F₁ hr1 rfl) (ih _ h2 F₂ hr2 rfl))
      · subst hn
        exact Bclass.iso hiso.symm
          (Bclass.amalg x y (ih _ h1 F₁ hr1 rfl) (ih _ h2 F₂ hr2 rfl))

/-! ### Adjoining isolated vertices -/

/-
`F.reduce` has no isolated vertices.
-/
theorem FTS.reduce_no_isolated (F : FTS) (v : F.reduce.V) : ¬ F.reduce.Isolated v := by
  simp +decide [ FTS.reduce ];
  cases v;
  unfold FTS.Isolated at *; aesop;

/-
The reduction of a `ReconOK`-input system is `ReconOK`.
-/
theorem reconOK_reduce (F : FTS) (hlin : F.Linear)
    (hbr : ∀ ed : {e : Finset F.V // e ∈ F.edges}, ∃ w ∈ ed.1, IsBridgeInc F w ed)
    (hev : ∀ c : BergeCycle F, Even c.m) : ReconOK F.reduce := by
  obtain ⟨hlinR, hbrR, hevR⟩ := (FTS.intrinsic_reduce_iff F).mp ⟨hlin, hbr, hev⟩;
  exact ⟨ hlinR, FTS.reduce_no_isolated F, hbrR, hevR ⟩

/-
Adjoining (or having) isolated vertices does not affect membership in `B`.
-/
theorem bclass_of_bclass_reduce (F : FTS) (h : Bclass F.reduce) : Bclass F := by
  -- Let $E$ be the edgeless FTS consisting of the isolated vertices of $F$.
  set E : FTS := ⟨{x : F.V // F.Isolated x}, ∅, by
    aesop⟩
  generalize_proofs at *;
  -- Let φ be the bijection between F.V and (F.reduce.V ⊕ E.V).
  obtain ⟨φ, hφ⟩ : ∃ φ : F.V ≃ F.reduce.V ⊕ E.V, ∀ x, φ x = if hx : ¬ F.Isolated x then Sum.inl ⟨x, hx⟩ else Sum.inr ⟨x, by
    exact Classical.not_not.mp hx⟩ := by
    refine' ⟨ _, _ ⟩;
    refine' Equiv.ofBijective ( fun x => if hx : ¬ F.Isolated x then Sum.inl ⟨ x, hx ⟩ else Sum.inr ⟨ x, by simpa using! hx ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩;
    all_goals norm_num at *;
    · grind;
    · rcases x with ( ⟨ x, hx ⟩ | ⟨ x, hx ⟩ ) <;> [ exact ⟨ x, by aesop ⟩ ; exact ⟨ x, by aesop ⟩ ]
  generalize_proofs at *;
  -- By definition of $φ$, we know that $e ∈ F.edges ↔ e.map φ.toEmbedding ∈ (F.reduce.disjUnion E).edges$.
  have h_iso : ∀ e : Finset F.V, e ∈ F.edges ↔ e.map φ.toEmbedding ∈ (F.reduce.disjUnion E).edges := by
    intro e;
    constructor <;> intro he;
    · have h_map : e.map φ.toEmbedding = (Finset.subtype (fun x => ¬ F.Isolated x) e).map Function.Embedding.inl := by
        ext z
        constructor
        · intro hz
          obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hz
          have hnv : ¬ F.Isolated v := FTS.not_isolated_of_mem he hv
          exact Finset.mem_map.mpr ⟨⟨v, hnv⟩, Finset.mem_subtype.mpr hv,
            by simp [hφ, hnv]; rfl⟩
        · intro hz
          obtain ⟨⟨v, hnv⟩, hv, rfl⟩ := Finset.mem_map.mp hz
          exact Finset.mem_map.mpr ⟨v, Finset.mem_subtype.mp hv,
            by simp [hφ, hnv]; rfl⟩
      simp [h_map, FTS.disjUnion];
      exact Or.inl <| FTS.subtype_edge_mem he;
    · unfold FTS.disjUnion at he; simp_all +decide [ Finset.mem_union, Finset.mem_image ] ;
      obtain ⟨ a, ha, he ⟩ | ⟨ a, ha, he ⟩ := he <;> simp_all +decide [ Finset.ext_iff ];
      · convert! FTS.reduce_edge_map_mem ha using 1;
        ext x; simp [he];
        grind;
      · aesop;
  apply Bclass.iso (by
  use φ.symm;
  intro e; specialize h_iso ( Finset.map φ.symm.toEmbedding e ) ; simp_all +decide [ Finset.map_map ] ;) (Bclass.union h (Bclass.edgeless E rfl))

/-! ### The finite bridge decomposition -/

/-- **Reverse direction of `prop:finite-decomposition`.**  If `F` is linear,
bridge-incident, and has only even Berge cycles, then `F ∈ B`. -/
theorem intrinsic_bclass (F : FTS) (h : F.IntrinsicObligatory) : Bclass F := by
  apply bclass_of_bclass_reduce
  exact bclass_of_reconOK F.reduce (reconOK_reduce F h.1 h.2.1 h.2.2)

/-- **Finite bridge decomposition** (`prop:finite-decomposition`): for every
finite triple system, membership in `B` is equivalent to the intrinsic bridge /
even-Berge-cycle condition on its reduction. -/
theorem finiteDecomposition_holds (F : FTS) :
    Bclass F ↔ F.reduce.IntrinsicObligatory :=
  ⟨fun h => (F.intrinsic_reduce_iff).mp (bclass_intrinsic h),
    fun h => intrinsic_bclass F ((F.intrinsic_reduce_iff).mpr h)⟩

end Erdos1177
