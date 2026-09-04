import Mathlib
import ErdosProblems.Erdos550.TauFineComponentRooting

set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A sum-type encoding of a τ-fine tree decomposition

The embedding layer uses a disjoint sum of skeleton and shrub vertices.  This
file supplies the exact combinatorial conversion for the indexed components of a
seed-deleted tree: seed vertices form the left summand, while the right summand
is the dependent sum of all component supports.  The resulting map is an
equivalence with the original vertex type.  It also chooses rooted parent/rank
data componentwise and transports all internal shrub edges to those parent
links.
-/

open SimpleGraph Finset

namespace Erdos550

open Classical

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Vertices belonging to the τ-fine seed set. -/
abbrev SeedVertex (S : Finset α) := {v : α // v ∈ S}

/-- The disjoint union of the supports of all nonseed components. -/
abbrev ShrubVertex (T : SimpleGraph α) (S : Finset α) :=
  Σ c : NonseedComponent T S, c.1.supp

/-- Forget the component label of a shrub vertex. -/
def ShrubVertex.val {T : SimpleGraph α} {S : Finset α} :
    ShrubVertex T S → α
  | ⟨_, v⟩ => v.1

lemma shrubVertex_val_not_mem
    (T : SimpleGraph α) (S : Finset α) (v : ShrubVertex T S) :
    v.val ∉ S := by
      by_contra h_contra;
      obtain ⟨c, hc⟩ : ∃ c : NonseedComponent T S, v.1 = c := by
        grind;
      obtain ⟨ v, hv ⟩ := v;
      have := componentNonseedVertices_eq_supp T S v; simp_all +decide ;
      replace this := Set.ext_iff.mp this hv; simp_all +decide [ componentNonseedVertices ] ;
      exact this ( by aesop ) h_contra

lemma shrubVertex_component_eq_of_val_eq
    (T : SimpleGraph α) (S : Finset α) {v w : ShrubVertex T S}
    (h : v.val = w.val) : v.1 = w.1 := by
      rcases v with ⟨ ⟨ c₁, hc₁ ⟩, v₁ ⟩ ; rcases w with ⟨ ⟨ c₂, hc₂ ⟩, v₂ ⟩ ; simp_all +decide [ ShrubVertex.val ];
      unfold nonseedComponents at hc₁ hc₂; aesop;

lemma shrubVertex_val_injective
    (T : SimpleGraph α) (S : Finset α) :
    Function.Injective (@ShrubVertex.val α _ _ T S) := by
      intro v w h; have := shrubVertex_component_eq_of_val_eq T S h; cases v; cases w; aesop;

/-- Seed vertices attached by a tree edge to a particular shrub vertex.  Unlike an
`Option`-valued anchor, this faithfully handles the case where one shrub vertex
is adjacent to several seeds. -/
noncomputable def shrubVertexSeeds
    (T : SimpleGraph α) (S : Finset α) (v : ShrubVertex T S) :
    Finset (SeedVertex S) :=
  Finset.univ.filter (fun s => T.Adj s.1 v.val)

@[simp] lemma mem_shrubVertexSeeds_iff
    (T : SimpleGraph α) (S : Finset α) (v : ShrubVertex T S)
    (s : SeedVertex S) :
    s ∈ shrubVertexSeeds T S v ↔ T.Adj s.1 v.val := by
  simp [shrubVertexSeeds]

lemma shrubVertexSeeds_card_le_seed_card
    (T : SimpleGraph α) (S : Finset α) (v : ShrubVertex T S) :
    (shrubVertexSeeds T S v).card ≤ S.card := by
      convert! Finset.card_le_univ ( shrubVertexSeeds T S v ) using 1 ; simp +decide [ Fintype.card_subtype ]

lemma componentSeeds_eq_biUnion_vertexSeeds
    (T : SimpleGraph α) (S : Finset α) (c : NonseedComponent T S) :
    componentSeeds T S c.1 =
      (Finset.univ.biUnion (fun v : c.1.supp =>
        (shrubVertexSeeds T S ⟨c, v⟩).image (fun s => s.1))) := by
          ext s;
          simp +decide [ componentSeeds, shrubVertexSeeds ];
          grind +locals

lemma shrubVertexSeeds_image_subset_componentSeeds
    (T : SimpleGraph α) (S : Finset α) (v : ShrubVertex T S) :
    (shrubVertexSeeds T S v).image (fun s => s.1) ⊆
      componentSeeds T S v.1.1 := by
        intro s hs;
        obtain ⟨ s, hs, rfl ⟩ := Finset.mem_image.mp hs;
        convert! Set.mem_setOf_eq.mpr _;
        convert! Finset.mem_filter.mpr _;
        exact ⟨ s.2, v.2, by simpa using! ‹s ∈ shrubVertexSeeds T S v› ⟩

lemma shrubVertexSeeds_card_le_componentSeeds
    (T : SimpleGraph α) (S : Finset α) (v : ShrubVertex T S) :
    (shrubVertexSeeds T S v).card ≤ (componentSeeds T S v.1.1).card := by
      refine' le_trans _ ( Finset.card_le_card <| shrubVertexSeeds_image_subset_componentSeeds T S v );
      rw [ Finset.card_image_of_injective _ fun x y hxy => by aesop ]

lemma shrubVertexSeeds_card_le_of_component_bound
    (T : SimpleGraph α) (S : Finset α) (r : ℕ)
    (hatt : ∀ c : NonseedComponent T S,
      (componentSeeds T S c.1).card ≤ r) :
    ∀ v : ShrubVertex T S, (shrubVertexSeeds T S v).card ≤ r := by
      exact fun v => le_trans ( shrubVertexSeeds_card_le_componentSeeds _ _ _ ) ( hatt _ )

/-- The canonical vertex map from the skeleton/shrub sum to the original tree. -/
def splitVertex (T : SimpleGraph α) (S : Finset α) :
    SeedVertex S ⊕ ShrubVertex T S → α
  | Sum.inl v => v.1
  | Sum.inr v => v.val

lemma splitVertex_injective (T : SimpleGraph α) (S : Finset α) :
    Function.Injective (splitVertex T S) := by
      intro x y hxy;
      cases x <;> cases y <;> simp_all +decide only [Sum.inr.injEq, reduceCtorEq];
      · rename_i x y;
        exact absurd ( shrubVertex_val_not_mem T S y ) ( by simp +decide [ ← hxy, x.2 ] );
      · rename_i x y;
        exact absurd hxy ( by exact fun h => by have := shrubVertex_val_not_mem T S x; aesop );
      · exact Sigma.ext ( by have := shrubVertex_component_eq_of_val_eq T S hxy; aesop ) ( by have := shrubVertex_val_injective T S hxy; aesop )

lemma splitVertex_surjective (T : SimpleGraph α) (S : Finset α) :
    Function.Surjective (splitVertex T S) := by
      -- For any vertex $v \in V$, we can split into two cases: $v \in S$ or $v \notin S$.
      intro v
      by_cases hv : v ∈ S;
      · exact ⟨ Sum.inl ⟨ v, hv ⟩, rfl ⟩;
      · exact ⟨ Sum.inr ⟨ nonseedComponentOf T S v hv, ⟨ v, mem_seedComponent_supp T S v ⟩ ⟩, rfl ⟩

/-- The exact equivalence between the decomposed sum and the original vertices. -/
noncomputable def treeSplitEquiv (T : SimpleGraph α) (S : Finset α) :
    SeedVertex S ⊕ ShrubVertex T S ≃ α :=
  Equiv.ofBijective (splitVertex T S)
    ⟨splitVertex_injective T S, splitVertex_surjective T S⟩

@[simp] lemma treeSplitEquiv_apply
    (T : SimpleGraph α) (S : Finset α)
    (x : SeedVertex S ⊕ ShrubVertex T S) :
    treeSplitEquiv T S x = splitVertex T S x := rfl

/-- Chosen componentwise parent map. -/
noncomputable def shrubParent
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α) :
    ShrubVertex T S → Option (ShrubVertex T S)
  | ⟨c, v⟩ =>
      ((exists_nonseedComponent_rooted_structure T hT S c).choose v).map
        (fun w => ⟨c, w⟩)

/-- Chosen componentwise rank. -/
noncomputable def shrubRank
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α) :
    ShrubVertex T S → ℕ
  | ⟨c, v⟩ =>
      (exists_nonseedComponent_rooted_structure T hT S c).choose_spec.choose v

lemma shrubParent_rank
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    {v w : ShrubVertex T S}
    (h : shrubParent T hT S v = some w) :
    shrubRank T hT S w < shrubRank T hT S v := by
      -- By definition of `shrubParent`, if `shrubParent T hT S v = some w`, then `w` is the parent of `v` in the nonseed component.
      obtain ⟨c, hc⟩ := v
      obtain ⟨d, hd⟩ := w
      simp [shrubParent] at h;
      obtain ⟨ a, ha, h₁, rfl, h₂ ⟩ := h; simp_all +decide [ shrubRank ] ;
      grind +suggestions

lemma shrubParent_adj_original
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    {v w : ShrubVertex T S}
    (h : shrubParent T hT S v = some w) :
    T.Adj v.val w.val := by
      obtain ⟨c, v⟩ := v
      obtain ⟨c', w⟩ := w
      simp [shrubParent] at h;
      obtain ⟨ a, ha, h₁, rfl, h₂ ⟩ := h; simp_all +decide [ ShrubVertex.val ] ;
      grind +suggestions

lemma shrub_adj_same_component
    (T : SimpleGraph α) (S : Finset α) {v w : ShrubVertex T S}
    (h : T.Adj v.val w.val) : v.1 = w.1 := by
      cases v ; cases w ; simp_all +decide;
      rename_i c₁ v₁ c₂ v₂;
      obtain ⟨c₁, hc₁⟩ := c₁
      obtain ⟨c₂, hc₂⟩ := c₂;
      have h_connected : (seedDeleted T S).Adj v₁.1 v₂.1 := by
        have h_connected : v₁.1 ∉ S ∧ v₂.1 ∉ S := by
          exact ⟨ shrubVertex_val_not_mem T S ⟨ ⟨ c₁, hc₁ ⟩, v₁ ⟩, shrubVertex_val_not_mem T S ⟨ ⟨ c₂, hc₂ ⟩, v₂ ⟩ ⟩;
        exact ⟨ h, fun hs => by have := v₁.2; aesop ⟩;
      grind +suggestions

lemma shrub_internal_edge_parent
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    {v w : ShrubVertex T S} (h : T.Adj v.val w.val) :
    shrubParent T hT S v = some w ∨ shrubParent T hT S w = some v := by
      cases v ; cases w;
      rename_i c v d w;
      have h_eq : c = d := by
        apply shrub_adj_same_component T S h;
      subst h_eq;
      have := Exists.choose_spec ( exists_nonseedComponent_rooted_structure T hT S c );
      convert! this.choose_spec.2.2 v w _;
      · unfold shrubParent; aesop;
      · unfold shrubParent; aesop;
      · convert! h using 1;
        convert! seedDeleted_adj_iff T S v w using 1;
        exact ⟨ fun h => ⟨ h, shrubVertex_val_not_mem T S ⟨ c, v ⟩, shrubVertex_val_not_mem T S ⟨ c, w ⟩ ⟩, fun h => h.1 ⟩

/-
Every edge of the original tree, expressed through the sum equivalence, is
seed--seed, internal to the rooted shrub forest, or seed--shrub.
-/
theorem treeSplit_edge_classification
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    {x y : SeedVertex S ⊕ ShrubVertex T S}
    (hxy : T.Adj (treeSplitEquiv T S x) (treeSplitEquiv T S y)) :
    (∃ a b : SeedVertex S, x = Sum.inl a ∧ y = Sum.inl b) ∨
    (∃ a b : ShrubVertex T S,
      (shrubParent T hT S a = some b ∨ shrubParent T hT S b = some a) ∧
      x = Sum.inr a ∧ y = Sum.inr b) ∨
    (∃ a : SeedVertex S, ∃ b : ShrubVertex T S,
      a ∈ shrubVertexSeeds T S b ∧
      ((x = Sum.inl a ∧ y = Sum.inr b) ∨
       (x = Sum.inr b ∧ y = Sum.inl a))) := by
        rcases x with ( x | x ) <;> rcases y with ( y | y );
        · exact Or.inl ⟨ x, y, rfl, rfl ⟩;
        · exact Or.inr <| Or.inr <| ⟨ x, y, by simpa using! hxy, Or.inl ⟨ rfl, rfl ⟩ ⟩;
        · exact Or.inr <| Or.inr <| ⟨ y, x, by simpa [SimpleGraph.adj_comm] using! hxy, by tauto ⟩;
        · have := shrub_internal_edge_parent T hT S hxy; aesop;

/-
The seed-induced forest admits parent/rank data classifying all seed--seed
edges.  It is obtained by restricting a rooted structure of the original tree;
a seed's parent is kept exactly when that parent is also a seed.
-/
theorem exists_seed_rooted_structure
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α) :
    ∃ (parent : SeedVertex S → Option (SeedVertex S))
      (rank : SeedVertex S → ℕ),
      (∀ a b, parent a = some b → rank b < rank a) ∧
      (∀ a b, parent a = some b → T.Adj a.1 b.1) ∧
      (∀ a b, T.Adj a.1 b.1 →
        parent a = some b ∨ parent b = some a) := by
          obtain ⟨ parent0, rank0, hparent0, hrank0 ⟩ := IsTree.exists_rooted_edge_structure T hT;
          refine' ⟨ fun a => Option.bind ( parent0 a ) fun b => if hb : b ∈ S then some ⟨ b, hb ⟩ else none, fun a => rank0 a, _, _, _ ⟩ <;> simp +decide only [Subtype.forall];
          · grind +suggestions;
          · intro a ha b hb h; cases h' : parent0 a <;> aesop;
          · grind

/-
Final combinatorial gluing interface for a τ-fine decomposition.  If a host
contains injective, disjoint maps of the seeds and shrub vertices respecting the
chosen forest links and every recorded seed attachment, then it contains the
original tree.
-/
theorem tauFine_split_maps_embed
    {V : Type*} [DecidableEq V]
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree) (S : Finset α)
    (G : SimpleGraph V)
    (parentSk : SeedVertex S → Option (SeedVertex S))
    (hparentSk : ∀ a b, T.Adj a.1 b.1 →
      parentSk a = some b ∨ parentSk b = some a)
    (fSk : SeedVertex S → V) (f : ShrubVertex T S → V)
    (hfSk : Function.Injective fSk) (hf : Function.Injective f)
    (hdisjoint : ∀ a, f a ∉ Finset.univ.image fSk)
    (hSkAdj : ∀ a b, parentSk a = some b → G.Adj (fSk a) (fSk b))
    (hShrubAdj : ∀ a b, shrubParent T hT S a = some b → G.Adj (f a) (f b))
    (hAnchor : ∀ a s, s ∈ shrubVertexSeeds T S a → G.Adj (fSk s) (f a)) :
    T ⊑ G := by
      -- Define the embedding map e : α → V by transporting the glued sum map through treeSplitEquiv.symm.
      set e : α → V := fun x => if hx : x ∈ S then fSk ⟨x, hx⟩ else f ⟨nonseedComponentOf T S x (by
      exact hx), ⟨x, by
        rfl⟩⟩
      generalize_proofs at *;
      have he_adj : ∀ x y : α, T.Adj x y → G.Adj (e x) (e y) := by
        intro x y hxy
        simp [e];
        split_ifs with hx hy;
        · cases hparentSk ⟨ x, hx ⟩ ⟨ y, hy ⟩ hxy <;> [ exact hSkAdj _ _ ‹_›; exact SimpleGraph.Adj.symm ( hSkAdj _ _ ‹_› ) ];
        · convert! hAnchor _ _ _;
          simp +decide [ shrubVertexSeeds ];
          exact hxy;
        · convert! hAnchor ⟨ nonseedComponentOf T S x hx, ⟨ x, by
            grind +qlia ⟩ ⟩ ⟨ y, by assumption ⟩ _ |> SimpleGraph.Adj.symm using 1
          generalize_proofs at *;
          simp +decide [ shrubVertexSeeds ];
          exact hxy.symm;
        · have h_parent : shrubParent T hT S ⟨nonseedComponentOf T S x hx, ⟨x, by
            grind⟩⟩ = some ⟨nonseedComponentOf T S y ‹_›, ⟨y, by
            grind +qlia⟩⟩ ∨ shrubParent T hT S ⟨nonseedComponentOf T S y ‹_›, ⟨y, by
            grind +qlia⟩⟩ = some ⟨nonseedComponentOf T S x hx, ⟨x, by
            grind⟩⟩ := by
            convert! shrub_internal_edge_parent T hT S _;
            exact hxy
          generalize_proofs at *;
          cases h_parent <;> [ exact hShrubAdj _ _ ‹_›; exact SimpleGraph.Adj.symm ( hShrubAdj _ _ ‹_› ) ];
      have he_inj : Function.Injective e := by
        intro x y hxy;
        grind;
      refine' ⟨ _, _ ⟩;
      use e;
      exact he_inj


/-- The component label of a shrub vertex. -/
def shrubComponent (T : SimpleGraph α) (S : Finset α) :
    ShrubVertex T S → NonseedComponent T S
  | ⟨c, _⟩ => c

lemma shrubComponent_surjective (T : SimpleGraph α) (S : Finset α) :
    Function.Surjective (shrubComponent T S) := by
      intro c;
      obtain ⟨v, hv⟩ : ∃ v : α, v ∈ c.1.supp := by
        have := componentNonseedVertices_nonempty T S c; simp_all +decide only [ConnectedComponent.mem_supp_iff];
        obtain ⟨ v, hv ⟩ := this; use v; simp_all +decide [ componentNonseedVertices ] ;
      exact ⟨ ⟨ c, ⟨ v, hv ⟩ ⟩, rfl ⟩

lemma shrubComponent_fiber_card
    (T : SimpleGraph α) (S : Finset α) (c : NonseedComponent T S) :
    (Finset.univ.filter (fun v : ShrubVertex T S => shrubComponent T S v = c)).card =
      (componentNonseedVertices T S c.1).card := by
        refine' Finset.card_bij ( fun v hv => v.val ) _ _ _ <;> simp +decide only [mem_filter, mem_univ, true_and, exists_prop, Sigma.exists, Subtype.exists,
    ConnectedComponent.mem_supp_iff];
        · intro a ha
          simp [componentNonseedVertices];
          exact ⟨ shrubVertex_val_not_mem T S a, by aesop ⟩;
        · grind +locals;
        · intro b hb
          obtain ⟨a, ha⟩ : ∃ a : c.1.supp, a.1 = b := by
            unfold componentNonseedVertices at hb; aesop;
          aesop

/-
The shrub sum has exactly the number of nonseed vertices.
-/
lemma shrubVertex_card (T : SimpleGraph α) (S : Finset α) :
    Fintype.card (ShrubVertex T S) = Fintype.card α - S.card := by
      rw [ ← Fintype.card_congr ( treeSplitEquiv T S ) ];
      simp +decide [ SeedVertex ]

omit [Fintype α] [DecidableEq α] in
@[simp] lemma seedVertex_card (S : Finset α) :
    Fintype.card (SeedVertex S) = S.card := by
      convert! Fintype.card_coe S using 1

lemma split_type_card (T : SimpleGraph α) (S : Finset α) :
    Fintype.card (SeedVertex S ⊕ ShrubVertex T S) = Fintype.card α := by
      fapply Fintype.card_congr;
      exact Classical.choice <| show Nonempty ( SeedVertex S ⊕ ShrubVertex T S ≃ α ) from by
        have := @treeSplitEquiv α _ _ T S
        exact ⟨this⟩

lemma shrubComponent_attachment_card_le
    (T : SimpleGraph α) (S : Finset α) (r : ℕ)
    (hatt : ∀ c : NonseedComponent T S,
      (componentSeeds T S c.1).card ≤ r) :
    ∀ c : NonseedComponent T S,
      (Finset.univ.biUnion (fun v : c.1.supp =>
        (shrubVertexSeeds T S ⟨c, v⟩).image (fun s => s.1))).card ≤ r := by
          intro c;
          convert! hatt c using 1;
          rw [ componentSeeds_eq_biUnion_vertexSeeds ]

/-
Exact total shrub mass grouped by component labels.
-/
lemma sum_shrubComponent_fiber_card
    (T : SimpleGraph α) (S : Finset α) :
    (∑ c : NonseedComponent T S,
      (Finset.univ.filter (fun v : ShrubVertex T S =>
        shrubComponent T S v = c)).card) = Fintype.card α - S.card := by
          rw [ ← shrubVertex_card T S, Finset.sum_congr rfl fun c hc => Finset.card_filter _ _ ];
          rw [ Finset.sum_comm ] ; aesop

/-
Fully bundled sum-typed τ-fine decomposition ready for the abstract embedding
layer: a small seed skeleton, small component fibres, bounded attachment sets,
rooted seed and shrub forests, exact mass, and complete edge classification.
-/
theorem tree_tau_fine_split_data
    (T : SimpleGraph α) [DecidableRel T.Adj] (hT : T.IsTree)
    (τ : ℝ) (hτ : 0 < τ)
    (hn : (1 : ℝ) ≤ τ * Fintype.card α) :
    ∃ S : Finset α,
      (S.card : ℝ) ≤ 1 / τ ∧
      Fintype.card (ShrubVertex T S) = Fintype.card α - S.card ∧
      (∀ c : NonseedComponent T S,
        ((Finset.univ.filter (fun v : ShrubVertex T S =>
          shrubComponent T S v = c)).card : ℝ) ≤ τ * Fintype.card α) ∧
      (∀ c : NonseedComponent T S,
        (Finset.univ.biUnion (fun v : c.1.supp =>
          (shrubVertexSeeds T S ⟨c, v⟩).image (fun s => s.1))).card
            ≤ Nat.floor (1 / τ)) ∧
      (∃ (parentSk : SeedVertex S → Option (SeedVertex S))
        (rankSk : SeedVertex S → ℕ),
        (∀ a b, parentSk a = some b → rankSk b < rankSk a) ∧
        (∀ a b, parentSk a = some b → T.Adj a.1 b.1) ∧
        (∀ a b, T.Adj a.1 b.1 →
          parentSk a = some b ∨ parentSk b = some a)) ∧
      (∀ a b, shrubParent T hT S a = some b →
        shrubRank T hT S b < shrubRank T hT S a) ∧
      (∀ a b, shrubParent T hT S a = some b → T.Adj a.val b.val) ∧
      (∀ a b : ShrubVertex T S, T.Adj a.val b.val →
        shrubParent T hT S a = some b ∨ shrubParent T hT S b = some a) := by
          obtain ⟨ S, hS₁, hS₂, hS₃, hS₄, hS₅, hS₆ ⟩ := tree_tau_fine_indexed_data T hT τ hτ hn;
          refine' ⟨ S, hS₁, _, _, _, _, _ ⟩;
          · convert! shrubVertex_card T S using 1;
          · intro c; specialize hS₂ c; simp_all +decide [ shrubComponent_fiber_card ] ;
          · exact fun c => shrubComponent_attachment_card_le T S _ hS₃ c;
          · exact exists_seed_rooted_structure T hT S;
          · exact ⟨ fun a b hab => shrubParent_rank T hT S hab, fun a b hab => shrubParent_adj_original T hT S hab, fun a b hab => shrub_internal_edge_parent T hT S hab ⟩

end Erdos550
