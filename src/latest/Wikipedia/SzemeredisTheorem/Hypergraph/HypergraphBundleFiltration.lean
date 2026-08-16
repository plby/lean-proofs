import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleDuplication

/-!
# Filtrations of hypergraph bundles

The generalized counting argument repeatedly discards all edges of the
current maximal rank and then duplicates the remaining bundle around one
selected maximal edge.  This file packages the elementary structural
operations used in that step.

Besides arbitrary edge filtering, we single out the lower-order part of a
bundle and the strict boundary below a fixed edge.  The final product
identity records the only collisions caused by duplication: the two
labelled copies of a strict boundary edge coincide, whereas every other
lower-order edge contributes two distinct copies.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-! ## Edge-filtered subbundles -/

/-- Retain exactly the occurrence edges satisfying `P`. -/
def filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    HypergraphBundle J K H where
  edges := B.edges.filter P
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_filter.mp hg).1
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_filter.mp hg).1

@[simp]
theorem filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges = B.edges.filter P :=
  rfl

@[simp]
theorem mem_filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (g : Finset K) :
    g ∈ (B.filterEdges P).edges ↔
      g ∈ B.edges ∧ P g := by
  simp [filterEdges]

@[simp]
theorem filterEdges_projection
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).projection = B.projection :=
  rfl

/-- Edge filtering cannot increase bundle order. -/
theorem filterEdges_order_le
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).order ≤ B.order := by
  unfold order
  apply Finset.sup_le
  intro g hg
  exact B.edge_card_le_order
    (Finset.mem_filter.mp hg).1

/-- Edge filtering cannot increase the number of occurrence edges. -/
theorem card_filterEdges_edges_le
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges.card ≤ B.edges.card := by
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- A hereditary edge predicate preserves downward closure. -/
theorem filterEdges_closed
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (hclosed : B.IsClosedUnderInclusion)
    (hP : ∀ ⦃g⦄, P g →
      ∀ ⦃f⦄, f ⊆ g → P f) :
    (B.filterEdges P).IsClosedUnderInclusion := by
  intro g hg f hfg
  have hg' := (B.mem_filterEdges_edges P g).1 hg
  exact (B.mem_filterEdges_edges P f).2
    ⟨hclosed hg'.1 hfg, hP hg'.2 hfg⟩

/-! ## The lower-order and strict-boundary filtrations -/

/-- The subbundle consisting of edges whose cardinality is strictly below
`d`. -/
def lowerOrder
    (B : HypergraphBundle J K H) (d : ℕ) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g.card < d

@[simp]
theorem lowerOrder_edges
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl

@[simp]
theorem mem_lowerOrder_edges
    (B : HypergraphBundle J K H)
    (d : ℕ) (g : Finset K) :
    g ∈ (B.lowerOrder d).edges ↔
      g ∈ B.edges ∧ g.card < d := by
  simp [lowerOrder]

/-- For a positive cutoff, every edge in the lower-order subbundle has
order strictly below that cutoff, including when the subbundle is empty. -/
theorem lowerOrder_order_lt
    (B : HypergraphBundle J K H)
    {d : ℕ} (hd : 0 < d) :
    (B.lowerOrder d).order < d := by
  unfold order
  rw [Finset.sup_lt_iff hd]
  intro g hg
  exact (Finset.mem_filter.mp hg).2

theorem lowerOrder_order_le
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).order ≤ B.order :=
  B.filterEdges_order_le _

theorem card_lowerOrder_edges_le
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges.card ≤ B.edges.card :=
  B.card_filterEdges_edges_le _

theorem lowerOrder_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (d : ℕ) :
    (B.lowerOrder d).IsClosedUnderInclusion := by
  apply B.filterEdges_closed _ hclosed
  intro g hg f hfg
  exact (Finset.card_le_card hfg).trans_lt hg

/-- The strict-boundary subbundle below `g₀`. -/
def strictBoundary
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g ⊂ g₀

@[simp]
theorem strictBoundary_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl

@[simp]
theorem mem_strictBoundary_edges
    (B : HypergraphBundle J K H)
    (g₀ g : Finset K) :
    g ∈ (B.strictBoundary g₀).edges ↔
      g ∈ B.edges ∧ g ⊂ g₀ := by
  simp [strictBoundary]

theorem strictBoundary_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).order ≤ B.order :=
  B.filterEdges_order_le _

/-- A strict boundary has order below the size of its ambient edge. -/
theorem strictBoundary_order_lt
    (B : HypergraphBundle J K H)
    {g₀ : Finset K} (hg₀ : g₀.Nonempty) :
    (B.strictBoundary g₀).order < g₀.card := by
  unfold order
  rw [Finset.sup_lt_iff (Finset.card_pos.mpr hg₀)]
  intro g hg
  exact Finset.card_lt_card (Finset.mem_filter.mp hg).2

theorem card_strictBoundary_edges_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges.card ≤ B.edges.card :=
  B.card_filterEdges_edges_le _

theorem strictBoundary_closed
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    (g₀ : Finset K) :
    (B.strictBoundary g₀).IsClosedUnderInclusion := by
  apply B.filterEdges_closed _ hclosed
  intro g hg f hfg
  exact lt_of_le_of_lt hfg hg

/-! ## Main-density products -/

/-- Product of a base density over all occurrence edges of a bundle. -/
noncomputable def bundleMainProduct
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges, p (g.image B.projection)

@[simp]
theorem bundleMainProduct_filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (p : Finset J → ℝ) :
    (B.filterEdges P).bundleMainProduct p =
      ∏ g ∈ B.edges.filter P,
        p (g.image B.projection) :=
  rfl

@[simp]
theorem bundleMainProduct_lowerOrder
    (B : HypergraphBundle J K H)
    (d : ℕ) (p : Finset J → ℝ) :
    (B.lowerOrder d).bundleMainProduct p =
      ∏ g ∈ B.edges.filter (fun g => g.card < d),
        p (g.image B.projection) :=
  rfl

@[simp]
theorem bundleMainProduct_strictBoundary
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.strictBoundary g₀).bundleMainProduct p =
      ∏ g ∈ B.edges.filter (fun g => g ⊂ g₀),
        p (g.image B.projection) :=
  rfl

/-- Splitting a bundle product according to a decidable edge predicate. -/
theorem bundleMainProduct_filter_mul_filter_not
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (p : Finset J → ℝ) :
    (B.filterEdges P).bundleMainProduct p *
        (B.filterEdges fun g => ¬ P g).bundleMainProduct p =
      B.bundleMainProduct p := by
  classical
  exact Finset.prod_filter_mul_prod_filter_not
    (s := B.edges)
    (p := P)
    (f := fun g => p (g.image B.projection))

/-- Erasing one edge removes precisely its main-density factor. -/
theorem bundleMainProduct_eraseEdge_mul
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges) :
    (B.eraseEdge g₀).bundleMainProduct p *
        p (g₀.image B.projection) =
      B.bundleMainProduct p := by
  classical
  unfold bundleMainProduct
  simp only [eraseEdge]
  rw [Finset.prod_erase_mul _ _ hg₀]

/-! ## The main product under duplication -/

/-- A fixed labelled lift is injective on occurrence edges.  Forgetting
the doubled vertices is a left inverse. -/
theorem doubledEdge_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledEdge g₀ copy) := by
  intro g h hgh
  have himage :=
    congrArg
      (Finset.image (doubledVertexForget g₀)) hgh
  simpa using himage

/-- The doubled edge family is the union of the two fixed-copy images. -/
theorem doubledEdges_eq_image_union
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    B.doubledEdges g₀ =
      (B.edges.erase g₀).image
          (doubledEdge g₀ false) ∪
        (B.edges.erase g₀).image
          (doubledEdge g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    cases copy
    · exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨g, hg, rfl⟩)
  · intro hd
    rcases Finset.mem_union.mp hd with hd | hd
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.mem_doubledEdges_iff g₀ _).2
        ⟨false, g, hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hd
      exact (B.mem_doubledEdges_iff g₀ _).2
        ⟨true, g, hg, rfl⟩

/-- Removing the first-copy image from the second-copy image leaves
exactly those old edges which meet the complement of the shared edge. -/
theorem image_true_sdiff_image_false
    (g₀ : Finset K) (s : Finset (Finset K)) :
    s.image (doubledEdge g₀ true) \
        s.image (doubledEdge g₀ false) =
      (s.filter fun g => ¬ g ⊆ g₀).image
        (doubledEdge g₀ true) := by
  classical
  ext d
  constructor
  · intro hd
    have hdtrue :
        d ∈ s.image (doubledEdge g₀ true) :=
      (Finset.mem_sdiff.mp hd).1
    obtain ⟨g, hg, hgd⟩ :=
      Finset.mem_image.mp hdtrue
    subst d
    apply Finset.mem_image.mpr
    refine ⟨g, Finset.mem_filter.mpr ⟨hg, ?_⟩, rfl⟩
    intro hgsub
    apply (Finset.mem_sdiff.mp hd).2
    apply Finset.mem_image.mpr
    refine ⟨g, hg, ?_⟩
    exact
      (doubledEdge_copy_independent_of_subset
        g₀ hgsub false true)
  · intro hd
    obtain ⟨g, hg, hgd⟩ :=
      Finset.mem_image.mp hd
    subst d
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_image.mpr
      ⟨g, (Finset.mem_filter.mp hg).1, rfl⟩, ?_⟩
    intro hfalse
    obtain ⟨h, hh, hhg⟩ :=
      Finset.mem_image.mp hfalse
    have hgh : h = g := by
      have himage :=
        congrArg
          (Finset.image (doubledVertexForget g₀)) hhg
      simpa using himage
    subst h
    exact (Finset.mem_filter.mp hg).2
      ((doubledEdge_false_eq_true_iff_subset
        g₀ g).1 hhg)

/-- A fixed-copy image has the same projected main-density product as its
source edge family. -/
theorem prod_image_doubledEdge_main
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (copy : Bool)
    (s : Finset (Finset K))
    (p : Finset J → ℝ) :
    (∏ d ∈ s.image (doubledEdge g₀ copy),
        p (d.image (B.doubledProjection g₀))) =
      ∏ g ∈ s, p (g.image B.projection) := by
  classical
  rw [Finset.prod_image
    (doubledEdge_injective g₀ copy).injOn]
  simp

/-- General main-density product identity for duplication.  Edges
contained in `g₀` have only one actual doubled copy; all other remaining
edges have two. -/
theorem bundleMainProduct_duplicateOutside
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.duplicateOutside g₀).bundleMainProduct p =
      (∏ g ∈ (B.edges.erase g₀).filter
          (fun g => g ⊆ g₀),
        p (g.image B.projection)) *
      ∏ g ∈ (B.edges.erase g₀).filter
          (fun g => ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  let s := B.edges.erase g₀
  let first :=
    s.image (doubledEdge g₀ false)
  let second :=
    s.image (doubledEdge g₀ true)
  have hsplit :
      (∏ g ∈ s.filter (fun g => g ⊆ g₀),
          p (g.image B.projection)) *
          (∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) =
        ∏ g ∈ s, p (g.image B.projection) :=
    Finset.prod_filter_mul_prod_filter_not
      s (fun g => g ⊆ g₀)
        (fun g => p (g.image B.projection))
  calc
    (B.duplicateOutside g₀).bundleMainProduct p =
        ∏ d ∈ first ∪ second,
          p (d.image (B.doubledProjection g₀)) := by
      unfold bundleMainProduct first second
      simp only [duplicateOutside_edges,
        duplicateOutside_projection]
      rw [B.doubledEdges_eq_image_union g₀]
    _ = ∏ d ∈ first ∪ (second \ first),
          p (d.image (B.doubledProjection g₀)) := by
      rw [Finset.union_sdiff_self_eq_union]
    _ =
        (∏ d ∈ first,
          p (d.image (B.doubledProjection g₀))) *
        ∏ d ∈ second \ first,
          p (d.image (B.doubledProjection g₀)) := by
      exact Finset.prod_union Finset.disjoint_sdiff
    _ =
        (∏ g ∈ s, p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      unfold first second
      rw [image_true_sdiff_image_false]
      rw [B.prod_image_doubledEdge_main g₀ false]
      rw [B.prod_image_doubledEdge_main g₀ true]
    _ =
        ((∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            p (g.image B.projection)) *
        ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
          p (g.image B.projection) := by
      rw [hsplit]
    _ =
        (∏ g ∈ s.filter (fun g => g ⊆ g₀),
            p (g.image B.projection)) *
          ∏ g ∈ s.filter (fun g => ¬ g ⊆ g₀),
            (p (g.image B.projection)) ^ 2 := by
      rw [mul_assoc, ← Finset.prod_mul_distrib]
      simp only [pow_two]
    _ = _ := rfl

/-- **Lower-order duplication identity.**  Duplicating the lower-order
subbundle around `g₀` contributes one copy of every strict-boundary
density and the square of every other lower-order density. -/
theorem bundleMainProduct_duplicateOutside_lowerOrder
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    ((B.lowerOrder g₀.card).duplicateOutside g₀).bundleMainProduct p =
      (B.strictBoundary g₀).bundleMainProduct p *
      ∏ g ∈ B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀),
        (p (g.image B.projection)) ^ 2 := by
  classical
  rw [(B.lowerOrder g₀.card).bundleMainProduct_duplicateOutside g₀ p]
  have hg₀' :
      g₀ ∉ B.edges.filter (fun g => g.card < g₀.card) := by
    simp
  have hboundary :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => g ⊆ g₀) =
        B.edges.filter (fun g => g ⊂ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hgB, hgcard⟩, hgsub⟩
      exact ⟨hgB,
        Finset.ssubset_iff_subset_ne.mpr
          ⟨hgsub, fun hgeq => by
            subst g
            exact (Nat.lt_irrefl _ hgcard)⟩⟩
    · rintro ⟨hgB, hgstrict⟩
      exact ⟨⟨hgB,
        Finset.card_lt_card hgstrict⟩, hgstrict.1⟩
  have hexterior :
      (B.edges.filter (fun g => g.card < g₀.card)).filter
          (fun g => ¬ g ⊆ g₀) =
        B.edges.filter
          (fun g => g.card < g₀.card ∧ ¬ g ⊆ g₀) := by
    ext g
    simp only [Finset.mem_filter]
    tauto
  simp only [lowerOrder, strictBoundary,
    filterEdges, bundleMainProduct]
  rw [Finset.erase_eq_of_notMem hg₀',
    hboundary, hexterior]

end HypergraphBundle

end Wikipedia.SzemeredisTheorem
