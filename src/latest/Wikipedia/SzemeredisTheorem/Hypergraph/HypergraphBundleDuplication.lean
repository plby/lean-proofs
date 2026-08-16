import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleCounting

/-!
# Duplicating the variables outside one bundle edge

The squared remainder in the bundle counting argument identifies the
variables on a selected edge `g₀` and takes two independent copies of every
variable outside `g₀`.  This file realizes that operation as a finite
hypergraph bundle.

An occurrence vertex in the doubled bundle is either a shared vertex of
`g₀`, or an outside vertex together with a Boolean copy label.  Every
remaining occurrence edge is lifted once into each copy.  The lift is
injective, preserves edge cardinality and projected base edges, and
therefore produces another valid bundle over the same base hypergraph.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

/-- Occurrence vertices after identifying `g₀` and doubling its
complement. -/
abbrev DoubledOccurrenceVertex (g₀ : Finset K) :=
  {v : K // v ∈ g₀} ⊕ (Bool × EdgeComplement g₀)

/-- Forget the copy label of a doubled occurrence vertex. -/
def doubledVertexForget
    (g₀ : Finset K) :
    DoubledOccurrenceVertex g₀ → K
  | Sum.inl v => v.1
  | Sum.inr v => v.2.1

/-- Put an old occurrence vertex into one of the two copies, sharing it
when it lies in `g₀`. -/
def doubledVertexLift
    (g₀ : Finset K) (copy : Bool) (v : K) :
    DoubledOccurrenceVertex g₀ :=
  if hv : v ∈ g₀ then
    Sum.inl ⟨v, hv⟩
  else
    Sum.inr ⟨copy, ⟨v, hv⟩⟩

@[simp]
theorem doubledVertexForget_lift
    (g₀ : Finset K) (copy : Bool) (v : K) :
    doubledVertexForget g₀
        (doubledVertexLift g₀ copy v) = v := by
  by_cases hv : v ∈ g₀ <;>
    simp [doubledVertexLift, doubledVertexForget, hv]

/-- A fixed-copy lift is injective. -/
theorem doubledVertexLift_injective
    (g₀ : Finset K) (copy : Bool) :
    Function.Injective (doubledVertexLift g₀ copy) := by
  intro v w hvw
  have h :=
    congrArg (doubledVertexForget g₀) hvw
  simpa using h

/-- Assemble one assignment on the shared vertices and two assignments on
the outside vertices into an assignment on the doubled occurrence set. -/
def doubledAssignment
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    DoubledOccurrenceVertex g₀ → G
  | Sum.inl v => y v
  | Sum.inr (false, v) => z.1 v
  | Sum.inr (true, v) => z.2 v

/-- Splitting an assignment on the doubled occurrence set recovers exactly
one shared assignment and a pair of independent outside assignments. -/
def splitDoubledAssignmentEquiv
    (g₀ : Finset K) :
    (DoubledOccurrenceVertex g₀ → G) ≃
      (({v : K // v ∈ g₀} → G) ×
        ((EdgeComplement g₀ → G) ×
          (EdgeComplement g₀ → G))) where
  toFun x :=
    (fun v => x (Sum.inl v),
      (fun v => x (Sum.inr (false, v)),
        fun v => x (Sum.inr (true, v))))
  invFun p := doubledAssignment g₀ p.1 p.2
  left_inv x := by
    funext v
    rcases v with v | ⟨copy, v⟩
    · rfl
    · cases copy <;> rfl
  right_inv p := by
    rcases p with ⟨y, zfalse, ztrue⟩
    rfl

omit [DecidableEq K] in
@[simp]
theorem splitDoubledAssignmentEquiv_symm_apply
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    (splitDoubledAssignmentEquiv g₀).symm (y, z) =
      doubledAssignment g₀ y z :=
  rfl

/-- Fubini decomposition for the doubled occurrence variables. -/
theorem mean_splitDoubledAssignment
    [Fintype K] [Fintype G]
    (g₀ : Finset K)
    (f : (DoubledOccurrenceVertex g₀ → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          f (doubledAssignment g₀ y z)) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G)) =>
          f ((splitDoubledAssignmentEquiv g₀).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (splitDoubledAssignmentEquiv g₀)
      intro x
      simp
    _ = _ := by
      change
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G)) =>
          f (doubledAssignment g₀ p.1 p.2)) =
        _
      exact
        mean_prod_type
          (fun y : {v : K // v ∈ g₀} → G =>
            fun z :
              (EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G) =>
              f (doubledAssignment g₀ y z))

/-- On the first copy, a doubled assignment agrees with the ordinary
assignment assembled from the shared tuple and first outside tuple. -/
@[simp]
theorem doubledAssignment_lift_false
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ false v) =
      (splitEdgeEquiv g₀).symm (y, z.1) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dif_pos hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]
  · simp only [doubledVertexLift, dif_neg hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]

/-- On the second copy, a doubled assignment agrees with the ordinary
assignment assembled from the shared tuple and second outside tuple. -/
@[simp]
theorem doubledAssignment_lift_true
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ true v) =
      (splitEdgeEquiv g₀).symm (y, z.2) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dif_pos hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]
  · simp only [doubledVertexLift, dif_neg hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]

/-- Lift an old occurrence edge into one Boolean copy. -/
def doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    Finset (DoubledOccurrenceVertex g₀) :=
  g.image (doubledVertexLift g₀ copy)

theorem mem_doubledEdge
    (g₀ : Finset K) (copy : Bool)
    (g : Finset K) (v : K) (hv : v ∈ g) :
    doubledVertexLift g₀ copy v ∈
      doubledEdge g₀ copy g :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

/-- Forgetting a lifted edge recovers the original edge. -/
@[simp]
theorem image_forget_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (doubledVertexForget g₀) = g := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    have huv : u = v := by
      simpa using hwv
    exact huv ▸ hu
  · intro hv
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv, by simp⟩

/-- Lifting preserves edge cardinality. -/
@[simp]
theorem card_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).card = g.card := by
  rw [doubledEdge,
    Finset.card_image_of_injective _
      (doubledVertexLift_injective g₀ copy)]

/-- An edge wholly contained in the shared edge is unchanged by its copy
label.  This is the precise collision which prevents treating doubled
edges as a multiset-free bundle without an extra hypothesis. -/
theorem doubledEdge_copy_independent_of_subset
    (g₀ : Finset K) {g : Finset K}
    (hg : g ⊆ g₀) (copy copy' : Bool) :
    doubledEdge g₀ copy g =
      doubledEdge g₀ copy' g := by
  unfold doubledEdge
  apply Finset.image_congr
  intro v hv
  simp [doubledVertexLift, hg hv]

/-- A vertex outside `g₀` distinguishes the two Boolean copies of an
edge. -/
theorem doubledEdge_false_ne_true_of_mem_complement
    (g₀ : Finset K) {g : Finset K}
    {v : K} (hvg : v ∈ g) (hvoutside : v ∉ g₀) :
    doubledEdge g₀ false g ≠
      doubledEdge g₀ true g := by
  intro hedges
  have hv :
      doubledVertexLift g₀ false v ∈
        doubledEdge g₀ true g := by
    rw [← hedges]
    exact mem_doubledEdge g₀ false g v hvg
  obtain ⟨w, hwg, hwv⟩ :=
    Finset.mem_image.mp hv
  have hwv' : w = v := by
    have := congrArg
      (doubledVertexForget g₀) hwv
    simpa using this
  subst w
  simp [doubledVertexLift, hvoutside] at hwv

/-- The two labelled copies coincide exactly when the old edge has no
outside vertex. -/
theorem doubledEdge_false_eq_true_iff_subset
    (g₀ : Finset K) (g : Finset K) :
    doubledEdge g₀ false g =
        doubledEdge g₀ true g ↔
      g ⊆ g₀ := by
  constructor
  · intro hedges v hvg
    by_contra hvoutside
    exact
      doubledEdge_false_ne_true_of_mem_complement
        g₀ hvg hvoutside hedges
  · intro hg
    exact doubledEdge_copy_independent_of_subset
      g₀ hg false true

/-- Every old edge/copy pair which contributes an edge to the doubled
bundle. -/
abbrev DoubledEdgeSource
    (B : HypergraphBundle J K H) (g₀ : Finset K) :=
  Bool × {g : Finset K // g ∈ (B.edges.erase g₀)}

/-- The doubled edge belonging to one source edge and one copy. -/
def doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (s : B.DoubledEdgeSource g₀) :
    Finset (DoubledOccurrenceVertex g₀) :=
  doubledEdge g₀ s.1 s.2.1

/-- Product indexed by the two labelled copies of every remaining edge.
This source-indexed form retains multiplicity even before one proves that
distinct sources give distinct doubled `Finset` edges. -/
noncomputable def doubledSourceProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : DoubledOccurrenceVertex g₀ → G) : ℝ :=
  ∏ s : B.DoubledEdgeSource g₀,
    A s.2.1 (fun v =>
      x (doubledVertexLift g₀ s.1 v.1))

/-- The source-indexed product on an assembled doubled assignment is
exactly the product of the two remainder fibers. -/
theorem doubledSourceProduct_doubledAssignment
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    B.doubledSourceProduct g₀ A
        (doubledAssignment g₀ y z) =
      B.edgeRemainderFiber g₀ A y z.1 *
        B.edgeRemainderFiber g₀ A y z.2 := by
  classical
  unfold doubledSourceProduct
  rw [Fintype.prod_prod_type, Fintype.prod_bool]
  simp_rw [doubledAssignment_lift_true,
    doubledAssignment_lift_false]
  have hfalse :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (splitEdgeEquiv g₀).symm
            (y, z.1) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.1))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (edgeTuple g.1
            ((splitEdgeEquiv g₀).symm
              (y, z.1))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.1))))
  have htrue :
      (∏ g : {g : Finset K //
          g ∈ B.edges.erase g₀},
        A g.1 (fun v =>
          (splitEdgeEquiv g₀).symm
            (y, z.2) v.1)) =
        ∏ g ∈ B.edges.erase g₀,
          A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.2))) := by
    calc
      _ = ∏ g : {g : Finset K //
            g ∈ B.edges.erase g₀},
          A g.1 (edgeTuple g.1
            ((splitEdgeEquiv g₀).symm
              (y, z.2))) := by
        apply Finset.prod_congr rfl
        intro g _hg
        apply congrArg (A g.1)
        rfl
      _ = _ :=
        Finset.prod_coe_sort
          (B.edges.erase g₀)
          (fun g => A g (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              (y, z.2))))
  rw [htrue, hfalse]
  unfold edgeRemainderFiber edgeRemainder bundleProduct
  rw [mul_comm]
  rfl

/-- The doubled Cauchy--Schwarz moment is a single normalized mean over
assignments on the doubled occurrence-vertex set.  The integrand is the
source-indexed product, so the identity is valid even when the two copies
of an edge contained in `g₀` coincide as `Finset`s. -/
theorem doubledRemainderMoment_eq_mean_doubledSourceProduct
    [Fintype K] [Fintype G]
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) :
    B.doubledRemainderMoment g₀ A =
      mean (B.doubledSourceProduct g₀ A) := by
  rw [B.doubledRemainderMoment_eq_mean₂_pair]
  rw [mean_splitDoubledAssignment]
  simp_rw [B.doubledSourceProduct_doubledAssignment]

/-- The finite family of all lifted remaining edges.  Using an image
correctly identifies two lifted edges when all their vertices lie in the
shared selected edge. -/
def doubledEdges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    Finset (Finset (DoubledOccurrenceVertex g₀)) :=
  Finset.univ.image (B.doubledEdgeOfSource g₀)

theorem doubledEdgeOfSource_mem_doubledEdges
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (s : B.DoubledEdgeSource g₀) :
    B.doubledEdgeOfSource g₀ s ∈
      B.doubledEdges g₀ := by
  classical
  exact Finset.mem_image.mpr
    ⟨s, Finset.mem_univ s, rfl⟩

theorem mem_doubledEdges_iff
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (d : Finset (DoubledOccurrenceVertex g₀)) :
    d ∈ B.doubledEdges g₀ ↔
      ∃ (copy : Bool) (g : Finset K),
        g ∈ B.edges.erase g₀ ∧
          doubledEdge g₀ copy g = d := by
  classical
  constructor
  · intro hd
    obtain ⟨s, _hs, hsd⟩ :=
      Finset.mem_image.mp hd
    exact ⟨s.1, s.2.1, s.2.2, hsd⟩
  · rintro ⟨copy, g, hg, rfl⟩
    exact
      Finset.mem_image.mpr
        ⟨(copy, ⟨g, hg⟩), Finset.mem_univ _, rfl⟩

/-- The doubled occurrence projection forgets the copy label and then uses
the original bundle projection. -/
def doubledProjection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    DoubledOccurrenceVertex g₀ → J :=
  fun v => B.projection (doubledVertexForget g₀ v)

@[simp]
theorem doubledProjection_lift
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (copy : Bool) (v : K) :
    B.doubledProjection g₀
        (doubledVertexLift g₀ copy v) =
      B.projection v := by
  simp [doubledProjection]

/-- A lifted occurrence edge has the same projected base edge. -/
@[simp]
theorem image_doubledProjection_doubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (B.doubledProjection g₀) =
      g.image B.projection := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨w, hw, by simpa using hvj⟩
  · intro hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv,
          by simpa using hvj⟩

/-- The occurrence bundle obtained by identifying `g₀` and duplicating all
outside vertices and remaining edges. -/
def duplicateOutside
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J (DoubledOccurrenceVertex g₀) H where
  edges := B.doubledEdges g₀
  projection := B.doubledProjection g₀
  projection_injective_on_edge := by
    intro d hd v hv w hw hvw
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    obtain ⟨v₀, hv₀, rfl⟩ :=
      Finset.mem_image.mp hv
    obtain ⟨w₀, hw₀, rfl⟩ :=
      Finset.mem_image.mp hw
    apply congrArg (doubledVertexLift g₀ copy)
    apply B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg) hv₀ hw₀
    simpa using hvw
  projection_mem_base := by
    intro d hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    rw [image_doubledProjection_doubledEdge]
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)

@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl

@[simp]
theorem duplicateOutside_projection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).projection =
      B.doubledProjection g₀ :=
  rfl

/-- Every doubled edge has the cardinality of the source edge which
produced it. -/
theorem duplicateOutside_edge_card
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ∈ (B.duplicateOutside g₀).edges) :
    ∃ g ∈ B.edges.erase g₀, d.card = g.card := by
  obtain ⟨copy, g, hg, hgd⟩ :=
    (B.mem_doubledEdges_iff g₀ d).1 hd
  subst d
  exact ⟨g, hg, card_doubledEdge g₀ copy g⟩

/-- Duplication does not increase bundle order. -/
theorem duplicateOutside_order_le_eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).order ≤
      (B.eraseEdge g₀).order := by
  unfold order
  apply Finset.sup_le
  intro d hd
  obtain ⟨g, hg, hdg⟩ :=
    B.duplicateOutside_edge_card g₀ hd
  rw [hdg]
  exact (B.eraseEdge g₀).edge_card_le_order hg

/-- In particular, duplication does not increase the original order. -/
theorem duplicateOutside_order_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).order ≤ B.order :=
  (B.duplicateOutside_order_le_eraseEdge g₀).trans
    (B.eraseEdge_order_le g₀)

/-- There are at most two doubled occurrence edges for each remaining
source edge. -/
theorem card_doubledEdges_le
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.doubledEdges g₀).card ≤
      2 * (B.edges.erase g₀).card := by
  unfold doubledEdges
  calc
    (Finset.univ.image
        (B.doubledEdgeOfSource g₀)).card ≤
        (Finset.univ :
          Finset (B.DoubledEdgeSource g₀)).card :=
      Finset.card_image_le
    _ = 2 * (B.edges.erase g₀).card := by
      simp [DoubledEdgeSource]

/-- The condition under which the two copies of every remaining edge are
genuinely distinct: every such edge contains at least one vertex outside
the shared edge. -/
def RemainingEdgesMeetComplement
    (B : HypergraphBundle J K H) (g₀ : Finset K) : Prop :=
  ∀ g ∈ B.edges.erase g₀,
    ∃ v ∈ g, v ∉ g₀

/-- If every remaining edge meets the complement of `g₀`, then the source
edge together with its Boolean copy label is recoverable from its doubled
edge. -/
theorem doubledEdgeOfSource_injective
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀) :
    Function.Injective (B.doubledEdgeOfSource g₀) := by
  rintro ⟨copy, ⟨g, hg⟩⟩
    ⟨copy', ⟨g', hg'⟩⟩ hedges
  change
    doubledEdge g₀ copy g =
      doubledEdge g₀ copy' g' at hedges
  have hgg' : g = g' := by
    have himage :=
      congrArg
        (Finset.image (doubledVertexForget g₀))
        hedges
    simpa using himage
  subst g'
  have hcopy : copy = copy' := by
    obtain ⟨v, hvg, hvoutside⟩ :=
      houtside g hg
    have hv :
        doubledVertexLift g₀ copy v ∈
          doubledEdge g₀ copy' g := by
      rw [← hedges]
      exact mem_doubledEdge g₀ copy g v hvg
    obtain ⟨w, hwg, hwv⟩ :=
      Finset.mem_image.mp hv
    have hwv' : w = v := by
      have := congrArg
        (doubledVertexForget g₀) hwv
      simpa using this
    subst w
    simpa [doubledVertexLift, hvoutside] using
      hwv.symm
  subst copy'
  rfl

/-- When every remaining edge meets the complement, labelled source edges
are equivalent to the actual doubled occurrence edges. -/
noncomputable def doubledEdgeSourceEquiv
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀) :
    B.DoubledEdgeSource g₀ ≃
      {d : Finset (DoubledOccurrenceVertex g₀) //
        d ∈ B.doubledEdges g₀} := by
  classical
  apply Equiv.ofBijective
    (fun s =>
      ⟨B.doubledEdgeOfSource g₀ s,
        B.doubledEdgeOfSource_mem_doubledEdges
          g₀ s⟩)
  constructor
  · intro s t hst
    apply B.doubledEdgeOfSource_injective
      g₀ houtside
    exact congrArg Subtype.val hst
  · rintro ⟨d, hd⟩
    obtain ⟨s, _hs, hsd⟩ :=
      Finset.mem_image.mp hd
    refine ⟨s, ?_⟩
    apply Subtype.ext
    exact hsd

/-- The unique labelled source of an actual doubled edge. -/
noncomputable def sourceOfDoubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀)
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ∈ B.doubledEdges g₀) :
    B.DoubledEdgeSource g₀ :=
  (B.doubledEdgeSourceEquiv g₀ houtside).symm
    ⟨d, hd⟩

theorem doubledEdgeOfSource_sourceOfDoubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀)
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ∈ B.doubledEdges g₀) :
    B.doubledEdgeOfSource g₀
        (B.sourceOfDoubledEdge g₀ houtside hd) = d := by
  exact congrArg Subtype.val
    (Equiv.apply_symm_apply
      (B.doubledEdgeSourceEquiv g₀ houtside)
      ⟨d, hd⟩)

theorem sourceOfDoubledEdge_doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀)
    (s : B.DoubledEdgeSource g₀) :
    B.sourceOfDoubledEdge g₀ houtside
        (B.doubledEdgeOfSource_mem_doubledEdges
          g₀ s) = s := by
  exact
    Equiv.symm_apply_apply
      (B.doubledEdgeSourceEquiv g₀ houtside) s

/-- Under the complement condition, duplication creates exactly two
occurrence edges for every remaining occurrence edge. -/
theorem card_doubledEdges_eq
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (houtside : B.RemainingEdgesMeetComplement g₀) :
    (B.doubledEdges g₀).card =
      2 * (B.edges.erase g₀).card := by
  unfold doubledEdges
  rw [Finset.card_image_of_injective _
    (B.doubledEdgeOfSource_injective g₀ houtside)]
  simp [DoubledEdgeSource]

/-- A doubled edge is stable under lifting after forgetting its vertices. -/
theorem doubledEdge_image_forget_of_subset
    (g₀ : Finset K) (copy : Bool)
    {g : Finset K}
    {d : Finset (DoubledOccurrenceVertex g₀)}
    (hd : d ⊆ doubledEdge g₀ copy g) :
    doubledEdge g₀ copy
        (d.image (doubledVertexForget g₀)) = d := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ := Finset.mem_image.mp hw
    have huLift :
        doubledVertexLift g₀ copy
            (doubledVertexForget g₀ u) = u := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hu)
      simp
    rw [← hwv, ← huw, huLift]
    exact hu
  · intro hv
    have hvLift :
        doubledVertexLift g₀ copy
            (doubledVertexForget g₀ v) = v := by
      obtain ⟨t, ht, rfl⟩ :=
        Finset.mem_image.mp (hd hv)
      simp
    exact Finset.mem_image.mpr
      ⟨doubledVertexForget g₀ v,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩,
        hvLift⟩

/-- Downward closure is preserved whenever it is already available after
erasing the selected edge. -/
theorem duplicateOutside_closed
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (hclosed :
      (B.eraseEdge g₀).IsClosedUnderInclusion) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion := by
  intro d hd f hfd
  obtain ⟨copy, g, hg, rfl⟩ :=
    (B.mem_doubledEdges_iff g₀ d).1 hd
  let h : Finset K :=
    f.image (doubledVertexForget g₀)
  have hhg : h ⊆ g := by
    intro v hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, huw⟩ :=
      Finset.mem_image.mp (hfd hw)
    rw [← hwv, ← huw]
    simpa using hu
  have hh : h ∈ B.edges.erase g₀ :=
    hclosed hg hhg
  have hlift :
      doubledEdge g₀ copy h = f :=
    doubledEdge_image_forget_of_subset
      g₀ copy hfd
  rw [← hlift]
  exact
    (B.mem_doubledEdges_iff g₀
      (doubledEdge g₀ copy h)).2
      ⟨copy, h, hh, rfl⟩

/-- Erasing a maximum edge from a downward-closed bundle and then doubling
preserves downward closure. -/
theorem duplicateOutside_closed_of_maximal
    (B : HypergraphBundle J K H)
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card) :
    (B.duplicateOutside g₀).IsClosedUnderInclusion :=
  B.duplicateOutside_closed g₀
    (B.eraseEdge_closed_of_maximal
      hclosed hg₀ hmax)

end HypergraphBundle

end Wikipedia.SzemeredisTheorem
