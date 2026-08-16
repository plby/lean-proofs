import Mathlib.Data.Fin.Tuple.Finset
import Wikipedia.SzemeredisTheorem.Hypergraph.CoarseConfigurationCounting
import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleFiltration
import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleIndicatorDuplication

/-!
# The ordered configuration as an initial hypergraph bundle

The generalized bundle counting lemma starts from the bundle having one
occurrence vertex above each vertex class.  Its edges are the empty edge
and the ranges of all positive ordered faces.  This file identifies that
initial bundle, its indicator weights, and its main-density product with
the ordered-configuration objects used by the removal argument.

The only small bookkeeping issue is that an ordered face is an increasing
map `Fin n ↪o Fin k`, whereas a bundle edge is a `Finset (Fin k)`.  A
nonempty finite set has a unique increasing enumeration, supplied by
`Finset.orderEmbOfFin`; the equivalence below packages this canonical
change of indices.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-! ## Positive ordered faces as nonempty finite edges -/

/-- The (unordered) range edge of a positive ordered face. -/
def positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    Finset (Fin k) :=
  Finset.univ.map e.face.toEmbedding

@[simp]
theorem positiveOrderedFaceEdge_card
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card = e.rank := by
  simp [positiveOrderedFaceEdge, PositiveOrderedFace.rank]

theorem positiveOrderedFaceEdge_nonempty
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).Nonempty := by
  apply Finset.card_pos.mp
  rw [positiveOrderedFaceEdge_card]
  exact e.rank_pos

theorem positiveOrderedFaceEdge_card_le
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    (positiveOrderedFaceEdge e).card ≤ r := by
  rw [positiveOrderedFaceEdge_card]
  unfold PositiveOrderedFace.rank
  omega

@[simp]
theorem mem_positiveOrderedFaceEdge
    {k r : ℕ} (e : PositiveOrderedFace k r)
    (v : Fin k) :
    v ∈ positiveOrderedFaceEdge e ↔
      v ∈ Set.range e.face := by
  simp [positiveOrderedFaceEdge]

/-- The positive ordered face obtained by increasingly enumerating a
nonempty edge of cardinality at most `r`. -/
noncomputable def positiveOrderedFaceOfEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    PositiveOrderedFace k r := by
  let j : Fin r :=
    ⟨t.card - 1, by
      have htcard : 0 < t.card :=
        Finset.card_pos.mpr ht
      omega⟩
  refine ⟨j, ?_⟩
  have hcard : t.card = j.1 + 1 := by
    dsimp [j]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact t.orderEmbOfFin hcard

@[simp]
theorem positiveOrderedFaceEdge_ofEdge
    {k r : ℕ} (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r) :
    positiveOrderedFaceEdge
        (positiveOrderedFaceOfEdge t ht htr) = t := by
  simp [positiveOrderedFaceEdge,
    positiveOrderedFaceOfEdge]
  exact Finset.map_orderEmbOfFin_univ t _

/-- Passing from a positive ordered face to its range edge is injective:
an increasing enumeration of a finite linearly ordered set is unique. -/
theorem positiveOrderedFaceEdge_injective
    {k r : ℕ} :
    Function.Injective
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)) := by
  intro e f hef
  have hrank : e.rank = f.rank := by
    rw [← positiveOrderedFaceEdge_card e,
      ← positiveOrderedFaceEdge_card f, hef]
  rcases e with ⟨je, e⟩
  rcases f with ⟨jf, f⟩
  simp only [PositiveOrderedFace.rank] at hrank
  have hj : je = jf := by
    apply Fin.ext
    omega
  subst jf
  have hrange : Set.range e = Set.range f := by
    ext v
    have hv :=
      congrArg
        (fun s : Finset (Fin k) => v ∈ s) hef
    simpa [positiveOrderedFaceEdge] using hv
  have hef' : e = f :=
    (OrderEmbedding.range_inj).mp hrange
  subst f
  rfl

@[simp]
theorem positiveOrderedFaceOfEdge_edge
    {k r : ℕ} (e : PositiveOrderedFace k r) :
    positiveOrderedFaceOfEdge
        (positiveOrderedFaceEdge e)
        (positiveOrderedFaceEdge_nonempty e)
        (positiveOrderedFaceEdge_card_le e) = e := by
  apply positiveOrderedFaceEdge_injective
  exact positiveOrderedFaceEdge_ofEdge
    (positiveOrderedFaceEdge e)
    (positiveOrderedFaceEdge_nonempty e)
    (positiveOrderedFaceEdge_card_le e)

/-- Nonempty bundle edges of size at most `r`. -/
abbrev PositiveOrderedBundleEdge (k r : ℕ) :=
  {t : Finset (Fin k) // t.Nonempty ∧ t.card ≤ r}

/-- Canonical equivalence between positive ordered faces and nonempty
finite edges of size at most `r`. -/
noncomputable def positiveOrderedFaceEdgeEquiv
    (k r : ℕ) :
    PositiveOrderedFace k r ≃
      PositiveOrderedBundleEdge k r where
  toFun e :=
    ⟨positiveOrderedFaceEdge e,
      positiveOrderedFaceEdge_nonempty e,
      positiveOrderedFaceEdge_card_le e⟩
  invFun t :=
    positiveOrderedFaceOfEdge t.1 t.2.1 t.2.2
  left_inv e :=
    positiveOrderedFaceOfEdge_edge e
  right_inv t := by
    apply Subtype.ext
    exact positiveOrderedFaceEdge_ofEdge
      t.1 t.2.1 t.2.2

/-! ## The complete initial bundle -/

/-- The base hypergraph consisting of the empty edge and every positive
ordered edge of rank at most `r`. -/
noncomputable def orderedConfigurationBaseEdges
    (k r : ℕ) : Finset (Finset (Fin k)) :=
  insert ∅
    (Finset.univ.image
      (positiveOrderedFaceEdge :
        PositiveOrderedFace k r → Finset (Fin k)))

@[simp]
theorem empty_mem_orderedConfigurationBaseEdges
    (k r : ℕ) :
    ∅ ∈ orderedConfigurationBaseEdges k r := by
  simp [orderedConfigurationBaseEdges]

theorem empty_not_mem_positiveOrderedFaceEdge_image
    (k r : ℕ) :
    (∅ : Finset (Fin k)) ∉
      Finset.univ.image
        (positiveOrderedFaceEdge :
          PositiveOrderedFace k r → Finset (Fin k)) := by
  intro h
  obtain ⟨e, _he, hedge⟩ :=
    Finset.mem_image.mp h
  exact (positiveOrderedFaceEdge_nonempty e).ne_empty
    hedge

/-- The explicit edge family is exactly the family of subsets of
cardinality at most `r`. -/
@[simp]
theorem mem_orderedConfigurationBaseEdges_iff
    {k r : ℕ} (t : Finset (Fin k)) :
    t ∈ orderedConfigurationBaseEdges k r ↔
      t.card ≤ r := by
  constructor
  · intro ht
    rw [orderedConfigurationBaseEdges,
      Finset.mem_insert] at ht
    rcases ht with rfl | ht
    · simp
    · obtain ⟨e, _he, rfl⟩ :=
        Finset.mem_image.mp ht
      exact positiveOrderedFaceEdge_card_le e
  · intro htr
    by_cases ht0 : t = ∅
    · subst t
      exact empty_mem_orderedConfigurationBaseEdges k r
    · have ht : t.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr ht0
      rw [orderedConfigurationBaseEdges,
        Finset.mem_insert]
      right
      apply Finset.mem_image.mpr
      refine
        ⟨positiveOrderedFaceOfEdge t ht htr,
          Finset.mem_univ _, ?_⟩
      exact positiveOrderedFaceEdge_ofEdge t ht htr

/-- The initial bundle has one occurrence vertex above each base vertex
and uses the identity projection. -/
noncomputable def orderedConfigurationInitialBundle
    (k r : ℕ) :
    HypergraphBundle (Fin k) (Fin k)
      (orderedConfigurationBaseEdges k r) where
  edges := orderedConfigurationBaseEdges k r
  projection := id
  projection_injective_on_edge := by
    intro g hg x hx y hy hxy
    exact hxy
  projection_mem_base := by
    intro g hg
    simpa using hg

@[simp]
theorem orderedConfigurationInitialBundle_edges
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).edges =
      orderedConfigurationBaseEdges k r :=
  rfl

@[simp]
theorem orderedConfigurationInitialBundle_projection
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).projection =
      id :=
  rfl

theorem orderedConfigurationInitialBundle_closed
    (k r : ℕ) :
    (orderedConfigurationInitialBundle k r).IsClosedUnderInclusion := by
  intro g hg f hfg
  rw [orderedConfigurationInitialBundle_edges] at hg ⊢
  rw [mem_orderedConfigurationBaseEdges_iff] at hg ⊢
  exact (Finset.card_le_card hfg).trans hg

/-! ## Canonical local tuples and base weights -/

/-- Reindex a tuple on a nonempty finite edge by its increasing
enumeration. -/
noncomputable def orderedConfigurationEdgeTuple
    {G : Type*} {k r : ℕ}
    (t : Finset (Fin k))
    (ht : t.Nonempty) (htr : t.card ≤ r)
    (y : {v : Fin k // v ∈ t} → G) :
    Fin ((positiveOrderedFaceOfEdge t ht htr).lowerRank.1 + 1) → G := by
  let e := positiveOrderedFaceOfEdge t ht htr
  have hcard : t.card = e.lowerRank.1 + 1 := by
    dsimp [e, positiveOrderedFaceOfEdge]
    have htcard : 0 < t.card :=
      Finset.card_pos.mpr ht
    omega
  exact fun i => y (t.orderIsoOfFin hcard i)

/-- The increasing order isomorphism of a positive face range recovers
the original ordered-face coordinate. -/
@[simp]
theorem positiveOrderedFaceEdge_orderIsoOfFin_val
    {k r : ℕ} (e : PositiveOrderedFace k r)
    (i : Fin (e.lowerRank.1 + 1)) :
    ((positiveOrderedFaceEdge e).orderIsoOfFin
        (by
          simp [PositiveOrderedFace.rank]) i).1 =
      e.face i := by
  rw [Finset.coe_orderIsoOfFin_apply]
  have hcanonical :
      e.face =
        (positiveOrderedFaceEdge e).orderEmbOfFin
          (by
            simp [PositiveOrderedFace.rank]) := by
    apply Finset.orderEmbOfFin_unique'
    intro q
    simp [positiveOrderedFaceEdge]
  exact congrArg (fun f => f i) hcanonical.symm

/-- Indicator base weights corresponding to a closed ordered atom
configuration.  The empty edge and irrelevant edges carry weight one. -/
noncomputable def orderedConfigurationBaseWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseEdgeWeight (Fin k) G := by
  classical
  intro t y
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact configurationFaceWeight A
        (positiveOrderedFaceOfEdge t ht htr)
        (orderedConfigurationEdgeTuple t ht htr y)
    · exact 1
  · exact 1

@[simp]
theorem orderedConfigurationBaseWeight_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (y : {v : Fin k // v ∈ (∅ : Finset (Fin k))} → G) :
    orderedConfigurationBaseWeight A ∅ y = 1 := by
  simp [orderedConfigurationBaseWeight]

/-- On the range of a positive face, the canonical edge tuple is the
usual ordered-face tuple. -/
@[simp]
theorem orderedConfigurationBaseWeight_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (y :
      {v : Fin k // v ∈ positiveOrderedFaceEdge e} → G) :
    orderedConfigurationBaseWeight A
        (positiveOrderedFaceEdge e) y =
      configurationFaceWeight A e
        (fun i =>
          y ⟨e.face i,
            (mem_positiveOrderedFaceEdge e
              (e.face i)).2 ⟨i, rfl⟩⟩) := by
  classical
  simp only [orderedConfigurationBaseWeight,
    dif_pos (positiveOrderedFaceEdge_nonempty e),
    dif_pos (positiveOrderedFaceEdge_card_le e)]
  change
    (fun p :
        (Σ f : PositiveOrderedFace k r,
          Fin (f.lowerRank.1 + 1) → G) =>
      configurationFaceWeight A p.1 p.2)
        ⟨positiveOrderedFaceOfEdge
            (positiveOrderedFaceEdge e)
            (positiveOrderedFaceEdge_nonempty e)
            (positiveOrderedFaceEdge_card_le e),
          orderedConfigurationEdgeTuple
            (positiveOrderedFaceEdge e)
            (positiveOrderedFaceEdge_nonempty e)
            (positiveOrderedFaceEdge_card_le e) y⟩ =
      (fun p :
          (Σ f : PositiveOrderedFace k r,
            Fin (f.lowerRank.1 + 1) → G) =>
        configurationFaceWeight A p.1 p.2)
          ⟨e, fun i =>
            y ⟨e.face i,
              (mem_positiveOrderedFaceEdge e
                (e.face i)).2 ⟨i, rfl⟩⟩⟩
  apply congrArg
    (fun p :
        (Σ f : PositiveOrderedFace k r,
          Fin (f.lowerRank.1 + 1) → G) =>
      configurationFaceWeight A p.1 p.2)
  have he :
      positiveOrderedFaceOfEdge
          (positiveOrderedFaceEdge e)
          (positiveOrderedFaceEdge_nonempty e)
          (positiveOrderedFaceEdge_card_le e) = e :=
    positiveOrderedFaceOfEdge_edge e
  apply Sigma.ext he
  simp only
  apply Function.hfunext
    (congrArg
      (fun f : PositiveOrderedFace k r =>
        Fin (f.lowerRank.1 + 1)) he)
  intro i i' hii
  apply heq_of_eq
  unfold orderedConfigurationEdgeTuple
  apply congrArg y
  apply Subtype.ext
  have hn :
      (positiveOrderedFaceOfEdge
          (positiveOrderedFaceEdge e)
          (positiveOrderedFaceEdge_nonempty e)
          (positiveOrderedFaceEdge_card_le e)).lowerRank.1 + 1 =
        e.lowerRank.1 + 1 :=
    congrArg (fun f : PositiveOrderedFace k r =>
      f.lowerRank.1 + 1) he
  have hval : i.1 = i'.1 := by
    have hcast :
        cast (congrArg Fin hn) i = i' := by
      exact eq_of_heq
        ((cast_heq (congrArg Fin hn) i).trans hii)
    calc
      i.1 = (cast (congrArg Fin hn) i).1 := by
        symm
        have hcastVal :
            ∀ {m n : ℕ} (h : m = n) (a : Fin m),
              (cast (congrArg Fin h) a).1 = a.1 := by
          intro m n h a
          cases h
          rfl
        exact hcastVal hn i
      _ = i'.1 := congrArg Fin.val hcast
  rw [Finset.coe_orderIsoOfFin_apply]
  calc
    (positiveOrderedFaceEdge e).orderEmbOfFin _ i =
        (positiveOrderedFaceEdge e).orderEmbOfFin _ i' :=
      Finset.orderEmbOfFin_eq_orderEmbOfFin_iff.mpr hval
    _ = e.face i' := by
      simpa only [Finset.coe_orderIsoOfFin_apply] using
        positiveOrderedFaceEdge_orderIsoOfFin_val e i'

/-- The configuration indicator weights take values in the unit
interval on the whole base hypergraph. -/
theorem orderedConfigurationBaseWeight_unitInterval
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseWeightsInUnitInterval
      (orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A) := by
  intro t ht y
  unfold orderedConfigurationBaseWeight
  by_cases ht0 : t.Nonempty
  · simp only [dif_pos ht0]
    by_cases htr : t.card ≤ r
    · simp only [dif_pos htr]
      exact
        ⟨configurationFaceWeight_nonneg A _ _,
          configurationFaceWeight_le_one A _ _⟩
    · simp [htr]
  · simp [ht0]

/-- The configuration base weights are pointwise idempotent, as required
when duplicate bundle edges are identified. -/
theorem orderedConfigurationBaseWeight_idempotent
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    HypergraphBundle.BaseWeightsIdempotent
      (orderedConfigurationBaseEdges k r)
      (orderedConfigurationBaseWeight A) := by
  intro t ht y
  unfold orderedConfigurationBaseWeight
  by_cases ht0 : t.Nonempty
  · simp only [dif_pos ht0]
    by_cases htr : t.card ≤ r
    · simp only [dif_pos htr]
      simpa [configurationFaceWeight, pow_two] using
        (partitionAtomIndicator_sq
          (C.partition
            (positiveOrderedFaceOfEdge t ht0 htr).lowerRank.succ
            (positiveOrderedFaceOfEdge t ht0 htr).face)
          (A.atom
            (positiveOrderedFaceOfEdge t ht0 htr).lowerRank.succ
            (positiveOrderedFaceOfEdge t ht0 htr).face)
          (orderedConfigurationEdgeTuple t ht0 htr y))
    · simp [htr]
  · simp [ht0]

/-! ## Main densities -/

/-- The base main density attached to a mixed coarse configuration.  As
for the weight, the empty and irrelevant edges carry the neutral value
one. -/
noncomputable def orderedConfigurationBaseDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    Finset (Fin k) → ℝ := by
  classical
  intro t
  by_cases ht : t.Nonempty
  · by_cases htr : t.card ≤ r
    · exact mixedConfigurationCoarseDensity P A
        (positiveOrderedFaceOfEdge t ht htr)
    · exact 1
  · exact 1

@[simp]
theorem orderedConfigurationBaseDensity_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    orderedConfigurationBaseDensity P A ∅ = 1 := by
  simp [orderedConfigurationBaseDensity]

@[simp]
theorem orderedConfigurationBaseDensity_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r) :
    orderedConfigurationBaseDensity P A
        (positiveOrderedFaceEdge e) =
      mixedConfigurationCoarseDensity P A e := by
  classical
  unfold orderedConfigurationBaseDensity
  simp only [dif_pos (positiveOrderedFaceEdge_nonempty e)]
  have hcard :
      (positiveOrderedFaceEdge e).card ≤ r := by
    simpa [positiveOrderedFaceEdge_card] using
      positiveOrderedFaceEdge_card_le e
  simp only [dif_pos hcard]
  exact congrArg (mixedConfigurationCoarseDensity P A)
    (positiveOrderedFaceOfEdge_edge e)

theorem orderedConfigurationBaseDensity_unitInterval
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    ∀ t ∈ orderedConfigurationBaseEdges k r,
      0 ≤ orderedConfigurationBaseDensity P A t ∧
        orderedConfigurationBaseDensity P A t ≤ 1 := by
  intro t ht
  unfold orderedConfigurationBaseDensity
  by_cases ht0 : t.Nonempty
  · simp only [dif_pos ht0]
    by_cases htr : t.card ≤ r
    · simp only [dif_pos htr]
      exact
        ⟨mixedConfigurationCoarseDensity_nonneg P A _,
          mixedConfigurationCoarseDensity_le_one P A _⟩
    · simp [htr]
  · simp [ht0]

/-! ## Exact initial count and product identities -/

/-- With the identity projection, transporting an edge tuple to the base
edge does not change any of its values. -/
theorem orderedConfigurationInitialBundle_projectedEdgeTuple
    {G : Type*} {k r : ℕ}
    {g : Finset (Fin k)}
    (hg :
      g ∈ (orderedConfigurationInitialBundle k r).edges)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).projectedEdgeTuple hg
          (HypergraphBundle.edgeTuple g x) =
      fun j => x j.1 := by
  funext j
  have hj :
      (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 := by
    have happly :=
      congrArg Subtype.val
        (((orderedConfigurationInitialBundle k r).projectionEquiv hg).apply_symm_apply j)
    change
      (orderedConfigurationInitialBundle k r).projection
          (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 at happly
    change
      (((orderedConfigurationInitialBundle k r).projectionEquiv hg).symm j).1 =
        j.1 at happly
    exact happly
  unfold HypergraphBundle.projectedEdgeTuple
    HypergraphBundle.edgeTuple
  exact congrArg x hj

theorem orderedConfigurationInitialBundle_pullback_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) ∅
          (HypergraphBundle.edgeTuple ∅ x) = 1 := by
  rw [(orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A)
      (empty_mem_orderedConfigurationBaseEdges k r)]
  exact orderedConfigurationBaseWeight_empty A _

/-- A positive-face factor in the pulled-back initial bundle is exactly
the corresponding selected atom indicator. -/
theorem orderedConfigurationInitialBundle_pullback_positiveOrderedFaceEdge
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (e : PositiveOrderedFace k r)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)
          (positiveOrderedFaceEdge e)
          (HypergraphBundle.edgeTuple
            (positiveOrderedFaceEdge e) x) =
      configurationFaceWeight A e
        (orderedFaceTuple e.face x) := by
  have hedge :
      positiveOrderedFaceEdge e ∈
        (orderedConfigurationInitialBundle k r).edges := by
    rw [orderedConfigurationInitialBundle_edges,
      mem_orderedConfigurationBaseEdges_iff]
    exact positiveOrderedFaceEdge_card_le e
  rw [(orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight_of_mem
    (orderedConfigurationBaseWeight A) hedge]
  have himage :
      (positiveOrderedFaceEdge e).image
          (orderedConfigurationInitialBundle k r).projection =
        positiveOrderedFaceEdge e := by
    simpa only [orderedConfigurationInitialBundle_projection] using
      (Finset.image_id :
        (positiveOrderedFaceEdge e).image id =
          positiveOrderedFaceEdge e)
  have hpair :
      (⟨(positiveOrderedFaceEdge e).image
            (orderedConfigurationInitialBundle k r).projection,
          (orderedConfigurationInitialBundle k r).projectedEdgeTuple
            hedge
            (HypergraphBundle.edgeTuple
              (positiveOrderedFaceEdge e) x)⟩ :
        Σ t : Finset (Fin k), ({j : Fin k // j ∈ t} → G)) =
      ⟨positiveOrderedFaceEdge e,
        HypergraphBundle.edgeTuple
          (positiveOrderedFaceEdge e) x⟩ := by
    apply Sigma.ext himage
    simp only
    apply Function.hfunext
      (congrArg
        (fun t : Finset (Fin k) =>
          {j : Fin k // j ∈ t}) himage)
    intro j j' hjj
    apply heq_of_eq
    rw [congrFun
      (orderedConfigurationInitialBundle_projectedEdgeTuple
        hedge x) j]
    apply congrArg x
    exact
      (Subtype.heq_iff_coe_eq
        (fun v : Fin k => by
          rw [himage])).1 hjj
  have hweight :=
    congrArg
      (fun p :
          (Σ t : Finset (Fin k),
            ({j : Fin k // j ∈ t} → G)) =>
        orderedConfigurationBaseWeight A p.1 p.2)
      hpair
  rw [hweight]
  rw [orderedConfigurationBaseWeight_positiveOrderedFaceEdge]
  apply congrArg (configurationFaceWeight A e)
  funext i
  rfl

/-- Pointwise, the product of all initial bundle factors is the full
ordered-configuration indicator. -/
theorem orderedConfigurationInitialBundle_bundleProduct
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (x : Fin k → G) :
    (orderedConfigurationInitialBundle k r).bundleProduct
        ((orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) x =
      partialConfigurationWeight A Finset.univ x := by
  classical
  change
    (∏ g ∈ (orderedConfigurationInitialBundle k r).edges,
      (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (HypergraphBundle.edgeTuple g x)) =
      partialConfigurationWeight A Finset.univ x
  rw [orderedConfigurationInitialBundle_edges]
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (positiveOrderedFaceEdge :
            PositiveOrderedFace k r → Finset (Fin k))),
      (orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (HypergraphBundle.edgeTuple g x)) =
      partialConfigurationWeight A Finset.univ x
  rw [
    Finset.prod_insert
      (empty_not_mem_positiveOrderedFaceEdge_image k r)]
  rw [orderedConfigurationInitialBundle_pullback_empty]
  simp only [one_mul]
  rw [Finset.prod_image
    positiveOrderedFaceEdge_injective.injOn]
  unfold partialConfigurationWeight
  apply Finset.prod_congr rfl
  intro e he
  exact
    orderedConfigurationInitialBundle_pullback_positiveOrderedFaceEdge
      A e x

/-- The normalized initial bundle count is exactly the full ordered
configuration count. -/
theorem orderedConfigurationInitialBundle_bundleCount
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C) :
    (orderedConfigurationInitialBundle k r).bundleCount
        ((orderedConfigurationInitialBundle k r).pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) =
      fullConfigurationCount A := by
  unfold HypergraphBundle.bundleCount
    fullConfigurationCount partialConfigurationCount
  apply congrArg mean
  funext x
  exact orderedConfigurationInitialBundle_bundleProduct A x

/-- The main product of the initial bundle is the product of all mixed
coarse densities; the extra empty-edge factor is one. -/
theorem orderedConfigurationInitialBundle_bundleMainProduct
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    (orderedConfigurationInitialBundle k r).bundleMainProduct
          (orderedConfigurationBaseDensity P A) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e := by
  classical
  change
    (∏ g ∈ (orderedConfigurationInitialBundle k r).edges,
      orderedConfigurationBaseDensity P A
        (g.image
          (orderedConfigurationInitialBundle k r).projection)) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e
  rw [orderedConfigurationInitialBundle_edges,
    orderedConfigurationInitialBundle_projection]
  simp only [Function.id_def, Finset.image_id']
  change
    (∏ g ∈ insert ∅
        (Finset.univ.image
          (positiveOrderedFaceEdge :
            PositiveOrderedFace k r → Finset (Fin k))),
      orderedConfigurationBaseDensity P A g) =
      ∏ e : PositiveOrderedFace k r,
        mixedConfigurationCoarseDensity P A e
  rw [
    Finset.prod_insert
      (empty_not_mem_positiveOrderedFaceEdge_image k r),
    orderedConfigurationBaseDensity_empty,
    one_mul]
  rw [Finset.prod_image
    positiveOrderedFaceEdge_injective.injOn]
  simp

end Wikipedia.SzemeredisTheorem
