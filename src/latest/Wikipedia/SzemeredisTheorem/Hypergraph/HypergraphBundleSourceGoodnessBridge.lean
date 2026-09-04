import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedFullBoundary
import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleConfigurationStep

/-!
# Source-full goodness supplies the bundle-localized defect bound

For a maximal nonempty occurrence edge of a closed bundle, projection is a
bijection onto the corresponding base edge.  Consequently its strict
occurrence boundary is just another indexing of all proper subsets of that
base edge.  The product of the configuration indicators on those subsets is
the indicator of the full lower atom used in `OrderedFullBoundary`.

This file makes that reindexing explicit.  It then transports the source-full
localized square estimate along the induced equivalence of tuple spaces.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## Tuple reindexing -/

/-- The canonical enumeration of the projected edge. -/
noncomputable def projectedEdgeOrderIso
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {j : Fin k // j ∈ g.image B.projection} := by
  let t := g.image B.projection
  let e := B.orderedConfigurationBundleFace hg hne
  have hcard : t.card = e.lowerRank.1 + 1 := by
    have hedge :
        positiveOrderedFaceEdge e = t := by
      dsimp [e, orderedConfigurationBundleFace, t]
      exact positiveOrderedFaceEdge_ofEdge
        (g.image B.projection)
        (B.projectedEdge_nonempty hg hne)
        (B.projectedEdge_card_le hg)
    calc
      t.card = (positiveOrderedFaceEdge e).card :=
        congrArg Finset.card hedge.symm
      _ = e.rank := positiveOrderedFaceEdge_card e
      _ = e.lowerRank.1 + 1 := rfl
  exact (t.orderIsoOfFin hcard).toEquiv

@[simp]
theorem projectedEdgeOrderIso_apply_val
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (i : Fin ((B.orderedConfigurationBundleFace
      hg hne).lowerRank.1 + 1)) :
    ((B.projectedEdgeOrderIso hg hne) i).1 =
      (B.orderedConfigurationBundleFace hg hne).face i := by
  rfl

/-- Reindex occurrence-edge assignments by the increasing enumeration of
their projected base edge. -/
noncomputable def orderedConfigurationBundleFaceTupleEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) → G) :=
  (Equiv.arrowCongr
      (B.projectionEquiv hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.projectedEdgeOrderIso hg hne).symm
      (Equiv.refl G))

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem orderedConfigurationBundleFaceTupleEquiv_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.orderedConfigurationBundleFaceTupleEquiv hg hne y =
      B.orderedConfigurationBundleFaceTuple hg hne y := by
  funext i
  unfold orderedConfigurationBundleFaceTupleEquiv
    orderedConfigurationBundleFaceTuple
    orderedConfigurationEdgeTuple projectedEdgeOrderIso
  rfl

/-! ## Proper subfaces -/

/-- The positive ambient face obtained from a proper positive local
subface. -/
def ambientPositiveFaceOfProperSubface
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    PositiveOrderedFace k r where
  lowerRank :=
    ⟨d.lowerRank.1,
      lt_trans d.lowerRank.2 e.lowerRank.2⟩
  face := orderedFullLowerAmbientFace e d

@[simp]
theorem ambientPositiveFaceOfProperSubface_rank
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    (ambientPositiveFaceOfProperSubface e d).rank = d.rank := by
  rfl

theorem ambientPositiveFaceOfProperSubface_edge_ssubset
    (e : PositiveOrderedFace k r)
    (d : ProperPositiveOrderedSubface e.lowerRank.1) :
    positiveOrderedFaceEdge
        (ambientPositiveFaceOfProperSubface e d) ⊂
      positiveOrderedFaceEdge e := by
  constructor
  · intro v hv
    rw [mem_positiveOrderedFaceEdge] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨d.face i, rfl⟩
  · intro h
    have hcard :=
      Finset.card_le_card h
    rw [positiveOrderedFaceEdge_card,
      positiveOrderedFaceEdge_card] at hcard
    exact
      (Nat.not_le_of_gt
        (properPositiveOrderedSubface_rank_lt_upper d)) hcard

/-- Every positive face whose range is a proper subset of `e` factors
uniquely through a proper positive local subface of `e`. -/
theorem exists_properPositiveOrderedSubface_of_edge_ssubset
    (e f : PositiveOrderedFace k r)
    (hfe :
      positiveOrderedFaceEdge f ⊂
        positiveOrderedFaceEdge e) :
    ∃ d : ProperPositiveOrderedSubface e.lowerRank.1,
      ambientPositiveFaceOfProperSubface e d = f := by
  have hrank : f.rank < e.rank := by
    rw [← positiveOrderedFaceEdge_card,
      ← positiveOrderedFaceEdge_card]
    exact Finset.card_lt_card hfe
  have hrange :
      Set.range f.face ⊆ Set.range e.face := by
    intro v hv
    rw [← mem_positiveOrderedFaceEdge] at hv ⊢
    exact hfe.1 hv
  choose q hq using fun i : Fin (f.lowerRank.1 + 1) =>
    hrange ⟨i, rfl⟩
  have hqmono : StrictMono q := by
    intro i j hij
    apply e.face.lt_iff_lt.mp
    rw [hq i, hq j]
    exact f.face.strictMono hij
  let dface : OrderedFace
      (e.lowerRank.1 + 1) (f.lowerRank.1 + 1) :=
    OrderEmbedding.ofStrictMono q hqmono
  have hdlt : f.lowerRank.1 < e.lowerRank.1 := by
    simpa [PositiveOrderedFace.rank] using hrank
  let d : ProperPositiveOrderedSubface e.lowerRank.1 :=
    ⟨⟨f.lowerRank.1, hdlt⟩, dface⟩
  refine ⟨d, ?_⟩
  apply positiveOrderedFaceEdge_injective
  apply Finset.Subset.antisymm
  · intro v hv
    rw [mem_positiveOrderedFaceEdge] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨i, (hq i).symm⟩
  · intro v hv
    rw [mem_positiveOrderedFaceEdge] at hv ⊢
    obtain ⟨i, rfl⟩ := hv
    exact ⟨i, hq i⟩

/-- The finite family of all positive ambient faces strictly below `e`. -/
noncomputable def orderedConfigurationStrictFaceFamily
    (e : PositiveOrderedFace k r) :
    Finset (PositiveOrderedFace k r) :=
  Finset.univ.filter fun f =>
    positiveOrderedFaceEdge f ⊂ positiveOrderedFaceEdge e

@[simp]
theorem mem_orderedConfigurationStrictFaceFamily
    (e f : PositiveOrderedFace k r) :
    f ∈ orderedConfigurationStrictFaceFamily e ↔
      positiveOrderedFaceEdge f ⊂ positiveOrderedFaceEdge e := by
  simp [orderedConfigurationStrictFaceFamily]

/-- Every positive immediate boundary is a proper positive subface. -/
theorem positiveOrderedFaceEdge_boundary_ssubset
    (e : PositiveOrderedFace k r)
    (hpos : 0 < e.lowerRank.1)
    (i : Fin (e.lowerRank.1 + 1)) :
    positiveOrderedFaceEdge (e.boundary hpos i) ⊂
      positiveOrderedFaceEdge e := by
  rcases e with ⟨⟨j, hjr⟩, eface⟩
  cases j with
  | zero =>
      simp at hpos
  | succ n =>
      constructor
      · intro v hv
        rw [mem_positiveOrderedFaceEdge] at hv ⊢
        obtain ⟨q, rfl⟩ := hv
        exact ⟨i.succAbove q, rfl⟩
      · intro h
        have hc := Finset.card_le_card h
        rw [positiveOrderedFaceEdge_card,
          positiveOrderedFaceEdge_card] at hc
        exact
          (Nat.not_le_of_gt
            ((⟨⟨n + 1, hjr⟩, eface⟩ :
                PositiveOrderedFace k r).boundary_rank_lt
              hpos i)) hc

/-! ## The full-lower atom as a strict-face product -/

/-- Extend a selected upper-face tuple by the configuration witness on
the complementary coordinates. -/
noncomputable def extendConfigurationFaceTuple
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    Fin k → G :=
  (splitOrderedFaceEquiv e.face).symm
    (y, orderedFaceComplementTuple e.face A.witness)

@[simp]
theorem orderedFaceTuple_extendConfigurationFaceTuple
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    orderedFaceTuple e.face
        (extendConfigurationFaceTuple P A e y) = y := by
  exact orderedFaceTuple_splitOrderedFaceEquiv_symm _ _ _

/-- Extending the canonical projected tuple recovers the original
occurrence-edge tuple at every projected vertex. -/
@[simp]
theorem extendConfigurationFaceTuple_projection
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G)
    (v : {v : K // v ∈ g}) :
    extendConfigurationFaceTuple P A
        (B.orderedConfigurationBundleFace hg hne)
        (B.orderedConfigurationBundleFaceTuple hg hne y)
        (B.projection v.1) =
      y v := by
  let j := B.projectionEquiv hg v
  let i :=
    (B.projectedEdgeOrderIso hg hne).symm j
  have hi :
      B.projectedEdgeOrderIso hg hne i = j :=
    (B.projectedEdgeOrderIso hg hne).apply_symm_apply j
  have hface :
      (B.orderedConfigurationBundleFace hg hne).face i =
        B.projection v.1 := by
    calc
      (B.orderedConfigurationBundleFace hg hne).face i =
          ((B.projectedEdgeOrderIso hg hne) i).1 := by
        rw [B.projectedEdgeOrderIso_apply_val]
      _ = j.1 := congrArg Subtype.val hi
      _ = B.projection v.1 := by
        exact B.projectionEquiv_apply_val hg v
  rw [← hface]
  change
    orderedFaceTuple
        (B.orderedConfigurationBundleFace hg hne).face
        (extendConfigurationFaceTuple P A
          (B.orderedConfigurationBundleFace hg hne)
          (B.orderedConfigurationBundleFaceTuple hg hne y)) i =
      y v
  rw [orderedFaceTuple_extendConfigurationFaceTuple]
  change
    B.projectedEdgeTuple hg y
        ((B.projectedEdgeOrderIso hg hne) i) =
      y v
  rw [hi]
  exact congrArg y
    ((B.projectionEquiv hg).symm_apply_apply v)

/-- Product form of the selected full-lower atom. -/
theorem sourceFullMixedBoundaryWeight_eq_strictFaceProduct
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (e : PositiveOrderedFace k r)
    (y : Fin (e.lowerRank.1 + 1) → G) :
    sourceFullMixedBoundaryWeight P A e y =
      partialConfigurationWeight A
        (orderedConfigurationStrictFaceFamily e)
        (extendConfigurationFaceTuple P A e y) := by
  classical
  let x := extendConfigurationFaceTuple P A e y
  have hxe : orderedFaceTuple e.face x = y :=
    orderedFaceTuple_extendConfigurationFaceTuple P A e y
  by_cases hy :
      y ∈ (orderedFullLowerBoundaryPartition P.coarse e).part
        (orderedFaceTuple e.face A.witness)
  · rw [show sourceFullMixedBoundaryWeight P A e y = 1 by
          exact partitionAtomIndicator_of_mem _ _ hy]
    unfold partialConfigurationWeight
    symm
    apply Finset.prod_eq_one
    intro f hf
    have hfe :
      positiveOrderedFaceEdge f ⊂
          positiveOrderedFaceEdge e :=
      (mem_orderedConfigurationStrictFaceFamily e f).1
        hf
    obtain ⟨d, rfl⟩ :=
      exists_properPositiveOrderedSubface_of_edge_ssubset e f hfe
    unfold configurationFaceWeight
    apply partitionAtomIndicator_of_mem
    have hd :=
      (mem_orderedFullLowerBoundaryPartition_part_iff
        P.coarse e
        (orderedFaceTuple e.face A.witness) y).1 hy |>.2 d
    change
      orderedFaceTuple
          (orderedFullLowerAmbientFace e d) x ∈
        (A.atom
          (orderedFullLowerComplexRank e d)
          (orderedFullLowerAmbientFace e d)).1
    rw [A.atom_eq_partitionAtomAt]
    change
      orderedFaceTuple d.face
          (orderedFaceTuple e.face x) ∈
        (P.coarse.partition
          (orderedFullLowerComplexRank e d)
          (orderedFullLowerAmbientFace e d)).part
          (orderedFaceTuple d.face
            (orderedFaceTuple e.face A.witness))
    rw [hxe]
    exact hd
  · rw [show sourceFullMixedBoundaryWeight P A e y = 0 by
          exact partitionAtomIndicator_of_not_mem _ _ hy]
    by_contra hprod
    have hprod' :
        partialConfigurationWeight A
            (orderedConfigurationStrictFaceFamily e) x ≠ 0 :=
      fun hz => hprod hz.symm
    have hall :
        ∀ f ∈ orderedConfigurationStrictFaceFamily e,
          configurationFaceWeight A f
              (orderedFaceTuple f.face x) ≠ 0 := by
      intro f hf
      exact Finset.prod_ne_zero_iff.mp
        (by simpa [partialConfigurationWeight] using hprod') f hf
    exfalso
    apply hy
    apply
      (mem_orderedFullLowerBoundaryPartition_part_iff
        P.coarse e
        (orderedFaceTuple e.face A.witness) y).2
    constructor
    · rw [mem_orderedBoundaryPartition_part_iff]
      intro i
      by_cases he0 : e.lowerRank.1 = 0
      · have hsub :
            eraseBoundaryCoordinate i y =
              eraseBoundaryCoordinate i
                (orderedFaceTuple e.face A.witness) :=
          by
            funext q
            have hq : q.1 < 0 := by
              simpa [he0] using q.2
            omega
        rw [hsub]
        exact
          (positiveFaceLowerLayer P.coarse e
            (eraseBoundaryFace e.face i)).mem_part
            (Finset.mem_univ _)
      · have hepos : 0 < e.lowerRank.1 :=
          Nat.pos_of_ne_zero he0
        let f := e.boundary hepos i
        have hfstrict :
            positiveOrderedFaceEdge f ⊂
              positiveOrderedFaceEdge e := by
          exact positiveOrderedFaceEdge_boundary_ssubset
            e hepos i
        have hfmem :
            f ∈ orderedConfigurationStrictFaceFamily e :=
          (mem_orderedConfigurationStrictFaceFamily e f).2 hfstrict
        have hfweight := hall f hfmem
        rw [← hxe]
        exact
          coarse_boundary_mem_of_coarse_configuration_weight_ne_zero
            P A e hepos i x hfweight
    · intro d
      let f := ambientPositiveFaceOfProperSubface e d
      have hfmem :
          f ∈ orderedConfigurationStrictFaceFamily e :=
        (mem_orderedConfigurationStrictFaceFamily e f).2
          (ambientPositiveFaceOfProperSubface_edge_ssubset e d)
      have hfweight := hall f hfmem
      unfold configurationFaceWeight at hfweight
      have hfatom :
          orderedFaceTuple f.face x ∈
            (A.atom f.lowerRank.succ f.face).1 := by
        by_contra hnot
        exact hfweight
          (partitionAtomIndicator_of_not_mem _ _ hnot)
      rw [A.atom_eq_partitionAtomAt] at hfatom
      change
        orderedFaceTuple
            (orderedFullLowerAmbientFace e d) x ∈
          (P.coarse.partition
            (orderedFullLowerComplexRank e d)
            (orderedFullLowerAmbientFace e d)).part
            (orderedFaceTuple
              (orderedFullLowerAmbientFace e d) A.witness)
        at hfatom
      simp only [orderedFaceTuple_orderedFullLowerAmbientFace]
        at hfatom
      simpa only [hxe] using hfatom

/-! ## Reindexing a closed bundle boundary -/

/-- Lift a projected subset back to the unique occurrence subedge inside
`g₀`. -/
def liftProjectedSubedge
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    Finset K :=
  g₀.filter fun v => B.projection v ∈ t

theorem liftProjectedSubedge_subset
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) (t : Finset (Fin k)) :
    B.liftProjectedSubedge g₀ t ⊆ g₀ := by
  exact Finset.filter_subset _ _

theorem image_liftProjectedSubedge
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (g₀ : Finset K) {t : Finset (Fin k)}
    (ht : t ⊆ g₀.image B.projection) :
    (B.liftProjectedSubedge g₀ t).image B.projection = t := by
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hv).2
  · intro hj
    obtain ⟨v, hvg, hvj⟩ :=
      Finset.mem_image.mp (ht hj)
    apply Finset.mem_image.mpr
    refine ⟨v, Finset.mem_filter.mpr ⟨hvg, ?_⟩, hvj⟩
    exact hvj ▸ hj

theorem liftProjectedSubedge_image_eq
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hgg₀ : g ⊆ g₀) :
    B.liftProjectedSubedge g₀
        (g.image B.projection) = g := by
  ext v
  constructor
  · intro hv
    have hvg₀ := (Finset.mem_filter.mp hv).1
    obtain ⟨w, hwg, hwv⟩ :=
      Finset.mem_image.mp (Finset.mem_filter.mp hv).2
    have hwg₀ : w ∈ g₀ := hgg₀ hwg
    have hwv' : w = v :=
      B.projection_injective_on_edge g₀ hg₀ hwg₀ hvg₀ hwv
    exact hwv' ▸ hwg
  · intro hv
    exact Finset.mem_filter.mpr
      ⟨hgg₀ hv,
        Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩

/-! The substantial pointwise identity. -/

theorem strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (y : {v : K // v ∈ g₀} → G) :
    B.strictBoundaryLocalProduct g₀
        (B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)) y =
      sourceFullMixedBoundaryWeight P A
        (B.orderedConfigurationBundleFace hg₀ hne)
        (B.orderedConfigurationBundleFaceTuple hg₀ hne y) := by
  classical
  let e := B.orderedConfigurationBundleFace hg₀ hne
  let u := B.orderedConfigurationBundleFaceTuple hg₀ hne y
  let x := extendConfigurationFaceTuple P A e u
  have heedge :
      positiveOrderedFaceEdge e =
        g₀.image B.projection := by
    dsimp [e, orderedConfigurationBundleFace]
    exact positiveOrderedFaceEdge_ofEdge
      (g₀.image B.projection)
      (B.projectedEdge_nonempty hg₀ hne)
      (B.projectedEdge_card_le hg₀)
  let z : EdgeComplement g₀ → G :=
    fun v => A.witness (B.projection v.1)
  let xK : K → G :=
    (splitEdgeEquiv g₀).symm (y, z)
  have hxK : edgeTuple g₀ xK = y := by
    exact edgeTuple_splitEdgeEquiv_symm g₀ y z
  have hlocalProduct :
      B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) y =
        (B.strictBoundary g₀).bundleProduct
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK := by
    calc
      B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) y =
        B.strictBoundaryLocalProduct g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A))
          (edgeTuple g₀ xK) := by
            rw [hxK]
      _ =
        (B.strictBoundary g₀).bundleProduct
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK :=
        B.strictBoundaryLocalProduct_edgeTuple g₀
          (B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A)) xK
  have hempty : ∅ ∈ (B.strictBoundary g₀).edges := by
    apply (B.mem_strictBoundary_edges g₀ ∅).2
    refine ⟨hclosed hg₀ (Finset.empty_subset g₀), ?_⟩
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.empty_subset _, hne.ne_empty.symm⟩
  have hemptyWeight :
      B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) ∅
          (edgeTuple ∅ xK) = 1 := by
    rw [B.pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A)
      ((B.mem_strictBoundary_edges g₀ ∅).1 hempty).1]
    exact orderedConfigurationBaseWeight_empty A _
  rw [hlocalProduct]
  rw [sourceFullMixedBoundaryWeight_eq_strictFaceProduct P A e u]
  unfold bundleProduct partialConfigurationWeight
  rw [← Finset.prod_erase_mul _ _ hempty,
    hemptyWeight, mul_one]
  apply Finset.prod_bij
    (fun g _hg =>
      positiveOrderedFaceOfEdge
        (g.image B.projection)
        (Finset.image_nonempty.mpr
          (Finset.nonempty_iff_ne_empty.mpr
            (Finset.mem_erase.mp _hg).1))
        (B.projectedEdge_card_le
          (((B.mem_strictBoundary_edges g₀ g).1
            (Finset.mem_of_mem_erase _hg)).1)))
  · intro g hg
    simp only [Finset.mem_erase] at hg
    rw [mem_orderedConfigurationStrictFaceFamily]
    rw [positiveOrderedFaceEdge_ofEdge]
    rw [heedge]
    have hgstrict :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).2
    constructor
    · intro j hj
      obtain ⟨v, hvg, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_image.mpr
        ⟨v, hgstrict.1 hvg, rfl⟩
    · intro hreverse
      apply hgstrict.2
      intro v hvg₀
      obtain ⟨w, hwg, hwv⟩ :=
        Finset.mem_image.mp
          (hreverse
            (Finset.mem_image.mpr
              ⟨v, hvg₀, rfl⟩))
      have hwg₀ : w ∈ g₀ := hgstrict.1 hwg
      have hwv' : w = v :=
        B.projection_injective_on_edge
          g₀ hg₀ hwg₀ hvg₀ hwv
      exact hwv' ▸ hwg
  · intro g₁ hg₁ g₂ hg₂ heq
    have himage :
        g₁.image B.projection =
          g₂.image B.projection := by
      simpa only [positiveOrderedFaceEdge_ofEdge] using
        congrArg positiveOrderedFaceEdge heq
    have hg₁sub :=
      ((B.mem_strictBoundary_edges g₀ g₁).1
        (Finset.mem_of_mem_erase hg₁)).2.1
    have hg₂sub :=
      ((B.mem_strictBoundary_edges g₀ g₂).1
        (Finset.mem_of_mem_erase hg₂)).2.1
    rw [← B.liftProjectedSubedge_image_eq hg₀ hg₁sub,
      ← B.liftProjectedSubedge_image_eq hg₀ hg₂sub,
      himage]
  · intro f hf
    have hfe :=
      (mem_orderedConfigurationStrictFaceFamily e f).1 hf
    let t := positiveOrderedFaceEdge f
    let g := B.liftProjectedSubedge g₀ t
    have ht : t ⊆ g₀.image B.projection := by
      simpa [e, orderedConfigurationBundleFace,
        positiveOrderedFaceEdge_ofEdge] using hfe.1
    have hgsub : g ⊆ g₀ :=
      B.liftProjectedSubedge_subset g₀ t
    have hgmem : g ∈ B.edges :=
      hclosed hg₀ hgsub
    have himage : g.image B.projection = t :=
      B.image_liftProjectedSubedge g₀ ht
    have hgne : g ≠ ∅ := by
      intro hzero
      have : t = ∅ := by simpa [hzero] using himage.symm
      have htne := positiveOrderedFaceEdge_nonempty f
      change t.Nonempty at htne
      rw [this] at htne
      exact Finset.not_nonempty_empty htne
    have hgproper : g ⊂ g₀ := by
      refine ⟨hgsub, ?_⟩
      intro hgg
      have hgeq : g = g₀ :=
        Finset.Subset.antisymm hgsub hgg
      have : t = g₀.image B.projection := by
        rw [← himage, hgeq]
      apply hfe.2
      rw [heedge, ← this]
    refine ⟨g, Finset.mem_erase.mpr
      ⟨hgne,
        (B.mem_strictBoundary_edges g₀ g).2
          ⟨hgmem, hgproper⟩⟩, ?_⟩
    apply positiveOrderedFaceEdge_injective
    simpa only [positiveOrderedFaceEdge_ofEdge] using himage
  · intro g hg
    simp only [Finset.mem_erase] at hg
    have hgB :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).1
    rw [B.pullbackBaseEdgeWeight_of_mem
      (orderedConfigurationBaseWeight A) hgB]
    unfold orderedConfigurationBaseWeight
    simp only [dif_pos (Finset.image_nonempty.mpr
      (Finset.nonempty_iff_ne_empty.mpr hg.1))]
    simp only [dif_pos (B.projectedEdge_card_le hgB)]
    congr 1
    have hgne : g.Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hg.1
    change
      B.orderedConfigurationBundleFaceTuple
          hgB hgne (edgeTuple g xK) =
        orderedFaceTuple
          (B.orderedConfigurationBundleFace hgB hgne).face x
    funext i
    let v : {v : K // v ∈ g} :=
      (B.projectionEquiv hgB).symm
        (B.projectedEdgeOrderIso hgB hgne i)
    have hgsub :
        g ⊆ g₀ :=
      ((B.mem_strictBoundary_edges g₀ g).1 hg.2).2.1
    let v₀ : {v : K // v ∈ g₀} :=
      ⟨v.1, hgsub v.2⟩
    have hprojection :
        (B.orderedConfigurationBundleFace hgB hgne).face i =
          B.projection v₀.1 := by
      calc
        (B.orderedConfigurationBundleFace hgB hgne).face i =
            (B.projectedEdgeOrderIso hgB hgne i).1 := by
          rw [B.projectedEdgeOrderIso_apply_val]
        _ = ((B.projectionEquiv hgB) v).1 := by
          rw [Equiv.apply_symm_apply]
        _ = B.projection v.1 :=
          B.projectionEquiv_apply_val hgB v
        _ = B.projection v₀.1 := rfl
    calc
      B.orderedConfigurationBundleFaceTuple
          hgB hgne (edgeTuple g xK) i =
          xK v.1 := by
        rfl
      _ = y v₀ := by
        have hv := congrFun hxK v₀
        exact hv
      _ = x (B.projection v₀.1) := by
        symm
        exact
          B.extendConfigurationFaceTuple_projection
            P A hg₀ hne y v₀
      _ =
          orderedFaceTuple
            (B.orderedConfigurationBundleFace hgB hgne).face
            x i := by
        rw [orderedFaceTuple, hprojection]

/-! ## Transport of the localized estimate -/

theorem strictBoundary_bundleCount_orderedConfiguration_eq_sourceFullMass
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    (hclosed : B.IsClosedUnderInclusion)
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty) :
    (B.strictBoundary g₀).bundleCount
        ((B.strictBoundary g₀).pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A)) =
      mean (sourceFullMixedBoundaryWeight P A
        (B.orderedConfigurationBundleFace hg₀ hne)) := by
  classical
  rw [← B.bundleCount_pullback_eq_of_subset_of_projection_eq
    (B.strictBoundary g₀)
    (Finset.filter_subset _ _)
    rfl
    (orderedConfigurationBaseWeight A)]
  cases isEmpty_or_nonempty G with
  | inl hG =>
      let : IsEmpty G := hG
      have : Nonempty K := ⟨hne.choose⟩
      have :
          Nonempty
            (Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1)) :=
        ⟨⟨0, Nat.succ_pos _⟩⟩
      simp only [bundleCount, mean_empty]
  | inr hG =>
      let : Nonempty G := hG
      unfold bundleCount
      rw [mean_splitEdge g₀]
      unfold mean₂
      have hfiber :
          ∀ y : {v : K // v ∈ g₀} → G,
            mean (fun z : EdgeComplement g₀ → G =>
                (B.strictBoundary g₀).bundleProduct
                  (B.pullbackBaseEdgeWeight
                    (orderedConfigurationBaseWeight A))
                  ((splitEdgeEquiv g₀).symm (y, z))) =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTupleEquiv
                  hg₀ hne y) := by
        intro y
        calc
          mean (fun z : EdgeComplement g₀ → G =>
              (B.strictBoundary g₀).bundleProduct
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A))
                ((splitEdgeEquiv g₀).symm (y, z))) =
              mean (fun _z : EdgeComplement g₀ → G =>
                B.strictBoundaryLocalProduct g₀
                  (B.pullbackBaseEdgeWeight
                    (orderedConfigurationBaseWeight A)) y) := by
            apply congrArg mean
            funext z
            rw [← B.strictBoundaryLocalProduct_edgeTuple g₀
              (B.pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A))
              ((splitEdgeEquiv g₀).symm (y, z))]
            rw [edgeTuple_splitEdgeEquiv_symm]
          _ =
              B.strictBoundaryLocalProduct g₀
                (B.pullbackBaseEdgeWeight
                  (orderedConfigurationBaseWeight A)) y := by
            exact mean_const _
          _ =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTuple hg₀ hne y) :=
            B.strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
              P A hclosed hg₀ hne y
          _ =
              sourceFullMixedBoundaryWeight P A
                (B.orderedConfigurationBundleFace hg₀ hne)
                (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne y) := by
            rw [orderedConfigurationBundleFaceTupleEquiv_apply]
      rw [show
        (fun y : {v : K // v ∈ g₀} → G =>
          mean (fun z : EdgeComplement g₀ → G =>
            (B.strictBoundary g₀).bundleProduct
              (B.pullbackBaseEdgeWeight
                (orderedConfigurationBaseWeight A))
              ((splitEdgeEquiv g₀).symm (y, z)))) =
          fun y =>
            sourceFullMixedBoundaryWeight P A
              (B.orderedConfigurationBundleFace hg₀ hne)
              (B.orderedConfigurationBundleFaceTupleEquiv
                hg₀ hne y) by
        funext y
        exact hfiber y]
      exact mean_equiv
        (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne)
        (fun y =>
          sourceFullMixedBoundaryWeight P A
            (B.orderedConfigurationBundleFace hg₀ hne)
            (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne y))
        (sourceFullMixedBoundaryWeight P A
          (B.orderedConfigurationBundleFace hg₀ hne))
        (fun _ => rfl)

/-- Source-full mixed goodness is exactly the weighted localization input
required by the generalized bundle-counting step. -/
theorem hasOrderedConfigurationBundleLocalizedDefect_of_sourceFullMixedGood
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (α β : ℕ → ℝ)
    (hgood : A.IsSourceFullMixedGood P α β) :
    HasOrderedConfigurationBundleLocalizedDefect P A β := by
  intro K _ _ B hclosed g₀ hg₀ hmax hne
  let e := B.orderedConfigurationBundleFace hg₀ hne
  have hrank : e.rank = g₀.card := by
    unfold e orderedConfigurationBundleFace
    rw [← positiveOrderedFaceEdge_card]
    rw [positiveOrderedFaceEdge_ofEdge]
    exact B.card_image_projection hg₀
  have hlocal := hgood.localized_defect P A α β e
  rw [← hrank]
  rw [B.strictBoundary_bundleCount_orderedConfiguration_eq_sourceFullMass
    P A hclosed hg₀ hne]
  calc
    mean (fun y =>
        B.orderedConfigurationBundleLocalizedDefect
            P A hg₀ hne y ^ 2) =
        sourceFullMixedLocalizedDefectSq P A e := by
      apply mean_equiv
        (B.orderedConfigurationBundleFaceTupleEquiv hg₀ hne)
      intro y
      unfold orderedConfigurationBundleLocalizedDefect
        orderedConfigurationBundleDefect
        sourceFullMixedDefect
      rw [B.strictBoundaryLocalProduct_orderedConfiguration_eq_sourceFull
        P A hclosed hg₀ hne y]
      rw [mul_pow, sourceFullMixedBoundaryWeight_sq]
      rw [orderedConfigurationBundleFaceTupleEquiv_apply]
    _ ≤
        β e.rank *
          mean (sourceFullMixedBoundaryWeight P A e) :=
      hlocal

end HypergraphBundle

end Wikipedia.SzemeredisTheorem
