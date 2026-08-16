import Wikipedia.SzemeredisTheorem.Hypergraph.HypergraphBundleFrozenUniformity

/-!
# Frozen bundle remainders are face cuts

Fix a maximum-cardinality nonempty occurrence edge `g₀`.  Every other
occurrence edge omits a vertex of `g₀`; we assign that edge to the
corresponding coordinate in the increasing enumeration of the projected
edge.  After the variables outside `g₀` are frozen, factors with the same
assigned coordinate form one member of a face-cut family.

The construction groups *occurrence* edges, rather than projected faces.
This is important because distinct occurrence edges in a bundle may have
the same projection.  The resulting product therefore retains every
factor with its correct multiplicity.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace HypergraphBundle

variable {G : Type*} [Fintype G] [DecidableEq G]
  {k r : ℕ}

/-! ## The canonical occurrence-edge ordering -/

/-- The increasing enumeration of the projected selected edge. -/
noncomputable def frozenProjectedEdgeOrderIso
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

/-- Increasing projected coordinates, lifted to their unique occurrence
vertices in the selected edge. -/
noncomputable def frozenOccurrenceOrderEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) ≃
      {v : K // v ∈ g} :=
  (B.frozenProjectedEdgeOrderIso hg hne).trans
    (B.projectionEquiv hg).symm

/-- Reindex selected-occurrence-edge tuples by their canonical projected
face coordinates. -/
noncomputable def frozenBundleFaceTupleEquiv
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty) :
    ({v : K // v ∈ g} → G) ≃
      (Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G) :=
  (Equiv.arrowCongr
      (B.projectionEquiv hg)
      (Equiv.refl G)).trans
    (Equiv.arrowCongr
      (B.frozenProjectedEdgeOrderIso hg hne).symm
      (Equiv.refl G))

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (y : {v : K // v ∈ g} → G) :
    B.frozenBundleFaceTupleEquiv hg hne y =
      B.orderedConfigurationBundleFaceTuple hg hne y := by
  funext i
  unfold frozenBundleFaceTupleEquiv frozenProjectedEdgeOrderIso
    orderedConfigurationBundleFaceTuple
    orderedConfigurationEdgeTuple
  rfl

omit [Fintype G] [DecidableEq G] in
@[simp]
theorem frozenBundleFaceTupleEquiv_symm_apply
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g : Finset K} (hg : g ∈ B.edges)
    (hne : g.Nonempty)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg hne).lowerRank.1 + 1) →
        G)
    (v : {v : K // v ∈ g}) :
    (B.frozenBundleFaceTupleEquiv hg hne).symm x v =
      x ((B.frozenOccurrenceOrderEquiv hg hne).symm v) := by
  rfl

/-! ## Assigning each remainder edge to a missing coordinate -/

/-- A totalized selected vertex omitted by a remainder occurrence edge.
The fallback branch is never used in the cut product. -/
noncomputable def frozenBundleMissingVertex
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K}
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (g : Finset K) : {v : K // v ∈ g₀} :=
  if hg : g ∈ B.edges.erase g₀ then
    ⟨Classical.choose
        (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax),
      (Classical.choose_spec
        (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax)).1⟩
  else
    ⟨Classical.choose hne, Classical.choose_spec hne⟩

theorem frozenBundleMissingVertex_not_mem
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K}
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀) :
    (B.frozenBundleMissingVertex hmax hne g).1 ∉ g := by
  classical
  simp only [frozenBundleMissingVertex, dif_pos hg]
  exact
    (Classical.choose_spec
      (B.exists_selectedVertex_not_mem_of_mem_erase hg hmax)).2

/-- Coordinate of the selected missing occurrence vertex. -/
noncomputable def frozenBundleMissingCoordinate
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (g : Finset K) :
    Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) :=
  (B.frozenOccurrenceOrderEquiv hg₀ hne).symm
    (B.frozenBundleMissingVertex hmax hne g)

theorem frozenOccurrenceOrder_missingCoordinate_not_mem
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀) :
    (B.frozenOccurrenceOrderEquiv hg₀ hne
      (B.frozenBundleMissingCoordinate hg₀ hmax hne g)).1 ∉ g := by
  unfold frozenBundleMissingCoordinate
  rw [(B.frozenOccurrenceOrderEquiv hg₀ hne).apply_symm_apply]
  exact B.frozenBundleMissingVertex_not_mem hmax hne hg

/-! ## Reconstructing and grouping a frozen remainder -/

/-- Insert an arbitrary value at one erased canonical face coordinate and
transport the resulting tuple back to the selected occurrence edge. -/
noncomputable def frozenBundleInsertedSelectedTuple
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (i :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1))
    (a : G)
    (y :
      Fin (B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 → G) :
    {v : K // v ∈ g₀} → G :=
  (B.frozenBundleFaceTupleEquiv hg₀ hne).symm
    (Fin.insertNth i a y)

/-- Recombine an inserted selected-edge tuple with the frozen outside
variables. -/
noncomputable def frozenBundleInsertedAssignment
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hne : g₀.Nonempty)
    (i :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1))
    (a : G)
    (y :
      Fin (B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 → G)
    (z : EdgeComplement g₀ → G) : K → G :=
  (splitEdgeEquiv g₀).symm
    (B.frozenBundleInsertedSelectedTuple hg₀ hne i a y, z)

omit [Fintype G] [DecidableEq G] in
theorem splitEdgeEquiv_symm_apply_of_mem
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G)
    {v : K} (hv : v ∈ g₀) :
    (splitEdgeEquiv g₀).symm (y, z) v = y ⟨v, hv⟩ := by
  have h :=
    congrFun (edgeTuple_splitEdgeEquiv_symm g₀ y z) ⟨v, hv⟩
  exact h

omit [Fintype G] [DecidableEq G] in
theorem splitEdgeEquiv_symm_apply_of_not_mem
    {K : Type*} [DecidableEq K]
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G)
    {v : K} (hv : v ∉ g₀) :
    (splitEdgeEquiv g₀).symm (y, z) v = z ⟨v, hv⟩ := by
  unfold splitEdgeEquiv
  convert
    Equiv.piCongrLeft_sumInr
      (fun _ : K => G) (edgeSumEquiv g₀)
      y z ⟨v, hv⟩ using 1 ;
    simp [edgeSumEquiv]

omit [Fintype G] [DecidableEq G] in
/-- Replacing the coordinate assigned to `g` does not alter the tuple
seen by `g`, since that occurrence edge omits the assigned vertex. -/
theorem edgeTuple_frozenBundleInsertedAssignment
    {K : Type*} [Fintype K] [DecidableEq K]
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ g : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ f ∈ B.edges, f.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (hg : g ∈ B.edges.erase g₀)
    (a : G)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) →
        G)
    (z : EdgeComplement g₀ → G) :
    edgeTuple g
        (B.frozenBundleInsertedAssignment hg₀ hne
          (B.frozenBundleMissingCoordinate hg₀ hmax hne g)
          a
          (Fin.removeNth
            (B.frozenBundleMissingCoordinate hg₀ hmax hne g) x)
          z) =
      edgeTuple g
        ((splitEdgeEquiv g₀).symm
          ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x, z)) := by
  classical
  funext w
  unfold edgeTuple
  let i :=
    B.frozenBundleMissingCoordinate hg₀ hmax hne g
  by_cases hw₀ : w.1 ∈ g₀
  · unfold frozenBundleInsertedAssignment
    rw [splitEdgeEquiv_symm_apply_of_mem g₀ _ _ hw₀]
    rw [splitEdgeEquiv_symm_apply_of_mem g₀ _ _ hw₀]
    unfold frozenBundleInsertedSelectedTuple
    rw [B.frozenBundleFaceTupleEquiv_symm_apply]
    rw [B.frozenBundleFaceTupleEquiv_symm_apply]
    let q :=
      (B.frozenOccurrenceOrderEquiv hg₀ hne).symm
        (⟨w.1, hw₀⟩ : {v : K // v ∈ g₀})
    have hqi : q ≠ i := by
      intro h
      have hsub :
          (⟨w.1, hw₀⟩ : {v : K // v ∈ g₀}) =
            B.frozenBundleMissingVertex hmax hne g := by
        apply (B.frozenOccurrenceOrderEquiv hg₀ hne).symm.injective
        simpa only [q, i, frozenBundleMissingCoordinate] using h
      apply B.frozenBundleMissingVertex_not_mem hmax hne hg
      have hwval :
          w.1 =
            (B.frozenBundleMissingVertex hmax hne g).1 :=
        congrArg Subtype.val hsub
      rw [← hwval]
      exact w.2
    change
      Fin.insertNth i a (Fin.removeNth i x) q = x q
    rw [Fin.insertNth_removeNth]
    simp [hqi]
  · unfold frozenBundleInsertedAssignment
    rw [splitEdgeEquiv_symm_apply_of_not_mem g₀ _ _ hw₀]
    rw [splitEdgeEquiv_symm_apply_of_not_mem g₀ _ _ hw₀]

/-- The grouped frozen remainder cut test.  The product is indexed by
occurrence edges, so repeated projected faces remain separate factors. -/
noncomputable def frozenBundleRemainderCutTest
    {K : Type*} [Fintype K] [DecidableEq K]
    {C : OrderedPartitionComplex G k r}
    (A : ClosedOrderedAtomConfiguration G k r C)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G) :
    CutTestFamily G
      ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) :=
  fun i y =>
    ∏ g ∈ B.edges.erase g₀,
      if _hcoord :
          B.frozenBundleMissingCoordinate hg₀ hmax hne g = i
      then
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a y z))
      else 1

/-- Every grouped remainder cut factor lies in `[0,1]`. -/
theorem frozenBundleRemainderCutTest_bounded
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G) :
    IsBoundedCutTest
      (B.frozenBundleRemainderCutTest A hg₀ hmax hne a z) := by
  constructor
  · intro i y
    unfold frozenBundleRemainderCutTest
    apply Finset.prod_nonneg
    intro g hg
    split_ifs
    · exact
        (B.pullbackBaseEdgeWeight_unitInterval
          (orderedConfigurationBaseWeight A)
          (orderedConfigurationBaseWeight_unitInterval A)
          (Finset.mem_of_mem_erase hg) _).1
    · positivity
  · intro i y
    unfold frozenBundleRemainderCutTest
    apply Finset.prod_le_one
    · intro g hg
      split_ifs
      · exact
          (B.pullbackBaseEdgeWeight_unitInterval
            (orderedConfigurationBaseWeight A)
            (orderedConfigurationBaseWeight_unitInterval A)
            (Finset.mem_of_mem_erase hg) _).1
      · positivity
    · intro g hg
      split_ifs
      · exact
          (B.pullbackBaseEdgeWeight_unitInterval
            (orderedConfigurationBaseWeight A)
            (orderedConfigurationBaseWeight_unitInterval A)
            (Finset.mem_of_mem_erase hg) _).2
      · exact le_rfl

/-- The cut product is exactly the complete frozen bundle remainder. -/
theorem cutTestProduct_frozenBundleRemainderCutTest
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse)
    (B : HypergraphBundle (Fin k) K
      (orderedConfigurationBaseEdges k r))
    {g₀ : Finset K} (hg₀ : g₀ ∈ B.edges)
    (hmax : ∀ g ∈ B.edges, g.card ≤ g₀.card)
    (hne : g₀.Nonempty)
    (a : G)
    (z : EdgeComplement g₀ → G)
    (x :
      Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1) →
        G) :
    cutTestProduct
        (B.frozenBundleRemainderCutTest A hg₀ hmax hne a z) x =
      B.edgeRemainderFiber g₀
        (B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A))
        ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x) z := by
  classical
  unfold cutTestProduct frozenBundleRemainderCutTest
  rw [Finset.prod_comm]
  unfold edgeRemainderFiber edgeRemainder bundleProduct
  apply Finset.prod_congr rfl
  intro g hg
  let i :=
    B.frozenBundleMissingCoordinate hg₀ hmax hne g
  calc
    (∏ q :
        Fin ((B.orderedConfigurationBundleFace hg₀ hne).lowerRank.1 + 1),
        if hcoord :
            B.frozenBundleMissingCoordinate hg₀ hmax hne g = q
        then
          B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A) g
            (edgeTuple g
              (B.frozenBundleInsertedAssignment hg₀ hne q a
                (Fin.removeNth q x) z))
        else 1) =
        (if hcoord :
            B.frozenBundleMissingCoordinate hg₀ hmax hne g = i
        then
          B.pullbackBaseEdgeWeight
            (orderedConfigurationBaseWeight A) g
            (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a
                (Fin.removeNth i x) z))
        else 1) := by
      apply Fintype.prod_eq_single i
      intro q hqi
      have hnecoord :
          B.frozenBundleMissingCoordinate hg₀ hmax hne g ≠ q := by
        intro h
        exact hqi h.symm
      simp [hnecoord]
    _ =
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            (B.frozenBundleInsertedAssignment hg₀ hne i a
              (Fin.removeNth i x) z)) := by
      simp [i]
    _ =
        B.pullbackBaseEdgeWeight
          (orderedConfigurationBaseWeight A) g
          (edgeTuple g
            ((splitEdgeEquiv g₀).symm
              ((B.frozenBundleFaceTupleEquiv hg₀ hne).symm x, z))) := by
      rw [B.edgeTuple_frozenBundleInsertedAssignment
        hg₀ hmax hne hg a x z]

/-! ## Exact correlation transport -/

/-- Every frozen remainder of an arbitrary closed bundle is a bounded cut
test on the canonical selected projected face. -/
theorem hasOrderedConfigurationBundleFrozenCutRepresentation
    [Nonempty G]
    (P : OrderedCoarseFineComplex G k r)
    (A : ClosedOrderedAtomConfiguration G k r P.coarse) :
    HasOrderedConfigurationBundleFrozenCutRepresentation P A := by
  intro K _instK _decK B _hclosed g₀ hg₀ hmax hne z
  let a : G := Classical.choice inferInstance
  let u :=
    B.frozenBundleRemainderCutTest A hg₀ hmax hne a z
  refine ⟨u, ?_, ?_⟩
  · exact
      B.frozenBundleRemainderCutTest_bounded
        P A hg₀ hmax hne a z
  · unfold frozenEdgeCorrelation
    unfold FaceRegularityState.faceCutCorrelation
    apply mean_equiv
      (B.frozenBundleFaceTupleEquiv hg₀ hne)
    intro y
    rw [B.cutTestProduct_frozenBundleRemainderCutTest
      P A hg₀ hmax hne a z]
    simp only [Equiv.symm_apply_apply]
    rw [B.frozenBundleFaceTupleEquiv_apply]
    rfl

end HypergraphBundle

end Wikipedia.SzemeredisTheorem
