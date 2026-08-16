import Mathlib.Order.Hom.PowersetCard
import Wikipedia.SzemeredisTheorem.Hypergraph.APRemoval
import Wikipedia.SzemeredisTheorem.Hypergraph.OrderedPattern

/-!
# Equal-vertex bridge from ordered removal to simplex removal

For `n + 1` equal vertex classes, the colours of a partite `n`-uniform
simplex hypergraph are canonically the increasing `n`-faces of
`Fin (n + 1)`: the colour `j` corresponds to the face which omits `j`.
This file makes that identification explicit and transports occurrences,
deletion covers, and normalized deletion cost.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The colour `j` regarded as the increasing codimension-one face which
omits `j`. -/
def orderedFacet {n : ℕ} (j : Fin (n + 1)) :
    OrderedFace (n + 1) n :=
  Fin.succAboveOrderEmb j

/-- Colours of an `(n + 1)`-vertex simplex are equivalent to increasing
rank-`n` faces.  The construction factors through finite subsets so that its
forward map is definitionally the complement of a singleton. -/
noncomputable def orderedFacetEquiv (n : ℕ) :
    Fin (n + 1) ≃ OrderedFace (n + 1) n :=
  (Set.powersetCard.ofSingleton :
      Fin (n + 1) ≃ Set.powersetCard (Fin (n + 1)) 1) |>.trans
    ((Set.powersetCard.compl (m := n) (n := 1) (by simp) :
        Set.powersetCard (Fin (n + 1)) 1 ≃
          Set.powersetCard (Fin (n + 1)) n) |>.trans
      (Set.powersetCard.ofFinEmbEquiv :
        OrderedFace (n + 1) n ≃
          Set.powersetCard (Fin (n + 1)) n).symm)

@[simp]
theorem orderedFacetEquiv_apply
    {n : ℕ} (j : Fin (n + 1)) :
    orderedFacetEquiv n j = orderedFacet j := by
  apply OrderEmbedding.range_inj.mp
  change
    Set.range ((orderedFacetEquiv n) j) =
      Set.range (Fin.succAboveOrderEmb j)
  rw [Fin.range_succAboveOrderEmb]
  ext i
  simp only [orderedFacetEquiv, Equiv.trans_apply]
  rw [
    Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem]
  rw [Set.powersetCard.mem_compl]
  change
    i ∉ ({j} : Finset (Fin (n + 1))) ↔
      i ∈ ({j} : Set (Fin (n + 1)))ᶜ
  simp

/-- The two standard presentations of a deleted coordinate vector are
mutually inverse. -/
@[simp]
theorem deletedVectorToFinTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    deletedVectorToFinTuple j
        (finTupleToDeletedVector j y) = y := by
  funext t
  simp [deletedVectorToFinTuple]

@[simp]
theorem finTupleToDeletedVector_deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    finTupleToDeletedVector j
        (deletedVectorToFinTuple j x) = x := by
  funext i
  change
    x (finSuccAboveEquiv j
        ((finSuccAboveEquiv j).symm i)) = x i
  rw [(finSuccAboveEquiv j).apply_symm_apply]

/-- Reindexing identifies the deleted-vector space of every colour with the
same ordinary tuple space. -/
noncomputable def deletedVectorFinTupleEquiv
    {G : Type*} {n : ℕ} (j : Fin (n + 1)) :
    DeletedVector (fun _ : Fin (n + 1) => G) j ≃
      (Fin n → G) where
  toFun := deletedVectorToFinTuple j
  invFun := finTupleToDeletedVector j
  left_inv := finTupleToDeletedVector_deletedVectorToFinTuple j
  right_inv := deletedVectorToFinTuple_finTupleToDeletedVector j

@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    deletedVectorToFinTuple j (deleteCoordinate x j) =
      orderedFaceTuple (orderedFacet j) x := by
  rfl

@[simp]
theorem finTupleToDeletedVector_orderedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) :
    finTupleToDeletedVector j
        (orderedFaceTuple (orderedFacet j) x) =
      deleteCoordinate x j := by
  rw [←
    finTupleToDeletedVector_deletedVectorToFinTuple j
      (deleteCoordinate x j)]
  congr

/-- Regard an equal-vertex simplex hypergraph as a complete ordered pattern.
An arbitrary ordered face is first decoded as its unique omitted colour. -/
noncomputable def SimplexHypergraph.toOrderedPattern
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    OrderedPattern G (n + 1) n where
  edge e y :=
    let j := (orderedFacetEquiv n).symm e
    H.edge j (finTupleToDeletedVector j y)

@[simp]
theorem SimplexHypergraph.toOrderedPattern_edge_orderedFacet
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (y : Fin n → G) :
    H.toOrderedPattern.edge (orderedFacet j) y ↔
      H.edge j (finTupleToDeletedVector j y) := by
  change
    H.edge ((orderedFacetEquiv n).symm (orderedFacet j))
        (finTupleToDeletedVector
          ((orderedFacetEquiv n).symm (orderedFacet j)) y) ↔
      H.edge j (finTupleToDeletedVector j y)
  have hj :
      (orderedFacetEquiv n).symm (orderedFacet j) = j := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).symm_apply_apply j
  rw [hj]

/-- Ordered occurrences are exactly labelled simplices. -/
theorem SimplexHypergraph.toOrderedPattern_isOccurrence_iff
    {G : Type*} {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (x : Fin (n + 1) → G) :
    H.toOrderedPattern.IsOccurrence x ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  constructor
  · intro hx j
    have hj := hx (orderedFacet j)
    rw [H.toOrderedPattern_edge_orderedFacet] at hj
    simpa using hj
  · intro hx e
    let j := (orderedFacetEquiv n).symm e
    have he : orderedFacet j = e := by
      rw [← orderedFacetEquiv_apply]
      exact (orderedFacetEquiv n).apply_symm_apply e
    rw [← he]
    rw [H.toOrderedPattern_edge_orderedFacet]
    simpa using hx j

/-- The finite occurrence set is unchanged by the ordered presentation. -/
theorem SimplexHypergraph.toOrderedPattern_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.occurrenceFinset =
      H.simplexFinset := by
  ext x
  rw [OrderedPattern.mem_occurrenceFinset,
    SimplexHypergraph.mem_simplexFinset,
    H.toOrderedPattern_isOccurrence_iff]

/-- In particular, the zero-one normalized pattern count is exactly the
zero-one normalized simplex count. -/
theorem SimplexHypergraph.toOrderedPattern_patternCount
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G)) :
    H.toOrderedPattern.toWeighted.patternCount =
      H.toWeighted.simplexCount := by
  rw [OrderedPattern.toWeighted_patternCount_eq,
    SimplexHypergraph.toWeighted_simplexCount_eq_card_div,
    H.toOrderedPattern_occurrenceFinset]

/-- Send an ordered deletion on the face omitting `j` to the corresponding
dependent deleted-vector space. -/
noncomputable def orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n) :
    SimplexHypergraph.DeletionFamily
      (fun _ : Fin (n + 1) => G) := by
  classical
  exact fun j =>
    (D (orderedFacet j)).image
      (finTupleToDeletedVector j)

@[simp]
theorem mem_orderedDeletionToSimplex_iff
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    x ∈ orderedDeletionToSimplex D j ↔
      deletedVectorToFinTuple j x ∈ D (orderedFacet j) := by
  classical
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    rw [← hyx]
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr
      ⟨deletedVectorToFinTuple j x, hx,
        finTupleToDeletedVector_deletedVectorToFinTuple j x⟩

/-- Reindexing a deletion face does not change its cardinality. -/
@[simp]
theorem card_orderedDeletionToSimplex
    {G : Type*} [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    (orderedDeletionToSimplex D j).card =
      (D (orderedFacet j)).card := by
  classical
  rw [orderedDeletionToSimplex,
    Finset.card_image_of_injective _]
  intro y z hyz
  have htuple :=
    congrArg (deletedVectorToFinTuple j) hyz
  simpa using htuple

/-- A cover of the ordered presentation transports to a simplex cover. -/
theorem SimplexHypergraph.isSimplexCover_orderedDeletionToSimplex
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : SimplexHypergraph (fun _ : Fin (n + 1) => G))
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (hcover : H.toOrderedPattern.IsCover D) :
    H.IsSimplexCover (orderedDeletionToSimplex D) := by
  intro x hx
  have hxOrdered :
      x ∈ H.toOrderedPattern.occurrenceFinset := by
    rw [H.toOrderedPattern_occurrenceFinset]
    exact hx
  obtain ⟨e, he⟩ := hcover x hxOrdered
  let j := (orderedFacetEquiv n).symm e
  have heq : orderedFacet j = e := by
    rw [← orderedFacetEquiv_apply]
    exact (orderedFacetEquiv n).apply_symm_apply e
  refine ⟨j, (mem_orderedDeletionToSimplex_iff D j _).2 ?_⟩
  rw [
    deletedVectorToFinTuple_deleteCoordinate_eq_orderedFaceTuple,
    heq]
  exact he

/-- The deletion density of a transported colour is its ordered-face
density. -/
theorem colorDeletionDensity_orderedDeletionToSimplex
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    (j : Fin (n + 1)) :
    SimplexHypergraph.colorDeletionDensity
        (orderedDeletionToSimplex D) j =
      OrderedPattern.faceDeletionDensity
        D (orderedFacet j) := by
  rw [SimplexHypergraph.colorDeletionDensity,
    OrderedPattern.faceDeletionDensity,
    card_orderedDeletionToSimplex]
  have hcard :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) =
        Fintype.card (Fin n → G) :=
    Fintype.card_congr (deletedVectorFinTupleEquiv j)
  rw [hcard]

/-- Uniform ordered-face density bounds imply the same bound for total
normalized simplex deletion cost. -/
theorem normalizedDeletionCost_orderedDeletionToSimplex_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (D : OrderedPattern.DeletionFamily
      (G := G) (n + 1) n)
    {ε : ℝ}
    (hD :
      ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ε) :
    SimplexHypergraph.normalizedDeletionCost
        (orderedDeletionToSimplex D) ≤ ε := by
  let M : ℕ := Fintype.card (Fin n → G)
  have hM : 0 < M := Fintype.card_pos
  have hface (j : Fin (n + 1)) :
      Fintype.card
          (DeletedVector
            (fun _ : Fin (n + 1) => G) j) = M := by
    exact Fintype.card_congr (deletedVectorFinTupleEquiv j)
  have hcard (j : Fin (n + 1)) :
      ((orderedDeletionToSimplex D j).card : ℝ) ≤
        ε * M := by
    have hdensity :=
      colorDeletionDensity_orderedDeletionToSimplex D j
    have hbound := hD (orderedFacet j)
    rw [← hdensity] at hbound
    rw [SimplexHypergraph.colorDeletionDensity,
      hface] at hbound
    have hMR : (0 : ℝ) < M := by
      exact_mod_cast hM
    exact (div_le_iff₀ hMR).mp hbound
  have hcount :
      (SimplexHypergraph.deletionCount
          (orderedDeletionToSimplex D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := by
    calc
      (SimplexHypergraph.deletionCount
          (orderedDeletionToSimplex D) : ℝ) =
          ∑ j : Fin (n + 1),
            ((orderedDeletionToSimplex D j).card : ℝ) := by
        simp [SimplexHypergraph.deletionCount]
      _ ≤ ∑ _j : Fin (n + 1), ε * M :=
        Finset.sum_le_sum fun j _ => hcard j
      _ = (n + 1 : ℝ) * (ε * M) := by
        simp
  have hcapacity :
      SimplexHypergraph.deletionCapacity
          (fun _ : Fin (n + 1) => G) =
        (n + 1) * M := by
    unfold SimplexHypergraph.deletionCapacity
    simp_rw [hface]
    simp
  rw [SimplexHypergraph.normalizedDeletionCost,
    hcapacity]
  have hdenom :
      (0 : ℝ) < ((n + 1) * M : ℕ) := by
    exact_mod_cast Nat.mul_pos (by omega) hM
  apply (div_le_iff₀ hdenom).2
  calc
    (SimplexHypergraph.deletionCount
        (orderedDeletionToSimplex D) : ℝ) ≤
        (n + 1 : ℝ) * (ε * M) := hcount
    _ = ε * (((n + 1) * M : ℕ) : ℝ) := by
      push_cast
      ring

/-- Uniform ordered removal for rank `n` patterns on `n + 1` equal vertex
classes implies uniform cyclic partite simplex removal on `n + 1` colours. -/
theorem hasUniformCyclicPartiteSimplexRemoval_of_ordered
    (n : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (n + 1) n) :
    HasUniformCyclicPartiteSimplexRemoval (n + 1) := by
  intro ε hε
  obtain ⟨c, hc, hremove⟩ := hordered ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst H hcount
  have horderedCount :
      H.toOrderedPattern.toWeighted.patternCount < c := by
    rw [H.toOrderedPattern_patternCount]
    exact hcount
  obtain ⟨D, hcover, hD⟩ :=
    hremove (ZMod N) H.toOrderedPattern horderedCount
  exact
    ⟨orderedDeletionToSimplex D,
      H.isSimplexCover_orderedDeletionToSimplex D hcover,
      normalizedDeletionCost_orderedDeletionToSimplex_le D hD⟩

/-- The successor-indexed bridge in the arithmetic-progression convention:
rank `r + 1` ordered removal on `r + 2` classes supplies the
`r + 2`-colour simplex-removal input. -/
theorem hasUniformCyclicPartiteSimplexRemoval_add_two_of_ordered
    (r : ℕ)
    (hordered :
      HasUniformOrderedPatternRemoval (r + 2) (r + 1)) :
    HasUniformCyclicPartiteSimplexRemoval (r + 2) := by
  simpa [Nat.add_assoc] using
    (hasUniformCyclicPartiteSimplexRemoval_of_ordered
      (r + 1) (by simpa [Nat.add_assoc] using hordered))

end Wikipedia.SzemeredisTheorem
