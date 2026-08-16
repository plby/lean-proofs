import Mathlib.Data.Finset.Max
import Wikipedia.SzemeredisTheorem.Hypergraph.Energy
import Wikipedia.SzemeredisTheorem.Hypergraph.Unweighted

/-!
# Finite deletion framework for simplex removal

This file supplies the finite combinatorial interface surrounding the deep
hypergraph-removal argument.  A deletion family consists of one finite set of
deleted faces for each colour.  We construct the surviving hypergraph, prove
that covers are exactly the deletion families with no surviving simplex, and
develop monotonicity, cost normalization, trimming, canonical covers, and
existence of a minimum finite cover.

No quantitative hypergraph-removal theorem is asserted here.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

namespace SimplexHypergraph

/-- One finite set of deleted faces for each edge colour. -/
abbrev DeletionFamily {k : ℕ} (V : Fin k → Type*) :=
  (j : Fin k) → Finset (DeletedVector V j)

/-- Delete a family of faces from an unweighted simplex hypergraph. -/
noncomputable def deleteEdges {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    SimplexHypergraph V := by
  classical
  exact
    { edge := fun j x => H.edge j x ∧ x ∉ deleted j }

@[simp]
theorem deleteEdges_edge {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) (deleted : DeletionFamily V)
    (j : Fin k) (x : DeletedVector V j) :
    (H.deleteEdges deleted).edge j x ↔
      H.edge j x ∧ x ∉ deleted j := by
  classical
  simp [deleteEdges]

/-- Exact description of the labelled simplices surviving a deletion. -/
@[simp]
theorem mem_deleteEdges_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V)
    (x : (i : Fin k) → V i) :
    x ∈ (H.deleteEdges deleted).simplexFinset ↔
      x ∈ H.simplexFinset ∧
        ∀ j, deleteCoordinate x j ∉ deleted j := by
  classical
  simp only [mem_simplexFinset, deleteEdges_edge, forall_and]

/-- A finite hypergraph is simplex-free when its labelled simplex finset is
empty. -/
def IsSimplexFree {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] (H : SimplexHypergraph V) : Prop :=
  H.simplexFinset = ∅

theorem isSimplexFree_iff {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.IsSimplexFree ↔
      ∀ x, ∃ j, ¬H.edge j (deleteCoordinate x j) := by
  classical
  rw [IsSimplexFree, Finset.eq_empty_iff_forall_notMem]
  simp only [mem_simplexFinset]
  push Not
  rfl

/-- The empty deletion family. -/
def emptyDeletion {k : ℕ} (V : Fin k → Type*) :
    DeletionFamily V :=
  fun _ => ∅

@[simp]
theorem mem_emptyDeletion {k : ℕ} {V : Fin k → Type*}
    (j : Fin k) (x : DeletedVector V j) :
    x ∉ emptyDeletion V j := by
  simp [emptyDeletion]

/-- Deleting nothing leaves the labelled simplex finset unchanged. -/
@[simp]
theorem deleteEdges_empty_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    (H.deleteEdges (emptyDeletion V)).simplexFinset =
      H.simplexFinset := by
  classical
  ext x
  simp

/-- Increasing every deleted-face set can only remove surviving simplices. -/
theorem deleteEdges_simplexFinset_antitone {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    {deleted₁ deleted₂ : DeletionFamily V}
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    (H.deleteEdges deleted₂).simplexFinset ⊆
      (H.deleteEdges deleted₁).simplexFinset := by
  intro x hx
  rw [mem_deleteEdges_simplexFinset] at hx ⊢
  exact ⟨hx.1, fun j hj => hx.2 j (hdel j hj)⟩

/-- A cover remains a cover after enlarging each deleted-face set. -/
theorem IsSimplexCover.mono {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    {H : SimplexHypergraph V}
    {deleted₁ deleted₂ : DeletionFamily V}
    (hcover : H.IsSimplexCover deleted₁)
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    H.IsSimplexCover deleted₂ := by
  intro x hx
  obtain ⟨j, hj⟩ := hcover x hx
  exact ⟨j, hdel j hj⟩

/-- A deletion family is supported on actual edges of the hypergraph. -/
def IsEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) : Prop :=
  ∀ j, deleted j ⊆ H.edgeFinset j

/-- Remove irrelevant nonedges from a deletion family. -/
noncomputable def trimDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    DeletionFamily V := by
  classical
  exact fun j => deleted j ∩ H.edgeFinset j

theorem trimDeletion_isEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    H.IsEdgeDeletion (H.trimDeletion deleted) := by
  classical
  intro j
  exact Finset.inter_subset_right

theorem trimDeletion_subset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V)
    (j : Fin k) :
    H.trimDeletion deleted j ⊆ deleted j := by
  classical
  exact Finset.inter_subset_left

/-- Trimming a cover to actual edges preserves the cover property. -/
theorem IsSimplexCover.trim {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    {H : SimplexHypergraph V} {deleted : DeletionFamily V}
    (hcover : H.IsSimplexCover deleted) :
    H.IsSimplexCover (H.trimDeletion deleted) := by
  classical
  intro x hx
  obtain ⟨j, hj⟩ := hcover x hx
  refine ⟨j, Finset.mem_inter.mpr ⟨hj, ?_⟩⟩
  exact H.mem_edgeFinset j (deleteCoordinate x j) |>.2
    ((H.mem_simplexFinset x).1 hx j)

/-- Trimming irrelevant nonedges does not change the surviving simplices. -/
theorem trimDeletion_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    (H.deleteEdges (H.trimDeletion deleted)).simplexFinset =
      (H.deleteEdges deleted).simplexFinset := by
  classical
  ext x
  rw [mem_deleteEdges_simplexFinset,
    mem_deleteEdges_simplexFinset]
  constructor
  · rintro ⟨hx, havoid⟩
    refine ⟨hx, fun j hj => ?_⟩
    apply havoid j
    refine Finset.mem_inter.mpr ⟨hj, ?_⟩
    exact (H.mem_edgeFinset j (deleteCoordinate x j)).2
      ((H.mem_simplexFinset x).1 hx j)
  · rintro ⟨hx, havoid⟩
    exact ⟨hx, fun j hj => havoid j (Finset.mem_inter.mp hj).1⟩

/-- The canonical deletion family consisting of all actual edges. -/
noncomputable def fullEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) : DeletionFamily V :=
  H.edgeFinset

theorem fullEdgeDeletion_isEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.IsEdgeDeletion H.fullEdgeDeletion :=
  fun _ => Finset.Subset.rfl

/-- When there is at least one edge colour, deleting all actual edges covers
every simplex. -/
theorem fullEdgeDeletion_isSimplexCover {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [Nonempty (Fin k)] (H : SimplexHypergraph V) :
    H.IsSimplexCover H.fullEdgeDeletion := by
  classical
  intro x hx
  let j : Fin k := Classical.choice inferInstance
  refine ⟨j, ?_⟩
  exact (H.mem_edgeFinset j (deleteCoordinate x j)).2
    ((H.mem_simplexFinset x).1 hx j)

/-- Project every labelled simplex to each of its coloured faces. -/
noncomputable def projectedSimplexDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) : DeletionFamily V := by
  classical
  exact fun j =>
    H.simplexFinset.image (fun x => deleteCoordinate x j)

theorem projectedSimplexDeletion_isEdgeDeletion {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.IsEdgeDeletion H.projectedSimplexDeletion := by
  classical
  intro j e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  exact (H.mem_edgeFinset j (deleteCoordinate x j)).2
    ((H.mem_simplexFinset x).1 hx j)

/-- If a colour exists, the projected faces of the simplices form a cover. -/
theorem projectedSimplexDeletion_isSimplexCover {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [Nonempty (Fin k)] (H : SimplexHypergraph V) :
    H.IsSimplexCover H.projectedSimplexDeletion := by
  classical
  intro x hx
  let j : Fin k := Classical.choice inferInstance
  refine ⟨j, ?_⟩
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

theorem card_projectedSimplexDeletion_le {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k) :
    (H.projectedSimplexDeletion j).card ≤
      H.simplexFinset.card := by
  classical
  exact Finset.card_image_le

/-- Total number of deleted coloured faces. -/
def deletionCount {k : ℕ} {V : Fin k → Type*}
    (deleted : DeletionFamily V) : ℕ :=
  ∑ j, (deleted j).card

@[simp]
theorem deletionCount_empty {k : ℕ} (V : Fin k → Type*) :
    deletionCount (emptyDeletion V) = 0 := by
  simp [deletionCount, emptyDeletion]

theorem deletionCount_mono {k : ℕ} {V : Fin k → Type*}
    {deleted₁ deleted₂ : DeletionFamily V}
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    deletionCount deleted₁ ≤ deletionCount deleted₂ := by
  apply Finset.sum_le_sum
  intro j _
  exact Finset.card_le_card (hdel j)

/-- A uniform per-colour cardinality bound controls the total deletion
count. -/
theorem deletionCount_le_of_card_le {k m : ℕ}
    {V : Fin k → Type*} (deleted : DeletionFamily V)
    (hcard : ∀ j, (deleted j).card ≤ m) :
    deletionCount deleted ≤ k * m := by
  calc
    deletionCount deleted ≤ ∑ _j : Fin k, m := by
      apply Finset.sum_le_sum
      intro j _
      exact hcard j
    _ = k * m := by
      simp

theorem deletionCount_trim_le {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    deletionCount (H.trimDeletion deleted) ≤
      deletionCount deleted :=
  deletionCount_mono (H.trimDeletion_subset deleted)

theorem deletionCount_projectedSimplexDeletion_le {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    deletionCount H.projectedSimplexDeletion ≤
      k * H.simplexFinset.card := by
  calc
    deletionCount H.projectedSimplexDeletion ≤
        ∑ _j : Fin k, H.simplexFinset.card := by
      apply Finset.sum_le_sum
      intro j _
      exact H.card_projectedSimplexDeletion_le j
    _ = k * H.simplexFinset.card := by
      simp

/-- A canonical finite cover deletes at most one projected face per labelled
simplex in each colour. -/
theorem exists_simplexCover_card_le_simplexFinset {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [Nonempty (Fin k)] (H : SimplexHypergraph V) :
    ∃ deleted : DeletionFamily V,
      H.IsSimplexCover deleted ∧
      H.IsEdgeDeletion deleted ∧
      (∀ j, (deleted j).card ≤ H.simplexFinset.card) ∧
      deletionCount deleted ≤ k * H.simplexFinset.card :=
  ⟨H.projectedSimplexDeletion,
    H.projectedSimplexDeletion_isSimplexCover,
    H.projectedSimplexDeletion_isEdgeDeletion,
    H.card_projectedSimplexDeletion_le,
    H.deletionCount_projectedSimplexDeletion_le⟩

/-- Total number of available coloured face slots. -/
def deletionCapacity {k : ℕ} (V : Fin k → Type*)
    [∀ i, Fintype (V i)] : ℕ :=
  ∑ j, Fintype.card (DeletedVector V j)

@[simp]
theorem card_deletedVector_fin (k n : ℕ) (j : Fin k) :
    Fintype.card
        (DeletedVector (fun _ : Fin k => Fin n) j) =
      n ^ (k - 1) := by
  simp [DeletedVector, Fintype.card_pi]

@[simp]
theorem deletionCapacity_fin (k n : ℕ) :
    deletionCapacity (fun _ : Fin k => Fin n) =
      k * n ^ (k - 1) := by
  simp [deletionCapacity]

theorem deletionCount_le_capacity {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) :
    deletionCount deleted ≤ deletionCapacity V := by
  apply Finset.sum_le_sum
  intro j _
  exact (deleted j).card_le_univ

/-- Density of the deleted faces in one colour class. -/
noncomputable def colorDeletionDensity {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) (j : Fin k) : ℝ :=
  ((deleted j).card : ℝ) /
    Fintype.card (DeletedVector V j)

theorem colorDeletionDensity_nonneg {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) (j : Fin k) :
    0 ≤ colorDeletionDensity deleted j :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem colorDeletionDensity_le_one {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) (j : Fin k) :
    colorDeletionDensity deleted j ≤ 1 := by
  apply div_le_one_of_le₀
  · exact_mod_cast (deleted j).card_le_univ
  · exact Nat.cast_nonneg _

@[simp]
theorem colorDeletionDensity_fin {k n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin k => Fin n))
    (j : Fin k) :
    colorDeletionDensity deleted j =
      ((deleted j).card : ℝ) / (n ^ (k - 1) : ℕ) := by
  simp [colorDeletionDensity]

/-- Deleted-face density among all coloured face slots.  If the capacity is
zero, Lean's field division convention makes the value zero. -/
noncomputable def normalizedDeletionCost {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) : ℝ :=
  (deletionCount deleted : ℝ) / (deletionCapacity V : ℝ)

theorem normalizedDeletionCost_nonneg {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) :
    0 ≤ normalizedDeletionCost deleted := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem normalizedDeletionCost_le_one {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (deleted : DeletionFamily V) :
    normalizedDeletionCost deleted ≤ 1 := by
  apply div_le_one_of_le₀
  · exact_mod_cast deletionCount_le_capacity deleted
  · exact Nat.cast_nonneg _

theorem normalizedDeletionCost_mono {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    {deleted₁ deleted₂ : DeletionFamily V}
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    normalizedDeletionCost deleted₁ ≤
      normalizedDeletionCost deleted₂ := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast deletionCount_mono hdel
  · exact Nat.cast_nonneg _

theorem normalizedDeletionCost_trim_le {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (deleted : DeletionFamily V) :
    normalizedDeletionCost (H.trimDeletion deleted) ≤
      normalizedDeletionCost deleted :=
  normalizedDeletionCost_mono (H.trimDeletion_subset deleted)

@[simp]
theorem normalizedDeletionCost_empty {k : ℕ}
    (V : Fin k → Type*) [∀ i, Fintype (V i)] :
    normalizedDeletionCost (emptyDeletion V) = 0 := by
  simp [normalizedDeletionCost]

/-- There is a minimum-cardinality cover, and it may be chosen to contain
only actual edges.  This is the finite compactness statement underlying later
quantitative optimization. -/
theorem exists_minimum_simplexCover {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [Nonempty (Fin k)] (H : SimplexHypergraph V) :
    ∃ deleted : DeletionFamily V,
      H.IsSimplexCover deleted ∧
      H.IsEdgeDeletion deleted ∧
      ∀ other : DeletionFamily V,
        H.IsSimplexCover other →
          deletionCount deleted ≤ deletionCount other := by
  classical
  let covers : Finset (DeletionFamily V) :=
    Finset.univ.filter H.IsSimplexCover
  have covers_nonempty : covers.Nonempty := by
    refine ⟨H.fullEdgeDeletion, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, H.fullEdgeDeletion_isSimplexCover⟩
  obtain ⟨deleted, hdeleted, hminimal⟩ :=
    Finset.exists_min_image covers deletionCount covers_nonempty
  have hcover : H.IsSimplexCover deleted :=
    (Finset.mem_filter.mp hdeleted).2
  refine
    ⟨H.trimDeletion deleted, hcover.trim,
      H.trimDeletion_isEdgeDeletion deleted, ?_⟩
  intro other hother
  calc
    deletionCount (H.trimDeletion deleted) ≤
        deletionCount deleted :=
      H.deletionCount_trim_le deleted
    _ ≤ deletionCount other := by
      apply hminimal other
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hother⟩

/-- The same finite minimizer is optimal for normalized deletion cost. -/
theorem exists_minimum_normalized_simplexCover {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [Nonempty (Fin k)] (H : SimplexHypergraph V) :
    ∃ deleted : DeletionFamily V,
      H.IsSimplexCover deleted ∧
      H.IsEdgeDeletion deleted ∧
      ∀ other : DeletionFamily V,
        H.IsSimplexCover other →
          normalizedDeletionCost deleted ≤
            normalizedDeletionCost other := by
  obtain ⟨deleted, hcover, hedge, hminimal⟩ :=
    H.exists_minimum_simplexCover
  refine ⟨deleted, hcover, hedge, ?_⟩
  intro other hother
  apply div_le_div_of_nonneg_right
  · exact_mod_cast hminimal other hother
  · exact Nat.cast_nonneg _

end SimplexHypergraph

/-- No labelled simplex survives after deleting the specified faces. -/
def NoSimplexAfterDeleting {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : SimplexHypergraph.DeletionFamily V) : Prop :=
  (H.deleteEdges deleted).IsSimplexFree

/-- Exact correspondence between combinatorial covers and simplex-free
surviving hypergraphs. -/
theorem isSimplexCover_iff_noSimplexAfterDeleting {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : SimplexHypergraph.DeletionFamily V) :
    H.IsSimplexCover deleted ↔
      NoSimplexAfterDeleting H deleted := by
  classical
  constructor
  · intro hcover
    rw [NoSimplexAfterDeleting,
      SimplexHypergraph.IsSimplexFree,
      Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [SimplexHypergraph.mem_deleteEdges_simplexFinset] at hx
    obtain ⟨j, hj⟩ := hcover x hx.1
    exact hx.2 j hj
  · intro hfree x hx
    by_contra h
    push Not at h
    have hsurvives :
        x ∈ (H.deleteEdges deleted).simplexFinset :=
      (H.mem_deleteEdges_simplexFinset deleted x).2 ⟨hx, h⟩
    rw [NoSimplexAfterDeleting,
      SimplexHypergraph.IsSimplexFree] at hfree
    rw [hfree] at hsurvives
    simp at hsurvives

/-- Enlarging a deletion family preserves absence of surviving simplices. -/
theorem NoSimplexAfterDeleting.mono {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    {H : SimplexHypergraph V}
    {deleted₁ deleted₂ : SimplexHypergraph.DeletionFamily V}
    (hfree : NoSimplexAfterDeleting H deleted₁)
    (hdel : ∀ j, deleted₁ j ⊆ deleted₂ j) :
    NoSimplexAfterDeleting H deleted₂ := by
  apply (isSimplexCover_iff_noSimplexAfterDeleting H deleted₂).1
  apply SimplexHypergraph.IsSimplexCover.mono
    ((isSimplexCover_iff_noSimplexAfterDeleting
      H deleted₁).2 hfree)
  exact hdel

/-- Deleting nothing is a cover exactly in the simplex-free case. -/
theorem emptyDeletion_isSimplexCover_iff {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.IsSimplexCover (SimplexHypergraph.emptyDeletion V) ↔
      H.IsSimplexFree := by
  rw [isSimplexCover_iff_noSimplexAfterDeleting,
    NoSimplexAfterDeleting,
    SimplexHypergraph.IsSimplexFree,
    SimplexHypergraph.deleteEdges_empty_simplexFinset]
  rfl

end Wikipedia.SzemeredisTheorem
