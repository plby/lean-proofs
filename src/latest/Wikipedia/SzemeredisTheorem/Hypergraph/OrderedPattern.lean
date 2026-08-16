import Wikipedia.SzemeredisTheorem.Finite.ProductMean

/-!
# Complete ordered partite hypergraph patterns

Recursive hypergraph removal naturally produces lower-rank constraints on a
fixed collection of vertex classes.  It is convenient to index an ordered
rank-`r` face by an embedding `Fin r ↪ Fin k`.  This permits composition of
faces without quotienting by permutations.

This file defines weighted and unweighted complete ordered patterns, their
normalized occurrence counts, deletions, and the uniform removal property
used by the rank induction.  Rank zero is proved directly.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The increasing rank-`r` face among `k` vertex classes with a specified
canonical order. -/
abbrev OrderedFace (k r : ℕ) :=
  Fin r ↪o Fin k

instance orderedFaceDecidableEq
    (k r : ℕ) : DecidableEq (OrderedFace k r) :=
  Function.Injective.decidableEq
    (f := fun e : OrderedFace k r => (e : Fin r → Fin k))
    DFunLike.coe_injective

/-- Restrict a full labelled tuple along an ordered face. -/
def orderedFaceTuple
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (x : Fin k → G) :
    Fin r → G :=
  fun i => x (e i)

/-- Vertex coordinates outside an ordered face. -/
abbrev OrderedFaceComplement
    {k r : ℕ} (e : OrderedFace k r) :=
  {v : Fin k // v ∉ Set.range e}

/-- Split the full vertex index into an ordered face and its complement. -/
noncomputable def orderedFaceSumEquiv
    {k r : ℕ} (e : OrderedFace k r) :
    Fin r ⊕ OrderedFaceComplement e ≃ Fin k :=
  (Equiv.sumCongr e.toEmbedding.toEquivRange
      (Equiv.refl (OrderedFaceComplement e))).trans
    (Equiv.sumCompl
      (fun v : Fin k => v ∈ Set.range e))

/-- Split a full tuple into its values on an ordered face and on the
complementary vertex coordinates. -/
noncomputable def splitOrderedFaceEquiv
    {G : Type*} {k r : ℕ} (e : OrderedFace k r) :
    (Fin k → G) ≃
      ((Fin r → G) × (OrderedFaceComplement e → G)) :=
  (Equiv.piCongrLeft (fun _ : Fin k => G)
      (orderedFaceSumEquiv e)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : Fin r ⊕ OrderedFaceComplement e => G))

@[simp]
theorem splitOrderedFaceEquiv_fst
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (x : Fin k → G) :
    (splitOrderedFaceEquiv e x).1 =
      orderedFaceTuple e x := by
  funext i
  simp [splitOrderedFaceEquiv, orderedFaceSumEquiv,
    orderedFaceTuple]
  rfl

/-- Restrict a full tuple to the complementary vertex coordinates. -/
def orderedFaceComplementTuple
    {G : Type*} {k r : ℕ}
    (e : OrderedFace k r) (x : Fin k → G) :
    OrderedFaceComplement e → G :=
  fun v => x v.1

@[simp]
theorem splitOrderedFaceEquiv_snd
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (x : Fin k → G) :
    (splitOrderedFaceEquiv e x).2 =
      orderedFaceComplementTuple e x := by
  funext v
  simp [splitOrderedFaceEquiv, orderedFaceSumEquiv,
    orderedFaceComplementTuple]

@[simp]
theorem orderedFaceTuple_splitOrderedFaceEquiv_symm
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple e
        ((splitOrderedFaceEquiv e).symm (y, z)) = y := by
  rw [← splitOrderedFaceEquiv_fst]
  simp

@[simp]
theorem orderedFaceComplementTuple_splitOrderedFaceEquiv_symm
    {G : Type*} {k r : ℕ} (e : OrderedFace k r)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceComplementTuple e
        ((splitOrderedFaceEquiv e).symm (y, z)) = z := by
  rw [← splitOrderedFaceEquiv_snd]
  simp

/-- Fubini decomposition of a full-tuple mean into an ordered face and its
complement. -/
theorem mean_splitOrderedFace
    {G : Type*} [Fintype G] {k r : ℕ}
    (e : OrderedFace k r) (f : (Fin k → G) → ℝ) :
    mean f =
      mean₂ (fun y : Fin r → G =>
        fun z : OrderedFaceComplement e → G =>
          f ((splitOrderedFaceEquiv e).symm (y, z))) := by
  calc
    mean f =
        mean (fun p :
          (Fin r → G) × (OrderedFaceComplement e → G) =>
            f ((splitOrderedFaceEquiv e).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (splitOrderedFaceEquiv e)
      intro x
      simp
    _ = _ := by
      simpa only [Prod.eta] using
        (mean_prod_type
          (fun y : Fin r → G =>
            fun z : OrderedFaceComplement e → G =>
              f ((splitOrderedFaceEquiv e).symm (y, z))))

/-- Two distinct increasing faces of the same rank differ by a vertex of
the first face which is absent from the second. -/
theorem exists_orderedFace_coordinate_not_mem_range
    {k r : ℕ} {e f : OrderedFace k r}
    (hef : e ≠ f) :
    ∃ i : Fin r, e i ∉ Set.range f := by
  classical
  by_contra hnone
  push Not at hnone
  have hsubset :
      Finset.univ.map e.toEmbedding ⊆
        Finset.univ.map f.toEmbedding := by
    intro v hv
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨j, hj⟩ := hnone i
    exact Finset.mem_map.mpr
      ⟨j, Finset.mem_univ _, hj⟩
  have heq :
      Finset.univ.map e.toEmbedding =
        Finset.univ.map f.toEmbedding := by
    apply Finset.eq_of_subset_of_card_le hsubset
    simp
  have hrange : Set.range e = Set.range f := by
    ext v
    have hv := Finset.ext_iff.mp heq v
    simpa using hv
  exact hef (OrderEmbedding.range_inj.mp hrange)

/-- A canonical missing coordinate for two distinct ordered faces. -/
noncomputable def orderedFaceMissingCoordinate
    {k r : ℕ} (e f : OrderedFace k r) (hef : e ≠ f) :
    Fin r :=
  Classical.choose
    (exists_orderedFace_coordinate_not_mem_range hef)

theorem orderedFaceMissingCoordinate_not_mem_range
    {k r : ℕ} (e f : OrderedFace k r) (hef : e ≠ f) :
    e (orderedFaceMissingCoordinate e f hef) ∉
      Set.range f :=
  Classical.choose_spec
    (exists_orderedFace_coordinate_not_mem_range hef)

/-- A weighted complete ordered rank-`r` pattern. -/
structure WeightedOrderedPattern
    (G : Type*) (k r : ℕ) where
  edgeWeight : OrderedFace k r → (Fin r → G) → ℝ

namespace WeightedOrderedPattern

/-- Product of all ordered face weights on a labelled full tuple. -/
noncomputable def patternWeight
    {G : Type*} {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (x : Fin k → G) : ℝ :=
  ∏ e : OrderedFace k r,
    H.edgeWeight e (orderedFaceTuple e x)

/-- Normalized density of labelled pattern occurrences. -/
noncomputable def patternCount
    {G : Type*} [Fintype G] {k r : ℕ}
    (H : WeightedOrderedPattern G k r) : ℝ :=
  mean H.patternWeight

/-- Pointwise unit-interval bounds for every ordered edge weight. -/
def EdgeWeightsInUnitInterval
    {G : Type*} {k r : ℕ}
    (H : WeightedOrderedPattern G k r) : Prop :=
  ∀ e y, 0 ≤ H.edgeWeight e y ∧ H.edgeWeight e y ≤ 1

theorem patternWeight_nonneg
    {G : Type*} {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (hH : ∀ e y, 0 ≤ H.edgeWeight e y)
    (x : Fin k → G) :
    0 ≤ H.patternWeight x := by
  exact Finset.prod_nonneg fun e _ => hH e _

theorem patternCount_nonneg
    {G : Type*} [Fintype G] {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (hH : ∀ e y, 0 ≤ H.edgeWeight e y) :
    0 ≤ H.patternCount :=
  mean_nonneg (H.patternWeight_nonneg hH)

end WeightedOrderedPattern

/-- A predicate-valued complete ordered rank-`r` pattern. -/
structure OrderedPattern
    (G : Type*) (k r : ℕ) where
  edge : OrderedFace k r → (Fin r → G) → Prop

namespace OrderedPattern

/-- A labelled full tuple satisfies every ordered edge predicate. -/
def IsOccurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) : Prop :=
  ∀ e, H.edge e (orderedFaceTuple e x)

/-- The finite set of labelled occurrences. -/
noncomputable def occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r) :
    Finset (Fin k → G) := by
  classical
  exact Finset.univ.filter H.IsOccurrence

@[simp]
theorem mem_occurrenceFinset
    {G : Type*} [Fintype G] [DecidableEq G] {k r : ℕ}
    (H : OrderedPattern G k r)
    (x : Fin k → G) :
    x ∈ H.occurrenceFinset ↔ H.IsOccurrence x := by
  simp [occurrenceFinset]

/-- Regard predicates as zero-one edge weights. -/
noncomputable def toWeighted
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r) :
    WeightedOrderedPattern G k r := by
  classical
  exact
    { edgeWeight := fun e y =>
        if H.edge e y then 1 else 0 }

theorem toWeighted_edgeWeight_nonneg
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    0 ≤ H.toWeighted.edgeWeight e y := by
  classical
  by_cases h : H.edge e y <;>
    simp [toWeighted, h]

theorem toWeighted_edgeWeight_le_one
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    H.toWeighted.edgeWeight e y ≤ 1 := by
  classical
  by_cases h : H.edge e y <;>
    simp [toWeighted, h]

theorem toWeighted_unitInterval
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r) :
    H.toWeighted.EdgeWeightsInUnitInterval :=
  fun e y =>
    ⟨H.toWeighted_edgeWeight_nonneg e y,
      H.toWeighted_edgeWeight_le_one e y⟩

/-- An occurrence has zero-one pattern weight one. -/
theorem toWeighted_patternWeight_of_occurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    {x : Fin k → G} (hx : H.IsOccurrence x) :
    H.toWeighted.patternWeight x = 1 := by
  classical
  unfold WeightedOrderedPattern.patternWeight
  apply Finset.prod_eq_one
  intro e _he
  simp [toWeighted, hx e]

/-- A nonoccurrence has zero-one pattern weight zero. -/
theorem toWeighted_patternWeight_of_not_occurrence
    {G : Type*} {k r : ℕ}
    (H : OrderedPattern G k r)
    {x : Fin k → G} (hx : ¬H.IsOccurrence x) :
    H.toWeighted.patternWeight x = 0 := by
  classical
  unfold WeightedOrderedPattern.patternWeight
  obtain ⟨e, he⟩ := not_forall.mp hx
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  simp [toWeighted, he]

/-- The weighted normalized count is exactly the normalized cardinality of
the occurrence finset. -/
theorem toWeighted_patternCount_eq
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r) :
    H.toWeighted.patternCount =
      (H.occurrenceFinset.card : ℝ) /
        Fintype.card (Fin k → G) := by
  rw [WeightedOrderedPattern.patternCount]
  have hfun :
      H.toWeighted.patternWeight =
        finsetIndicator H.occurrenceFinset := by
    funext x
    by_cases hx : H.IsOccurrence x
    · rw [H.toWeighted_patternWeight_of_occurrence hx,
        finsetIndicator_of_mem]
      exact (H.mem_occurrenceFinset x).2 hx
    · rw [H.toWeighted_patternWeight_of_not_occurrence hx,
        finsetIndicator_of_not_mem]
      exact fun hmem =>
        hx ((H.mem_occurrenceFinset x).1 hmem)
  rw [hfun, mean_finsetIndicator]

/-- One deleted rank-`r` face set for every ordered face. -/
abbrev DeletionFamily
    {G : Type*} [DecidableEq G] (k r : ℕ) :=
  (e : OrderedFace k r) → Finset (Fin r → G)

/-- Every original occurrence meets at least one deleted ordered face. -/
def IsCover
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : OrderedPattern G k r)
    (D : DeletionFamily (G := G) k r) : Prop :=
  ∀ x, x ∈ H.occurrenceFinset →
    ∃ e, orderedFaceTuple e x ∈ D e

/-- Normalized density of the deletion in one ordered face. -/
noncomputable def faceDeletionDensity
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (D : DeletionFamily (G := G) k r)
    (e : OrderedFace k r) : ℝ :=
  (D e).card / Fintype.card (Fin r → G)

/-- Empty ordered deletion family. -/
def emptyDeletion
    {G : Type*} [DecidableEq G] (k r : ℕ) :
    DeletionFamily (G := G) k r :=
  fun _ => ∅

@[simp]
theorem faceDeletionDensity_empty
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ} (e : OrderedFace k r) :
    faceDeletionDensity
        (emptyDeletion (G := G) k r) e = 0 := by
  simp [faceDeletionDensity, emptyDeletion]

end OrderedPattern

/-- Uniform per-ordered-face removal for complete ordered rank-`r`
patterns on `k` equal finite vertex classes. -/
def HasUniformOrderedPatternRemoval (k r : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (G : Type) [Fintype G] [DecidableEq G] [Nonempty G],
        ∀ H : OrderedPattern G k r,
          H.toWeighted.patternCount < c →
            ∃ D : OrderedPattern.DeletionFamily
                (G := G) k r,
              H.IsCover D ∧
                ∀ e, OrderedPattern.faceDeletionDensity D e ≤ ε

/-- If one rank-zero occurrence exists, every full tuple is an occurrence.
-/
theorem OrderedPattern.isOccurrence_all_of_rank_zero
    {G : Type*} {k : ℕ}
    (H : OrderedPattern G k 0)
    {x₀ : Fin k → G} (hx₀ : H.IsOccurrence x₀)
    (x : Fin k → G) :
    H.IsOccurrence x := by
  intro e
  have htuple :
      orderedFaceTuple e x =
        orderedFaceTuple e x₀ := by
    funext i
    exact Fin.elim0 i
  rw [htuple]
  exact hx₀ e

/-- Rank-zero ordered removal: with threshold one, a count below the
threshold means that there are no occurrences at all. -/
theorem hasUniformOrderedPatternRemoval_zero (k : ℕ) :
    HasUniformOrderedPatternRemoval k 0 := by
  intro ε hε
  refine ⟨1, by norm_num, ?_⟩
  intro G _instFintype _instDecidableEq _instNonempty H hcount
  have hempty : H.occurrenceFinset = ∅ := by
    by_contra hne
    obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hx₀' : H.IsOccurrence x₀ :=
      (H.mem_occurrenceFinset x₀).1 hx₀
    have hall : H.occurrenceFinset = Finset.univ := by
      ext x
      simp only [H.mem_occurrenceFinset,
        Finset.mem_univ, iff_true]
      exact H.isOccurrence_all_of_rank_zero hx₀' x
    have hcount_one :
        H.toWeighted.patternCount = 1 := by
      rw [H.toWeighted_patternCount_eq, hall]
      simp
    rw [hcount_one] at hcount
    exact (lt_irrefl 1) hcount
  refine
    ⟨OrderedPattern.emptyDeletion k 0, ?_,
      fun e => ?_⟩
  · intro x hx
    rw [hempty] at hx
    simp at hx
  · rw [OrderedPattern.faceDeletionDensity_empty]
    exact hε.le

end Wikipedia.SzemeredisTheorem
