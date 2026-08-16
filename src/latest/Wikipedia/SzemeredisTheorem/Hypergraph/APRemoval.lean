import Wikipedia.SzemeredisTheorem.Hypergraph.APCorrespondence
import Wikipedia.SzemeredisTheorem.Hypergraph.Removal
import Wikipedia.SzemeredisTheorem.Szemeredi.Weighted
import Wikipedia.SzemeredisTheorem.Transference.APCut

/-!
# From partite simplex removal to dense arithmetic progressions

For a finite set `A ⊆ ZMod N`, its arithmetic-progression hypergraph has
one edge of colour `j` whenever the `j`th AP form belongs to `A`.  The
degenerate progressions of common difference zero give a large,
edge-disjoint family of labelled simplices.  Consequently every simplex
cover has normalized deletion cost at least `mean (1_A) / k`.

This is the elementary half of the standard deduction of dense
Szemerédi from the partite simplex-removal lemma.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- The unweighted partite hypergraph cut out by membership of each AP form
in `A`. -/
def apSetHypergraph (k N : ℕ) (A : Finset (ZMod N)) :
    SimplexHypergraph (fun _ : Fin k => ZMod N) where
  edge j x := apSimplexForm k N j x ∈ A

@[simp]
theorem apSetHypergraph_edge
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).edge j x ↔
      apSimplexForm k N j x ∈ A :=
  Iff.rfl

/-- The zero-one weight of the AP-set hypergraph is exactly the set
indicator evaluated on the corresponding AP form. -/
@[simp]
theorem apSetHypergraph_toWeighted_edgeWeight
    (k N : ℕ) (A : Finset (ZMod N))
    (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) :
    (apSetHypergraph k N A).toWeighted.edgeWeight j x =
      finsetIndicator A (apSimplexForm k N j x) := by
  classical
  by_cases hx : apSimplexForm k N j x ∈ A
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_edge]
    · exact (finsetIndicator_of_mem hx).symm
    · exact hx
  · rw [SimplexHypergraph.toWeighted_edgeWeight_of_not_edge]
    · exact (finsetIndicator_of_not_mem hx).symm
    · exact hx

/-- The labelled simplex density of the AP-set hypergraph is its normalized
cyclic arithmetic-progression count. -/
theorem apSetHypergraph_simplexCount_eq_cyclicAPCount
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    (apSetHypergraph (r + 2) N A).toWeighted.simplexCount =
      cyclicAPCount (r + 2) N (finsetIndicator A) := by
  rw [← apSimplexSystem_simplexCount_eq_cyclicAPCount
    r N (finsetIndicator A)]
  simp only [WeightedSimplexSystem.simplexCount]
  apply congrArg mean
  funext x
  apply Finset.prod_congr rfl
  intro j _
  exact apSetHypergraph_toWeighted_edgeWeight
    (r + 2) N A j (deleteCoordinate x j)

/-- Parameters for degenerate AP simplices: a member of `A` and the free
tail in the AP/simplex coordinate equivalence. -/
abbrev DiagonalAPParameter
    (r N : ℕ) (A : Finset (ZMod N)) :=
  ↥A × (Fin r → ZMod N)

/-- The labelled simplex corresponding to the constant progression with
value `a`. -/
def diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) → ZMod N :=
  simplexCoordinatesOfAP r N p.1.1 0 p.2

@[simp]
theorem simplexCoordinateSum_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    simplexCoordinateSum (r + 2) N
      (diagonalAPSimplex r N A p) = 0 := by
  simp [diagonalAPSimplex]

@[simp]
theorem simplexCoordinateMoment_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    simplexCoordinateMoment (r + 2) N
      (diagonalAPSimplex r N A p) = p.1.1 := by
  simp [diagonalAPSimplex]

/-- Every edge form on a degenerate AP simplex is the same member of `A`. -/
@[simp]
theorem apSimplexForm_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A)
    (j : Fin (r + 2)) :
    apSimplexForm (r + 2) N j
        (deleteCoordinate (diagonalAPSimplex r N A p) j) =
      p.1.1 := by
  rw [apSimplexForm_deleteCoordinate,
    simplexCoordinateMoment_diagonalAPSimplex,
    simplexCoordinateSum_diagonalAPSimplex]
  simp

/-- Every degenerate AP parameter gives an actual labelled simplex of the
AP-set hypergraph. -/
theorem diagonalAPSimplex_mem_simplexFinset
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    diagonalAPSimplex r N A p ∈
      (apSetHypergraph (r + 2) N A).simplexFinset := by
  letI : ∀ _ : Fin (r + 2), Fintype (ZMod N) :=
    fun _ => inferInstance
  rw [SimplexHypergraph.mem_simplexFinset]
  intro j
  rw [apSetHypergraph_edge,
    apSimplexForm_diagonalAPSimplex]
  exact p.1.2

/-- Distinct degenerate AP parameters give distinct labelled simplices. -/
theorem diagonalAPSimplex_injective
    (r N : ℕ) (A : Finset (ZMod N)) :
    Function.Injective (diagonalAPSimplex r N A) := by
  intro p q hpq
  apply Prod.ext
  · apply Subtype.ext
    have hmoment :=
      congrArg
        (simplexCoordinateMoment (r + 2) N) hpq
    simpa using hmoment
  · funext i
    exact congrFun hpq i.succ.succ

/-- Present a dependent deleted-coordinate vector by the canonical
`Fin n` list of its remaining coordinates. -/
noncomputable def deletedVectorToFinTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)

@[simp]
theorem deletedVectorToFinTuple_deleteCoordinate
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) (t : Fin n) :
    deletedVectorToFinTuple j (deleteCoordinate x j) t =
      x (j.succAbove t) :=
  rfl

/-- A full tuple is determined by one deleted-coordinate tuple together
with its total sum. -/
theorem eq_of_deletedVectorToFinTuple_eq_of_sum_eq
    {G : Type*} [AddCommGroup G] {n : ℕ}
    {x y : Fin (n + 1) → G}
    {j l : Fin (n + 1)}
    (hjl : j = l)
    (hdeleted :
      deletedVectorToFinTuple j (deleteCoordinate x j) =
        deletedVectorToFinTuple l (deleteCoordinate y l))
    (hsum : (∑ i, x i) = ∑ i, y i) :
    x = y := by
  subst l
  have hother :
      ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i =
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          y i := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun hdeleted t
  have hj : x j = y j := by
    apply add_left_cancel
      (a :=
        ∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i)
    calc
      (∑ i ∈ (Finset.univ : Finset (Fin (n + 1))).erase j,
          x i) + x j =
          ∑ i, x i :=
        Finset.sum_erase_add _ _ (Finset.mem_univ j)
      _ = ∑ i, y i := hsum
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              y i) + y j :=
        (Finset.sum_erase_add _ _ (Finset.mem_univ j)).symm
      _ =
          (∑ i ∈
              (Finset.univ : Finset (Fin (n + 1))).erase j,
              x i) + y j := by
        rw [hother]
  funext i
  by_cases hij : i = j
  · simpa [hij] using hj
  · obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq hij
    subst i
    exact congrFun hdeleted t

namespace SimplexHypergraph

/-- All deleted coloured faces, embedded into one fixed finite type by the
canonical ordering of each deleted coordinate space. -/
noncomputable def deletionSlotFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G)) :
    Finset (Fin (n + 1) × (Fin n → G)) := by
  classical
  exact Finset.univ.biUnion fun j =>
    (deleted j).image fun x =>
      (j, deletedVectorToFinTuple j x)

theorem mem_deletionSlotFinset
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j)
    (hx : x ∈ deleted j) :
    (j, deletedVectorToFinTuple j x) ∈
      deletionSlotFinset deleted := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, ?_⟩
  exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- The fixed-type union of deletion slots has cardinality at most the sum
of the individual coloured deletion cardinalities. -/
theorem card_deletionSlotFinset_le_deletionCount
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (deleted :
      DeletionFamily (fun _ : Fin (n + 1) => G)) :
    (deletionSlotFinset deleted).card ≤
      deletionCount deleted := by
  classical
  calc
    (deletionSlotFinset deleted).card ≤
        ∑ j : Fin (n + 1),
          ((deleted j).image fun x =>
            (j, deletedVectorToFinTuple j x)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ j : Fin (n + 1), (deleted j).card := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.card_image_le
    _ = deletionCount deleted := rfl

end SimplexHypergraph

/-- Choose one deleted colour witnessing that a cover meets a given
degenerate arithmetic-progression simplex. -/
noncomputable def diagonalCoverColor
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) :=
  Classical.choose
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))

@[simp]
theorem diagonalCoverColor_mem
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    deleteCoordinate (diagonalAPSimplex r N A p)
        (diagonalCoverColor r N A deleted hcover p) ∈
      deleted (diagonalCoverColor r N A deleted hcover p) :=
  Classical.choose_spec
    (hcover (diagonalAPSimplex r N A p)
      (diagonalAPSimplex_mem_simplexFinset r N A p))

/-- Encode the face selected by a cover in a fixed finite disjoint union of
coloured deletion slots. -/
noncomputable def diagonalCoveredSlot
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    Fin (r + 2) × (Fin (r + 1) → ZMod N) :=
  let j := diagonalCoverColor r N A deleted hcover p
  (j, deletedVectorToFinTuple j
    (deleteCoordinate (diagonalAPSimplex r N A p) j))

theorem diagonalCoveredSlot_mem_deletionSlotFinset
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted)
    (p : DiagonalAPParameter r N A) :
    diagonalCoveredSlot r N A deleted hcover p ∈
      SimplexHypergraph.deletionSlotFinset deleted := by
  classical
  exact SimplexHypergraph.mem_deletionSlotFinset deleted
    (diagonalCoverColor r N A deleted hcover p)
    (deleteCoordinate (diagonalAPSimplex r N A p)
      (diagonalCoverColor r N A deleted hcover p))
    (diagonalCoverColor_mem r N A deleted hcover p)

/-- No deleted coloured face can cover two different members of the
degenerate simplex family.  Equality off the deleted coordinate and equality
of the total coordinate sums recover the whole labelled simplex. -/
theorem diagonalCoveredSlot_injective
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    Function.Injective
      (diagonalCoveredSlot r N A deleted hcover) := by
  intro p q hpq
  apply diagonalAPSimplex_injective r N A
  apply eq_of_deletedVectorToFinTuple_eq_of_sum_eq
  · exact congrArg Prod.fst hpq
  · exact congrArg Prod.snd hpq
  · change
      simplexCoordinateSum (r + 2) N
          (diagonalAPSimplex r N A p) =
        simplexCoordinateSum (r + 2) N
          (diagonalAPSimplex r N A q)
    simp

/-- The parameter set for the degenerate simplex family has the expected
cardinality `|A| N^r`. -/
@[simp]
theorem card_diagonalAPParameter
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N)) :
    Fintype.card (DiagonalAPParameter r N A) =
      A.card * N ^ r := by
  simp [DiagonalAPParameter, ZMod.card]

/-- Every cover of the AP-set hypergraph deletes at least one distinct face
for each member of the degenerate simplex family. -/
theorem card_diagonalAPParameter_le_deletionCount
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    Fintype.card (DiagonalAPParameter r N A) ≤
      SimplexHypergraph.deletionCount deleted := by
  classical
  let f := diagonalCoveredSlot r N A deleted hcover
  calc
    Fintype.card (DiagonalAPParameter r N A) =
        (Finset.univ.image f).card := by
      rw [Finset.card_image_of_injective _ 
        (diagonalCoveredSlot_injective r N A deleted hcover)]
      simp
    _ ≤
        (SimplexHypergraph.deletionSlotFinset deleted).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hy
      exact diagonalCoveredSlot_mem_deletionSlotFinset
        r N A deleted hcover p
    _ ≤ SimplexHypergraph.deletionCount deleted :=
      SimplexHypergraph.card_deletionSlotFinset_le_deletionCount
        deleted

/-- For constant vertex classes `ZMod N`, the total number of coloured face
slots is `(r+2) N^(r+1)`. -/
@[simp]
theorem deletionCapacity_zmod
    (r N : ℕ) [NeZero N] :
    SimplexHypergraph.deletionCapacity
        (fun _ : Fin (r + 2) => ZMod N) =
      (r + 2) * N ^ (r + 1) := by
  simp [SimplexHypergraph.deletionCapacity, DeletedVector,
    Fintype.card_pi, ZMod.card]

/-- A simplex cover of the AP-set hypergraph has normalized deletion cost at
least one `1/(r+2)` share of the density of `A`.  This is the exact
edge-disjoint-degenerate-simplices estimate used in the removal argument. -/
theorem mean_finsetIndicator_div_le_normalizedDeletionCost
    (r N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (deleted :
      SimplexHypergraph.DeletionFamily
        (fun _ : Fin (r + 2) => ZMod N))
    (hcover :
      (apSetHypergraph (r + 2) N A).IsSimplexCover deleted) :
    mean (finsetIndicator A) / (r + 2 : ℝ) ≤
      SimplexHypergraph.normalizedDeletionCost deleted := by
  have hcount :
      A.card * N ^ r ≤
        SimplexHypergraph.deletionCount deleted := by
    simpa using
      card_diagonalAPParameter_le_deletionCount
        r N A deleted hcover
  have hN : (N : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne N)
  rw [mean_finsetIndicator, ZMod.card,
    SimplexHypergraph.normalizedDeletionCost,
    deletionCapacity_zmod]
  calc
    (A.card : ℝ) / (N : ℝ) / (r + 2 : ℝ) =
        ((A.card * N ^ r : ℕ) : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul, Nat.cast_pow]
      field_simp
      ring
    _ ≤
        (SimplexHypergraph.deletionCount deleted : ℝ) /
          (((r + 2) * N ^ (r + 1) : ℕ) : ℝ) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcount
      · positivity

/-- Uniform partite simplex removal on cyclic vertex classes of a fixed
number of colours.  The constant is independent of the modulus.  This is the
precise deep combinatorial input still required from the hypergraph
regularity/removal development. -/
def HasUniformCyclicPartiteSimplexRemoval (k : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ c : ℝ, 0 < c ∧
      ∀ (N : ℕ) [NeZero N],
        ∀ H :
            SimplexHypergraph (fun _ : Fin k => ZMod N),
          H.toWeighted.simplexCount < c →
            ∃ deleted :
                SimplexHypergraph.DeletionFamily
                  (fun _ : Fin k => ZMod N),
              H.IsSimplexCover deleted ∧
                SimplexHypergraph.normalizedDeletionCost
                    deleted ≤ ε

/-- Uniform partite simplex removal implies a uniform quantitative dense
Szemerédi theorem.  The proof is the standard contrapositive: a set whose AP
hypergraph has too few simplices admits a cheap cover, while the
edge-disjoint degenerate simplices force every cover to cost at least
`density / k`. -/
theorem exists_uniformDenseAPCount_of_simplexRemoval
    (r : ℕ)
    (hrem :
      HasUniformCyclicPartiteSimplexRemoval (r + 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformDenseAPCount (r + 2) δ c := by
  let ε : ℝ := (δ / (r + 2 : ℝ)) / 2
  have hk : 0 < (r + 2 : ℝ) := by positivity
  have hbase : 0 < δ / (r + 2 : ℝ) :=
    div_pos hδ hk
  have hε : 0 < ε := by
    exact div_pos hbase (by norm_num)
  obtain ⟨c, hc, hremove⟩ := hrem ε hε
  refine ⟨c, hc, ?_⟩
  intro N inst A hA
  by_contra hcount
  have hcount_lt :
      cyclicAPCount (r + 2) N (finsetIndicator A) < c :=
    lt_of_not_ge hcount
  have hsimplex_lt :
      (apSetHypergraph (r + 2) N A).toWeighted.simplexCount <
        c := by
    simpa [apSetHypergraph_simplexCount_eq_cyclicAPCount]
      using hcount_lt
  obtain ⟨deleted, hcover, hcost⟩ :=
    hremove N (apSetHypergraph (r + 2) N A) hsimplex_lt
  have hlower :
      mean (finsetIndicator A) / (r + 2 : ℝ) ≤
        SimplexHypergraph.normalizedDeletionCost deleted :=
    mean_finsetIndicator_div_le_normalizedDeletionCost
      r N A deleted hcover
  have hdensity :
      δ / (r + 2 : ℝ) ≤
        mean (finsetIndicator A) / (r + 2 : ℝ) :=
    div_le_div_of_nonneg_right hA hk.le
  have hε_lt : ε < δ / (r + 2 : ℝ) := by
    dsimp [ε]
    linarith
  linarith

/-- The thresholding argument upgrades the set-valued consequence of
simplex removal to bounded weights, retaining a positive uniform constant. -/
theorem exists_uniformWeightedAPCount_of_simplexRemoval
    (r : ℕ)
    (hrem :
      HasUniformCyclicPartiteSimplexRemoval (r + 2))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧
      HasUniformWeightedAPCount (r + 2) δ c := by
  obtain ⟨c₀, hc₀, hdense⟩ :=
    exists_uniformDenseAPCount_of_simplexRemoval
      r hrem (half_pos hδ)
  refine ⟨(δ / 2) ^ (r + 2) * c₀, ?_, ?_⟩
  · exact mul_pos (pow_pos (half_pos hδ) _) hc₀
  · intro N inst g hg0 hg1 hmean
    exact weightedAPCount_of_denseAPCount
      hδ.le (hdense N) hg0 hg1 hmean

end Wikipedia.SzemeredisTheorem
