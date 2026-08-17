import ErdosProblems.Erdos842.ChordCrossing

/-!
# Good one-side-per-triangle selections

For canonical triangle coordinates, a choice in `Fin 3` specifies the side
opposite that coordinate.  This file packages the resulting crossing
relation for Petrov's odd-transversal lemma and constructs the compressed
Hamiltonian endpoint order of a selected family of sides.
-/

namespace Erdos842

namespace GoodChords

open ChordCrossing

/-- The three vertices of triangle `i`, in its canonical coordinates. -/
def triangleVertices {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (i : Fin n) (j : Fin 3) : Fin (3 * n) :=
  triangleCoord.symm (i, j)

@[simp]
lemma triangleCoord_triangleVertices {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (i : Fin n) (j : Fin 3) :
    triangleCoord (triangleVertices triangleCoord i j) = (i, j) := by
  simp [triangleVertices]

/-- Crossing relation between side choices of canonical triangles. -/
def crossRel {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    OddTransversal.CrossRel (fun _ : Fin n ↦ Fin 3) :=
  fun i j ei ej ↦ i ≠ j ∧
    triangleCrossRel (triangleVertices triangleCoord) i j ei ej

/-- Sides belonging to distinct canonical triangles have pairwise disjoint
endpoints, so their chord-crossing relation is symmetric. -/
lemma crossRel_comm_of_ne {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {i j : Fin n} (hij : i ≠ j) (ei ej : Fin 3) :
    crossRel triangleCoord i j ei ej ↔
      crossRel triangleCoord j i ej ei := by
  simp only [crossRel, hij, ne_eq, not_false_eq_true, true_and, Ne.symm hij]
  unfold triangleCrossRel
  apply crosses_comm_of_endpoint_ne
  all_goals
    intro h
    apply hij
    have hc := congrArg triangleCoord h
    simpa [triangleSide, triangleVertices] using congrArg Prod.fst hc

/-- Two sides of the same triangle do not cross. -/
lemma not_crossRel_self {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (i : Fin n) (ei ej : Fin 3) :
    ¬ crossRel triangleCoord i i ei ej := by
  simp [crossRel]

/-- Full symmetry in the form required by `OddTransversal`. -/
lemma crossRel_symmetric {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    OddTransversal.Symmetric (fun _ : Fin n ↦ Fin 3) (crossRel triangleCoord) := by
  intro i j ei ej
  by_cases hij : i = j
  · subst j
    simp only [not_crossRel_self]
  · exact crossRel_comm_of_ne triangleCoord hij ei ej

/-- Every bipartite crossing degree is even. -/
lemma crossDegree_even {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (i j : Fin n) (ei : Fin 3) :
    Even (OddTransversal.crossDegree (fun _ : Fin n ↦ Fin 3)
      (crossRel triangleCoord) i j ei) := by
  by_cases hij : i = j
  · subst j
    unfold OddTransversal.crossDegree
    simp [crossRel]
  · have h := triangle_crossDegree_even (triangleVertices triangleCoord) i j ei
    unfold OddTransversal.crossDegree at h ⊢
    convert h using 1
    congr 1
    ext ej
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change (i ≠ j ∧ triangleCrossRel (triangleVertices triangleCoord) i j ei ej) ↔ _
    exact and_iff_right hij

/-- A good choice selects one side of each triangle and has even selected
crossing degree at every triangle. -/
abbrev GoodSelection {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :=
  OddTransversal.goodTransversals (fun _ : Fin n ↦ Fin 3) (crossRel triangleCoord)

/-- Finset presentation of all good side selections. -/
noncomputable def goodSelections {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    Finset (Fin n → Fin 3) := by
  classical
  exact Finset.univ.filter fun f ↦
    OddTransversal.Good (fun _ : Fin n ↦ Fin 3) (crossRel triangleCoord) f

@[simp]
lemma mem_goodSelections {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) :
    f ∈ goodSelections triangleCoord ↔
      OddTransversal.Good (fun _ : Fin n ↦ Fin 3) (crossRel triangleCoord) f := by
  classical
  simp [goodSelections]

/-- The subtype and finset presentations have the same cardinality. -/
lemma card_goodSelections_eq_card_goodSelection {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    (goodSelections triangleCoord).card =
      Fintype.card (GoodSelection triangleCoord) := by
  classical
  change (goodSelections triangleCoord).card =
    Fintype.card {f : Fin n → Fin 3 //
      OddTransversal.Good (fun _ : Fin n ↦ Fin 3) (crossRel triangleCoord) f}
  symm
  simpa only [goodSelections] using
    (Fintype.card_subtype (fun f : Fin n → Fin 3 ↦
      OddTransversal.Good (fun _ : Fin n ↦ Fin 3) (crossRel triangleCoord) f))

/-- Petrov's lemma gives an odd number of good side selections. -/
theorem odd_card_goodSelection {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    Odd (Fintype.card (GoodSelection triangleCoord)) := by
  apply OddTransversal.odd_goodTransversals_fin_three n
    (crossRel triangleCoord) (crossRel_symmetric triangleCoord)
  intro i j ei _hij
  exact crossDegree_even triangleCoord i j ei

/-- Finset-cardinality form of `odd_card_goodSelection`. -/
theorem odd_card_goodSelections {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    Odd (goodSelections triangleCoord).card := by
  rw [card_goodSelections_eq_card_goodSelection]
  exact odd_card_goodSelection triangleCoord

/-! ## Compressing the selected endpoints in Hamiltonian order -/

/-- The endpoint of the side selected at triangle `p.1`.  Endpoint `0` is
the first component of `triangleSide`, and endpoint `1` the second. -/
def selectedEndpoint {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (p : Endpoint (Fin n)) : Fin (3 * n) :=
  if p.2 = 0 then
    (triangleSide (triangleVertices triangleCoord p.1) (f p.1)).1
  else
    (triangleSide (triangleVertices triangleCoord p.1) (f p.1)).2

@[simp]
lemma selectedEndpoint_zero {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (i : Fin n) :
    selectedEndpoint triangleCoord f (i, 0) =
      (triangleSide (triangleVertices triangleCoord i) (f i)).1 := by
  simp [selectedEndpoint]

@[simp]
lemma selectedEndpoint_one {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (i : Fin n) :
    selectedEndpoint triangleCoord f (i, 1) =
      (triangleSide (triangleVertices triangleCoord i) (f i)).2 := by
  simp [selectedEndpoint]

@[simp]
private lemma fin_three_add_one_ne_add_two (k : Fin 3) : k + 1 ≠ k + 2 := by
  fin_cases k <;> decide

@[simp]
lemma triangleCoord_selectedEndpoint {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (i : Fin n) (e : Fin 2) :
    triangleCoord (selectedEndpoint triangleCoord f (i, e)) =
      (i, if e = 0 then f i + 1 else f i + 2) := by
  fin_cases e <;> simp [selectedEndpoint, triangleSide, triangleVertices]

/-- The chosen sides have pairwise distinct indexed endpoints. -/
lemma selectedEndpoint_injective {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) :
    Function.Injective (selectedEndpoint triangleCoord f) := by
  rintro ⟨i, e⟩ ⟨j, e'⟩ h
  have hc := congrArg triangleCoord h
  rw [triangleCoord_selectedEndpoint, triangleCoord_selectedEndpoint] at hc
  have hij : i = j := congrArg Prod.fst hc
  subst j
  congr 1
  fin_cases e <;> fin_cases e' <;>
    simp at hc ⊢

/-- The vertices retained after deleting the unused vertex opposite each
selected side. -/
noncomputable def selectedVertices {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) : Finset (Fin (3 * n)) := by
  classical
  exact Finset.univ.image (selectedEndpoint triangleCoord f)

@[simp]
lemma mem_selectedVertices {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (v : Fin (3 * n)) :
    v ∈ selectedVertices triangleCoord f ↔
      ∃ p : Endpoint (Fin n), selectedEndpoint triangleCoord f p = v := by
  classical
  simp [selectedVertices]

lemma card_selectedVertices {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) :
    (selectedVertices triangleCoord f).card = 2 * Fintype.card (Fin n) := by
  classical
  unfold selectedVertices
  rw [Finset.card_image_of_injective _ (selectedEndpoint_injective triangleCoord f),
    Finset.card_univ, Fintype.card_prod]
  simp [Nat.mul_comm]

/-- The selected endpoint as an element of the retained-vertex subtype. -/
noncomputable def selectedEndpointSubtype {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (p : Endpoint (Fin n)) :
    selectedVertices triangleCoord f := by
  refine ⟨selectedEndpoint triangleCoord f p, ?_⟩
  exact (mem_selectedVertices triangleCoord f _).2 ⟨p, rfl⟩

/-- Each retained vertex is uniquely one selected endpoint. -/
noncomputable def endpointEquivSelectedVertices {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) :
    Endpoint (Fin n) ≃ selectedVertices triangleCoord f := by
  apply Equiv.ofBijective (selectedEndpointSubtype triangleCoord f)
  constructor
  · intro p q h
    apply selectedEndpoint_injective triangleCoord f
    exact congrArg Subtype.val h
  · rintro ⟨v, hv⟩
    obtain ⟨p, hp⟩ := (mem_selectedVertices triangleCoord f v).1 hv
    refine ⟨p, Subtype.ext ?_⟩
    exact hp

/-- Enumerate the retained endpoints in their inherited Hamiltonian order. -/
noncomputable def endpointCyclicOrder {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) :
    Endpoint (Fin n) ≃ Fin (2 * Fintype.card (Fin n)) :=
  (endpointEquivSelectedVertices triangleCoord f).trans
    ((selectedVertices triangleCoord f).orderIsoOfFin
      (card_selectedVertices triangleCoord f)).symm.toEquiv

/-- Compression to retained ranks preserves the inherited strict order. -/
lemma endpointCyclicOrder_lt_iff {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (p q : Endpoint (Fin n)) :
    endpointCyclicOrder triangleCoord f p < endpointCyclicOrder triangleCoord f q ↔
      selectedEndpoint triangleCoord f p < selectedEndpoint triangleCoord f q := by
  change
    ((selectedVertices triangleCoord f).orderIsoOfFin
      (card_selectedVertices triangleCoord f)).symm
        (endpointEquivSelectedVertices triangleCoord f p) <
      ((selectedVertices triangleCoord f).orderIsoOfFin
      (card_selectedVertices triangleCoord f)).symm
        (endpointEquivSelectedVertices triangleCoord f q) ↔ _
  rw [OrderIso.lt_iff_lt]
  rfl

lemma between_endpointCyclicOrder_iff {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (p q r : Endpoint (Fin n)) :
    Between (endpointCyclicOrder triangleCoord f p)
        (endpointCyclicOrder triangleCoord f q)
        (endpointCyclicOrder triangleCoord f r) ↔
      Between (selectedEndpoint triangleCoord f p)
        (selectedEndpoint triangleCoord f q)
        (selectedEndpoint triangleCoord f r) := by
  simp only [Between, endpointCyclicOrder_lt_iff]

lemma crosses_endpointCyclicOrder_iff {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (p q r s : Endpoint (Fin n)) :
    Crosses (endpointCyclicOrder triangleCoord f p)
        (endpointCyclicOrder triangleCoord f q)
        (endpointCyclicOrder triangleCoord f r)
        (endpointCyclicOrder triangleCoord f s) ↔
      Crosses (selectedEndpoint triangleCoord f p)
        (selectedEndpoint triangleCoord f q)
        (selectedEndpoint triangleCoord f r)
        (selectedEndpoint triangleCoord f s) := by
  simp only [Crosses, between_endpointCyclicOrder_iff]

/-- Crossing in the compressed Hamiltonian order is exactly the canonical
side-crossing relation. -/
lemma selectedCrosses_endpointCyclicOrder_iff {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (i j : Fin n) :
    selectedCrosses (endpointCyclicOrder triangleCoord f) i j ↔
      crossRel triangleCoord i j (f i) (f j) := by
  by_cases hij : i = j
  · subst j
    simp [crossRel]
  · unfold selectedCrosses
    rw [crosses_endpointCyclicOrder_iff]
    simp only [selectedEndpoint_zero, selectedEndpoint_one]
    simp [crossRel, triangleCrossRel, hij]

/-- The compressed-family degree is the selected degree appearing in
Petrov's `Good` predicate. -/
lemma selectedCrossingDegree_endpointCyclicOrder {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) (i : Fin n) :
    selectedCrossingDegree (endpointCyclicOrder triangleCoord f) i =
      OddTransversal.selectedDegree (fun _ : Fin n ↦ Fin 3)
        (crossRel triangleCoord) f i := by
  classical
  rw [selectedCrossingDegree_eq_erase]
  unfold OddTransversal.selectedDegree
  apply congrArg Finset.card
  ext j
  simp only [Finset.mem_filter, Finset.mem_erase]
  exact and_congr_right fun _ ↦ selectedCrosses_endpointCyclicOrder_iff
    triangleCoord f i j

/-- A side selection is good exactly when its retained endpoints, compressed
in Hamiltonian order, all have even crossing degree. -/
theorem mem_goodSelections_iff_allSelectedCrossingDegreesEven {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (f : Fin n → Fin 3) :
    f ∈ goodSelections triangleCoord ↔
      AllSelectedCrossingDegreesEven (endpointCyclicOrder triangleCoord f) := by
  rw [mem_goodSelections]
  simp only [OddTransversal.Good, AllSelectedCrossingDegreesEven,
    selectedCrossingDegree_endpointCyclicOrder]

/-- Hence every good selection has exactly the two alternating endpoint
orientations used in the survivor-fibre argument. -/
theorem card_alternatingOrientations_eq_two_of_mem_goodSelections {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {f : Fin n → Fin 3} (hf : f ∈ goodSelections triangleCoord) :
    (alternatingOrientations (endpointCyclicOrder triangleCoord f)).card = 2 := by
  exact (all_even_iff_card_alternatingOrientations_eq_two _).mp
    ((mem_goodSelections_iff_allSelectedCrossingDegreesEven triangleCoord f).mp hf)

@[simp]
lemma goodSelection_mem_goodSelections {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (g : GoodSelection triangleCoord) :
    g.1 ∈ goodSelections triangleCoord := by
  exact (mem_goodSelections triangleCoord g.1).2 g.2

lemma goodSelection_allSelectedCrossingDegreesEven {n : ℕ}
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (g : GoodSelection triangleCoord) :
    AllSelectedCrossingDegreesEven
      (endpointCyclicOrder triangleCoord g.1) := by
  exact (mem_goodSelections_iff_allSelectedCrossingDegreesEven
    triangleCoord g.1).mp (goodSelection_mem_goodSelections triangleCoord g)

end GoodChords

end Erdos842
