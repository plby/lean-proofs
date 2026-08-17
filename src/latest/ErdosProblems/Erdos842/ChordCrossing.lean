import ErdosProblems.Erdos842.OddTransversal

/-!
# Crossing parities for chords in cyclic order

Vertices are represented by `Fin m` in their order around the Hamiltonian
cycle.  Two chords cross when exactly one endpoint of the second chord lies in
the open linear interval cut out by the endpoints of the first.  This is the
usual alternating-endpoints definition and is independent of which endpoint
of either chord is listed first.

The first part of the file proves the local parity input to Petrov's
odd-transversal theorem: a fixed chord crosses either zero or two sides of a
triangle, counted modulo two.  The second part treats a family of disjoint
chords and relates even crossing degree to the two globally alternating
endpoint orientations.
-/

open scoped BigOperators

namespace Erdos842

namespace ChordCrossing

universe u

/-! ## Chords in an ambient finite cyclic order -/

/-- `Between a b x` means that `x` lies strictly between `a` and `b` in the
linear order obtained by cutting the cyclic order anywhere outside the three
points.  The definition is symmetric in `a` and `b`. -/
abbrev Between {m : ℕ} (a b x : Fin m) : Prop :=
  (a < x ∧ x < b) ∨ (b < x ∧ x < a)

/-- The side of the chord `ab` on which `x` lies, with the open interval as
one side. -/
def side {m : ℕ} (a b x : Fin m) : Bool :=
  decide (Between a b x)

/-- Chords `ab` and `cd` cross when exactly one of `c,d` is strictly between
`a,b`. -/
def Crosses {m : ℕ} (a b c d : Fin m) : Prop :=
  (Between a b c ∧ ¬ Between a b d) ∨
    (Between a b d ∧ ¬ Between a b c)

instance {m : ℕ} (a b c d : Fin m) : Decidable (Crosses a b c d) :=
  inferInstanceAs (Decidable
    ((Between a b c ∧ ¬ Between a b d) ∨
      (Between a b d ∧ ¬ Between a b c)))

lemma crosses_iff_side_ne {m : ℕ} (a b c d : Fin m) :
    Crosses a b c d ↔ side a b c ≠ side a b d := by
  simp only [Crosses, side]
  by_cases hc : Between a b c <;> by_cases hd : Between a b d <;> simp [hc, hd]

@[simp]
lemma between_swap {m : ℕ} (a b x : Fin m) : Between b a x ↔ Between a b x := by
  simp only [Between]
  tauto

@[simp]
lemma between_left_self {m : ℕ} (a b : Fin m) : ¬ Between a b a := by
  simp [Between]

@[simp]
lemma between_right_self {m : ℕ} (a b : Fin m) : ¬ Between a b b := by
  simp [Between]

@[simp]
lemma side_swap {m : ℕ} (a b x : Fin m) : side b a x = side a b x := by
  simp [side, between_swap]

@[simp]
lemma side_left_self {m : ℕ} (a b : Fin m) : side a b a = false := by
  simp [side]

@[simp]
lemma side_right_self {m : ℕ} (a b : Fin m) : side a b b = false := by
  simp [side]

@[simp]
lemma crosses_swap_left {m : ℕ} (a b c d : Fin m) :
    Crosses b a c d ↔ Crosses a b c d := by
  simp [Crosses, between_swap]

@[simp]
lemma crosses_swap_right {m : ℕ} (a b c d : Fin m) :
    Crosses a b d c ↔ Crosses a b c d := by
  simp [Crosses, and_comm, or_comm]

/-- Alternating endpoints is symmetric between the two chords.  Endpoint
disjointness is exactly what is needed at the boundary cases of the cut. -/
lemma crosses_comm_of_endpoint_ne {m : ℕ} {a b c d : Fin m}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    Crosses a b c d ↔ Crosses c d a b := by
  simp only [Crosses, Between]
  omega

/-! ## The three sides of a triangle -/

/-- The side of a triangle opposite `k`.  As `k` runs through `Fin 3`, these
are the three unordered sides, each exactly once. -/
def triangleSide {m : ℕ} (t : Fin 3 → Fin m) (k : Fin 3) : Fin m × Fin m :=
  (t (k + 1), t (k + 2))

/-- Crossing relation on the three side choices of indexed triangles. -/
def triangleCrossRel {m : ℕ} {I : Type u} (triangle : I → Fin 3 → Fin m) :
    OddTransversal.CrossRel (fun _ : I ↦ Fin 3) :=
  fun i j ei ej ↦
    Crosses (triangleSide (triangle i) ei).1 (triangleSide (triangle i) ei).2
      (triangleSide (triangle j) ej).1 (triangleSide (triangle j) ej).2

/-- Around a 3-cycle, the number of changes of any Boolean label is even.
This is the local reason a chord crosses an even number of triangle sides. -/
lemma even_bool_changes_three (p : Fin 3 → Bool) :
    Even (((Finset.univ : Finset (Fin 3)).filter fun k ↦
      p (k + 1) ≠ p (k + 2)).card) := by
  classical
  rw [OddTransversal.even_iff_cast_zmod_two_eq_zero,
    OddTransversal.cast_card_filter_eq_sum_indicator]
  simp only [Fin.sum_univ_succ]
  cases h0 : p 0 <;> cases h1 : p 1 <;> cases h2 : p 2 <;>
    simp [h0, h1, h2] <;> decide

/-- A fixed chord crosses an even number (necessarily zero or two) of the
three sides of any triangle. -/
lemma even_triangle_crossings {m : ℕ} (a b : Fin m) (t : Fin 3 → Fin m) :
    Even (((Finset.univ : Finset (Fin 3)).filter fun k ↦
      Crosses a b (triangleSide t k).1 (triangleSide t k).2).card) := by
  simpa only [crosses_iff_side_ne, triangleSide] using
    even_bool_changes_three (fun k ↦ side a b (t k))

/-- The preceding parity statement has only the two possible cardinalities
zero and two. -/
lemma card_triangle_crossings_eq_zero_or_two
    {m : ℕ} (a b : Fin m) (t : Fin 3 → Fin m) :
    ((Finset.univ : Finset (Fin 3)).filter fun k ↦
      Crosses a b (triangleSide t k).1 (triangleSide t k).2).card = 0 ∨
    ((Finset.univ : Finset (Fin 3)).filter fun k ↦
      Crosses a b (triangleSide t k).1 (triangleSide t k).2).card = 2 := by
  let count := ((Finset.univ : Finset (Fin 3)).filter fun k ↦
    Crosses a b (triangleSide t k).1 (triangleSide t k).2).card
  have heven : Even count := even_triangle_crossings a b t
  obtain ⟨r, hr⟩ := heven
  have hle : count ≤ 3 := by
    exact (Finset.card_filter_le _ _).trans_eq (Fintype.card_fin 3)
  omega

/-- The local even-degree hypothesis in the exact form expected by
`OddTransversal.crossDegree`. -/
lemma triangle_crossDegree_even {m : ℕ} {I : Type u}
    (triangle : I → Fin 3 → Fin m) (i j : I) (ei : Fin 3) :
    Even (OddTransversal.crossDegree (fun _ : I ↦ Fin 3)
      (triangleCrossRel triangle) i j ei) := by
  unfold OddTransversal.crossDegree triangleCrossRel
  convert even_triangle_crossings
    (triangleSide (triangle i) ei).1 (triangleSide (triangle i) ei).2 (triangle j) using 1
  congr 1
  ext k
  simp

/-! ## A disjoint family of selected chords -/

/-- The two endpoints belonging to each chord. -/
abbrev Endpoint (I : Type u) := I × Fin 2

/-- Crossing of two chords after all selected endpoints have been enumerated
in their cyclic order. -/
def selectedCrosses {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i j : I) : Prop :=
  Crosses (cyclicOrder (i, 0)) (cyclicOrder (i, 1))
    (cyclicOrder (j, 0)) (cyclicOrder (j, 1))

instance {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i j : I) :
    Decidable (selectedCrosses cyclicOrder i j) := by
  unfold selectedCrosses
  infer_instance

/-- Crossing degree in a selected chord family.  Including `i` itself does
not alter the count, since a chord does not cross itself. -/
def selectedCrossingDegree {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i : I) : ℕ :=
  ((Finset.univ : Finset I).filter fun j ↦ selectedCrosses cyclicOrder i j).card

@[simp]
lemma not_selectedCrosses_self {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i : I) :
    ¬ selectedCrosses cyclicOrder i i := by
  simp [selectedCrosses, Crosses]

/-- Crossing is symmetric for a disjoint selected chord family. -/
lemma selectedCrosses_comm {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i j : I) :
    selectedCrosses cyclicOrder i j ↔ selectedCrosses cyclicOrder j i := by
  by_cases hij : i = j
  · subst j
    rfl
  unfold selectedCrosses
  apply crosses_comm_of_endpoint_ne
  all_goals
    intro h
    have hp := cyclicOrder.injective h
    apply hij
    exact congrArg Prod.fst hp

/-- The diagonal-free form of the selected crossing degree. -/
lemma selectedCrossingDegree_eq_erase
    {I : Type u} [Fintype I] [DecidableEq I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i : I) :
    selectedCrossingDegree cyclicOrder i =
      ((Finset.univ.erase i).filter fun j ↦ selectedCrosses cyclicOrder i j).card := by
  classical
  unfold selectedCrossingDegree
  apply congrArg Finset.card
  ext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji]

/-- The selected chord family as a relation on singleton parts.  This is a
small adapter to the predicates in `OddTransversal`. -/
def selectedChordCrossRel {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) :
    OddTransversal.CrossRel (fun _ : I ↦ Unit) :=
  fun i j _ _ ↦ selectedCrosses cyclicOrder i j

lemma selectedChordCrossRel_symmetric {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) :
    OddTransversal.Symmetric (fun _ : I ↦ Unit)
      (selectedChordCrossRel cyclicOrder) := by
  intro i j _ _
  exact selectedCrosses_comm cyclicOrder i j

lemma selectedDegree_unit_eq_selectedCrossingDegree
    {I : Type u} [Fintype I] [DecidableEq I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i : I) :
    OddTransversal.selectedDegree (fun _ : I ↦ Unit)
        (selectedChordCrossRel cyclicOrder) (fun _ ↦ ()) i =
      selectedCrossingDegree cyclicOrder i := by
  classical
  rw [selectedCrossingDegree_eq_erase]
  unfold OddTransversal.selectedDegree selectedChordCrossRel
  apply congrArg Finset.card
  ext j
  simp

/-- Number of selected endpoints strictly between the two endpoints of chord
`i` in the linear representative of the cyclic order. -/
def insideEndpointCount {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i : I) : ℕ :=
  ((Finset.univ : Finset (Endpoint I)).filter fun p ↦
    Between (cyclicOrder (i, 0)) (cyclicOrder (i, 1)) (cyclicOrder p)).card

private lemma pair_indicator_eq_crossing_indicator {m : ℕ} (a b c d : Fin m) :
    ((if Between a b c then 1 else 0) + (if Between a b d then 1 else 0) : ZMod 2) =
      if Crosses a b c d then 1 else 0 := by
  by_cases hc : Between a b c <;> by_cases hd : Between a b d <;>
    simp [Crosses, hc, hd] <;> decide

/-- Modulo two, an intervening endpoint contributes precisely when its chord
crosses the fixed chord. -/
lemma cast_insideEndpointCount_eq_cast_selectedCrossingDegree
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i : I) :
    (insideEndpointCount cyclicOrder i : ZMod 2) =
      (selectedCrossingDegree cyclicOrder i : ZMod 2) := by
  classical
  let a := cyclicOrder (i, 0)
  let b := cyclicOrder (i, 1)
  calc
    (insideEndpointCount cyclicOrder i : ZMod 2) =
        ∑ p : Endpoint I,
          if Between a b (cyclicOrder p) then 1 else 0 := by
      exact OddTransversal.cast_card_filter_eq_sum_indicator _
    _ = ∑ j : I,
        ((if Between a b (cyclicOrder (j, 0)) then 1 else 0) +
          if Between a b (cyclicOrder (j, 1)) then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_congr
      intro j
      rw [Fin.sum_univ_two]
    _ = ∑ j : I, if selectedCrosses cyclicOrder i j then 1 else 0 := by
      apply Fintype.sum_congr
      intro j
      simpa only [selectedCrosses, a, b] using
        pair_indicator_eq_crossing_indicator a b
          (cyclicOrder (j, 0)) (cyclicOrder (j, 1))
    _ = (selectedCrossingDegree cyclicOrder i : ZMod 2) := by
      symm
      exact OddTransversal.cast_card_filter_eq_sum_indicator _

/-- Crossing degree is even exactly when the number of endpoints between the
ends of the chord is even. -/
lemma even_selectedCrossingDegree_iff_even_insideEndpointCount
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i : I) :
    Even (selectedCrossingDegree cyclicOrder i) ↔
      Even (insideEndpointCount cyclicOrder i) := by
  rw [OddTransversal.even_iff_cast_zmod_two_eq_zero,
    OddTransversal.even_iff_cast_zmod_two_eq_zero,
    cast_insideEndpointCount_eq_cast_selectedCrossingDegree]

/-! ## Alternating endpoint signs -/

/-- Enumerating the endpoints transports the open interval between the ends
of a chord to the corresponding interval in `Fin`. -/
lemma insideEndpointCount_eq
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (i : I) :
    insideEndpointCount cyclicOrder i =
      if cyclicOrder (i, 0) < cyclicOrder (i, 1) then
        (cyclicOrder (i, 1)).val - (cyclicOrder (i, 0)).val - 1
      else
        (cyclicOrder (i, 0)).val - (cyclicOrder (i, 1)).val - 1 := by
  classical
  let a := cyclicOrder (i, 0)
  let b := cyclicOrder (i, 1)
  by_cases hab : a < b
  · rw [if_pos hab]
    calc
      insideEndpointCount cyclicOrder i =
          Fintype.card {p : Endpoint I // Between a b (cyclicOrder p)} := by
        symm
        exact Fintype.card_subtype _
      _ = Fintype.card {x : Fin (2 * Fintype.card I) // a < x ∧ x < b} := by
        apply Fintype.card_congr
        exact cyclicOrder.subtypeEquiv fun p ↦ by
          simp only [Between]
          omega
      _ = (Finset.Ioo a b).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simp
      _ = b.val - a.val - 1 := by
        exact Fin.card_Ioo a b
  · rw [if_neg hab]
    calc
      insideEndpointCount cyclicOrder i =
          Fintype.card {p : Endpoint I // Between a b (cyclicOrder p)} := by
        symm
        exact Fintype.card_subtype _
      _ = Fintype.card {x : Fin (2 * Fintype.card I) // b < x ∧ x < a} := by
        apply Fintype.card_congr
        exact cyclicOrder.subtypeEquiv fun p ↦ by
          simp only [Between]
          omega
      _ = (Finset.Ioo b a).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext x
        simp
      _ = a.val - b.val - 1 := by
        exact Fin.card_Ioo b a

/-- The canonical alternating sign on endpoints, determined by the sign at
rank zero.  Thus the two choices of `base` are the only two globally
alternating signings of the enumerated endpoints. -/
def alternatingSign {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I))
    (base : Bool) (p : Endpoint I) : Bool :=
  if (cyclicOrder p).val % 2 = 0 then base else !base

/-- Consecutive positions in the linear endpoint order receive opposite
signs. -/
lemma alternatingSign_ne_of_succ
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I))
    (base : Bool) {p q : Endpoint I}
    (hsucc : (cyclicOrder q).val = (cyclicOrder p).val + 1) :
    alternatingSign cyclicOrder base p ≠ alternatingSign cyclicOrder base q := by
  unfold alternatingSign
  by_cases hp : (cyclicOrder p).val % 2 = 0 <;>
    by_cases hq : (cyclicOrder q).val % 2 = 0 <;>
    cases base <;> simp [hp, hq] <;> omega

/-- The end and beginning of the even cyclic endpoint order also receive
opposite signs. -/
lemma alternatingSign_ne_of_last_first
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I))
    (base : Bool) {p q : Endpoint I}
    (hlast : (cyclicOrder p).val + 1 = 2 * Fintype.card I)
    (hfirst : (cyclicOrder q).val = 0) :
    alternatingSign cyclicOrder base p ≠ alternatingSign cyclicOrder base q := by
  unfold alternatingSign
  by_cases hp : (cyclicOrder p).val % 2 = 0 <;>
    by_cases hq : (cyclicOrder q).val % 2 = 0 <;>
    cases base <;> simp [hp, hq] <;> omega

/-- The two initial signs induce distinct (indeed pointwise opposite)
endpoint signings. -/
lemma alternatingSign_false_ne_true
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I))
    (p : Endpoint I) :
    alternatingSign cyclicOrder false p ≠ alternatingSign cyclicOrder true p := by
  unfold alternatingSign
  by_cases hp : (cyclicOrder p).val % 2 = 0 <;> simp [hp]

/-- A base sign is compatible with the chord family when the endpoints of
every selected chord receive opposite alternating signs. -/
def CompatibleAlternatingBase {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I))
    (base : Bool) : Prop :=
  ∀ i : I, alternatingSign cyclicOrder base (i, 0) ≠
    alternatingSign cyclicOrder base (i, 1)

/-- Every selected chord has even crossing degree. -/
def AllSelectedCrossingDegreesEven {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) : Prop :=
  ∀ i : I, Even (selectedCrossingDegree cyclicOrder i)

lemma good_unit_iff_allSelectedCrossingDegreesEven
    {I : Type u} [Fintype I] [DecidableEq I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) :
    OddTransversal.Good (fun _ : I ↦ Unit) (selectedChordCrossRel cyclicOrder)
        (fun _ ↦ ()) ↔
      AllSelectedCrossingDegreesEven cyclicOrder := by
  simp only [OddTransversal.Good, AllSelectedCrossingDegreesEven,
    selectedDegree_unit_eq_selectedCrossingDegree]

/-- For one chord, opposite endpoint signs are equivalent to even crossing
degree.  The statement is independent of the choice of the initial sign. -/
lemma alternatingSign_endpoints_ne_iff_even_crossingDegree
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I))
    (base : Bool) (i : I) :
    alternatingSign cyclicOrder base (i, 0) ≠
        alternatingSign cyclicOrder base (i, 1) ↔
      Even (selectedCrossingDegree cyclicOrder i) := by
  rw [even_selectedCrossingDegree_iff_even_insideEndpointCount,
    insideEndpointCount_eq]
  simp only [Nat.even_iff]
  have hne : cyclicOrder (i, 0) ≠ cyclicOrder (i, 1) := by
    intro h
    have hp := cyclicOrder.injective h
    have hf : (0 : Fin 2) = 1 := congrArg Prod.snd hp
    omega
  unfold alternatingSign
  by_cases hab : cyclicOrder (i, 0) < cyclicOrder (i, 1)
  · rw [if_pos hab]
    by_cases h0 : (cyclicOrder (i, 0)).val % 2 = 0 <;>
      by_cases h1 : (cyclicOrder (i, 1)).val % 2 = 0 <;>
      cases base <;> simp [h0, h1] <;> omega
  · rw [if_neg hab]
    have hba : cyclicOrder (i, 1) < cyclicOrder (i, 0) := lt_of_le_of_ne
      (not_lt.mp hab) (Ne.symm hne)
    by_cases h0 : (cyclicOrder (i, 0)).val % 2 = 0 <;>
      by_cases h1 : (cyclicOrder (i, 1)).val % 2 = 0 <;>
      cases base <;> simp [h0, h1] <;> omega

/-- All crossing degrees are even exactly when either (equivalently, both)
initial signs gives a compatible global alternating orientation. -/
theorem all_even_iff_compatibleAlternatingBase
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (base : Bool) :
    AllSelectedCrossingDegreesEven cyclicOrder ↔
      CompatibleAlternatingBase cyclicOrder base := by
  simp only [AllSelectedCrossingDegreesEven, CompatibleAlternatingBase,
    alternatingSign_endpoints_ne_iff_even_crossingDegree]

/-- Existence form: the endpoints have a globally alternating signing whose
two signs orient every chord oppositely exactly when all crossing degrees are
even. -/
theorem all_even_iff_exists_compatibleAlternatingBase
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) :
    AllSelectedCrossingDegreesEven cyclicOrder ↔
      ∃ base : Bool, CompatibleAlternatingBase cyclicOrder base := by
  constructor
  · intro hall
    exact ⟨false,
      (all_even_iff_compatibleAlternatingBase cyclicOrder false).mp hall⟩
  · rintro ⟨base, hbase⟩
    exact (all_even_iff_compatibleAlternatingBase cyclicOrder base).mpr hbase

/-- The compatible alternating orientations, encoded by their sign at rank
zero.  Each base determines the full endpoint signing via `alternatingSign`. -/
noncomputable def alternatingOrientations {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) : Finset Bool := by
  classical
  exact Finset.univ.filter fun base ↦ CompatibleAlternatingBase cyclicOrder base

@[simp]
lemma mem_alternatingOrientations
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) (base : Bool) :
    base ∈ alternatingOrientations cyclicOrder ↔
      CompatibleAlternatingBase cyclicOrder base := by
  classical
  simp [alternatingOrientations]

/-- This is the endpoint-orientation form used in the Petrov argument: all
selected crossing degrees are even iff there are exactly two globally
alternating compatible orientations. -/
theorem all_even_iff_card_alternatingOrientations_eq_two
    {I : Type u} [Fintype I]
    (cyclicOrder : Endpoint I ≃ Fin (2 * Fintype.card I)) :
    AllSelectedCrossingDegreesEven cyclicOrder ↔
      (alternatingOrientations cyclicOrder).card = 2 := by
  classical
  by_cases hall : AllSelectedCrossingDegreesEven cyclicOrder
  · have hcompat : ∀ base : Bool, CompatibleAlternatingBase cyclicOrder base :=
      fun base ↦ (all_even_iff_compatibleAlternatingBase cyclicOrder base).mp hall
    simp [hall, alternatingOrientations, hcompat]
  · have hcompat : ∀ base : Bool, ¬ CompatibleAlternatingBase cyclicOrder base :=
      fun base hbase ↦ hall <|
        (all_even_iff_compatibleAlternatingBase cyclicOrder base).mpr hbase
    simp [hall, alternatingOrientations, hcompat]


end ChordCrossing

end Erdos842
