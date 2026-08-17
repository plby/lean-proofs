import ErdosProblems.Erdos842.CanonicalArcs
import ErdosProblems.Erdos842.GoodChords
import ErdosProblems.Erdos842.SignedCancellation

/-!
# Coefficient reductions for Erdős Problem 842

This file develops the finite combinatorics used after the generic indexed-arc coefficient
identity in `Erdos842.Parity`.  There are two independent pieces.

* A full directed triangle is balanced.  Symmetric difference with its three arcs therefore
  preserves balance and reverses the sign in the signed subset expansion.  A proper nonempty
  subset of the three arcs has one of the six possible nonzero boundary vectors, equivalently
  it specifies an oriented chord of the triangle.
* On a directed cycle, the boundary of a Boolean edge selection is the cyclic finite difference
  `s (pred v) - s v`.  If that boundary is nonzero then its fibre consists of exactly one edge
  selection; the zero fibre consists of the empty and full selections.

Together with `Parity.IndexedArcs.coeff_central_eq_signed_balanced`, these lemmas are the
algebraic and fibre-decomposition layer of the Fleischner--Stiebitz coefficient calculation.
-/

open scoped BigOperators symmDiff

namespace Erdos842.Coefficient

open Erdos842.Parity

section GenericCoefficient

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- Re-export of the central coefficient identity in the namespace used by the remaining
Erdős 842 development. -/
theorem centralCoeff_eq_signedBalanced (D : IndexedArcs V A)
    (hout : ∀ v, ((Finset.univ : Finset A).filter fun a ↦ D.tail a = v).card = 2) :
    MvPolynomial.coeff D.centralExponent D.polynomial =
      ∑ S : Finset A, if D.Balanced S then ((-1 : ℤ) ^ S.card) else 0 :=
  D.coeff_central_eq_signed_balanced hout

end GenericCoefficient

section CoefficientFibres

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- The finite set which supports the signed central-coefficient sum. -/
noncomputable def balancedSelections (D : IndexedArcs V A) : Finset (Finset A) :=
  Finset.univ.filter D.Balanced

/-- The sign of an indexed-arc selection in the graph-polynomial expansion. -/
def selectionSign (S : Finset A) : ℤ := (-1 : ℤ) ^ S.card

@[simp] theorem mem_balancedSelections (D : IndexedArcs V A) (S : Finset A) :
    S ∈ balancedSelections D ↔ D.Balanced S := by
  classical
  simp [balancedSelections]

/-- Remove the zero summands from the generic signed-balanced identity. -/
theorem centralCoeff_eq_sum_balancedSelections (D : IndexedArcs V A)
    (hout : ∀ v, ((Finset.univ : Finset A).filter fun a ↦ D.tail a = v).card = 2) :
    MvPolynomial.coeff D.centralExponent D.polynomial =
      ∑ S ∈ balancedSelections D, selectionSign S := by
  classical
  rw [centralCoeff_eq_signedBalanced D hout]
  simp [balancedSelections, selectionSign, Finset.sum_filter]

/-- Integration theorem for the cancellation and chord-fibre layer.

The input `survivors` is the set left after triangle-degenerate selections have been paired.
The finite type `B` is intended to be the type of unoriented chord selections, and `good` its
even-crossing subset.  The hypotheses say exactly that the nonsurvivors cancel in pairs and that
each good chord selection has the two equal-sign global orientations.  An odd number of good
selections then forces the canonical coefficient to be `2` modulo `4`.

This statement is deliberately over arbitrary indexed arcs, so the canonical cycle-plus-triangle
family can apply it without identifying parallel occurrences. -/
theorem centralCoeff_modEq_two_of_odd_good_fibres
    {B : Type*} [DecidableEq B]
    (D : IndexedArcs V A)
    (hout : ∀ v, ((Finset.univ : Finset A).filter fun a ↦ D.tail a = v).card = 2)
    (survivors : Finset (Finset A)) (good : Finset B)
    (key : Finset A → B) (toggle : Finset A → Finset A)
    (survivors_subset : survivors ⊆ balancedSelections D)
    (toggle_mem : ∀ S ∈ balancedSelections D \ survivors,
      toggle S ∈ balancedSelections D \ survivors)
    (toggle_involutive : ∀ S ∈ balancedSelections D \ survivors,
      toggle (toggle S) = S)
    (toggle_fixedPointFree : ∀ S ∈ balancedSelections D \ survivors,
      toggle S ≠ S)
    (toggle_negates : ∀ S ∈ balancedSelections D \ survivors,
      selectionSign (toggle S) = -selectionSign S)
    (key_good : ∀ S ∈ survivors, key S ∈ good)
    (two_orientations : ∀ g ∈ good,
      (survivors.filter fun S ↦ key S = g).card = 2)
    (same_sign : ∀ g ∈ good,
      (∀ S ∈ survivors, key S = g → selectionSign S = 1) ∨
        (∀ S ∈ survivors, key S = g → selectionSign S = -1))
    (odd_good : Odd good.card) :
    MvPolynomial.coeff D.centralExponent D.polynomial ≡ 2 [ZMOD 4] := by
  rw [centralCoeff_eq_sum_balancedSelections D hout]
  exact SignedCancellation.sum_modEq_two_of_involution_and_survivor_fibers
    (balancedSelections D) survivors good key selectionSign toggle survivors_subset
      toggle_mem toggle_involutive toggle_fixedPointFree toggle_negates key_good
      two_orientations same_sign odd_good

/-- Nonvanishing form of `centralCoeff_modEq_two_of_odd_good_fibres`, ready for the
Alon--Tarsi coloring theorem. -/
theorem centralCoeff_ne_zero_of_odd_good_fibres
    {B : Type*} [DecidableEq B]
    (D : IndexedArcs V A)
    (hout : ∀ v, ((Finset.univ : Finset A).filter fun a ↦ D.tail a = v).card = 2)
    (survivors : Finset (Finset A)) (good : Finset B)
    (key : Finset A → B) (toggle : Finset A → Finset A)
    (survivors_subset : survivors ⊆ balancedSelections D)
    (toggle_mem : ∀ S ∈ balancedSelections D \ survivors,
      toggle S ∈ balancedSelections D \ survivors)
    (toggle_involutive : ∀ S ∈ balancedSelections D \ survivors,
      toggle (toggle S) = S)
    (toggle_fixedPointFree : ∀ S ∈ balancedSelections D \ survivors,
      toggle S ≠ S)
    (toggle_negates : ∀ S ∈ balancedSelections D \ survivors,
      selectionSign (toggle S) = -selectionSign S)
    (key_good : ∀ S ∈ survivors, key S ∈ good)
    (two_orientations : ∀ g ∈ good,
      (survivors.filter fun S ↦ key S = g).card = 2)
    (same_sign : ∀ g ∈ good,
      (∀ S ∈ survivors, key S = g → selectionSign S = 1) ∨
        (∀ S ∈ survivors, key S = g → selectionSign S = -1))
    (odd_good : Odd good.card) :
    MvPolynomial.coeff D.centralExponent D.polynomial ≠ 0 := by
  apply D.coeff_central_ne_zero_of_modEq_two
  exact centralCoeff_modEq_two_of_odd_good_fibres D hout survivors good key toggle
    survivors_subset toggle_mem toggle_involutive toggle_fixedPointFree toggle_negates
      key_good two_orientations same_sign odd_good

end CoefficientFibres

section CanonicalCoefficientFibres

/-- Canonical cycle-plus-triangles specialization of the complete cancellation/fibre interface.
This is the form consumed by the final Erdős 842 assembly: its conclusion refers directly to the
polynomial of `canonicalIndexedArcs`, and two-out-regularity is discharged internally. -/
theorem canonicalCoeff_modEq_two_of_odd_good_fibres
    {n : ℕ} (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {B : Type*} [DecidableEq B]
    (survivors : Finset (Finset (CanonicalOccurrence n))) (good : Finset B)
    (key : Finset (CanonicalOccurrence n) → B)
    (toggle : Finset (CanonicalOccurrence n) → Finset (CanonicalOccurrence n))
    (survivors_subset : survivors ⊆ balancedSelections (canonicalIndexedArcs n triangleCoord))
    (toggle_mem : ∀ S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \ survivors,
      toggle S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \ survivors)
    (toggle_involutive :
      ∀ S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \ survivors,
        toggle (toggle S) = S)
    (toggle_fixedPointFree :
      ∀ S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \ survivors,
        toggle S ≠ S)
    (toggle_negates :
      ∀ S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \ survivors,
        selectionSign (toggle S) = -selectionSign S)
    (key_good : ∀ S ∈ survivors, key S ∈ good)
    (two_orientations :
      ∀ g ∈ good, (survivors.filter fun S ↦ key S = g).card = 2)
    (same_sign : ∀ g ∈ good,
      (∀ S ∈ survivors, key S = g → selectionSign S = 1) ∨
        (∀ S ∈ survivors, key S = g → selectionSign S = -1))
    (odd_good : Odd good.card) :
    MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
      (canonicalIndexedArcs n triangleCoord).polynomial ≡ 2 [ZMOD 4] := by
  exact centralCoeff_modEq_two_of_odd_good_fibres
    (canonicalIndexedArcs n triangleCoord)
    (canonicalIndexedArcs_outdegree_two n triangleCoord)
    survivors good key toggle survivors_subset toggle_mem toggle_involutive
      toggle_fixedPointFree toggle_negates key_good two_orientations same_sign odd_good

/-- Canonical nonvanishing conclusion under the odd-good-chord fibre hypotheses. -/
theorem canonicalCoeff_ne_zero_of_odd_good_fibres
    {n : ℕ} (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {B : Type*} [DecidableEq B]
    (survivors : Finset (Finset (CanonicalOccurrence n))) (good : Finset B)
    (key : Finset (CanonicalOccurrence n) → B)
    (toggle : Finset (CanonicalOccurrence n) → Finset (CanonicalOccurrence n))
    (survivors_subset : survivors ⊆ balancedSelections (canonicalIndexedArcs n triangleCoord))
    (toggle_mem : ∀ S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \ survivors,
      toggle S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \ survivors)
    (toggle_involutive :
      ∀ S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \ survivors,
        toggle (toggle S) = S)
    (toggle_fixedPointFree :
      ∀ S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \ survivors,
        toggle S ≠ S)
    (toggle_negates :
      ∀ S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \ survivors,
        selectionSign (toggle S) = -selectionSign S)
    (key_good : ∀ S ∈ survivors, key S ∈ good)
    (two_orientations :
      ∀ g ∈ good, (survivors.filter fun S ↦ key S = g).card = 2)
    (same_sign : ∀ g ∈ good,
      (∀ S ∈ survivors, key S = g → selectionSign S = 1) ∨
        (∀ S ∈ survivors, key S = g → selectionSign S = -1))
    (odd_good : Odd good.card) :
    MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
      (canonicalIndexedArcs n triangleCoord).polynomial ≠ 0 := by
  apply (canonicalIndexedArcs n triangleCoord).coeff_central_ne_zero_of_modEq_two
  exact canonicalCoeff_modEq_two_of_odd_good_fibres triangleCoord survivors good key toggle
    survivors_subset toggle_mem toggle_involutive toggle_fixedPointFree toggle_negates
      key_good two_orientations same_sign odd_good

end CanonicalCoefficientFibres

section FinThree

/-- Cyclic successor on the three directed sides of a triangle. -/
def triSucc (j : Fin 3) : Fin 3 := ⟨(j.1 + 1) % 3, by omega⟩

@[simp] theorem triSucc_zero : triSucc 0 = 1 := rfl
@[simp] theorem triSucc_one : triSucc 1 = 2 := rfl
@[simp] theorem triSucc_two : triSucc 2 = 0 := rfl

/-- Cyclic predecessor on the three directed sides of a triangle. -/
def triPred (j : Fin 3) : Fin 3 := ⟨(j.1 + 2) % 3, by omega⟩

@[simp] theorem triPred_zero : triPred 0 = 2 := rfl
@[simp] theorem triPred_one : triPred 1 = 0 := rfl
@[simp] theorem triPred_two : triPred 2 = 1 := rfl

@[simp] theorem triSucc_triPred (j : Fin 3) : triSucc (triPred j) = j := by
  fin_cases j <;> rfl

@[simp] theorem triPred_triSucc (j : Fin 3) : triPred (triSucc j) = j := by
  fin_cases j <;> rfl

theorem triSucc_injective : Function.Injective triSucc :=
  Function.LeftInverse.injective triPred_triSucc

/-- The integer boundary of a selected subset of the cyclically oriented triangle. -/
def triangleBoundary (S : Finset (Fin 3)) (j : Fin 3) : ℤ :=
  (if triPred j ∈ S then 1 else 0) - if j ∈ S then 1 else 0

@[simp] theorem triangleBoundary_empty (j : Fin 3) : triangleBoundary ∅ j = 0 := by
  simp [triangleBoundary]

@[simp] theorem triangleBoundary_univ (j : Fin 3) :
    triangleBoundary Finset.univ j = 0 := by
  simp [triangleBoundary]

/-- Complementing a triangle selection reverses its boundary. -/
theorem triangleBoundary_compl (S : Finset (Fin 3)) (j : Fin 3) :
    triangleBoundary (Finset.univ \ S) j = -triangleBoundary S j := by
  simp only [triangleBoundary, Finset.mem_sdiff, Finset.mem_univ, true_and]
  split_ifs <;> omega

/-- A subset of a directed triangle has zero boundary exactly in the two degenerate cases:
no side is selected, or all three sides are selected. -/
theorem triangleBoundary_eq_zero_iff (S : Finset (Fin 3)) :
    (∀ j, triangleBoundary S j = 0) ↔ S = ∅ ∨ S = Finset.univ := by
  classical
  constructor
  · intro h
    have hmem : ∀ j, (triPred j ∈ S ↔ j ∈ S) := by
      intro j
      specialize h j
      simp only [triangleBoundary] at h
      split_ifs at h <;> simp_all
    have hm0 := hmem 0
    have hm1 := hmem 1
    have hm2 := hmem 2
    by_cases hz : (0 : Fin 3) ∈ S
    · right
      ext j
      fin_cases j <;> simp_all
    · left
      ext j
      fin_cases j <;> simp_all
  · rintro (rfl | rfl) <;> simp

/-- Every nondegenerate triangle selection has one `+1`, one `-1`, and one zero in its
boundary.  Thus it is precisely an oriented chord between the two nonzero vertices. -/
theorem triangleBoundary_nondegenerate
    (S : Finset (Fin 3)) (hne : S ≠ ∅) (hfull : S ≠ Finset.univ) :
    ∃ p q : Fin 3, p ≠ q ∧ triangleBoundary S p = 1 ∧
      triangleBoundary S q = -1 ∧
      ∀ r, r ≠ p → r ≠ q → triangleBoundary S r = 0 := by
  classical
  by_cases h0 : (0 : Fin 3) ∈ S <;>
    by_cases h1 : (1 : Fin 3) ∈ S <;>
    by_cases h2 : (2 : Fin 3) ∈ S
  · exfalso
    apply hfull
    ext j
    fin_cases j <;> simp_all
  · refine ⟨2, 0, by decide, ?_, ?_, ?_⟩
    · simp [triangleBoundary, h0, h1, h2]
    · simp [triangleBoundary, h0, h1, h2]
    · intro r hr0 hr2
      fin_cases r <;> simp_all [triangleBoundary]
  · refine ⟨1, 2, by decide, ?_, ?_, ?_⟩
    · simp [triangleBoundary, h0, h1, h2]
    · simp [triangleBoundary, h0, h1, h2]
    · intro r hr2 hr1
      fin_cases r <;> simp_all [triangleBoundary]
  · refine ⟨1, 0, by decide, ?_, ?_, ?_⟩
    · simp [triangleBoundary, h0, h1, h2]
    · simp [triangleBoundary, h0, h1, h2]
    · intro r hr1 hr2
      fin_cases r <;> simp_all [triangleBoundary]
  · refine ⟨0, 1, by decide, ?_, ?_, ?_⟩
    · simp [triangleBoundary, h0, h1, h2]
    · simp [triangleBoundary, h0, h1, h2]
    · intro r hr0 hr1
      fin_cases r <;> simp_all [triangleBoundary]
  · refine ⟨2, 1, by decide, ?_, ?_, ?_⟩
    · simp [triangleBoundary, h0, h1, h2]
    · simp [triangleBoundary, h0, h1, h2]
    · intro r hr1 hr0
      fin_cases r <;> simp_all [triangleBoundary]
  · refine ⟨0, 2, by decide, ?_, ?_, ?_⟩
    · simp [triangleBoundary, h0, h1, h2]
    · simp [triangleBoundary, h0, h1, h2]
    · intro r hr2 hr0
      fin_cases r <;> simp_all [triangleBoundary]
  · exfalso
    apply hne
    ext j
    fin_cases j <;> simp_all

/-- The unoriented chord encoded by a proper nonempty directed-triangle selection: it is indexed
by the unique vertex at which the boundary vanishes, i.e. the vertex opposite the chord. -/
def triangleChordIndex (S : Finset (Fin 3)) : Fin 3 :=
  if triangleBoundary S 0 = 0 then 0
  else if triangleBoundary S 1 = 0 then 1 else 2

theorem triangleBoundary_chordIndex_eq_zero
    (S : Finset (Fin 3)) (hne : S ≠ ∅) (hfull : S ≠ Finset.univ) :
    triangleBoundary S (triangleChordIndex S) = 0 := by
  obtain ⟨p, q, hpq, hp, hq, hrest⟩ := triangleBoundary_nondegenerate S hne hfull
  fin_cases p <;> fin_cases q <;>
    simp_all [triangleChordIndex] <;>
    first | exact hrest 0 (by decide) (by decide)
          | exact hrest 1 (by decide) (by decide)
          | exact hrest 2 (by decide) (by decide)

/-- Complementing the directed sides reverses orientation but keeps the underlying chord. -/
theorem triangleChordIndex_compl (S : Finset (Fin 3)) :
    triangleChordIndex (Finset.univ \ S) = triangleChordIndex S := by
  unfold triangleChordIndex
  simp only [triangleBoundary_compl, neg_eq_zero]

/-- Symmetric difference with the full triangle is ordinary complement. -/
theorem symmDiff_univ_fin3 (S : Finset (Fin 3)) :
    S ∆ Finset.univ = Finset.univ \ S := by
  ext j
  simp [Finset.mem_symmDiff]

/-- Toggling all three triangle arcs reverses the parity sign. -/
theorem triangleToggle_sign (S : Finset (Fin 3)) :
    (-1 : ℤ) ^ (S ∆ Finset.univ).card = -((-1 : ℤ) ^ S.card) := by
  rw [symmDiff_univ_fin3]
  have hc : (Finset.univ \ S).card + S.card = 3 := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  have hle : S.card ≤ 3 := by
    simpa using Finset.card_le_card (Finset.subset_univ S)
  interval_cases h : S.card <;> simp_all

end FinThree

section TriangleInIndexedArcs

variable {V A : Type*} [Fintype V] [Fintype A] [DecidableEq V] [DecidableEq A]

/-- Three indexed arcs form a coherently directed triangle.  Injectivity records that they are
three distinct occurrences, even if another arc family has parallel endpoints. -/
structure DirectedTriangle (D : IndexedArcs V A) where
  arc : Fin 3 → A
  injective_arc : Function.Injective arc
  vertex : Fin 3 → V
  tail_arc : ∀ j, D.tail (arc j) = vertex j
  head_arc : ∀ j, D.head (arc j) = vertex (triSucc j)

namespace DirectedTriangle

variable {D : IndexedArcs V A} (T : DirectedTriangle D)

/-- The indexed arc set of a directed triangle. -/
def arcSet : Finset A := Finset.univ.map ⟨T.arc, T.injective_arc⟩

@[simp] theorem mem_arcSet (a : A) : a ∈ T.arcSet ↔ ∃ j, T.arc j = a := by
  simp [arcSet]

@[simp] theorem arc_mem_arcSet (j : Fin 3) : T.arc j ∈ T.arcSet := by
  exact T.mem_arcSet (T.arc j) |>.2 ⟨j, rfl⟩

@[simp] theorem card_arcSet : T.arcSet.card = 3 := by
  simp [arcSet]

/-- A whole coherently directed triangle is balanced. -/
theorem arcSet_balanced : D.Balanced T.arcSet := by
  intro v
  classical
  simp only [IndexedArcs.selectedIn, IndexedArcs.selectedOut]
  have hin :
      (T.arcSet.filter fun a ↦ D.head a = v).card =
        ((Finset.univ : Finset (Fin 3)).filter fun j ↦ T.vertex (triSucc j) = v).card := by
    rw [arcSet]
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    ext j
    simp [T.head_arc]
  have hout :
      (T.arcSet.filter fun a ↦ D.tail a = v).card =
        ((Finset.univ : Finset (Fin 3)).filter fun j ↦ T.vertex j = v).card := by
    rw [arcSet]
    rw [Finset.filter_map, Finset.card_map]
    congr 1
    ext j
    simp [T.tail_arc]
  rw [hin, hout]
  apply Finset.card_bij (fun j _ ↦ triSucc j)
  · intro j hj
    simpa using hj
  · intro j₁ hj₁ j₂ hj₂ heq
    exact triSucc_injective heq
  · intro j hj
    refine ⟨triPred j, ?_, ?_⟩
    · simpa using hj
    · simp

/-- Restriction of an indexed-arc selection to the three occurrences of this triangle. -/
def restriction (S : Finset A) : Finset (Fin 3) :=
  Finset.univ.filter fun j ↦ T.arc j ∈ S

@[simp] theorem mem_restriction (S : Finset A) (j : Fin 3) :
    j ∈ T.restriction S ↔ T.arc j ∈ S := by
  simp [restriction]

theorem restriction_eq_empty_iff (S : Finset A) :
    T.restriction S = ∅ ↔ Disjoint S T.arcSet := by
  classical
  constructor
  · intro h
    rw [Finset.disjoint_left]
    intro a haS haT
    obtain ⟨j, rfl⟩ := T.mem_arcSet a |>.mp haT
    have hj : j ∈ T.restriction S := T.mem_restriction S j |>.mpr haS
    rw [h] at hj
    simp at hj
  · intro hd
    ext j
    simp only [T.mem_restriction]
    constructor
    · intro hj
      exact False.elim ((Finset.disjoint_left.mp hd) hj (T.arc_mem_arcSet j))
    · intro hj
      simp at hj

theorem restriction_eq_univ_iff (S : Finset A) :
    T.restriction S = Finset.univ ↔ T.arcSet ⊆ S := by
  classical
  constructor
  · intro h a ha
    obtain ⟨j, rfl⟩ := T.mem_arcSet a |>.mp ha
    apply T.mem_restriction S j |>.mp
    rw [h]
    simp
  · intro hsub
    apply Finset.eq_univ_iff_forall.mpr
    intro j
    exact T.mem_restriction S j |>.mpr (hsub (T.arc_mem_arcSet j))

/-- Toggle all three indexed occurrences of the triangle. -/
def toggle (S : Finset A) : Finset A := S ∆ T.arcSet

@[simp] theorem toggle_toggle (S : Finset A) : T.toggle (T.toggle S) = S := by
  classical
  ext a
  simp [toggle, Finset.mem_symmDiff]

theorem toggle_ne (S : Finset A) : T.toggle S ≠ S := by
  classical
  intro h
  have hm := congrArg (fun U : Finset A ↦ T.arc 0 ∈ U) h
  simp [toggle, Finset.mem_symmDiff] at hm

/-- On triangle restrictions, toggling the full directed triangle is complementation. -/
theorem restriction_toggle (S : Finset A) :
    T.restriction (T.toggle S) = Finset.univ \ T.restriction S := by
  classical
  ext j
  simp [restriction, toggle, Finset.mem_symmDiff, T.arc_mem_arcSet]

/-- Restricting the global complement is the complement of the triangle restriction. -/
theorem restriction_compl (S : Finset A) :
    T.restriction (Finset.univ \ S) = Finset.univ \ T.restriction S := by
  classical
  ext j
  simp [restriction]

/-- Hence the predicate "empty or full triangle restriction" is invariant under toggling. -/
theorem restriction_toggle_degenerate_iff (S : Finset A) :
    (T.restriction (T.toggle S) = ∅ ∨ T.restriction (T.toggle S) = Finset.univ) ↔
      (T.restriction S = ∅ ∨ T.restriction S = Finset.univ) := by
  rw [T.restriction_toggle]
  constructor
  · rintro (h | h)
    · right
      apply Finset.eq_univ_iff_forall.mpr
      intro j
      by_contra hj
      have : j ∈ Finset.univ \ T.restriction S := by simp [hj]
      rw [h] at this
      simp at this
    · left
      ext j
      constructor
      · intro hj
        have hcomp : j ∈ Finset.univ \ T.restriction S := by
          rw [h]
          simp
        exact False.elim ((Finset.mem_sdiff.mp hcomp).2 hj)
      · intro hj
        simp at hj
  · rintro (h | h)
    · rw [h]
      simp
    · rw [h]
      simp

end DirectedTriangle

/-- Balanced indexed selections are closed under disjoint union. -/
theorem balanced_union_of_disjoint
    {D : IndexedArcs V A} {S U : Finset A} (hd : Disjoint S U)
    (hS : D.Balanced S) (hU : D.Balanced U) : D.Balanced (S ∪ U) := by
  classical
  intro v
  have hdin : Disjoint
      (S.filter fun a ↦ D.head a = v) (U.filter fun a ↦ D.head a = v) :=
    hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hdout : Disjoint
      (S.filter fun a ↦ D.tail a = v) (U.filter fun a ↦ D.tail a = v) :=
    hd.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  simp only [IndexedArcs.Balanced, IndexedArcs.selectedIn,
    IndexedArcs.selectedOut] at hS hU ⊢
  rw [Finset.filter_union, Finset.filter_union,
    Finset.card_union_of_disjoint hdin, Finset.card_union_of_disjoint hdout,
    hS v, hU v]

/-- Removing a balanced indexed selection from a larger balanced selection preserves balance. -/
theorem balanced_sdiff_of_subset
    {D : IndexedArcs V A} {S U : Finset A} (hsub : U ⊆ S)
    (hS : D.Balanced S) (hU : D.Balanced U) : D.Balanced (S \ U) := by
  classical
  intro v
  have hin : U.filter (fun a ↦ D.head a = v) ⊆ S.filter (fun a ↦ D.head a = v) := by
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨hsub ha.1, ha.2⟩
  have hout : U.filter (fun a ↦ D.tail a = v) ⊆ S.filter (fun a ↦ D.tail a = v) := by
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨hsub ha.1, ha.2⟩
  have hfin : (S \ U).filter (fun a ↦ D.head a = v) =
      S.filter (fun a ↦ D.head a = v) \ U.filter (fun a ↦ D.head a = v) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have hfout : (S \ U).filter (fun a ↦ D.tail a = v) =
      S.filter (fun a ↦ D.tail a = v) \ U.filter (fun a ↦ D.tail a = v) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  simp only [IndexedArcs.Balanced, IndexedArcs.selectedIn,
    IndexedArcs.selectedOut] at hS hU ⊢
  rw [hfin, hfout,
    Finset.card_sdiff_of_subset hin, Finset.card_sdiff_of_subset hout,
    hS v, hU v]

/-- If the total indexed indegree and outdegree agree at every vertex, then the full occurrence
set is balanced.  This is the small adapter needed for global complementation. -/
theorem univ_balanced_of_degrees_eq
    {D : IndexedArcs V A}
    (hdeg : ∀ v,
      ((Finset.univ : Finset A).filter fun a ↦ D.head a = v).card =
        ((Finset.univ : Finset A).filter fun a ↦ D.tail a = v).card) :
    D.Balanced (Finset.univ : Finset A) := by
  intro v
  exact hdeg v

/-- Toggling an empty or full directed-triangle restriction preserves balancedness. -/
theorem DirectedTriangle.balanced_toggle_of_degenerate
    {D : IndexedArcs V A} (T : DirectedTriangle D) (S : Finset A)
    (hS : D.Balanced S)
    (hdeg : T.restriction S = ∅ ∨ T.restriction S = Finset.univ) :
    D.Balanced (T.toggle S) := by
  classical
  rcases hdeg with hempty | hfull
  · have hd : Disjoint S T.arcSet := (T.restriction_eq_empty_iff S).mp hempty
    rw [toggle, Finset.symmDiff_eq_union hd]
    exact balanced_union_of_disjoint hd hS T.arcSet_balanced
  · have hsub : T.arcSet ⊆ S := (T.restriction_eq_univ_iff S).mp hfull
    have htog : T.toggle S = S \ T.arcSet := by
      ext a
      simp only [toggle, Finset.mem_symmDiff, Finset.mem_sdiff]
      constructor
      · rintro (⟨haS, haT⟩ | ⟨haT, haS⟩)
        · exact ⟨haS, haT⟩
        · exact False.elim (haS (hsub haT))
      · rintro ⟨haS, haT⟩
        exact Or.inl ⟨haS, haT⟩
    rw [htog]
    exact balanced_sdiff_of_subset hsub hS T.arcSet_balanced

/-- A degenerate full-triangle toggle reverses the subset-expansion sign. -/
theorem DirectedTriangle.selectionSign_toggle_of_degenerate
    {D : IndexedArcs V A} (T : DirectedTriangle D) (S : Finset A)
    (hdeg : T.restriction S = ∅ ∨ T.restriction S = Finset.univ) :
    selectionSign (T.toggle S) = -selectionSign S := by
  classical
  rcases hdeg with hempty | hfull
  · have hd : Disjoint S T.arcSet := (T.restriction_eq_empty_iff S).mp hempty
    unfold selectionSign
    rw [toggle, Finset.symmDiff_eq_union hd,
      Finset.card_union_of_disjoint hd, T.card_arcSet, pow_add]
    norm_num
  · have hsub : T.arcSet ⊆ S := (T.restriction_eq_univ_iff S).mp hfull
    have htog : T.toggle S = S \ T.arcSet := by
      ext a
      simp only [toggle, Finset.mem_symmDiff, Finset.mem_sdiff]
      aesop
    have hcard := Finset.card_sdiff_add_card_eq_card hsub
    unfold selectionSign
    rw [htog, ← hcard, T.card_arcSet, pow_add]
    norm_num

section CanonicalTriangle

/-- The `i`th directed triangle inside the canonical indexed occurrence family. -/
def canonicalDirectedTriangle (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) (i : Fin n) :
    DirectedTriangle (canonicalIndexedArcs n triangleCoord) where
  arc j := Sum.inr (i, j)
  injective_arc := by
    intro j k h
    simpa using congrArg (fun a : CanonicalOccurrence n ↦
      match a with | .inl _ => (0 : Fin 3) | .inr p => p.2) h
  vertex j := triangleCoord.symm (i, j)
  tail_arc j := rfl
  head_arc j := by
    simp only [canonicalIndexedArcs_head, canonicalOccurrenceHead]
    congr 2

/-- The unoriented chord selected in each canonical triangle by a nondegenerate arc selection. -/
def canonicalChordKey (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) : Fin n → Fin 3 := fun i ↦
  triangleChordIndex ((canonicalDirectedTriangle n triangleCoord i).restriction S)

/-- Global complementation reverses every oriented chord and preserves the underlying chord key. -/
theorem canonicalChordKey_compl (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    canonicalChordKey n triangleCoord (Finset.univ \ S) =
      canonicalChordKey n triangleCoord S := by
  funext i
  rw [canonicalChordKey, canonicalChordKey,
    (canonicalDirectedTriangle n triangleCoord i).restriction_compl,
    triangleChordIndex_compl]

/-- The three vertices of each canonical triangle, regarded in Hamilton-cycle order. -/
def canonicalTriangleVertices (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (i : Fin n) (j : Fin 3) : Fin (3 * n) := triangleCoord.symm (i, j)

/-- Crossing relation for sides from distinct canonical triangles.  The explicit off-diagonal
guard is immaterial to selected degrees (which erase the diagonal) and makes symmetry literal
even though the open-interval crossing predicate is intentionally not symmetric for chords that
share an endpoint. -/
def canonicalChordCrossRel (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    OddTransversal.CrossRel (fun _ : Fin n ↦ Fin 3) :=
  fun i j ei ej ↦ i ≠ j ∧
    ChordCrossing.triangleCrossRel (canonicalTriangleVertices n triangleCoord) i j ei ej

/-- Unoriented chord selections whose selected crossing degree is even at every triangle. -/
noncomputable def canonicalGoodChordKeys (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    Finset (Fin n → Fin 3) := by
  classical
  exact Finset.univ.filter fun key ↦
    OddTransversal.Good (fun _ : Fin n ↦ Fin 3)
      (canonicalChordCrossRel n triangleCoord) key

@[simp] theorem mem_canonicalGoodChordKeys (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key : Fin n → Fin 3) :
    key ∈ canonicalGoodChordKeys n triangleCoord ↔
      OddTransversal.Good (fun _ : Fin n ↦ Fin 3)
        (canonicalChordCrossRel n triangleCoord) key := by
  classical
  simp [canonicalGoodChordKeys]

/-- Crossing of sides belonging to two canonical triangles is a symmetric relation. -/
theorem canonical_triangleCrossRel_symmetric (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    OddTransversal.Symmetric (fun _ : Fin n ↦ Fin 3)
      (canonicalChordCrossRel n triangleCoord) := by
  intro i j ei ej
  by_cases hij : i = j
  · subst j
    simp [canonicalChordCrossRel]
  · constructor
    · rintro ⟨_, hcross⟩
      refine ⟨Ne.symm hij, ?_⟩
      apply (ChordCrossing.crosses_comm_of_endpoint_ne ?_ ?_ ?_ ?_).mp hcross
      all_goals
        intro h
        apply hij
        have hp := congrArg triangleCoord h
        dsimp [ChordCrossing.triangleCrossRel, ChordCrossing.triangleSide,
          canonicalTriangleVertices] at hp
        simpa only [Equiv.apply_symm_apply] using congrArg Prod.fst hp
    · rintro ⟨_, hcross⟩
      refine ⟨hij, ?_⟩
      apply (ChordCrossing.crosses_comm_of_endpoint_ne ?_ ?_ ?_ ?_).mpr hcross
      all_goals
        intro h
        apply hij
        have hp := congrArg triangleCoord h
        dsimp [ChordCrossing.triangleCrossRel, ChordCrossing.triangleSide,
          canonicalTriangleVertices] at hp
        simpa only [Equiv.apply_symm_apply] using congrArg Prod.fst hp

/-- Petrov's odd-transversal lemma makes the set of good canonical chord keys odd. -/
theorem canonicalGoodChordKeys_odd (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    Odd (canonicalGoodChordKeys n triangleCoord).card := by
  classical
  unfold canonicalGoodChordKeys
  apply OddTransversal.odd_card_good_filter_fin_three
  · exact canonical_triangleCrossRel_symmetric n triangleCoord
  · intro i j ei hij
    unfold canonicalChordCrossRel OddTransversal.crossDegree
    convert ChordCrossing.triangle_crossDegree_even
      (canonicalTriangleVertices n triangleCoord) i j ei using 1
    congr 1
    ext ej
    simp [hij]

/-- The coefficient layer's canonical vertex notation is definitionally the endpoint notation
used by `GoodChords`. -/
theorem canonicalTriangleVertices_eq_goodChords (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    canonicalTriangleVertices n triangleCoord = GoodChords.triangleVertices triangleCoord := rfl

/-- The two presentations use exactly the same guarded crossing relation. -/
theorem canonicalChordCrossRel_eq_goodChords (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    canonicalChordCrossRel n triangleCoord = GoodChords.crossRel triangleCoord := rfl

/-- The Petrov-good keys in this coefficient reduction are definitionally the good selections
whose endpoint order is constructed in `GoodChords`. -/
theorem canonicalGoodChordKeys_eq_goodSelections (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    canonicalGoodChordKeys n triangleCoord = GoodChords.goodSelections triangleCoord := rfl

theorem canonical_restriction_toggle_ne (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) {i k : Fin n} (hik : i ≠ k) :
    (canonicalDirectedTriangle n triangleCoord k).restriction
        ((canonicalDirectedTriangle n triangleCoord i).toggle S) =
      (canonicalDirectedTriangle n triangleCoord k).restriction S := by
  classical
  ext j
  simp only [DirectedTriangle.mem_restriction, DirectedTriangle.toggle,
    Finset.mem_symmDiff]
  have hnot : (canonicalDirectedTriangle n triangleCoord k).arc j ∉
      (canonicalDirectedTriangle n triangleCoord i).arcSet := by
    rw [(canonicalDirectedTriangle n triangleCoord i).mem_arcSet]
    simp only [canonicalDirectedTriangle, Sum.inr.injEq, Prod.mk.injEq, not_exists]
    intro q
    exact fun h ↦ hik h.1
  tauto

/-- Indices of canonical triangles whose selected restriction is empty or full. -/
noncomputable def canonicalDegenerateIndices (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦
    (canonicalDirectedTriangle n triangleCoord i).restriction S = ∅ ∨
      (canonicalDirectedTriangle n triangleCoord i).restriction S = Finset.univ

@[simp] theorem mem_canonicalDegenerateIndices (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) (i : Fin n) :
    i ∈ canonicalDegenerateIndices n triangleCoord S ↔
      (canonicalDirectedTriangle n triangleCoord i).restriction S = ∅ ∨
        (canonicalDirectedTriangle n triangleCoord i).restriction S = Finset.univ := by
  classical
  simp [canonicalDegenerateIndices]

/-- Toggling a degenerate canonical triangle does not change the set of degenerate indices. -/
theorem canonicalDegenerateIndices_toggle (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) (i : Fin n)
    (hi : i ∈ canonicalDegenerateIndices n triangleCoord S) :
    canonicalDegenerateIndices n triangleCoord
        ((canonicalDirectedTriangle n triangleCoord i).toggle S) =
      canonicalDegenerateIndices n triangleCoord S := by
  classical
  ext k
  simp only [mem_canonicalDegenerateIndices]
  by_cases hik : i = k
  · subst k
    exact (canonicalDirectedTriangle n triangleCoord i).restriction_toggle_degenerate_iff S
  · rw [canonical_restriction_toggle_ne n triangleCoord S hik]

/-- Balanced selections with no empty/full triangle restriction. -/
noncomputable def canonicalSurvivors (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    Finset (Finset (CanonicalOccurrence n)) :=
  (balancedSelections (canonicalIndexedArcs n triangleCoord)).filter fun S ↦
    canonicalDegenerateIndices n triangleCoord S = ∅

@[simp] theorem mem_canonicalSurvivors (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    S ∈ canonicalSurvivors n triangleCoord ↔
      (canonicalIndexedArcs n triangleCoord).Balanced S ∧
        canonicalDegenerateIndices n triangleCoord S = ∅ := by
  classical
  simp [canonicalSurvivors]

/-- Globally complementing a canonical balanced selection preserves balancedness.  The proof
uses the genuinely two-in/two-out occurrence structure, rather than any property of the simple
underlying graph. -/
theorem canonical_balanced_compl (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : (canonicalIndexedArcs n triangleCoord).Balanced S) :
    (canonicalIndexedArcs n triangleCoord).Balanced (Finset.univ \ S) := by
  classical
  apply balanced_sdiff_of_subset (Finset.subset_univ S) _ hS
  apply univ_balanced_of_degrees_eq
  intro v
  rw [canonicalIndexedArcs_indegree_two n triangleCoord v,
    canonicalIndexedArcs_outdegree_two n triangleCoord v]

/-- Global complementation preserves exactly which triangle restrictions are degenerate. -/
theorem canonicalDegenerateIndices_compl (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    canonicalDegenerateIndices n triangleCoord (Finset.univ \ S) =
      canonicalDegenerateIndices n triangleCoord S := by
  classical
  ext i
  simp only [mem_canonicalDegenerateIndices,
    (canonicalDirectedTriangle n triangleCoord i).restriction_compl]
  constructor
  · rintro (h | h)
    · right
      ext j
      have hm := congrArg (fun U : Finset (Fin 3) ↦ j ∈ U) h
      simpa using hm
    · left
      ext j
      have hm := congrArg (fun U : Finset (Fin 3) ↦ j ∈ U) h
      simpa using hm
  · rintro (h | h)
    · right
      rw [h]
      simp
    · left
      rw [h]
      simp

/-- The survivor set is closed under global complementation. -/
theorem canonicalSurvivors_compl (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : S ∈ canonicalSurvivors n triangleCoord) :
    Finset.univ \ S ∈ canonicalSurvivors n triangleCoord := by
  rw [mem_canonicalSurvivors] at hS ⊢
  exact ⟨canonical_balanced_compl n triangleCoord hS.1,
    (canonicalDegenerateIndices_compl n triangleCoord S).trans hS.2⟩

/-- Because the canonical occurrence universe has even cardinality, complementary selections
have the same graph-polynomial sign. -/
theorem canonical_selectionSign_compl (n : ℕ)
    (S : Finset (CanonicalOccurrence n)) :
    selectionSign (Finset.univ \ S) = selectionSign S := by
  classical
  have hcard : (Finset.univ \ S).card + S.card =
      Fintype.card (CanonicalOccurrence n) := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ S)
  have hevenTotal : Even (Fintype.card (CanonicalOccurrence n)) := by
    rw [canonicalOccurrence_card]
    exact even_two_mul _
  have hevenSum : Even ((Finset.univ \ S).card + S.card) := by
    rw [hcard]
    exact hevenTotal
  unfold selectionSign
  exact neg_one_pow_congr (Nat.even_add.mp hevenSum)

/-- For a nonempty canonical graph, no occurrence selection equals its global complement. -/
theorem canonical_compl_ne_self {n : ℕ} (hn : 0 < n)
    (S : Finset (CanonicalOccurrence n)) : Finset.univ \ S ≠ S := by
  classical
  let v : Fin (3 * n) := ⟨0, by omega⟩
  let a : CanonicalOccurrence n := Sum.inl v
  intro h
  have ha := Finset.ext_iff.mp h a
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at ha
  tauto

/-- Once a chord-key fibre has cardinality two, its two elements are necessarily a survivor and
its global complement.  Thus the equal-sign assertion is not an extra fibre hypothesis. -/
theorem canonicalChord_fibre_eq_pair {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : S ∈ canonicalSurvivors n triangleCoord)
    (htwo : ((canonicalSurvivors n triangleCoord).filter fun T ↦
      canonicalChordKey n triangleCoord T = canonicalChordKey n triangleCoord S).card = 2) :
    (canonicalSurvivors n triangleCoord).filter (fun T ↦
        canonicalChordKey n triangleCoord T = canonicalChordKey n triangleCoord S) =
      {S, Finset.univ \ S} := by
  classical
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro T hT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hT
    rw [Finset.mem_filter]
    rcases hT with rfl | rfl
    · exact ⟨hS, rfl⟩
    · exact ⟨canonicalSurvivors_compl n triangleCoord hS,
        canonicalChordKey_compl n triangleCoord S⟩
  · rw [htwo, Finset.card_pair (canonical_compl_ne_self hn S).symm]

/-- Every two-element canonical chord fibre has a common unit sign.  Complementation supplies
the second member and preserves the sign because there are `6n` indexed occurrences. -/
theorem canonicalChord_fibre_same_unit_sign {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (g : Fin n → Fin 3)
    (htwo : ((canonicalSurvivors n triangleCoord).filter fun S ↦
      canonicalChordKey n triangleCoord S = g).card = 2) :
    (∀ S ∈ canonicalSurvivors n triangleCoord,
        canonicalChordKey n triangleCoord S = g → selectionSign S = 1) ∨
      (∀ S ∈ canonicalSurvivors n triangleCoord,
        canonicalChordKey n triangleCoord S = g → selectionSign S = -1) := by
  classical
  let F := (canonicalSurvivors n triangleCoord).filter fun S ↦
    canonicalChordKey n triangleCoord S = g
  have hFcard : F.card = 2 := htwo
  have hFne : F.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h] at hFcard
    simp at hFcard
  obtain ⟨S, hSF⟩ := hFne
  have hS : S ∈ canonicalSurvivors n triangleCoord := (Finset.mem_filter.mp hSF).1
  have hSkey : canonicalChordKey n triangleCoord S = g := (Finset.mem_filter.mp hSF).2
  have hpair := canonicalChord_fibre_eq_pair hn triangleCoord hS (by simpa [hSkey] using htwo)
  have hall : ∀ T ∈ canonicalSurvivors n triangleCoord,
      canonicalChordKey n triangleCoord T = g → selectionSign T = selectionSign S := by
    intro T hT hTkey
    have hTF : T ∈ (canonicalSurvivors n triangleCoord).filter (fun U ↦
        canonicalChordKey n triangleCoord U = canonicalChordKey n triangleCoord S) := by
      rw [Finset.mem_filter]
      exact ⟨hT, hTkey.trans hSkey.symm⟩
    rw [hpair] at hTF
    simp only [Finset.mem_insert, Finset.mem_singleton] at hTF
    rcases hTF with rfl | rfl
    · rfl
    · exact canonical_selectionSign_compl n S
  rcases Nat.even_or_odd S.card with heven | hodd
  · left
    intro T hT hTkey
    rw [hall T hT hTkey]
    exact heven.neg_one_pow
  · right
    intro T hT hTkey
    rw [hall T hT hTkey]
    exact hodd.neg_one_pow

/-- Toggle the least degenerate triangle, using the order on `Fin n`.  On survivors this is the
identity, but the cancellation theorem only uses it off the survivor set. -/
noncomputable def toggleFirstDegenerate (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) : Finset (CanonicalOccurrence n) :=
  if h : (canonicalDegenerateIndices n triangleCoord S).Nonempty then
    (canonicalDirectedTriangle n triangleCoord
      ((canonicalDegenerateIndices n triangleCoord S).min' h)).toggle S
  else S

theorem toggleFirstDegenerate_of_nonempty (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (h : (canonicalDegenerateIndices n triangleCoord S).Nonempty) :
    toggleFirstDegenerate n triangleCoord S =
      (canonicalDirectedTriangle n triangleCoord
        ((canonicalDegenerateIndices n triangleCoord S).min' h)).toggle S := by
  rw [toggleFirstDegenerate, dif_pos h]

theorem toggleFirstDegenerate_mem_complement (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \
      canonicalSurvivors n triangleCoord) :
    toggleFirstDegenerate n triangleCoord S ∈
      balancedSelections (canonicalIndexedArcs n triangleCoord) \
        canonicalSurvivors n triangleCoord := by
  classical
  have hbal : (canonicalIndexedArcs n triangleCoord).Balanced S :=
    mem_balancedSelections _ _ |>.mp (Finset.mem_sdiff.mp hS).1
  have hdegne : canonicalDegenerateIndices n triangleCoord S ≠ ∅ := by
    intro he
    exact (Finset.mem_sdiff.mp hS).2
      (mem_canonicalSurvivors n triangleCoord S |>.2 ⟨hbal, he⟩)
  have hnon : (canonicalDegenerateIndices n triangleCoord S).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hdegne
  let i := (canonicalDegenerateIndices n triangleCoord S).min' hnon
  have hi : i ∈ canonicalDegenerateIndices n triangleCoord S :=
    Finset.min'_mem _ _
  have hideg := mem_canonicalDegenerateIndices n triangleCoord S i |>.mp hi
  rw [toggleFirstDegenerate_of_nonempty n triangleCoord S hnon]
  change (canonicalDirectedTriangle n triangleCoord i).toggle S ∈ _
  apply Finset.mem_sdiff.mpr
  constructor
  · apply mem_balancedSelections _ _ |>.2
    exact (canonicalDirectedTriangle n triangleCoord i).balanced_toggle_of_degenerate S
      hbal hideg
  · intro hsurv
    have hempty : canonicalDegenerateIndices n triangleCoord
        ((canonicalDirectedTriangle n triangleCoord i).toggle S) = ∅ :=
      (mem_canonicalSurvivors n triangleCoord _ |>.mp hsurv).2
    rw [canonicalDegenerateIndices_toggle n triangleCoord S i hi] at hempty
    exact hdegne hempty

theorem toggleFirstDegenerate_involutive (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \
      canonicalSurvivors n triangleCoord) :
    toggleFirstDegenerate n triangleCoord (toggleFirstDegenerate n triangleCoord S) = S := by
  classical
  have hdegne : canonicalDegenerateIndices n triangleCoord S ≠ ∅ := by
    intro he
    have hbal := mem_balancedSelections _ _ |>.mp (Finset.mem_sdiff.mp hS).1
    exact (Finset.mem_sdiff.mp hS).2
      (mem_canonicalSurvivors n triangleCoord S |>.2 ⟨hbal, he⟩)
  have hnon := Finset.nonempty_iff_ne_empty.mpr hdegne
  let i := (canonicalDegenerateIndices n triangleCoord S).min' hnon
  have hi : i ∈ canonicalDegenerateIndices n triangleCoord S := Finset.min'_mem _ _
  have hind := canonicalDegenerateIndices_toggle n triangleCoord S i hi
  rw [toggleFirstDegenerate_of_nonempty n triangleCoord S hnon]
  have hnon' : (canonicalDegenerateIndices n triangleCoord
      ((canonicalDirectedTriangle n triangleCoord i).toggle S)).Nonempty := by
    rw [hind]
    exact hnon
  rw [toggleFirstDegenerate_of_nonempty n triangleCoord _ hnon']
  have hmin : (canonicalDegenerateIndices n triangleCoord
      ((canonicalDirectedTriangle n triangleCoord i).toggle S)).min' hnon' = i := by
    apply (Finset.min'_eq_iff
      (canonicalDegenerateIndices n triangleCoord
        ((canonicalDirectedTriangle n triangleCoord i).toggle S)) hnon' i).2
    constructor
    · rw [hind]
      exact hi
    · intro b hb
      apply Finset.min'_le
      rw [← hind]
      exact hb
  rw [hmin]
  exact (canonicalDirectedTriangle n triangleCoord i).toggle_toggle S

theorem toggleFirstDegenerate_ne (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \
      canonicalSurvivors n triangleCoord) :
    toggleFirstDegenerate n triangleCoord S ≠ S := by
  classical
  have hdegne : canonicalDegenerateIndices n triangleCoord S ≠ ∅ := by
    intro he
    have hbal := mem_balancedSelections _ _ |>.mp (Finset.mem_sdiff.mp hS).1
    exact (Finset.mem_sdiff.mp hS).2
      (mem_canonicalSurvivors n triangleCoord S |>.2 ⟨hbal, he⟩)
  have hnon := Finset.nonempty_iff_ne_empty.mpr hdegne
  rw [toggleFirstDegenerate_of_nonempty n triangleCoord S hnon]
  exact (canonicalDirectedTriangle n triangleCoord _).toggle_ne S

theorem toggleFirstDegenerate_negates (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n))
    (hS : S ∈ balancedSelections (canonicalIndexedArcs n triangleCoord) \
      canonicalSurvivors n triangleCoord) :
    selectionSign (toggleFirstDegenerate n triangleCoord S) = -selectionSign S := by
  classical
  have hdegne : canonicalDegenerateIndices n triangleCoord S ≠ ∅ := by
    intro he
    have hbal := mem_balancedSelections _ _ |>.mp (Finset.mem_sdiff.mp hS).1
    exact (Finset.mem_sdiff.mp hS).2
      (mem_canonicalSurvivors n triangleCoord S |>.2 ⟨hbal, he⟩)
  have hnon := Finset.nonempty_iff_ne_empty.mpr hdegne
  let i := (canonicalDegenerateIndices n triangleCoord S).min' hnon
  have hi : i ∈ canonicalDegenerateIndices n triangleCoord S := Finset.min'_mem _ _
  rw [toggleFirstDegenerate_of_nonempty n triangleCoord S hnon]
  exact (canonicalDirectedTriangle n triangleCoord i).selectionSign_toggle_of_degenerate S
    (mem_canonicalDegenerateIndices n triangleCoord S i |>.mp hi)

/-- Exact cancellation of every balanced subset containing an empty or full triangle
restriction.  This reduces the central coefficient to the nondegenerate survivors. -/
theorem canonicalCoeff_eq_survivor_sum (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3) :
    MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
        (canonicalIndexedArcs n triangleCoord).polynomial =
      ∑ S ∈ canonicalSurvivors n triangleCoord, selectionSign S := by
  rw [centralCoeff_eq_sum_balancedSelections _
    (canonicalIndexedArcs_outdegree_two n triangleCoord)]
  apply SignedCancellation.sum_eq_sum_survivors
    (balancedSelections (canonicalIndexedArcs n triangleCoord))
    (canonicalSurvivors n triangleCoord) selectionSign
    (toggleFirstDegenerate n triangleCoord)
  · intro S hS
    exact (Finset.mem_filter.mp hS).1
  · exact toggleFirstDegenerate_mem_complement n triangleCoord
  · exact toggleFirstDegenerate_involutive n triangleCoord
  · exact toggleFirstDegenerate_ne n triangleCoord
  · exact toggleFirstDegenerate_negates n triangleCoord

/-- Canonical coefficient fibre theorem after triangle-degenerate cancellation.

At this point all cancellation data are internal.  A caller supplies only the map from surviving
balanced selections to good unoriented chord selections, the fact that every good chord selection
has its two global orientations, equality of their signs, and the oddness of the good set. -/
theorem canonicalCoeff_modEq_two_of_survivor_fibres
    (n : ℕ) (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {B : Type*} [DecidableEq B] (good : Finset B)
    (key : Finset (CanonicalOccurrence n) → B)
    (key_good : ∀ S ∈ canonicalSurvivors n triangleCoord, key S ∈ good)
    (two_orientations : ∀ g ∈ good,
      ((canonicalSurvivors n triangleCoord).filter fun S ↦ key S = g).card = 2)
    (same_sign : ∀ g ∈ good,
      (∀ S ∈ canonicalSurvivors n triangleCoord,
          key S = g → selectionSign S = 1) ∨
        (∀ S ∈ canonicalSurvivors n triangleCoord,
          key S = g → selectionSign S = -1))
    (odd_good : Odd good.card) :
    MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
      (canonicalIndexedArcs n triangleCoord).polynomial ≡ 2 [ZMOD 4] := by
  rw [canonicalCoeff_eq_survivor_sum n triangleCoord]
  exact SignedCancellation.survivor_sum_modEq_two
    (canonicalSurvivors n triangleCoord) good key selectionSign key_good
      two_orientations same_sign odd_good

/-- Nonvanishing version of the fully internalized canonical cancellation theorem. -/
theorem canonicalCoeff_ne_zero_of_survivor_fibres
    (n : ℕ) (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {B : Type*} [DecidableEq B] (good : Finset B)
    (key : Finset (CanonicalOccurrence n) → B)
    (key_good : ∀ S ∈ canonicalSurvivors n triangleCoord, key S ∈ good)
    (two_orientations : ∀ g ∈ good,
      ((canonicalSurvivors n triangleCoord).filter fun S ↦ key S = g).card = 2)
    (same_sign : ∀ g ∈ good,
      (∀ S ∈ canonicalSurvivors n triangleCoord,
          key S = g → selectionSign S = 1) ∨
        (∀ S ∈ canonicalSurvivors n triangleCoord,
          key S = g → selectionSign S = -1))
    (odd_good : Odd good.card) :
    MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
      (canonicalIndexedArcs n triangleCoord).polynomial ≠ 0 := by
  apply (canonicalIndexedArcs n triangleCoord).coeff_central_ne_zero_of_modEq_two
  exact canonicalCoeff_modEq_two_of_survivor_fibres n triangleCoord good key key_good
    two_orientations same_sign odd_good

/-- Concrete canonical reduction: Petrov's odd good-chord theorem and the equal-sign assertion
are discharged internally.  The only remaining mathematical fibre facts are that every survivor
has a good underlying chord key and that every good key has its two global orientations. -/
theorem canonicalCoeff_modEq_two_of_goodChord_fibres
    {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key_good : ∀ S ∈ canonicalSurvivors n triangleCoord,
      canonicalChordKey n triangleCoord S ∈ canonicalGoodChordKeys n triangleCoord)
    (two_orientations : ∀ g ∈ canonicalGoodChordKeys n triangleCoord,
      ((canonicalSurvivors n triangleCoord).filter fun S ↦
        canonicalChordKey n triangleCoord S = g).card = 2) :
    MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
      (canonicalIndexedArcs n triangleCoord).polynomial ≡ 2 [ZMOD 4] := by
  apply canonicalCoeff_modEq_two_of_survivor_fibres n triangleCoord
    (canonicalGoodChordKeys n triangleCoord) (canonicalChordKey n triangleCoord)
  · exact key_good
  · exact two_orientations
  · intro g hg
    exact canonicalChord_fibre_same_unit_sign hn triangleCoord g (two_orientations g hg)
  · exact canonicalGoodChordKeys_odd n triangleCoord

/-- Nonvanishing form of the concrete good-chord reduction. -/
theorem canonicalCoeff_ne_zero_of_goodChord_fibres
    {n : ℕ} (hn : 0 < n)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (key_good : ∀ S ∈ canonicalSurvivors n triangleCoord,
      canonicalChordKey n triangleCoord S ∈ canonicalGoodChordKeys n triangleCoord)
    (two_orientations : ∀ g ∈ canonicalGoodChordKeys n triangleCoord,
      ((canonicalSurvivors n triangleCoord).filter fun S ↦
        canonicalChordKey n triangleCoord S = g).card = 2) :
    MvPolynomial.coeff (canonicalIndexedArcs n triangleCoord).centralExponent
      (canonicalIndexedArcs n triangleCoord).polynomial ≠ 0 := by
  apply (canonicalIndexedArcs n triangleCoord).coeff_central_ne_zero_of_modEq_two
  exact canonicalCoeff_modEq_two_of_goodChord_fibres hn triangleCoord key_good two_orientations

/-- The empty (`n = 0`) canonical instance has polynomial and central monomial both equal to one.
This is the base case for the final all-`n` coefficient theorem. -/
theorem canonicalCoeff_ne_zero_zero
    (triangleCoord : Fin (3 * 0) ≃ Fin 0 × Fin 3) :
    MvPolynomial.coeff (canonicalIndexedArcs 0 triangleCoord).centralExponent
      (canonicalIndexedArcs 0 triangleCoord).polynomial ≠ 0 := by
  simp [IndexedArcs.centralExponent, IndexedArcs.polynomial,
    canonicalIndexedArcs, CanonicalOccurrence]

/-- Every canonical survivor supplies, in each triangle, one positive and one negative endpoint
of its oriented chord and a zero boundary at the remaining endpoint. -/
theorem canonicalSurvivor_has_orientedChord
    (n : ℕ) (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : S ∈ canonicalSurvivors n triangleCoord) (i : Fin n) :
    ∃ p q : Fin 3, p ≠ q ∧
      triangleBoundary ((canonicalDirectedTriangle n triangleCoord i).restriction S) p = 1 ∧
      triangleBoundary ((canonicalDirectedTriangle n triangleCoord i).restriction S) q = -1 ∧
      ∀ r, r ≠ p → r ≠ q →
        triangleBoundary ((canonicalDirectedTriangle n triangleCoord i).restriction S) r = 0 := by
  have hnone : i ∉ canonicalDegenerateIndices n triangleCoord S := by
    have hdeg := (mem_canonicalSurvivors n triangleCoord S |>.mp hS).2
    rw [hdeg]
    simp
  rw [mem_canonicalDegenerateIndices] at hnone
  push_neg at hnone
  exact triangleBoundary_nondegenerate _ hnone.1.ne_empty hnone.2

end CanonicalTriangle

end TriangleInIndexedArcs

section CircularBoundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The boundary of a Boolean edge choice under a cyclic predecessor permutation. -/
def cycleBoundary (pred : Equiv.Perm ι) (S : Finset ι) (v : ι) : ℤ :=
  (if pred v ∈ S then 1 else 0) - if v ∈ S then 1 else 0

@[simp] theorem cycleBoundary_empty (pred : Equiv.Perm ι) (v : ι) :
    cycleBoundary pred ∅ v = 0 := by simp [cycleBoundary]

@[simp] theorem cycleBoundary_univ (pred : Equiv.Perm ι) (v : ι) :
    cycleBoundary pred Finset.univ v = 0 := by simp [cycleBoundary]

/-- Equality of cyclic boundaries propagates membership across one predecessor step. -/
theorem mem_iff_mem_of_cycleBoundary_eq
    (pred : Equiv.Perm ι) {S T : Finset ι}
    (h : ∀ v, cycleBoundary pred S v = cycleBoundary pred T v) (v : ι) :
    (v ∈ S ↔ v ∈ T) ↔ (pred v ∈ S ↔ pred v ∈ T) := by
  simp only [cycleBoundary] at h
  specialize h v
  by_cases hvS : v ∈ S <;> by_cases hvT : v ∈ T <;>
    by_cases hpS : pred v ∈ S <;> by_cases hpT : pred v ∈ T <;> simp_all

/-- Knowing only the support of the cyclic boundary is enough to propagate whether two Boolean
edge selections agree.  At a supported vertex both selections toggle; away from the support
neither toggles. -/
theorem mem_iff_mem_of_cycleBoundary_support_eq
    (pred : Equiv.Perm ι) {S T : Finset ι}
    (h : ∀ v, (cycleBoundary pred S v ≠ 0 ↔ cycleBoundary pred T v ≠ 0))
    (v : ι) :
    (v ∈ S ↔ v ∈ T) ↔ (pred v ∈ S ↔ pred v ∈ T) := by
  specialize h v
  simp only [cycleBoundary] at h
  by_cases hvS : v ∈ S <;> by_cases hvT : v ∈ T <;>
    by_cases hpS : pred v ∈ S <;> by_cases hpT : pred v ∈ T <;> simp_all

/-- On a single cyclic orbit, two Boolean selections with the same change-point set are equal or
global complements.  Unlike `eq_or_compl_of_cycleBoundary_eq`, this forgets the signs of the
changes and is the precise uniqueness statement needed for unoriented chord fibres. -/
theorem eq_or_compl_of_cycleBoundary_support_eq
    (pred : Equiv.Perm ι)
    (htrans : ∀ u v : ι, ∃ k : ℕ, (pred ^ k) u = v)
    {S T : Finset ι}
    (h : ∀ v, (cycleBoundary pred S v ≠ 0 ↔ cycleBoundary pred T v ≠ 0)) :
    S = T ∨ S = Finset.univ \ T := by
  classical
  by_cases hbase : ∃ u, (u ∈ S ↔ u ∈ T)
  · left
    ext v
    obtain ⟨u, hu⟩ := hbase
    obtain ⟨k, hk⟩ := htrans v u
    have step : ∀ x, (x ∈ S ↔ x ∈ T) ↔ (pred x ∈ S ↔ pred x ∈ T) :=
      mem_iff_mem_of_cycleBoundary_support_eq pred h
    have orbit : ∀ k : ℕ,
        (v ∈ S ↔ v ∈ T) ↔ ((pred ^ k) v ∈ S ↔ (pred ^ k) v ∈ T) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ']
          exact ih.trans (step ((pred ^ k) v))
    exact (orbit k).mpr (by simpa [hk] using hu)
  · right
    ext v
    have hv : ¬(v ∈ S ↔ v ∈ T) := by
      intro hv
      exact hbase ⟨v, hv⟩
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto

/-- If `pred` consists of a single orbit, two edge selections with the same boundary are either
equal or complementary.  A later specialization to `Fin m` supplies the single-orbit fact. -/
theorem eq_or_compl_of_cycleBoundary_eq
    (pred : Equiv.Perm ι)
    (htrans : ∀ u v : ι, ∃ k : ℕ, (pred ^ k) u = v)
    {S T : Finset ι}
    (h : ∀ v, cycleBoundary pred S v = cycleBoundary pred T v) :
    S = T ∨ S = Finset.univ \ T := by
  classical
  by_cases hbase : ∃ u, (u ∈ S ↔ u ∈ T)
  · left
    ext v
    obtain ⟨u, hu⟩ := hbase
    obtain ⟨k, hk⟩ := htrans v u
    have step : ∀ x, (x ∈ S ↔ x ∈ T) ↔ (pred x ∈ S ↔ pred x ∈ T) :=
      mem_iff_mem_of_cycleBoundary_eq pred h
    have orbit : ∀ k : ℕ, (v ∈ S ↔ v ∈ T) ↔ ((pred ^ k) v ∈ S ↔ (pred ^ k) v ∈ T) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [pow_succ']
          exact ih.trans (step ((pred ^ k) v))
    exact (orbit k).mpr (by simpa [hk] using hu)
  · right
    ext v
    have hv : ¬(v ∈ S ↔ v ∈ T) := by
      intro hv
      exact hbase ⟨v, hv⟩
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    tauto

/-- Consequently a nonzero cyclic boundary has at most one preimage. -/
theorem unique_of_cycleBoundary_eq_of_nonzero
    (pred : Equiv.Perm ι)
    (htrans : ∀ u v : ι, ∃ k : ℕ, (pred ^ k) u = v)
    {S T : Finset ι}
    (hS : ∃ v, cycleBoundary pred S v ≠ 0)
    (h : ∀ v, cycleBoundary pred S v = cycleBoundary pred T v) : S = T := by
  rcases eq_or_compl_of_cycleBoundary_eq pred htrans h with hEq | hCompl
  · exact hEq
  · exfalso
    obtain ⟨v, hv⟩ := hS
    have hb : cycleBoundary pred (Finset.univ \ T) v =
        -cycleBoundary pred T v := by
      simp only [cycleBoundary, Finset.mem_sdiff, Finset.mem_univ, true_and]
      split_ifs <;> omega
    have heq := h v
    rw [hCompl, hb] at heq
    rw [hCompl, hb] at hv
    omega

end CircularBoundary

section CanonicalBoundaryDecomposition

/-- Restrict an indexed occurrence selection to its Hamilton-cycle occurrences. -/
noncomputable def canonicalCycleRestriction (n : ℕ)
    (S : Finset (CanonicalOccurrence n)) : Finset (Fin (3 * n)) :=
  Finset.univ.filter fun v ↦ Sum.inl v ∈ S

@[simp] theorem mem_canonicalCycleRestriction (n : ℕ)
    (S : Finset (CanonicalOccurrence n)) (v : Fin (3 * n)) :
    v ∈ canonicalCycleRestriction n S ↔ Sum.inl v ∈ S := by
  classical
  simp [canonicalCycleRestriction]

/-- The predecessor of a vertex in the canonical Hamiltonian cycle. -/
noncomputable def canonicalCyclePred (n : ℕ) : Equiv.Perm (Fin (3 * n)) :=
  (finRotate (3 * n)).symm

/-- The selected outdegree splits into its unique cycle occurrence and its unique triangle
occurrence. -/
theorem canonical_selectedOut_eq (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) (v : Fin (3 * n)) :
    (canonicalIndexedArcs n triangleCoord).selectedOut S v =
      (if v ∈ canonicalCycleRestriction n S then 1 else 0) +
      (if (triangleCoord v).2 ∈
          (canonicalDirectedTriangle n triangleCoord (triangleCoord v).1).restriction S
        then 1 else 0) := by
  classical
  unfold IndexedArcs.selectedOut
  have hf : S.filter (fun a ↦ (canonicalIndexedArcs n triangleCoord).tail a = v) =
      ({Sum.inl v, Sum.inr (triangleCoord v)} : Finset (CanonicalOccurrence n)).filter
        (fun a ↦ a ∈ S) := by
    ext a
    simp only [Finset.mem_filter]
    cases a with
    | inl i => simp [canonicalIndexedArcs, canonicalOccurrenceTail, and_comm]
    | inr ij =>
      constructor
      · rintro ⟨hm, ht⟩
        have hp := congrArg triangleCoord ht
        simp only [canonicalIndexedArcs_tail, canonicalOccurrenceTail,
          Equiv.apply_symm_apply] at hp
        exact ⟨by simp [hp], hm⟩
      · rintro ⟨hp, hm⟩
        have hij : ij = triangleCoord v := by simpa using hp
        subst ij
        exact ⟨hm, triangleCoord.symm_apply_apply v⟩
  rw [hf]
  by_cases hc : Sum.inl v ∈ S <;>
    by_cases ht : Sum.inr (triangleCoord v) ∈ S <;>
    simp_all [DirectedTriangle.mem_restriction, canonicalDirectedTriangle,
      Finset.filter_insert, Finset.filter_singleton]

/-- The selected indegree similarly splits into the preceding cycle occurrence and preceding
triangle side. -/
theorem canonical_selectedIn_eq (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) (v : Fin (3 * n)) :
    (canonicalIndexedArcs n triangleCoord).selectedIn S v =
      (if canonicalCyclePred n v ∈ canonicalCycleRestriction n S then 1 else 0) +
      (if triPred (triangleCoord v).2 ∈
          (canonicalDirectedTriangle n triangleCoord (triangleCoord v).1).restriction S
        then 1 else 0) := by
  classical
  unfold IndexedArcs.selectedIn
  let cin : CanonicalOccurrence n := Sum.inl (canonicalCyclePred n v)
  let tin : CanonicalOccurrence n :=
    Sum.inr ((triangleCoord v).1, triPred (triangleCoord v).2)
  have hf : S.filter (fun a ↦ (canonicalIndexedArcs n triangleCoord).head a = v) =
      ({cin, tin} : Finset (CanonicalOccurrence n)).filter (fun a ↦ a ∈ S) := by
    ext a
    simp only [Finset.mem_filter]
    cases a with
    | inl u =>
      simp only [canonicalIndexedArcs_head, canonicalOccurrenceHead,
        Finset.mem_insert, Finset.mem_singleton, cin, tin, Sum.inl.injEq,
        Sum.inl_ne_inr, or_false]
      change (Sum.inl u ∈ S ∧ finCyclicSucc (3 * n) u = v) ↔
        (u = canonicalCyclePred n v ∧ Sum.inl u ∈ S)
      rw [finCyclicSucc_eq_finRotate]
      constructor
      · rintro ⟨hm, h⟩
        exact ⟨(Equiv.eq_symm_apply (finRotate (3 * n))).mpr h, hm⟩
      · rintro ⟨h, hm⟩
        exact ⟨hm, (Equiv.eq_symm_apply (finRotate (3 * n))).mp h⟩
    | inr iq =>
      constructor
      · rintro ⟨hm, ht⟩
        have hp := congrArg triangleCoord ht
        simp only [canonicalIndexedArcs_head, canonicalOccurrenceHead,
          Equiv.apply_symm_apply] at hp
        have hp' := Prod.ext_iff.mp hp
        have hi : iq.1 = (triangleCoord v).1 := hp'.1
        have hsucc : triSucc iq.2 = (triangleCoord v).2 := by
          change iq.2 + 1 = (triangleCoord v).2
          exact hp'.2
        have hq : iq.2 = triPred (triangleCoord v).2 := by
          rw [← hsucc, triPred_triSucc]
        have hiq : iq = ((triangleCoord v).1, triPred (triangleCoord v).2) :=
          Prod.ext hi hq
        exact ⟨by simp [cin, tin, hiq], hm⟩
      · rintro ⟨hp, hm⟩
        have hiq : iq = ((triangleCoord v).1, triPred (triangleCoord v).2) := by
          simpa [cin, tin] using hp
        subst iq
        refine ⟨hm, ?_⟩
        change triangleCoord.symm
          ((triangleCoord v).1, triSucc (triPred (triangleCoord v).2)) = v
        simp
  rw [hf]
  by_cases hc : Sum.inl (canonicalCyclePred n v) ∈ S <;>
    by_cases ht : Sum.inr ((triangleCoord v).1, triPred (triangleCoord v).2) ∈ S <;>
    simp_all [cin, tin, DirectedTriangle.mem_restriction, canonicalDirectedTriangle,
      Finset.filter_insert, Finset.filter_singleton]

/-- Canonical balance at a vertex is exactly cancellation between the Hamilton-cycle boundary
and the directed-triangle boundary. -/
theorem canonical_balance_boundary (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : (canonicalIndexedArcs n triangleCoord).Balanced S)
    (v : Fin (3 * n)) :
    cycleBoundary (canonicalCyclePred n) (canonicalCycleRestriction n S) v +
      triangleBoundary
        ((canonicalDirectedTriangle n triangleCoord (triangleCoord v).1).restriction S)
        (triangleCoord v).2 = 0 := by
  have hv := hS v
  rw [canonical_selectedIn_eq n triangleCoord S v,
    canonical_selectedOut_eq n triangleCoord S v] at hv
  unfold cycleBoundary triangleBoundary
  split_ifs at hv ⊢ <;> omega

/-- Conversely, the vertexwise boundary cancellation equations imply canonical balance. -/
theorem canonical_balanced_of_boundary (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    {S : Finset (CanonicalOccurrence n)}
    (hS : ∀ v,
      cycleBoundary (canonicalCyclePred n) (canonicalCycleRestriction n S) v +
        triangleBoundary
          ((canonicalDirectedTriangle n triangleCoord (triangleCoord v).1).restriction S)
          (triangleCoord v).2 = 0) :
    (canonicalIndexedArcs n triangleCoord).Balanced S := by
  intro v
  rw [canonical_selectedIn_eq n triangleCoord S v,
    canonical_selectedOut_eq n triangleCoord S v]
  specialize hS v
  unfold cycleBoundary triangleBoundary at hS
  split_ifs at hS ⊢ <;> omega

theorem canonical_balanced_iff_boundary (n : ℕ)
    (triangleCoord : Fin (3 * n) ≃ Fin n × Fin 3)
    (S : Finset (CanonicalOccurrence n)) :
    (canonicalIndexedArcs n triangleCoord).Balanced S ↔
      ∀ v,
        cycleBoundary (canonicalCyclePred n) (canonicalCycleRestriction n S) v +
          triangleBoundary
            ((canonicalDirectedTriangle n triangleCoord (triangleCoord v).1).restriction S)
            (triangleCoord v).2 = 0 := by
  constructor
  · exact fun h ↦ canonical_balance_boundary n triangleCoord h
  · exact canonical_balanced_of_boundary n triangleCoord

end CanonicalBoundaryDecomposition

end Erdos842.Coefficient
