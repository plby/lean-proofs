/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.FiveLayerInverse
import ErdosProblems.Erdos360.AffineConnector

/-!
# Affine coherence for the five-layer branch

At support cardinality five the sharp Fourier core has doubling strictly
below `12/5`.  The graph-cell argument in this file uses the matching
integer inequality: every non-affine normalized five-point graph has enough
incident cells to force `12` times the vertex mass below `5` times the
graph-cell mass.
-/

namespace Erdos360

open scoped Pointwise BigOperators

attribute [local instance] Classical.propDecidable

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Every threshold subset of a non-affine normalized five-point graph has
the sharp `12/5` incident-cell lower bound. -/
theorem twelve_card_le_five_card_incident_of_not_affine_five
    (A T : Finset ℕ) (x : ℕ → G)
    (hzero : 0 ∈ A) (hAcard : A.card = 5)
    (hgcd : A.gcd (fun n : ℕ => n) = 1)
    (hTA : T ⊆ A)
    (hnot : ¬ ∃ u v : G, ∀ a ∈ A, x a = a • u + v) :
    12 * T.card ≤ 5 * (incidentGraphPairCells A T x).card := by
  classical
  by_cases hT : T.Nonempty
  · by_cases hTsmall : T.card ≤ 2
    · have hadd : T.card + A.card - 1 ≤ (T + A).card :=
        cauchy_davenport_add_of_linearOrder_isCancelAdd hT
          (Finset.card_pos.mp (by omega))
      have hinc := card_add_le_card_incidentGraphPairCells A T x
      omega
    · let C := A \ T
      have hCcard : C.card = A.card - T.card := by
        simpa [C] using Finset.card_sdiff_of_subset hTA
      have hCA : C ⊆ A := Finset.sdiff_subset
      have hU : A = T ∪ C := by
        ext a
        simp only [Finset.mem_union, Finset.mem_sdiff, C]
        constructor
        · intro ha
          by_cases haT : a ∈ T
          · exact Or.inl haT
          · exact Or.inr ⟨ha, haT⟩
        · rintro (haT | ⟨ha, -⟩)
          · exact hTA haT
          · exact ha
      have hgraph :=
        three_card_sub_three_le_graphPairCells_of_not_affine_normalized
          A x hzero hgcd (by omega) hnot
      have hunion := graphPairCells_union_le_incident_add x hTA hCA hU
      have hsmallC := graphPairCells_card_le_choose_two_add_card C x
      have hcombined : 3 * A.card - 3 ≤
          (incidentGraphPairCells A T x).card +
            (graphPairCells C x).card := by
        omega
      have hTle : T.card ≤ A.card := Finset.card_le_card hTA
      have hCle : C.card ≤ 2 := by omega
      have hCcases : C.card = 0 ∨ C.card = 1 ∨ C.card = 2 := by omega
      rcases hCcases with hC0 | hC1 | hC2
      · have hsmallC' : (graphPairCells C x).card ≤ 0 := by
          simpa [hC0, Nat.choose] using hsmallC
        omega
      · have hsmallC' : (graphPairCells C x).card ≤ 1 := by
          simpa [hC1, Nat.choose] using hsmallC
        omega
      · have hsmallC' : (graphPairCells C x).card ≤ 3 := by
          simpa [hC2, Nat.choose] using hsmallC
        omega
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    simp [hTempty, incidentGraphPairCells]

/-- Layer-cake form of the sharp five-point graph inequality. -/
theorem weighted_graph_bound_of_not_affine_five
    (A : Finset ℕ) (x : ℕ → G) (w : ℕ → ℕ) (M : ℕ)
    (hzero : 0 ∈ A) (hAcard : A.card = 5)
    (hgcd : A.gcd (fun n : ℕ => n) = 1)
    (hmax : ∀ a ∈ A, w a ≤ M)
    (hnot : ¬ ∃ u v : G, ∀ a ∈ A, x a = a • u + v) :
    12 * (∑ a ∈ A, w a) ≤
      5 * ∑ c ∈ graphPairCells A x, graphCellWeight A x w c := by
  have hwLayer := sum_card_filter_lt_eq_sum A w M hmax
  have hsum :
      (∑ t ∈ Finset.range M,
          12 * (A.filter fun a => t < w a).card) ≤
        ∑ t ∈ Finset.range M,
          5 * (incidentGraphPairCells A
            (A.filter fun a => t < w a) x).card := by
    apply Finset.sum_le_sum
    intro t ht
    exact twelve_card_le_five_card_incident_of_not_affine_five A
      (A.filter fun a => t < w a) x hzero hAcard hgcd
        (Finset.filter_subset _ _) hnot
  rw [← Finset.mul_sum, hwLayer] at hsum
  rw [weighted_graph_cells_layerCake A x w M hmax]
  simpa only [Finset.mul_sum] using hsum

/-- Strict product doubling below `12/5` forces the quotient labels of a
common subgroup to be affine on a normalized five-point support. -/
theorem coordinateFiberRepresentative_affine_of_common_cosets_five
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (H : AddSubgroup (ZMod d))
    (hzero : 0 ∈ firstCoordinateSet X)
    (hAcard : (firstCoordinateSet X).card = 5)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hAll : ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a))
    (hsmall : 5 * (X + X).card < 12 * X.card) :
    ∃ u v : ZMod d ⧸ H, ∀ a ∈ firstCoordinateSet X,
      QuotientAddGroup.mk' H (coordinateFiberRepresentative X a) =
        a • u + v := by
  classical
  let A := firstCoordinateSet X
  let x : ℕ → ZMod d ⧸ H := fun a =>
    QuotientAddGroup.mk' H (coordinateFiberRepresentative X a)
  let w : ℕ → ℕ := fun a => (coordinateFiber X a).card
  have hgcdNat : A.gcd (fun n : ℕ => n) = 1 := by
    have hgcd' := hgcd
    rw [Erdos13Additive.nat_int_finset_gcd] at hgcd'
    exact_mod_cast hgcd'
  have hmax : ∀ a ∈ A, w a ≤ X.card := by
    intro a ha
    dsimp only [w]
    rw [card_coordinateFiber]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  by_contra hnot
  have hlower := weighted_graph_bound_of_not_affine_five A x w X.card
    (by simpa [A] using hzero) (by simpa [A] using hAcard)
    hgcdNat hmax hnot
  have hupper :
      (∑ c ∈ graphPairCells A x, graphCellWeight A x w c) ≤
        (X + X).card := by
    simpa [A, x, w] using common_coset_graphCellWeight_le_sumset X H hAll
  have hXcard : X.card = ∑ a ∈ A, w a := by
    simpa [A, w] using card_eq_sum_card_coordinateFiber X
  have hlarge : 12 * X.card ≤ 5 * (X + X).card := by
    rw [hXcard]
    exact hlower.trans (Nat.mul_le_mul_left 5 hupper)
  omega

/-- Lift the five-layer affine quotient label to representatives in
`ZMod d`. -/
theorem affine_commonFiberCosets_of_common_cosets_five
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (H : AddSubgroup (ZMod d))
    (hzero : 0 ∈ firstCoordinateSet X)
    (hAcard : (firstCoordinateSet X).card = 5)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hAll : ∀ a ∈ firstCoordinateSet X,
      ContainedInAddCoset H (coordinateFiber X a))
    (hsmall : 5 * (X + X).card < 12 * X.card) :
    ∃ u v : ZMod d, ∀ a ∈ firstCoordinateSet X,
      ∀ y ∈ coordinateFiber X a, y - (a • u + v) ∈ H := by
  classical
  obtain ⟨ubar, vbar, haff⟩ :=
    coordinateFiberRepresentative_affine_of_common_cosets_five X H
      hzero hAcard hgcd hAll hsmall
  obtain ⟨u, hu⟩ := QuotientAddGroup.mk'_surjective H ubar
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk'_surjective H vbar
  refine ⟨u, v, ?_⟩
  intro a ha y hy
  have hquot : QuotientAddGroup.mk' H y =
      QuotientAddGroup.mk' H (coordinateFiberRepresentative X a) := by
    obtain ⟨r, hr⟩ := hAll a ha
    have hyr := hr (by simpa using hy)
    have hrr := hr (by simpa using
      (coordinateFiberRepresentative_mem (X := X) (a := a) ha))
    rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hyr hrr
    apply (QuotientAddGroup.eq_iff_sub_mem).2
    have hdiff := H.sub_mem hyr hrr
    convert hdiff using 1 <;> simp [vadd_eq_add]
  apply (QuotientAddGroup.eq_iff_sub_mem).1
  calc
    QuotientAddGroup.mk' H y =
        QuotientAddGroup.mk' H (coordinateFiberRepresentative X a) := hquot
    _ = a • ubar + vbar := haff a ha
    _ = QuotientAddGroup.mk' H (a • u + v) := by
      rw [← hu, ← hv]
      simp

/-- Full controlled affine-coset package for the normalized five-layer
cyclic inverse branch. -/
theorem exists_common_dense_coset_with_mass_bound_and_affine_labels_five
    {d : ℕ} [NeZero d] (X : Finset (ℕ × ZMod d))
    (hA : (firstCoordinateSet X).Nonempty)
    (hzero : 0 ∈ firstCoordinateSet X)
    (hAcard : (firstCoordinateSet X).card = 5)
    (hgcd : (firstCoordinateSet X).gcd (fun n => (n : ℤ)) = 1)
    (hsmall : 5 * (X + X).card < 12 * X.card) :
    ∃ base ∈ firstCoordinateSet X, ∃ H : AddSubgroup (ZMod d),
      ∃ u v : ZMod d,
        ContainedInAddCoset H (coordinateFiber X base) ∧
        2 * Nat.card H < 3 * (coordinateFiber X base).card ∧
        (∀ a ∈ firstCoordinateSet X,
          (coordinateFiber X a).card ≤ (coordinateFiber X base).card) ∧
        (∀ a ∈ firstCoordinateSet X,
          ContainedInAddCoset H (coordinateFiber X a)) ∧
        (firstCoordinateSet X).card * Nat.card H ≤
          4 * ((X + X).card - X.card) ∧
        (∀ a ∈ firstCoordinateSet X, ∀ y ∈ coordinateFiber X a,
          y - (a • u + v) ∈ H) := by
  obtain ⟨base, hbase, H, hbaseCos, hHdense, hbaseMax, hAll, hmass⟩ :=
    exists_common_dense_coset_with_mass_bound_five X hA hzero hAcard
      hgcd hsmall
  obtain ⟨u, v, haff⟩ := affine_commonFiberCosets_of_common_cosets_five
    X H hzero hAcard hgcd hAll hsmall
  exact ⟨base, hbase, H, u, v, hbaseCos, hHdense, hbaseMax, hAll,
    hmass, haff⟩

end Erdos360

#print axioms Erdos360.weighted_graph_bound_of_not_affine_five
#print axioms Erdos360.coordinateFiberRepresentative_affine_of_common_cosets_five
#print axioms Erdos360.exists_common_dense_coset_with_mass_bound_and_affine_labels_five
