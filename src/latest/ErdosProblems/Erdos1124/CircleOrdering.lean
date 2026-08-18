/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos1124.OneDimensionalDiscrepancy
import ErdosProblems.Erdos1124.ProductGrid

/-!
# Ordering finite subsets of the circle

This file transports the interval discrepancy of a finite subset of
`UnitAddCircle` to the ordered representatives in the fundamental interval
`[0,1)`.  A general interval `[a,b)` is treated as the difference of the two
initial arcs `[0,b)` and `[0,a)`, which costs only a factor of two.
-/

open Finset Function Set

namespace Erdos1124.CircleOrdering

noncomputable section

open ProductGrid

abbrev UnitCircle := OneDimensionalDiscrepancy.Circle

/-- The representatives in `[0,1)` of a finite subset of the unit circle. -/
def representatives (F : Finset UnitCircle) : Finset (Set.Ico (0 : ℝ) (0 + 1)) :=
  F.map (AddCircle.equivIco (1 : ℝ) 0).toEmbedding

@[simp]
theorem card_representatives (F : Finset UnitCircle) :
    (representatives F).card = F.card := by
  simp [representatives]

/-- The increasing enumeration of the representatives of `F`. -/
def orderedRepresentatives (F : Finset UnitCircle) : Fin F.card → ℝ :=
  fun i ↦ ((representatives F).orderIsoOfFin (card_representatives F) i :
    Set.Ico (0 : ℝ) (0 + 1))

theorem strictMono_orderedRepresentatives (F : Finset UnitCircle) :
    StrictMono (orderedRepresentatives F) := by
  exact ((representatives F).orderIsoOfFin (card_representatives F)).strictMono

theorem orderedRepresentatives_mem_Ico (F : Finset UnitCircle) (i : Fin F.card) :
    orderedRepresentatives F i ∈ Set.Ico (0 : ℝ) 1 :=
  by
    simpa [orderedRepresentatives] using
      ((representatives F).orderIsoOfFin (card_representatives F) i).val.property

/-- The ordered representatives, viewed back on the circle, enumerate `F`. -/
def orderedEquiv (F : Finset UnitCircle) : Fin F.card ≃ F where
  toFun i := by
    let y := (representatives F).orderIsoOfFin (card_representatives F) i
    refine ⟨(AddCircle.equivIco (1 : ℝ) 0).symm y.1, ?_⟩
    have hy : y.1 ∈ representatives F := y.2
    rcases Finset.mem_map.mp hy with ⟨z, hz, hzy⟩
    have : z = (AddCircle.equivIco (1 : ℝ) 0).symm y.1 := by
      rw [← hzy]
      exact ((AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply z).symm
    simpa [← this] using hz
  invFun z :=
    ((representatives F).orderIsoOfFin (card_representatives F)).symm
      ⟨AddCircle.equivIco (1 : ℝ) 0 z.1, by
        exact Finset.mem_map.mpr ⟨z.1, z.2, rfl⟩⟩
  left_inv i := by
    apply ((representatives F).orderIsoOfFin (card_representatives F)).injective
    apply Subtype.ext
    simp
  right_inv z := by
    apply Subtype.ext
    simp

@[simp]
theorem equivIco_orderedEquiv (F : Finset UnitCircle) (i : Fin F.card) :
    ((AddCircle.equivIco (1 : ℝ) 0) (orderedEquiv F i) : ℝ) =
      orderedRepresentatives F i := by
  simp [orderedEquiv, orderedRepresentatives]

/-- Existence package for the ordered representative list and its bijection
with the original finite set. -/
theorem exists_ordered_representatives (F : Finset UnitCircle) :
    ∃ (x : Fin F.card → ℝ) (e : Fin F.card ≃ F),
      StrictMono x ∧
      (∀ i, x i ∈ Set.Ico (0 : ℝ) 1) ∧
      (∀ i, ((AddCircle.equivIco (1 : ℝ) 0) (e i) : ℝ) = x i) := by
  exact ⟨orderedRepresentatives F, orderedEquiv F,
    strictMono_orderedRepresentatives F, orderedRepresentatives_mem_Ico F,
    equivIco_orderedEquiv F⟩

/-- Filtering the ordered representatives by a real predicate has the same
cardinality as filtering the original circle set by that predicate applied to
the fundamental representative. -/
theorem card_filter_orderedRepresentatives (F : Finset UnitCircle)
    (P : ℝ → Prop) [DecidablePred P] :
    (Finset.univ.filter fun i ↦ P (orderedRepresentatives F i)).card =
      (F.filter fun z ↦ P ((AddCircle.equivIco (1 : ℝ) 0 z :
        Set.Ico (0 : ℝ) (0 + 1)) : ℝ)).card := by
  classical
  apply Finset.card_bij (fun i _ ↦ (orderedEquiv F i : UnitCircle))
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact ⟨(orderedEquiv F i).property, by
      simpa only [equivIco_orderedEquiv] using hi⟩
  · intro i₁ hi₁ i₂ hi₂ h
    exact (orderedEquiv F).injective (Subtype.ext h)
  · intro z hz
    simp only [Finset.mem_filter] at hz
    let i : Fin F.card := (orderedEquiv F).symm ⟨z, hz.1⟩
    have hei : orderedEquiv F i = ⟨z, hz.1⟩ :=
      (orderedEquiv F).apply_symm_apply ⟨z, hz.1⟩
    refine ⟨i, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← equivIco_orderedEquiv F i, hei]
      exact hz.2
    · exact congrArg Subtype.val hei

/-- The cardinality of the part of a finite set lying on a circle arc. -/
noncomputable def arcCount (F : Finset UnitCircle) (a : UnitCircle) (b : ℝ) : ℕ := by
  classical
  exact (F.filter (· ∈ OneDimensionalDiscrepancy.arc a b)).card

/-- Initial intervals of the ordered representatives are exactly initial
arcs of the circle. -/
theorem intervalCount_zero_eq_arc_card (F : Finset UnitCircle) (b : ℝ) :
    ProductGrid.intervalCount (orderedRepresentatives F) 0 b =
      arcCount F 0 b := by
  classical
  rw [ProductGrid.intervalCount]
  calc
    (Finset.univ.filter fun i ↦ orderedRepresentatives F i ∈ Set.Ico 0 b).card =
        (Finset.univ.filter fun i ↦ orderedRepresentatives F i < b).card := by
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico]
      exact and_iff_right (orderedRepresentatives_mem_Ico F i).1
    _ = (F.filter fun z ↦
        ((AddCircle.equivIco (1 : ℝ) 0 z : Set.Ico (0 : ℝ) (0 + 1)) : ℝ) < b).card :=
      card_filter_orderedRepresentatives F (fun t ↦ t < b)
    _ = arcCount F 0 b := by
      rw [arcCount]
      congr 1
      ext z
      simp [OneDimensionalDiscrepancy.arc]

theorem arcCount_div_card (F : Finset UnitCircle) (a : UnitCircle) (b : ℝ) :
    (arcCount F a b : ℝ) / F.card =
      OneDimensionalDiscrepancy.arcMass F a b := by
  classical
  simp [arcCount, OneDimensionalDiscrepancy.arcMass]

/-- Every particular arc error is bounded by the supremum defining circle
interval discrepancy. -/
theorem abs_arcMass_sub_le_intervalDiscrepancy {F : Finset UnitCircle}
    (hF : F.Nonempty) (a : UnitCircle) {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    |OneDimensionalDiscrepancy.arcMass F a b - b| ≤
      OneDimensionalDiscrepancy.intervalDiscrepancy F := by
  rw [OneDimensionalDiscrepancy.intervalDiscrepancy]
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro r ⟨c, ℓ, hℓ, rfl⟩
    rw [abs_le]
    constructor
    · linarith [OneDimensionalDiscrepancy.arcMass_nonneg F c ℓ, hℓ.2]
    · linarith [OneDimensionalDiscrepancy.arcMass_le_one hF c ℓ, hℓ.1]
  · exact ⟨a, b, hb, rfl⟩

/-- An interval count is the difference of its two initial-interval counts. -/
theorem intervalCount_eq_prefix_sub (F : Finset UnitCircle)
    {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) :
    ProductGrid.intervalCount (orderedRepresentatives F) a b =
      ProductGrid.intervalCount (orderedRepresentatives F) 0 b -
        ProductGrid.intervalCount (orderedRepresentatives F) 0 a := by
  classical
  let Sa := Finset.univ.filter fun i : Fin F.card ↦ orderedRepresentatives F i < a
  let Sb := Finset.univ.filter fun i : Fin F.card ↦ orderedRepresentatives F i < b
  have hSaSb : Sa ⊆ Sb := by
    intro i hi
    simp only [Sa, Sb, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.trans_le hab
  have hint :
      Finset.univ.filter (fun i : Fin F.card ↦
        orderedRepresentatives F i ∈ Set.Ico a b) = Sb \ Sa := by
    ext i
    simp only [Sa, Sb, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff, Set.mem_Ico]
    constructor
    · rintro ⟨hai, hib⟩
      exact ⟨hib, not_lt_of_ge hai⟩
    · rintro ⟨hib, hnia⟩
      exact ⟨le_of_not_gt hnia, hib⟩
  rw [ProductGrid.intervalCount, hint, Finset.card_sdiff_of_subset hSaSb]
  congr 1
  · rw [ProductGrid.intervalCount]
    congr 1
    ext i
    simp only [Sb, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico]
    exact (and_iff_right (orderedRepresentatives_mem_Ico F i).1).symm
  · rw [ProductGrid.intervalCount]
    congr 1
    ext i
    simp only [Sa, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico]
    exact (and_iff_right (orderedRepresentatives_mem_Ico F i).1).symm

/-- The increasing representative list has real interval discrepancy at most
twice the intrinsic circle interval discrepancy. -/
theorem orderedRepresentatives_hasIntervalDiscrepancy {F : Finset UnitCircle}
    (hF : F.Nonempty) :
    ProductGrid.HasIntervalDiscrepancy (orderedRepresentatives F)
      (2 * OneDimensionalDiscrepancy.intervalDiscrepancy F) := by
  intro a b ha hab hb
  have hcardpos : 0 < F.card := hF.card_pos
  have hprefixmono :
      ProductGrid.intervalCount (orderedRepresentatives F) 0 a ≤
        ProductGrid.intervalCount (orderedRepresentatives F) 0 b := by
    rw [ProductGrid.intervalCount, ProductGrid.intervalCount]
    apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Ico] at hi ⊢
    exact ⟨hi.1, hi.2.trans_le hab⟩
  have ha1 : a ≤ 1 := hab.trans hb
  have hprea :
      |(ProductGrid.intervalCount (orderedRepresentatives F) 0 a : ℝ) / F.card - a| ≤
        OneDimensionalDiscrepancy.intervalDiscrepancy F := by
    rw [intervalCount_zero_eq_arc_card, arcCount_div_card]
    exact abs_arcMass_sub_le_intervalDiscrepancy hF 0 ⟨ha, ha1⟩
  have hpreb :
      |(ProductGrid.intervalCount (orderedRepresentatives F) 0 b : ℝ) / F.card - b| ≤
        OneDimensionalDiscrepancy.intervalDiscrepancy F := by
    rw [intervalCount_zero_eq_arc_card, arcCount_div_card]
    exact abs_arcMass_sub_le_intervalDiscrepancy hF 0 ⟨ha.trans hab, hb⟩
  rw [intervalCount_eq_prefix_sub F ha hab]
  rw [Nat.cast_sub hprefixmono]
  have htriangle :
      |((ProductGrid.intervalCount (orderedRepresentatives F) 0 b : ℝ) / F.card - b) -
          ((ProductGrid.intervalCount (orderedRepresentatives F) 0 a : ℝ) / F.card - a)| ≤
        |(ProductGrid.intervalCount (orderedRepresentatives F) 0 b : ℝ) / F.card - b| +
          |(ProductGrid.intervalCount (orderedRepresentatives F) 0 a : ℝ) / F.card - a| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le ((ProductGrid.intervalCount (orderedRepresentatives F) 0 b : ℝ) / F.card - b)
        (-((ProductGrid.intervalCount (orderedRepresentatives F) 0 a : ℝ) / F.card - a))
  have heq :
      ((ProductGrid.intervalCount (orderedRepresentatives F) 0 b : ℝ) -
            ProductGrid.intervalCount (orderedRepresentatives F) 0 a) / F.card - (b - a) =
        ((ProductGrid.intervalCount (orderedRepresentatives F) 0 b : ℝ) / F.card - b) -
          ((ProductGrid.intervalCount (orderedRepresentatives F) 0 a : ℝ) / F.card - a) := by
    field_simp [show (F.card : ℝ) ≠ 0 by exact_mod_cast hcardpos.ne']
    ring
  rw [heq]
  exact htriangle.trans (by linarith)

/-- Combined bridge used by the product-grid argument: a nonempty finite
circle set has an increasing enumeration in `[0,1)`, compatible with the
circle representatives, whose interval discrepancy grows by at most a factor
of two. -/
theorem exists_ordered_representatives_with_discrepancy
    {F : Finset UnitCircle} (hF : F.Nonempty) :
    ∃ (x : Fin F.card → ℝ) (e : Fin F.card ≃ F),
      StrictMono x ∧
      (∀ i, x i ∈ Set.Ico (0 : ℝ) 1) ∧
      (∀ i, ((AddCircle.equivIco (1 : ℝ) 0) (e i) : ℝ) = x i) ∧
      ProductGrid.HasIntervalDiscrepancy x
        (2 * OneDimensionalDiscrepancy.intervalDiscrepancy F) := by
  exact ⟨orderedRepresentatives F, orderedEquiv F,
    strictMono_orderedRepresentatives F, orderedRepresentatives_mem_Ico F,
    equivIco_orderedEquiv F, orderedRepresentatives_hasIntervalDiscrepancy hF⟩

end

end Erdos1124.CircleOrdering
