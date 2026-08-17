/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos651.Definitions
import ErdosProblems.Erdos651.CupsCaps
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Order.Antisymmetrization
import Mathlib.Analysis.Convex.Radon

/-!
# The polytope-cap reduction in Pohoata--Zakharov

This file isolates Proposition 2.1 of Pohoata--Zakharov.  The two geometric
notions in the statement, `PFree` and `PCap`, are stated directly in affine
and convex geometry.  The proof of the proposition is factored through the
finite family of preorders obtained by projecting along the edges of
the polytope.

The finite chain-cover consequence of Dilworth is proved here from Hall's
marriage theorem, first for partial orders and then for preorders via
antisymmetrization.  Thus the geometric certificate below contains only
the projection-separation and planar lifting facts.  The theorem
`pohoata_zakharov_prop_two_one` proves the published cardinal bound,
including its exact exponent.
-/

namespace Erdos651

open Set

noncomputable section

/-! ## Oriented trihedral polyhedra -/

/-- The closed negative orthant in `Point d`. -/
def negativeOrthant (d : ℕ) : Set (Point d) :=
  {x | ∀ i, x i ≤ 0}

theorem convex_negativeOrthant (d : ℕ) : Convex ℝ (negativeOrthant d) := by
  intro x hx y hy a b ha hb hab i
  change a * x i + b * y i ≤ 0
  have hxi := hx i
  have hyi := hy i
  nlinarith

/-- An oriented nondegenerate intersection of three affine halfspaces.
The affine equivalence is the simultaneous coordinate map of the three
normalized affine functionals.  Thus its carrier is literally
`φ₀ ≤ 0 ∩ φ₁ ≤ 0 ∩ φ₂ ≤ 0`, and affine independence of the
three bounding planes is built into the equivalence rather than postulated
by a determinant side condition. -/
structure OrientedTrihedral where
  normalization : Point 3 ≃ᵃ[ℝ] Point 3

namespace OrientedTrihedral

/-- The `i`th normalized oriented affine functional. -/
def functional (T : OrientedTrihedral) (i : Fin 3) (x : Point 3) : ℝ :=
  T.normalization x i

/-- The actual three-halfspace polyhedron. -/
def carrier (T : OrientedTrihedral) : Set (Point 3) :=
  T.normalization ⁻¹' negativeOrthant 3

theorem mem_carrier_iff (T : OrientedTrihedral) (x : Point 3) :
    x ∈ T.carrier ↔ ∀ i, T.functional i x ≤ 0 := by
  rfl

theorem carrier_eq_iInter (T : OrientedTrihedral) :
    T.carrier = ⋂ i : Fin 3, {x | T.functional i x ≤ 0} := by
  ext x
  simp [mem_carrier_iff]

theorem convex_carrier (T : OrientedTrihedral) : Convex ℝ T.carrier := by
  exact (convex_negativeOrthant 3).affine_preimage T.normalization.toAffineMap

end OrientedTrihedral

/-- Delete coordinate zero; this is projection along the first edge of the
standard trihedral cone. -/
def dropCoordinate0 : Point 3 →ₗ[ℝ] Point 2 where
  toFun x := WithLp.toLp 2 ![x 1, x 2]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- Delete coordinate one. -/
def dropCoordinate1 : Point 3 →ₗ[ℝ] Point 2 where
  toFun x := WithLp.toLp 2 ![x 0, x 2]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- Delete coordinate two. -/
def dropCoordinate2 : Point 3 →ₗ[ℝ] Point 2 where
  toFun x := WithLp.toLp 2 ![x 0, x 1]
  map_add' x y := by ext i; fin_cases i <;> simp
  map_smul' c x := by ext i; fin_cases i <;> simp

/-- Canonical projection along one of the three trihedral edges. -/
def dropCoordinate3 (i : Fin 3) : Point 3 →ₗ[ℝ] Point 2 :=
  if i = 0 then dropCoordinate0
  else if i = 1 then dropCoordinate1
  else dropCoordinate2

def insertCoordinate0 (y : Point 2) : Point 3 :=
  WithLp.toLp 2 ![0, y 0, y 1]

def insertCoordinate1 (y : Point 2) : Point 3 :=
  WithLp.toLp 2 ![y 0, 0, y 1]

def insertCoordinate2 (y : Point 2) : Point 3 :=
  WithLp.toLp 2 ![y 0, y 1, 0]

theorem dropCoordinate3_image_negativeOrthant (i : Fin 3) :
    dropCoordinate3 i '' negativeOrthant 3 = negativeOrthant 2 := by
  fin_cases i
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ j
      fin_cases j
      · exact hx 1
      · exact hx 2
    · intro hy
      refine ⟨insertCoordinate0 y, ?_, ?_⟩
      · intro j
        fin_cases j
        · simp [insertCoordinate0]
        · simpa [insertCoordinate0] using hy 0
        · simpa [insertCoordinate0] using hy 1
      · ext j
        fin_cases j <;> simp [dropCoordinate3, dropCoordinate0,
          insertCoordinate0]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ j
      fin_cases j
      · exact hx 0
      · exact hx 2
    · intro hy
      refine ⟨insertCoordinate1 y, ?_, ?_⟩
      · intro j
        fin_cases j
        · simpa [insertCoordinate1] using hy 0
        · simp [insertCoordinate1]
        · simpa [insertCoordinate1] using hy 1
      · ext j
        fin_cases j <;> simp [dropCoordinate3, dropCoordinate1,
          insertCoordinate1]
  · ext y
    constructor
    · rintro ⟨x, hx, rfl⟩ j
      fin_cases j
      · exact hx 0
      · exact hx 1
    · intro hy
      refine ⟨insertCoordinate2 y, ?_, ?_⟩
      · intro j
        fin_cases j
        · simpa [insertCoordinate2] using hy 0
        · simpa [insertCoordinate2] using hy 1
        · simp [insertCoordinate2]
      · ext j
        fin_cases j <;> simp [dropCoordinate3, dropCoordinate2,
          insertCoordinate2]

/-! The one-dimensional feasibility sets used to select a separating edge. -/

/-- Parameters at which coordinate `j` of the line from `x` to `y` lies
in the negative half-line. -/
def coordinateFeasible (x y : Point 3) (j : Fin 3) : Set ℝ :=
  {t | x j + t * (y j - x j) ≤ 0}

theorem convex_coordinateFeasible (x y : Point 3) (j : Fin 3) :
    Convex ℝ (coordinateFeasible x y j) := by
  intro p hp q hq a b ha hb hab
  change x j + (a * p + b * q) * (y j - x j) ≤ 0
  change x j + p * (y j - x j) ≤ 0 at hp
  change x j + q * (y j - x j) ≤ 0 at hq
  calc
    x j + (a * p + b * q) * (y j - x j) =
        (a + b) * x j + (a * p + b * q) * (y j - x j) := by
          rw [hab, one_mul]
    _ =
        a * (x j + p * (y j - x j)) +
          b * (x j + q * (y j - x j)) := by ring
    _ ≤ 0 := add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hp)
      (mul_nonpos_of_nonneg_of_nonpos hb hq)

theorem mem_coordinateFeasible_iff (x y : Point 3) (j : Fin 3) (t : ℝ) :
    t ∈ coordinateFeasible x y j ↔ AffineMap.lineMap x y t j ≤ 0 := by
  simp only [coordinateFeasible, Set.mem_setOf_eq, AffineMap.lineMap_apply_module',
    PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
  constructor <;> intro h <;> linarith

/-- Helly's theorem in dimension one, specialized to the three coordinate
half-lines: if their triple intersection is empty, one coordinate pair
already has empty intersection. -/
theorem coordinateFeasible_empty_pair {x y : Point 3}
    (h : ¬ (⋂ j : Fin 3, coordinateFeasible x y j).Nonempty) :
    ¬ (coordinateFeasible x y 1 ∩ coordinateFeasible x y 2).Nonempty ∨
      ¬ (coordinateFeasible x y 0 ∩ coordinateFeasible x y 2).Nonempty ∨
      ¬ (coordinateFeasible x y 0 ∩ coordinateFeasible x y 1).Nonempty := by
  by_contra hpairs
  push Not at hpairs
  rcases hpairs with ⟨h12, h02, h01⟩
  apply h
  suffices (⋂ j ∈ (Finset.univ : Finset (Fin 3)),
      coordinateFeasible x y j).Nonempty by simpa using this
  apply Convex.helly_theorem' (𝕜 := ℝ) (E := ℝ) (s := Finset.univ)
  · intro i hi
    exact convex_coordinateFeasible x y i
  · intro I hI hcard
    have hcard' : I.card ≤ 2 := by simpa using hcard
    have hmiss : ∃ k : Fin 3, k ∉ I := by
      by_contra hall
      push Not at hall
      have huniv : Finset.univ ⊆ I := by
        intro k hk
        exact hall k
      have hthree : 3 ≤ I.card := by
        simpa using Finset.card_le_card huniv
      omega
    obtain ⟨k, hk⟩ := hmiss
    fin_cases k
    · obtain ⟨t, ht1, ht2⟩ := h12
      refine ⟨t, ?_⟩
      simp only [Set.mem_iInter]
      intro j
      intro hj
      fin_cases j
      · exact (hk hj).elim
      · exact ht1
      · exact ht2
    · obtain ⟨t, ht0, ht2⟩ := h02
      refine ⟨t, ?_⟩
      simp only [Set.mem_iInter]
      intro j
      intro hj
      fin_cases j
      · exact ht0
      · exact (hk hj).elim
      · exact ht2
    · obtain ⟨t, ht0, ht1⟩ := h01
      refine ⟨t, ?_⟩
      simp only [Set.mem_iInter]
      intro j
      intro hj
      fin_cases j
      · exact ht0
      · exact ht1
      · exact (hk hj).elim

theorem coordinateFeasible_mem_congr_of_coordinate_eq
    {x y : Point 3} {j : Fin 3} (hxy : x j = y j) (s t : ℝ) :
    s ∈ coordinateFeasible x y j ↔ t ∈ coordinateFeasible x y j := by
  simp [coordinateFeasible, hxy]

theorem coordinateFeasible_empty_left_or_right_of_constant
    {x y : Point 3} {j k : Fin 3}
    (hj : x j = y j) (hk : x k = y k)
    (hempty : ¬ (coordinateFeasible x y j ∩ coordinateFeasible x y k).Nonempty) :
    ¬ (coordinateFeasible x y j).Nonempty ∨
      ¬ (coordinateFeasible x y k).Nonempty := by
  by_contra h
  push Not at h
  rcases h with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
  apply hempty
  exact ⟨0,
    (coordinateFeasible_mem_congr_of_coordinate_eq hj s 0).mp hs,
    (coordinateFeasible_mem_congr_of_coordinate_eq hk t 0).mp ht⟩

/-- For distinct endpoints, an empty coordinate pair can be chosen so that
at least one of its two coordinates changes along the line.  Equivalently,
the corresponding edge projection has distinct endpoints. -/
theorem coordinateFeasible_empty_changing_pair {x y : Point 3} (hxy : x ≠ y)
    (h : ¬ (⋂ j : Fin 3, coordinateFeasible x y j).Nonempty) :
    (¬ (coordinateFeasible x y 1 ∩ coordinateFeasible x y 2).Nonempty ∧
        (x 1 ≠ y 1 ∨ x 2 ≠ y 2)) ∨
      (¬ (coordinateFeasible x y 0 ∩ coordinateFeasible x y 2).Nonempty ∧
        (x 0 ≠ y 0 ∨ x 2 ≠ y 2)) ∨
      (¬ (coordinateFeasible x y 0 ∩ coordinateFeasible x y 1).Nonempty ∧
        (x 0 ≠ y 0 ∨ x 1 ≠ y 1)) := by
  rcases coordinateFeasible_empty_pair h with h12 | h02 | h01
  · by_cases hchange : x 1 ≠ y 1 ∨ x 2 ≠ y 2
    · exact Or.inl ⟨h12, hchange⟩
    · push Not at hchange
      have h0 : x 0 ≠ y 0 := by
        intro heq
        apply hxy
        ext j
        fin_cases j
        · exact heq
        · exact hchange.1
        · exact hchange.2
      rcases coordinateFeasible_empty_left_or_right_of_constant
          hchange.1 hchange.2 h12 with h1 | h2
      · exact Or.inr (Or.inr ⟨by
          intro hn
          exact h1 ⟨hn.some, hn.some_mem.2⟩, Or.inl h0⟩)
      · exact Or.inr (Or.inl ⟨by
          intro hn
          exact h2 ⟨hn.some, hn.some_mem.2⟩, Or.inl h0⟩)
  · by_cases hchange : x 0 ≠ y 0 ∨ x 2 ≠ y 2
    · exact Or.inr (Or.inl ⟨h02, hchange⟩)
    · push Not at hchange
      have h1 : x 1 ≠ y 1 := by
        intro heq
        apply hxy
        ext j
        fin_cases j
        · exact hchange.1
        · exact heq
        · exact hchange.2
      rcases coordinateFeasible_empty_left_or_right_of_constant
          hchange.1 hchange.2 h02 with h0 | h2
      · exact Or.inr (Or.inr ⟨by
          intro hn
          exact h0 ⟨hn.some, hn.some_mem.1⟩, Or.inr h1⟩)
      · exact Or.inl ⟨by
          intro hn
          exact h2 ⟨hn.some, hn.some_mem.2⟩, Or.inl h1⟩
  · by_cases hchange : x 0 ≠ y 0 ∨ x 1 ≠ y 1
    · exact Or.inr (Or.inr ⟨h01, hchange⟩)
    · push Not at hchange
      have h2 : x 2 ≠ y 2 := by
        intro heq
        apply hxy
        ext j
        fin_cases j
        · exact hchange.1
        · exact hchange.2
        · exact heq
      rcases coordinateFeasible_empty_left_or_right_of_constant
          hchange.1 hchange.2 h01 with h0 | h1
      · exact Or.inr (Or.inl ⟨by
          intro hn
          exact h0 ⟨hn.some, hn.some_mem.1⟩, Or.inr h2⟩)
      · exact Or.inl ⟨by
          intro hn
          exact h1 ⟨hn.some, hn.some_mem.1⟩, Or.inr h2⟩

theorem coordinateFeasible_iInter_empty_of_line_disjoint {x y : Point 3}
    (hdisj : Disjoint
      (↑(affineSpan ℝ ({x, y} : Set (Point 3))) : Set (Point 3))
      (negativeOrthant 3)) :
    ¬ (⋂ j : Fin 3, coordinateFeasible x y j).Nonempty := by
  rintro ⟨t, ht⟩
  have hzneg : AffineMap.lineMap x y t ∈ negativeOrthant 3 := by
    intro j
    exact (mem_coordinateFeasible_iff x y j t).mp (Set.mem_iInter.mp ht j)
  exact Set.disjoint_left.mp hdisj
    (AffineMap.lineMap_mem_affineSpan_pair t x y) hzneg

/-- A line missing the standard trihedral cone has one of the three edge
projections with distinct projected endpoints and projected line missing
the planar negative orthant. -/
theorem exists_dropCoordinate3_separating {x y : Point 3} (hxy : x ≠ y)
    (hdisj : Disjoint
      (↑(affineSpan ℝ ({x, y} : Set (Point 3))) : Set (Point 3))
      (negativeOrthant 3)) :
    ∃ i : Fin 3,
      dropCoordinate3 i x ≠ dropCoordinate3 i y ∧
        Disjoint
          (↑(affineSpan ℝ
            ({dropCoordinate3 i x, dropCoordinate3 i y} : Set (Point 2))) : Set (Point 2))
          (negativeOrthant 2) := by
  have hall := coordinateFeasible_iInter_empty_of_line_disjoint hdisj
  rcases coordinateFeasible_empty_changing_pair hxy hall with
      ⟨h12, hchange⟩ | ⟨h02, hchange⟩ | ⟨h01, hchange⟩
  · refine ⟨0, ?_, ?_⟩
    · intro heq
      rcases hchange with h1 | h2
      · apply h1
        have := congrArg (fun z : Point 2 => z 0) heq
        simpa [dropCoordinate3, dropCoordinate0] using this
      · apply h2
        have := congrArg (fun z : Point 2 => z 1) heq
        simpa [dropCoordinate3, dropCoordinate0] using this
    · rw [Set.disjoint_left]
      intro z hzline hzneg
      change z ∈ affineSpan ℝ
        ({dropCoordinate3 0 x, dropCoordinate3 0 y} : Set (Point 2)) at hzline
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hzline
      obtain ⟨t, rfl⟩ := hzline
      apply h12
      refine ⟨t, ?_, ?_⟩
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate0,
          AffineMap.lineMap_apply_module'] using hzneg 0
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate0,
          AffineMap.lineMap_apply_module'] using hzneg 1
  · refine ⟨1, ?_, ?_⟩
    · intro heq
      rcases hchange with h0 | h2
      · apply h0
        have := congrArg (fun z : Point 2 => z 0) heq
        simpa [dropCoordinate3, dropCoordinate1] using this
      · apply h2
        have := congrArg (fun z : Point 2 => z 1) heq
        simpa [dropCoordinate3, dropCoordinate1] using this
    · rw [Set.disjoint_left]
      intro z hzline hzneg
      change z ∈ affineSpan ℝ
        ({dropCoordinate3 1 x, dropCoordinate3 1 y} : Set (Point 2)) at hzline
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hzline
      obtain ⟨t, rfl⟩ := hzline
      apply h02
      refine ⟨t, ?_, ?_⟩
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate1,
          AffineMap.lineMap_apply_module'] using hzneg 0
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate1,
          AffineMap.lineMap_apply_module'] using hzneg 1
  · refine ⟨2, ?_, ?_⟩
    · intro heq
      rcases hchange with h0 | h1
      · apply h0
        have := congrArg (fun z : Point 2 => z 0) heq
        simpa [dropCoordinate3, dropCoordinate2] using this
      · apply h1
        have := congrArg (fun z : Point 2 => z 1) heq
        simpa [dropCoordinate3, dropCoordinate2] using this
    · rw [Set.disjoint_left]
      intro z hzline hzneg
      change z ∈ affineSpan ℝ
        ({dropCoordinate3 2 x, dropCoordinate3 2 y} : Set (Point 2)) at hzline
      rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hzline
      obtain ⟨t, rfl⟩ := hzline
      apply h01
      refine ⟨t, ?_, ?_⟩
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate2,
          AffineMap.lineMap_apply_module'] using hzneg 0
      · rw [mem_coordinateFeasible_iff]
        simpa [dropCoordinate3, dropCoordinate2,
          AffineMap.lineMap_apply_module'] using hzneg 1

/-- Projection along the `i`th edge of an oriented trihedral polyhedron,
obtained by normalizing and then deleting coordinate `i`. -/
def OrientedTrihedral.edgeProjection (T : OrientedTrihedral) (i : Fin 3) :
    Point 3 →ᵃ[ℝ] Point 2 :=
  (dropCoordinate3 i).toAffineMap.comp T.normalization.toAffineMap

theorem OrientedTrihedral.edgeProjection_image_carrier
    (T : OrientedTrihedral) (i : Fin 3) :
    T.edgeProjection i '' T.carrier = negativeOrthant 2 := by
  rw [← dropCoordinate3_image_negativeOrthant i]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨T.normalization x, hx, ?_⟩
    rfl
  · rintro ⟨z, hz, rfl⟩
    refine ⟨T.normalization.symm z, ?_, ?_⟩
    · simpa [OrientedTrihedral.carrier]
    · simp [OrientedTrihedral.edgeProjection]

/-- The affine line through two points. -/
def lineThrough (x y : Point 3) : Set (Point 3) :=
  affineSpan ℝ ({x, y} : Set (Point 3))

theorem OrientedTrihedral.normalized_line_disjoint
    (T : OrientedTrihedral) {x y : Point 3}
    (hdisj : Disjoint (lineThrough x y) T.carrier) :
    Disjoint
      (↑(affineSpan ℝ
        ({T.normalization x, T.normalization y} : Set (Point 3))) : Set (Point 3))
      (negativeOrthant 3) := by
  rw [Set.disjoint_left]
  intro z hzline hzneg
  change z ∈ affineSpan ℝ
    ({T.normalization x, T.normalization y} : Set (Point 3)) at hzline
  rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hzline
  obtain ⟨t, rfl⟩ := hzline
  have hmap : T.normalization (AffineMap.lineMap x y t) =
      AffineMap.lineMap (T.normalization x) (T.normalization y) t := by
    rw [AffineMap.lineMap_apply, AffineMap.lineMap_apply]
    change T.normalization.toAffineMap (t • (y -ᵥ x) +ᵥ x) =
      t • (T.normalization.toAffineMap y -ᵥ T.normalization.toAffineMap x) +ᵥ
        T.normalization.toAffineMap x
    rw [
      T.normalization.toAffineMap.map_vadd,
      T.normalization.toAffineMap.linear.map_smul,
      T.normalization.toAffineMap.linearMap_vsub]
  apply Set.disjoint_left.mp hdisj
  · exact AffineMap.lineMap_mem_affineSpan_pair t x y
  · change T.normalization (AffineMap.lineMap x y t) ∈ negativeOrthant 3
    simpa [hmap]

/-- A finite set is `P`-free when it is outside `P`, and the line through
any two of its distinct points misses `P`.  In the application `P` is the
underlying set of a (possibly unbounded) convex polytope. -/
def PFree (P : Set (Point 3)) (X : Finset (Point 3)) : Prop :=
  Disjoint (↑X : Set (Point 3)) P ∧
    ∀ {x}, x ∈ X → ∀ {y}, y ∈ X → x ≠ y →
      Disjoint (lineThrough x y) P

/-- A `P`-cap is a finite set in convex position for which every one of its
points remains exposed even after the background polytope `P` is added. -/
def PCap (P : Set (Point 3)) (C : Finset (Point 3)) : Prop :=
  InConvexPosition C ∧
    ∀ x ∈ C,
      x ∉ convexHull ℝ (P ∪ (↑(C.erase x) : Set (Point 3)))

/-- The relation used in (2.5): after projection along an edge, `x ≼ y`
means that the image of `x` lies in the convex hull of the projected
polytope together with the image of `y`. -/
def projectionLE (P : Set (Point 3))
    (π : Point 3 →ᵃ[ℝ] Point 2) (x y : Point 3) : Prop :=
  π x ∈ convexHull ℝ (π '' P ∪ {π y})

/-- The projection relation (2.5) is always a preorder.  Transitivity is
the nesting `conv(Q ∪ {y}) ⊆ conv(Q ∪ {z})` whenever
`y ∈ conv(Q ∪ {z})`. -/
theorem projectionLE_isPreorder (P : Set (Point 3))
    (π : Point 3 →ᵃ[ℝ] Point 2) : IsPreorder (Point 3) (projectionLE P π) := by
  let hr : Std.Refl (projectionLE P π) := ⟨by
    intro x
    exact subset_convexHull ℝ _ (Or.inr (Set.mem_singleton _))
    ⟩
  let ht : IsTrans (Point 3) (projectionLE P π) := ⟨by
    intro x y z hxy hyz
    apply convexHull_min ?_ (convex_convexHull ℝ _) hxy
    intro w hw
    rcases hw with hw | rfl
    · exact subset_convexHull ℝ _ (Or.inl hw)
    · exact hyz
    ⟩
  exact @IsPreorder.mk _ _ hr ht

/-- If the projected line through two distinct projected points misses the
projected polyhedron, then the two points are incomparable in the
projection preorder.  This is the geometric implication used after the
edge-separation lemma. -/
theorem projectionLE_incomparable_of_line_disjoint
    (P : Set (Point 3)) (pi : Point 3 →ᵃ[ℝ] Point 2)
    (hconv : Convex ℝ (pi '' P)) (hnonempty : (pi '' P).Nonempty)
    (hne : pi x ≠ pi y)
    (hdisj : Disjoint (↑(affineSpan ℝ ({pi x, pi y} : Set (Point 2))) : Set (Point 2))
      (pi '' P)) :
    ¬ projectionLE P pi x y ∧ ¬ projectionLE P pi y x := by
  constructor
  · intro hrel
    change pi x ∈ convexHull ℝ (pi '' P ∪ {pi y}) at hrel
    rw [hconv.convexHull_union (convex_singleton (pi y)) hnonempty
      (Set.singleton_nonempty (pi y))] at hrel
    rw [mem_convexJoin] at hrel
    obtain ⟨q, hq, z, hz, hseg⟩ := hrel
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hqline : q ∈
        (↑(affineSpan ℝ ({pi x, pi y} : Set (Point 2))) : Set (Point 2)) := by
      rw [Set.pair_comm]
      exact ((mem_segment_iff_wbtw).mp hseg).left_mem_affineSpan_of_right_ne hne.symm
    exact Set.disjoint_left.mp hdisj hqline hq
  · intro hrel
    change pi y ∈ convexHull ℝ (pi '' P ∪ {pi x}) at hrel
    rw [hconv.convexHull_union (convex_singleton (pi x)) hnonempty
      (Set.singleton_nonempty (pi x))] at hrel
    rw [mem_convexJoin] at hrel
    obtain ⟨q, hq, z, hz, hseg⟩ := hrel
    rw [Set.mem_singleton_iff] at hz
    subst z
    have hqline : q ∈
        (↑(affineSpan ℝ ({pi x, pi y} : Set (Point 2))) : Set (Point 2)) := by
      exact ((mem_segment_iff_wbtw).mp hseg).left_mem_affineSpan_of_right_ne hne
    exact Set.disjoint_left.mp hdisj hqline hq

/-- The three canonical edge projections of an oriented trihedral cone
separate every line disjoint from the cone. -/
theorem OrientedTrihedral.edgeProjection_separates
    (T : OrientedTrihedral) {x y : Point 3} (hxy : x ≠ y)
    (hdisj : Disjoint (lineThrough x y) T.carrier) :
    ∃ i : Fin 3,
      ¬ projectionLE T.carrier (T.edgeProjection i) x y ∧
        ¬ projectionLE T.carrier (T.edgeProjection i) y x := by
  have hnormxy : T.normalization x ≠ T.normalization y :=
    T.normalization.injective.ne hxy
  obtain ⟨i, hne, hline⟩ := exists_dropCoordinate3_separating hnormxy
    (T.normalized_line_disjoint hdisj)
  refine ⟨i, ?_⟩
  apply projectionLE_incomparable_of_line_disjoint T.carrier (T.edgeProjection i)
  · rw [T.edgeProjection_image_carrier]
    exact convex_negativeOrthant 2
  · rw [T.edgeProjection_image_carrier]
    exact ⟨0, fun _ => le_rfl⟩
  · exact hne
  · rw [T.edgeProjection_image_carrier]
    simpa [OrientedTrihedral.edgeProjection] using hline

theorem OrientedTrihedral.projectionOrders_separated
    (T : OrientedTrihedral) {X : Finset (Point 3)} (hfree : PFree T.carrier X)
    {x y : ↑X} (hxy : x ≠ y) :
    ∃ i : Fin 3,
      ¬ projectionLE T.carrier (T.edgeProjection i) x.1 y.1 ∧
        ¬ projectionLE T.carrier (T.edgeProjection i) y.1 x.1 := by
  apply T.edgeProjection_separates (fun h => hxy (Subtype.ext h))
  exact hfree.2 x.2 y.2 (fun h => hxy (Subtype.ext h))

/-- The three canonical edge projections in a coordinate frame chosen
generically for the finite set `X`.  The background remains the negative
orthant, while the two retained coordinates are injective on `X` and no
three projected points have an equal consecutive secant slope. -/
structure OrientedTrihedral.GenericProjectionFamily
    (T : OrientedTrihedral) (X : Finset (Point 3)) where
  projection : Fin 3 → Point 3 →ᵃ[ℝ] Point 2
  image_carrier : ∀ i, projection i '' T.carrier = negativeOrthant 2
  separated : PFree T.carrier X → ∀ {x y : ↑X}, x ≠ y →
    ∃ i, ¬ projectionLE T.carrier (projection i) x.1 y.1 ∧
      ¬ projectionLE T.carrier (projection i) y.1 x.1
  planeX_ne : ∀ i {x y : Point 3}, x ∈ X → y ∈ X → x ≠ y →
    planeX (projection i x) ≠ planeX (projection i y)
  planeY_ne : ∀ i {x y : Point 3}, x ∈ X → y ∈ X → x ≠ y →
    planeY (projection i x) ≠ planeY (projection i y)
  slope_ne : ∀ i {x y z : Point 3},
    x ∈ X → y ∈ X → z ∈ X →
    x ≠ y → y ≠ z → x ≠ z →
    secantSlope (projection i x) (projection i y) ≠
      secantSlope (projection i y) (projection i z)

/-! ## The planar negative-orthant geometry -/

/-- The numerator of the vertical intercept of the oriented line `pq`.
When `p.x < q.x`, it has the same sign as that intercept. -/
def interceptNumerator (p q : Point 2) : ℝ :=
  planeY p * planeX q - planeY q * planeX p

/-- A convex combination of a point of the negative orthant and `p` belongs
to `conv(Q₂ ∪ {p})`.  This elementary form is used to extract the strict
intercept inequalities forced by projection-antichainness. -/
theorem negativeOrthant_lineMap_mem_convexHull
    {r p : Point 2} (hr : r ∈ negativeOrthant 2) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap r p t ∈
      convexHull ℝ (negativeOrthant 2 ∪ {p}) := by
  apply (convex_convexHull ℝ _).lineMap_mem
  · exact subset_convexHull ℝ _ (Or.inl hr)
  · exact subset_convexHull ℝ _ (Or.inr (Set.mem_singleton p))
  · exact ht

/-- A convenient coordinatewise sufficient condition for membership in
`conv(Q₂ ∪ {q})`. -/
theorem mem_convexHull_negativeOrthant_union_singleton_of_scaled_le
    {p q : Point 2} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1)
    (hle : ∀ i, p i ≤ t * q i) :
    p ∈ convexHull ℝ (negativeOrthant 2 ∪ {q}) := by
  let r : Point 2 := (1 - t)⁻¹ • (p - t • q)
  have hr : r ∈ negativeOrthant 2 := by
    intro i
    change (1 - t)⁻¹ * (p i - t * q i) ≤ 0
    exact mul_nonpos_of_nonneg_of_nonpos
      (inv_nonneg.mpr (sub_nonneg.mpr ht1.le)) (sub_nonpos.mpr (hle i))
  have hline : AffineMap.lineMap r q t = p := by
    simp only [AffineMap.lineMap_apply_module]
    have hne : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
    dsimp [r]
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    module
  rw [← hline]
  exact negativeOrthant_lineMap_mem_convexHull hr ⟨ht0, ht1.le⟩

/-- Strictly southwest points belong to the cone hull of the northeast
point.  This is the only monotonicity property of the projection preorder
needed to order an antichain from left to right. -/
theorem mem_convexHull_negativeOrthant_of_both_lt {p q : Point 2}
    (hx : planeX p < planeX q) (hy : planeY p < planeY q) :
    p ∈ convexHull ℝ (negativeOrthant 2 ∪ {q}) := by
  by_cases hqx : planeX q ≤ 0
  · by_cases hqy : planeY q ≤ 0
    · apply subset_convexHull ℝ _
      left
      intro i
      fin_cases i
      · exact hx.le.trans hqx
      · exact hy.le.trans hqy
    · have hqy' : 0 < planeY q := lt_of_not_ge hqy
      by_cases hpy : planeY p ≤ 0
      · apply subset_convexHull ℝ _
        left
        intro i
        fin_cases i
        · exact hx.le.trans hqx
        · exact hpy
      · have hpy' : 0 < planeY p := lt_of_not_ge hpy
        let t := planeY p / planeY q
        apply mem_convexHull_negativeOrthant_union_singleton_of_scaled_le
            (t := t)
        · exact div_nonneg hpy'.le hqy'.le
        · exact (div_lt_one hqy').mpr hy
        · intro i
          fin_cases i
          · have ht1 : t ≤ 1 := ((div_lt_one hqy').mpr hy).le
            change planeX p ≤ t * planeX q
            exact hx.le.trans (le_mul_of_le_one_left hqx ht1)
          · dsimp [t]
            field_simp
            simp [planeY]
  · have hqx' : 0 < planeX q := lt_of_not_ge hqx
    by_cases hqy : planeY q ≤ 0
    · by_cases hpx : planeX p ≤ 0
      · apply subset_convexHull ℝ _
        left
        intro i
        fin_cases i
        · exact hpx
        · exact hy.le.trans hqy
      · have hpx' : 0 < planeX p := lt_of_not_ge hpx
        let t := planeX p / planeX q
        apply mem_convexHull_negativeOrthant_union_singleton_of_scaled_le
            (t := t)
        · exact div_nonneg hpx'.le hqx'.le
        · exact (div_lt_one hqx').mpr hx
        · intro i
          fin_cases i
          · dsimp [t]
            field_simp
            simp [planeX]
          · have ht1 : t ≤ 1 := ((div_lt_one hqx').mpr hx).le
            change planeY p ≤ t * planeY q
            exact hy.le.trans (le_mul_of_le_one_left hqy ht1)
    · have hqy' : 0 < planeY q := lt_of_not_ge hqy
      by_cases hpy : planeY p ≤ 0
      · by_cases hpx : planeX p ≤ 0
        · apply subset_convexHull ℝ _
          left
          intro i
          fin_cases i
          · exact hpx
          · exact hpy
        · have hpx' : 0 < planeX p := lt_of_not_ge hpx
          let t := planeX p / planeX q
          apply mem_convexHull_negativeOrthant_union_singleton_of_scaled_le
              (t := t)
          · exact div_nonneg hpx'.le hqx'.le
          · exact (div_lt_one hqx').mpr hx
          · intro i
            fin_cases i
            · dsimp [t]
              field_simp
              simp [planeX]
            · exact hpy.trans (mul_pos
                (div_pos hpx' hqx') hqy').le
      · have hpy' : 0 < planeY p := lt_of_not_ge hpy
        let u := planeX p / planeX q
        let v := planeY p / planeY q
        let t := (max u v + 1) / 2
        have hv0 : 0 ≤ v := div_nonneg hpy'.le hqy'.le
        have hu1 : u < 1 := (div_lt_one hqx').mpr hx
        have hv1 : v < 1 := (div_lt_one hqy').mpr hy
        have hmax0 : 0 ≤ max u v := le_max_of_le_right hv0
        have hmax1 : max u v < 1 := max_lt hu1 hv1
        have ht0 : 0 ≤ t := by dsimp [t]; linarith
        have ht1 : t < 1 := by dsimp [t]; linarith
        apply mem_convexHull_negativeOrthant_union_singleton_of_scaled_le ht0 ht1
        intro i
        fin_cases i
        · have hut : u ≤ t := by
            have := le_max_left u v
            dsimp [t]
            linarith
          change planeX p ≤ t * planeX q
          exact (div_le_iff₀ hqx').mp hut
        · have hvt : v ≤ t := by
            have := le_max_right u v
            dsimp [t]
            linarith
          change planeY p ≤ t * planeY q
          exact (div_le_iff₀ hqy').mp hvt

theorem not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton
    {p q : Point 2}
    (h : q ∉ convexHull ℝ (negativeOrthant 2 ∪ {p})) :
    q ∉ negativeOrthant 2 := by
  intro hq
  exact h (subset_convexHull ℝ _ (Or.inl hq))

/-- If the right endpoint has nonpositive first coordinate, failure of the
projection relation forces the line intercept to be strictly positive. -/
theorem interceptNumerator_pos_of_right_nonpos
    {p q : Point 2} (hx : planeX p < planeX q)
    (hy : planeY q < planeY p) (hqx : planeX q ≤ 0)
    (hnot : q ∉ convexHull ℝ (negativeOrthant 2 ∪ {p})) :
    0 < interceptNumerator p q := by
  by_contra hpos
  have hnum : interceptNumerator p q ≤ 0 := le_of_not_gt hpos
  have hqout := not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton hnot
  have hqy : 0 < planeY q := by
    by_contra h
    apply hqout
    intro i
    fin_cases i
    · exact hqx
    · simpa [planeY] using le_of_not_gt h
  have hpy : 0 < planeY p := hqy.trans hy
  let t : ℝ := planeY q / planeY p
  have ht0 : 0 ≤ t := div_nonneg hqy.le hpy.le
  have ht1 : t < 1 := (div_lt_one hpy).mpr hy
  let r : Point 2 := WithLp.toLp 2
    ![(planeX q - t * planeX p) / (1 - t), 0]
  have hr : r ∈ negativeOrthant 2 := by
    intro i
    fin_cases i
    · change (planeX q - t * planeX p) / (1 - t) ≤ 0
      have hden : 0 < 1 - t := sub_pos.mpr ht1
      rw [div_nonpos_iff]
      right
      refine ⟨?_, hden.le⟩
      dsimp [t, interceptNumerator] at hnum ⊢
      rw [sub_nonpos]
      rw [div_mul_eq_mul_div, le_div_iff₀ hpy]
      nlinarith
    · simp [r]
  have hline : AffineMap.lineMap r p t = q := by
    apply PiLp.ext
    intro i
    fin_cases i
    · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply,
        PiLp.smul_apply, PiLp.sub_apply]
      change t * (planeX p -
          (planeX q - t * planeX p) / (1 - t)) +
          (planeX q - t * planeX p) / (1 - t) = planeX q
      have hden : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
      field_simp
      ring
    · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply,
        PiLp.smul_apply, PiLp.sub_apply]
      change t * (planeY p - 0) + 0 = planeY q
      dsimp [t]
      field_simp
      ring
  apply hnot
  rw [← hline]
  exact negativeOrthant_lineMap_mem_convexHull hr ⟨ht0, ht1.le⟩

/-- The symmetric strict-intercept lemma when the left endpoint has
nonnegative first coordinate. -/
theorem interceptNumerator_pos_of_left_nonneg
    {p q : Point 2} (hx : planeX p < planeX q)
    (hy : planeY q < planeY p) (hpx : 0 ≤ planeX p)
    (hnot : p ∉ convexHull ℝ (negativeOrthant 2 ∪ {q})) :
    0 < interceptNumerator p q := by
  by_cases hpx0 : planeX p = 0
  · have hqx : 0 < planeX q := by linarith
    have hpout :=
      not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton hnot
    have hpy : 0 < planeY p := by
      by_contra h
      apply hpout
      intro i
      fin_cases i
      · change planeX p ≤ 0
        exact hpx0.le
      · simpa [planeY] using le_of_not_gt h
    simp [interceptNumerator, hpx0]
    positivity
  · have hpx' : 0 < planeX p := lt_of_le_of_ne hpx (Ne.symm hpx0)
    have hqx : 0 < planeX q := hpx'.trans hx
    by_contra hpos
    have hnum : interceptNumerator p q ≤ 0 := le_of_not_gt hpos
    let t : ℝ := planeX p / planeX q
    have ht0 : 0 ≤ t := div_nonneg hpx'.le hqx.le
    have ht1 : t < 1 := (div_lt_one hqx).mpr hx
    let r : Point 2 := WithLp.toLp 2
      ![0, (planeY p - t * planeY q) / (1 - t)]
    have hr : r ∈ negativeOrthant 2 := by
      intro i
      fin_cases i
      · simp [r]
      · change (planeY p - t * planeY q) / (1 - t) ≤ 0
        have hden : 0 < 1 - t := sub_pos.mpr ht1
        rw [div_nonpos_iff]
        right
        refine ⟨?_, hden.le⟩
        dsimp [t, interceptNumerator] at hnum ⊢
        rw [sub_nonpos]
        rw [div_mul_eq_mul_div, le_div_iff₀ hqx]
        nlinarith
    have hline : AffineMap.lineMap r q t = p := by
      apply PiLp.ext
      intro i
      fin_cases i
      · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply,
          PiLp.smul_apply, PiLp.sub_apply]
        change t * (planeX q - 0) + 0 = planeX p
        dsimp [t]
        field_simp
        ring
      · simp only [AffineMap.lineMap_apply_module', PiLp.add_apply,
          PiLp.smul_apply, PiLp.sub_apply]
        change t * (planeY q -
            (planeY p - t * planeY q) / (1 - t)) +
            (planeY p - t * planeY q) / (1 - t) = planeY p
        have hden : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1)
        field_simp
        ring
    apply hnot
    rw [← hline]
    exact negativeOrthant_lineMap_mem_convexHull hr ⟨ht0, ht1.le⟩

/-- The positive-normal functional whose level sets have slope `m`. -/
def planeLineValue (m : ℝ) (p : Point 2) : ℝ :=
  planeY p - m * planeX p

def planeLineValueLinear (m : ℝ) : Point 2 →ₗ[ℝ] ℝ where
  toFun := planeLineValue m
  map_add' x y := by simp [planeLineValue, planeX, planeY]; ring
  map_smul' c x := by simp [planeLineValue, planeX, planeY]; ring

theorem convex_planeLineValue_lt (m c : ℝ) :
    Convex ℝ {p : Point 2 | planeLineValue m p < c} := by
  exact (convex_Iio c).linear_preimage (planeLineValueLinear m)

theorem planeLineValue_nonpos_on_negativeOrthant {m : ℝ} (hm : m ≤ 0)
    {p : Point 2} (hp : p ∈ negativeOrthant 2) :
    planeLineValue m p ≤ 0 := by
  have hx := hp 0
  have hy := hp 1
  change planeY p - m * planeX p ≤ 0
  have hmx : 0 ≤ m * planeX p := mul_nonneg_of_nonpos_of_nonpos hm hx
  simpa [planeY] using sub_nonpos.mpr (hy.trans hmx)

/-- Signed turn of the oriented triple `p,q,r`. -/
def planeTurn (p q r : Point 2) : ℝ :=
  (planeX q - planeX p) * (planeY r - planeY p) -
    (planeY q - planeY p) * (planeX r - planeX p)

theorem planeTurn_rotate (p q r : Point 2) :
    planeTurn q r p = planeTurn p q r := by
  simp [planeTurn]
  ring

theorem planeTurn_rotate' (p q r : Point 2) :
    planeTurn r p q = planeTurn p q r := by
  simp [planeTurn]
  ring

theorem planeTurn_swap_right (p q r : Point 2) :
    planeTurn p r q = -planeTurn p q r := by
  simp [planeTurn]
  ring

theorem slope_lt_slope_iff_turn_pos {p q r : Point 2}
    (hpq : planeX p < planeX q) (hqr : planeX q < planeX r) :
    secantSlope p q < secantSlope q r ↔ 0 < planeTurn p q r := by
  simp only [secantSlope]
  rw [div_lt_div_iff₀ (sub_pos.mpr hpq) (sub_pos.mpr hqr)]
  simp only [planeTurn]
  ring_nf
  constructor <;> intro h <;> nlinarith

theorem slope_gt_slope_iff_turn_neg {p q r : Point 2}
    (hpq : planeX p < planeX q) (hqr : planeX q < planeX r) :
    secantSlope q r < secantSlope p q ↔ planeTurn p q r < 0 := by
  simp only [secantSlope]
  rw [div_lt_div_iff₀ (sub_pos.mpr hqr) (sub_pos.mpr hpq)]
  simp only [planeTurn]
  ring_nf
  constructor <;> intro h <;> nlinarith

theorem secantSlope_neg_of_x_lt_y_gt {p q : Point 2}
    (hx : planeX p < planeX q) (hy : planeY q < planeY p) :
    secantSlope p q < 0 := by
  dsimp [secantSlope]
  exact div_neg_of_neg_of_pos (sub_neg.mpr hy) (sub_pos.mpr hx)

theorem planeLineValue_sub_eq_slope {m : ℝ} {p q : Point 2}
    (hx : planeX p < planeX q) :
    planeLineValue m q - planeLineValue m p =
      (planeX q - planeX p) * (secantSlope p q - m) := by
  have hne : planeX q - planeX p ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  simp [planeLineValue, secantSlope]
  field_simp
  ring

theorem planeLineValue_secantSlope {p q : Point 2}
    (hx : planeX p < planeX q) :
    planeLineValue (secantSlope p q) q =
      interceptNumerator p q / (planeX q - planeX p) := by
  have hne : planeX q - planeX p ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  simp [planeLineValue, secantSlope, interceptNumerator]
  field_simp
  ring

theorem secantSlope_long_lt_left_of_turn_neg {p q r : Point 2}
    (hpq : planeX p < planeX q) (hqr : planeX q < planeX r)
    (hturn : planeTurn p q r < 0) :
    secantSlope p r < secantSlope p q := by
  have hpr : planeX p < planeX r := hpq.trans hqr
  simp only [secantSlope]
  rw [div_lt_div_iff₀ (sub_pos.mpr hpr) (sub_pos.mpr hpq)]
  dsimp [planeTurn] at hturn
  nlinarith [mul_pos (sub_pos.mpr hpq) (sub_pos.mpr hqr)]

theorem secantSlope_right_lt_long_of_turn_neg {p q r : Point 2}
    (hpq : planeX p < planeX q) (hqr : planeX q < planeX r)
    (hturn : planeTurn p q r < 0) :
    secantSlope q r < secantSlope p r := by
  have hpr : planeX p < planeX r := hpq.trans hqr
  simp only [secantSlope]
  rw [div_lt_div_iff₀ (sub_pos.mpr hqr) (sub_pos.mpr hpr)]
  dsimp [planeTurn] at hturn
  nlinarith [mul_pos (sub_pos.mpr hpq) (sub_pos.mpr hqr)]

theorem planeTurn_transitive_pos {a b c d : Point 2}
    (hab : planeX a < planeX b) (hbc : planeX b < planeX c)
    (hcd : planeX c < planeX d)
    (habc : 0 < planeTurn a b c) (hbcd : 0 < planeTurn b c d) :
    0 < planeTurn a b d ∧ 0 < planeTurn a c d := by
  simp only [planeTurn] at habc hbcd ⊢
  constructor <;> nlinarith [mul_pos (sub_pos.mpr hbc) habc,
    mul_pos (sub_pos.mpr hab) hbcd, mul_pos (sub_pos.mpr hcd) habc,
    mul_pos (sub_pos.mpr hbc) hbcd]

theorem planeTurn_transitive_neg {a b c d : Point 2}
    (hab : planeX a < planeX b) (hbc : planeX b < planeX c)
    (hcd : planeX c < planeX d)
    (habc : planeTurn a b c < 0) (hbcd : planeTurn b c d < 0) :
    planeTurn a b d < 0 ∧ planeTurn a c d < 0 := by
  simp only [planeTurn] at habc hbcd ⊢
  constructor <;> nlinarith [mul_pos (sub_pos.mpr hbc) (neg_pos.mpr habc),
    mul_pos (sub_pos.mpr hab) (neg_pos.mpr hbcd),
    mul_pos (sub_pos.mpr hcd) (neg_pos.mpr habc),
    mul_pos (sub_pos.mpr hbc) (neg_pos.mpr hbcd)]

theorem adjacent_planeTurn_pos_all (q : ℕ → Point 2) (n : ℕ)
    (hx : ∀ i j, i < j → j < n → planeX (q i) < planeX (q j))
    (hadj : ∀ i, i + 2 < n → 0 < planeTurn (q i) (q (i + 1)) (q (i + 2))) :
    ∀ i j k, i < j → j < k → k < n → 0 < planeTurn (q i) (q j) (q k) := by
  intro i j k hij hjk hkn
  induction k using Nat.strong_induction_on generalizing i j with
  | h k ih =>
      have hk2 : 2 ≤ k := by omega
      have hlast : ∀ a, a < k - 1 → 0 < planeTurn (q a) (q (k - 1)) (q k) := by
        intro a hak
        by_cases ha : a + 1 = k - 1
        · have hak' : a + 2 = k := by omega
          simpa [ha, hak'] using hadj a (by omega)
        · have ha' : a < k - 2 := by omega
          have hm : k - 2 < k - 1 := by omega
          have hmk : k - 1 < k := by omega
          have hold := ih (k - 1) (by omega) a (k - 2) ha' hm (by omega)
          have hadj' : 0 < planeTurn (q (k - 2)) (q (k - 1)) (q k) := by
            have h1 : k - 2 + 1 = k - 1 := by omega
            have h2 : k - 2 + 2 = k := by omega
            simpa [h1, h2] using hadj (k - 2) (by omega)
          exact (planeTurn_transitive_pos
            (hx a (k - 2) ha' (by omega))
            (hx (k - 2) (k - 1) hm (by omega))
            (hx (k - 1) k hmk hkn) hold hadj').2
      by_cases hjlast : j = k - 1
      · subst j
        exact hlast i (by omega)
      · have hj' : j < k - 1 := by omega
        have hold := ih (k - 1) (by omega) i j hij hj' (by omega)
        exact (planeTurn_transitive_pos
          (hx i j hij (by omega))
          (hx j (k - 1) hj' (by omega))
          (hx (k - 1) k (by omega) hkn) hold (hlast j hj')).1

theorem adjacent_planeTurn_neg_all (q : ℕ → Point 2) (n : ℕ)
    (hx : ∀ i j, i < j → j < n → planeX (q i) < planeX (q j))
    (hadj : ∀ i, i + 2 < n → planeTurn (q i) (q (i + 1)) (q (i + 2)) < 0) :
    ∀ i j k, i < j → j < k → k < n → planeTurn (q i) (q j) (q k) < 0 := by
  intro i j k hij hjk hkn
  induction k using Nat.strong_induction_on generalizing i j with
  | h k ih =>
      have hk2 : 2 ≤ k := by omega
      have hlast : ∀ a, a < k - 1 → planeTurn (q a) (q (k - 1)) (q k) < 0 := by
        intro a hak
        by_cases ha : a + 1 = k - 1
        · have hak' : a + 2 = k := by omega
          simpa [ha, hak'] using hadj a (by omega)
        · have ha' : a < k - 2 := by omega
          have hm : k - 2 < k - 1 := by omega
          have hmk : k - 1 < k := by omega
          have hold := ih (k - 1) (by omega) a (k - 2) ha' hm (by omega)
          have hadj' : planeTurn (q (k - 2)) (q (k - 1)) (q k) < 0 := by
            have h1 : k - 2 + 1 = k - 1 := by omega
            have h2 : k - 2 + 2 = k := by omega
            simpa [h1, h2] using hadj (k - 2) (by omega)
          exact (planeTurn_transitive_neg
            (hx a (k - 2) ha' (by omega))
            (hx (k - 2) (k - 1) hm (by omega))
            (hx (k - 1) k hmk hkn) hold hadj').2
      by_cases hjlast : j = k - 1
      · subst j
        exact hlast i (by omega)
      · have hj' : j < k - 1 := by omega
        have hold := ih (k - 1) (by omega) i j hij hj' (by omega)
        exact (planeTurn_transitive_neg
          (hx i j hij (by omega))
          (hx j (k - 1) hj' (by omega))
          (hx (k - 1) k (by omega) hkn) hold (hlast j hj')).1

/-- Every vertex of a strictly concave, southwest-to-northeast antichain
has a supporting line with negative slope and strictly positive intercept.
Equivalently, it is strictly exposed by a linear functional with both
coefficients positive, so adding the whole negative orthant does not destroy
the vertex. -/
theorem exists_negativeSlope_strict_support {n : ℕ} (hn : 2 ≤ n)
    (q : Fin n → Point 2)
    (hx : ∀ {i j}, i < j → planeX (q i) < planeX (q j))
    (hy : ∀ {i j}, i < j → planeY (q j) < planeY (q i))
    (hturn : ∀ {i j k}, i < j → j < k → planeTurn (q i) (q j) (q k) < 0)
    (hanti : ∀ {i j}, i ≠ j →
      q i ∉ convexHull ℝ (negativeOrthant 2 ∪ {q j}))
    (k : Fin n) :
    ∃ m : ℝ, m < 0 ∧ 0 < planeLineValue m (q k) ∧
      ∀ j, j ≠ k → planeLineValue m (q j) < planeLineValue m (q k) := by
  have hn0 : 0 < n := by omega
  have hklt : k.val < n := k.isLt
  by_cases hk0 : k.val = 0
  · let r : Fin n := ⟨1, by omega⟩
    have hkr : k < r := by simpa [Fin.lt_iff_val_lt_val, r, hk0]
    let s := secantSlope (q k) (q r)
    have hs : s < 0 := secantSlope_neg_of_x_lt_y_gt (hx hkr) (hy hkr)
    have hkout : q k ∉ negativeOrthant 2 :=
      not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton
        (hanti (show k ≠ r by exact ne_of_lt hkr))
    have hall (m : ℝ) (hsm : s < m) :
        ∀ j, j ≠ k → planeLineValue m (q j) < planeLineValue m (q k) := by
      intro j hj
      have hkj : k < j := by
        apply Fin.lt_iff_val_lt_val.mpr
        have : j.val ≠ 0 := by
          intro hj0
          apply hj
          apply Fin.ext
          omega
        omega
      have hslope : secantSlope (q k) (q j) < m := by
        by_cases hjr : j = r
        · simpa [hjr, s] using hsm
        · have hrj : r < j := by
            apply Fin.lt_iff_val_lt_val.mpr
            dsimp [r]
            have hjv : j.val ≠ 1 := by
              intro h
              apply hjr
              apply Fin.ext
              simpa [r] using h
            omega
          exact (secantSlope_long_lt_left_of_turn_neg (hx hkr) (hx hrj)
            (hturn hkr hrj)).trans hsm
      have hdiff := planeLineValue_sub_eq_slope (m := m) (hx hkj)
      have hdx : 0 < planeX (q j) - planeX (q k) := sub_pos.mpr (hx hkj)
      nlinarith [mul_neg_of_pos_of_neg hdx (sub_neg.mpr hslope)]
    rcases lt_trichotomy (planeX (q k)) 0 with hkx | hkx | hkx
    · have hky : 0 < planeY (q k) := by
        by_contra h
        apply hkout
        intro i
        fin_cases i
        · exact hkx.le
        · simpa [planeY] using le_of_not_gt h
      let u := max s (planeY (q k) / planeX (q k))
      let m := u / 2
      have hratio : planeY (q k) / planeX (q k) < 0 :=
        div_neg_of_pos_of_neg hky hkx
      have hu : u < 0 := max_lt hs hratio
      have hum : u < m := by dsimp [m]; linarith
      have hsm : s < m := (le_max_left _ _).trans_lt hum
      refine ⟨m, by dsimp [m]; linarith, ?_, hall m hsm⟩
      have hratm : planeY (q k) / planeX (q k) < m :=
        (le_max_right _ _).trans_lt hum
      have := (div_lt_iff_of_neg hkx).mp hratm
      dsimp [planeLineValue]
      nlinarith
    · have hky : 0 < planeY (q k) := by
        by_contra h
        apply hkout
        intro i
        fin_cases i
        · change planeX (q k) ≤ 0
          exact hkx.le
        · change planeY (q k) ≤ 0
          exact le_of_not_gt h
      let m := s / 2
      have hsm : s < m := by dsimp [m]; linarith
      refine ⟨m, by dsimp [m]; linarith, ?_, hall m hsm⟩
      dsimp [planeLineValue]
      rw [hkx, mul_zero, sub_zero]
      exact hky
    · have hnum : 0 < interceptNumerator (q k) (q r) :=
        interceptNumerator_pos_of_left_nonneg (hx hkr) (hy hkr) hkx.le
          (hanti (show k ≠ r by exact ne_of_lt hkr))
      let B := planeLineValue s (q k)
      have hB : 0 < B := by
        have heq : planeLineValue (secantSlope (q k) (q r)) (q k) =
            planeLineValue (secantSlope (q k) (q r)) (q r) := by
          have hdiff := planeLineValue_sub_eq_slope
            (m := secantSlope (q k) (q r)) (hx hkr)
          have hz : planeLineValue (secantSlope (q k) (q r)) (q r) -
              planeLineValue (secantSlope (q k) (q r)) (q k) = 0 := by
            simpa only [sub_self, mul_zero] using hdiff
          exact (sub_eq_zero.mp hz).symm
        rw [show B = planeLineValue (secantSlope (q k) (q r)) (q k) by rfl,
          heq, planeLineValue_secantSlope (hx hkr)]
        exact div_pos hnum (sub_pos.mpr (hx hkr))
      let U := min 0 (s + B / (2 * planeX (q k)))
      let m := (s + U) / 2
      have hden : 0 < 2 * planeX (q k) := mul_pos (by norm_num) hkx
      have hratioB : 0 < B / (2 * planeX (q k)) := div_pos hB hden
      have hsU : s < U := lt_min hs (by
        linarith [hratioB])
      have hmU : m < U := by dsimp [m]; linarith
      have hsm : s < m := by dsimp [m]; linarith
      have hm0 : m < 0 := hmU.trans_le (min_le_left _ _)
      refine ⟨m, hm0, ?_, hall m hsm⟩
      have hmB : m ≤ s + B / (2 * planeX (q k)) :=
        hmU.le.trans (min_le_right _ _)
      have hrewrite : planeLineValue m (q k) =
          B - (m - s) * planeX (q k) := by
        simp [B, planeLineValue]
        ring
      rw [hrewrite]
      have hmsB : m - s ≤ B / (2 * planeX (q k)) := by linarith
      have := (le_div_iff₀ hden).mp hmsB
      nlinarith [mul_pos hB (show (0 : ℝ) < 1 by norm_num)]
  · by_cases hklast : k.val + 1 = n
    · let l : Fin n := ⟨k.val - 1, by omega⟩
      have hlk : l < k := by
        apply Fin.lt_iff_val_lt_val.mpr
        dsimp [l]
        omega
      let s := secantSlope (q l) (q k)
      have hs : s < 0 := secantSlope_neg_of_x_lt_y_gt (hx hlk) (hy hlk)
      have hkout : q k ∉ negativeOrthant 2 :=
        not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton
          (hanti (show k ≠ l by exact ne_of_gt hlk))
      have hall (m : ℝ) (hms : m < s) :
          ∀ j, j ≠ k → planeLineValue m (q j) < planeLineValue m (q k) := by
        intro j hj
        have hjk : j < k := by
          apply Fin.lt_iff_val_lt_val.mpr
          have : j.val ≠ k.val := by
            intro h
            exact hj (Fin.ext h)
          omega
        have hslope : m < secantSlope (q j) (q k) := by
          by_cases hjl : j = l
          · simpa [hjl, s] using hms
          · have hjl' : j < l := by
              apply Fin.lt_iff_val_lt_val.mpr
              dsimp [l]
              have hjv : j.val ≠ k.val - 1 := by
                intro h
                apply hjl
                apply Fin.ext
                simpa [l] using h
              omega
            exact hms.trans (secantSlope_right_lt_long_of_turn_neg
              (hx hjl') (hx hlk) (hturn hjl' hlk))
        have hdiff := planeLineValue_sub_eq_slope (m := m) (hx hjk)
        have hdx : 0 < planeX (q k) - planeX (q j) := sub_pos.mpr (hx hjk)
        nlinarith [mul_pos hdx (sub_pos.mpr hslope)]
      rcases lt_trichotomy (planeX (q k)) 0 with hkx | hkx | hkx
      · have hnum : 0 < interceptNumerator (q l) (q k) :=
          interceptNumerator_pos_of_right_nonpos (hx hlk) (hy hlk) hkx.le
            (hanti (show k ≠ l by exact ne_of_gt hlk))
        let B := planeLineValue s (q k)
        have hB : 0 < B := by
          rw [show B = planeLineValue (secantSlope (q l) (q k)) (q k) by rfl]
          rw [planeLineValue_secantSlope (hx hlk)]
          exact div_pos hnum (sub_pos.mpr (hx hlk))
        let d := min 1 (B / (2 * (-planeX (q k))))
        let m := s - d
        have hden : 0 < 2 * (-planeX (q k)) :=
          mul_pos (by norm_num) (neg_pos.mpr hkx)
        have hratioB : 0 < B / (2 * (-planeX (q k))) := div_pos hB hden
        have hd : 0 < d := by
          dsimp [d]
          exact lt_min (by norm_num) hratioB
        refine ⟨m, by dsimp [m]; linarith, ?_, hall m (by dsimp [m]; linarith)⟩
        have hdB : d ≤ B / (2 * (-planeX (q k))) := min_le_right _ _
        have hrewrite : planeLineValue m (q k) = B + d * planeX (q k) := by
          simp [B, m, planeLineValue]
          ring
        rw [hrewrite]
        have := (le_div_iff₀ hden).mp hdB
        nlinarith
      · have hky : 0 < planeY (q k) := by
          by_contra h
          apply hkout
          intro i
          fin_cases i
          · change planeX (q k) ≤ 0
            exact hkx.le
          · change planeY (q k) ≤ 0
            exact le_of_not_gt h
        let m := s - 1
        refine ⟨m, by dsimp [m]; linarith, ?_, hall m (by dsimp [m]; linarith)⟩
        dsimp [planeLineValue]
        rw [hkx, mul_zero, sub_zero]
        exact hky
      · let u := min s (planeY (q k) / planeX (q k))
        let m := u - 1
        have hums : m < s := (sub_lt_self u (by norm_num)).trans_le (min_le_left _ _)
        have humr : m < planeY (q k) / planeX (q k) :=
          (sub_lt_self u (by norm_num)).trans_le (min_le_right _ _)
        refine ⟨m, hums.trans hs, ?_, hall m hums⟩
        have := (lt_div_iff₀ hkx).mp humr
        dsimp [planeLineValue]
        nlinarith
    · let l : Fin n := ⟨k.val - 1, by omega⟩
      let r : Fin n := ⟨k.val + 1, by omega⟩
      have hlk : l < k := by
        apply Fin.lt_iff_val_lt_val.mpr
        dsimp [l]
        omega
      have hkr : k < r := by
        apply Fin.lt_iff_val_lt_val.mpr
        dsimp [r]
        omega
      let sL := secantSlope (q l) (q k)
      let sR := secantSlope (q k) (q r)
      have hsL : sL < 0 := secantSlope_neg_of_x_lt_y_gt (hx hlk) (hy hlk)
      have hsR : sR < sL :=
        (slope_gt_slope_iff_turn_neg (hx hlk) (hx hkr)).2 (hturn hlk hkr)
      have hkout : q k ∉ negativeOrthant 2 :=
        not_mem_negativeOrthant_of_not_mem_convexHull_union_singleton
          (hanti (show k ≠ l by exact ne_of_gt hlk))
      have hleft (m : ℝ) (hm : m < sL) :
          ∀ j, j < k → planeLineValue m (q j) < planeLineValue m (q k) := by
        intro j hjk
        have hslope : sL ≤ secantSlope (q j) (q k) := by
          by_cases hjl : j = l
          · simp [hjl, sL]
          · have hjl' : j < l := by
              apply Fin.lt_iff_val_lt_val.mpr
              dsimp [l]
              have hjv : j.val ≠ k.val - 1 := by
                intro h
                apply hjl
                apply Fin.ext
                simpa [l] using h
              omega
            exact (secantSlope_right_lt_long_of_turn_neg (hx hjl') (hx hlk)
              (hturn hjl' hlk)).le
        have hdiff := planeLineValue_sub_eq_slope (m := m) (hx hjk)
        have hdx : 0 < planeX (q k) - planeX (q j) := sub_pos.mpr (hx hjk)
        nlinarith [mul_pos hdx (sub_pos.mpr (hm.trans_le hslope))]
      have hright (m : ℝ) (hm : sR < m) :
          ∀ j, k < j → planeLineValue m (q j) < planeLineValue m (q k) := by
        intro j hkj
        have hslope : secantSlope (q k) (q j) ≤ sR := by
          by_cases hjr : j = r
          · simp [hjr, sR]
          · have hrj : r < j := by
              apply Fin.lt_iff_val_lt_val.mpr
              dsimp [r]
              have hjv : j.val ≠ k.val + 1 := by
                intro h
                apply hjr
                apply Fin.ext
                simpa [r] using h
              omega
            exact (secantSlope_long_lt_left_of_turn_neg (hx hkr) (hx hrj)
              (hturn hkr hrj)).le
        have hdiff := planeLineValue_sub_eq_slope (m := m) (hx hkj)
        have hdx : 0 < planeX (q j) - planeX (q k) := sub_pos.mpr (hx hkj)
        nlinarith [mul_neg_of_pos_of_neg hdx (sub_neg.mpr (hslope.trans_lt hm))]
      have hall (m : ℝ) (hmL : m < sL) (hmR : sR < m) :
          ∀ j, j ≠ k → planeLineValue m (q j) < planeLineValue m (q k) := by
        intro j hj
        rcases lt_or_gt_of_ne hj with hjk | hkj
        · exact hleft m hmL j hjk
        · exact hright m hmR j hkj
      rcases lt_trichotomy (planeX (q k)) 0 with hkx | hkx | hkx
      · have hnum : 0 < interceptNumerator (q l) (q k) :=
          interceptNumerator_pos_of_right_nonpos (hx hlk) (hy hlk) hkx.le
            (hanti (show k ≠ l by exact ne_of_gt hlk))
        let B := planeLineValue sL (q k)
        have hB : 0 < B := by
          rw [show B = planeLineValue (secantSlope (q l) (q k)) (q k) by rfl]
          rw [planeLineValue_secantSlope (hx hlk)]
          exact div_pos hnum (sub_pos.mpr (hx hlk))
        let d := min ((sL - sR) / 2) (B / (2 * (-planeX (q k))))
        let m := sL - d
        have hden : 0 < 2 * (-planeX (q k)) :=
          mul_pos (by norm_num) (neg_pos.mpr hkx)
        have hratioB : 0 < B / (2 * (-planeX (q k))) := div_pos hB hden
        have hd : 0 < d := by
          dsimp [d]
          exact lt_min (by linarith) hratioB
        have hmR : sR < m := by
          have hdgap := min_le_left ((sL - sR) / 2) (B / (2 * (-planeX (q k))))
          dsimp [m, d]
          linarith
        refine ⟨m, (sub_lt_self sL hd).trans hsL, ?_,
          hall m (sub_lt_self sL hd) hmR⟩
        have hdB := min_le_right ((sL - sR) / 2) (B / (2 * (-planeX (q k))))
        have hrewrite : planeLineValue m (q k) = B + d * planeX (q k) := by
          simp [B, m, planeLineValue]
          ring
        rw [hrewrite]
        have := (le_div_iff₀ hden).mp hdB
        nlinarith
      · have hky : 0 < planeY (q k) := by
          by_contra h
          apply hkout
          intro i
          fin_cases i
          · change planeX (q k) ≤ 0
            exact hkx.le
          · change planeY (q k) ≤ 0
            exact le_of_not_gt h
        let m := (sL + sR) / 2
        have hmL : m < sL := by dsimp [m]; linarith
        have hmR : sR < m := by dsimp [m]; linarith
        refine ⟨m, hmL.trans hsL, ?_, hall m hmL hmR⟩
        dsimp [planeLineValue]
        rw [hkx, mul_zero, sub_zero]
        exact hky
      · have hnum : 0 < interceptNumerator (q k) (q r) :=
          interceptNumerator_pos_of_left_nonneg (hx hkr) (hy hkr) hkx.le
            (hanti (show k ≠ r by exact ne_of_lt hkr))
        let B := planeLineValue sR (q k)
        have hB : 0 < B := by
          have heq : planeLineValue (secantSlope (q k) (q r)) (q k) =
              planeLineValue (secantSlope (q k) (q r)) (q r) := by
            have := planeLineValue_sub_eq_slope (m := secantSlope (q k) (q r))
              (hx hkr)
            have hz : planeLineValue (secantSlope (q k) (q r)) (q r) -
                planeLineValue (secantSlope (q k) (q r)) (q k) = 0 := by
              simpa only [sub_self, mul_zero] using this
            exact (sub_eq_zero.mp hz).symm
          rw [show B = planeLineValue (secantSlope (q k) (q r)) (q k) by rfl,
            heq, planeLineValue_secantSlope (hx hkr)]
          exact div_pos hnum (sub_pos.mpr (hx hkr))
        let d := min ((sL - sR) / 2) (B / (2 * planeX (q k)))
        let m := sR + d
        have hden : 0 < 2 * planeX (q k) := mul_pos (by norm_num) hkx
        have hratioB : 0 < B / (2 * planeX (q k)) := div_pos hB hden
        have hd : 0 < d := by
          dsimp [d]
          exact lt_min (by linarith) hratioB
        have hmL : m < sL := by
          have hdgap := min_le_left ((sL - sR) / 2) (B / (2 * planeX (q k)))
          dsimp [m, d]
          linarith
        refine ⟨m, hmL.trans hsL, ?_, hall m hmL (lt_add_of_pos_right sR hd)⟩
        have hdB := min_le_right ((sL - sR) / 2) (B / (2 * planeX (q k)))
        have hrewrite : planeLineValue m (q k) = B - d * planeX (q k) := by
          simp [B, m, planeLineValue]
          ring
        rw [hrewrite]
        have := (le_div_iff₀ hden).mp hdB
        nlinarith

/-- A finite concave antichain is in relative convex position even after
the negative orthant is adjoined. -/
theorem fin_concaveChain_negativeOrthantCap {n : ℕ} (hn : 2 ≤ n)
    (q : Fin n → Point 2)
    (hx : ∀ {i j}, i < j → planeX (q i) < planeX (q j))
    (hy : ∀ {i j}, i < j → planeY (q j) < planeY (q i))
    (hturn : ∀ {i j k}, i < j → j < k → planeTurn (q i) (q j) (q k) < 0)
    (hanti : ∀ {i j}, i ≠ j →
      q i ∉ convexHull ℝ (negativeOrthant 2 ∪ {q j})) :
    ∀ k : Fin n, q k ∉ convexHull ℝ
      (negativeOrthant 2 ∪
        ↑((Finset.univ.image q).erase (q k)) : Set (Point 2)) := by
  classical
  intro k hkHull
  obtain ⟨m, hm, hkpos, hstrict⟩ :=
    exists_negativeSlope_strict_support hn q hx hy hturn hanti k
  let H : Set (Point 2) := {z | planeLineValue m z < planeLineValue m (q k)}
  have hsub : negativeOrthant 2 ∪
      ↑((Finset.univ.image q).erase (q k)) ⊆ H := by
    intro z hz
    rcases hz with hzQ | hzC
    · exact (planeLineValue_nonpos_on_negativeOrthant hm.le hzQ).trans_lt hkpos
    · obtain ⟨hzneq, hzmem⟩ := Finset.mem_erase.mp hzC
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hzmem
      apply hstrict j
      intro hjk
      apply hzneq
      exact congrArg q hjk
  have : q k ∈ H := convexHull_min hsub (convex_planeLineValue_lt _ _) hkHull
  have hbad : planeLineValue m (q k) < planeLineValue m (q k) := by
    simpa [H] using this
  exact (lt_irrefl _ hbad)

theorem fin_concaveChain_inConvexPosition {n : ℕ} (hn : 2 ≤ n)
    (q : Fin n → Point 2)
    (hx : ∀ {i j}, i < j → planeX (q i) < planeX (q j))
    (hy : ∀ {i j}, i < j → planeY (q j) < planeY (q i))
    (hturn : ∀ {i j k}, i < j → j < k → planeTurn (q i) (q j) (q k) < 0)
    (hanti : ∀ {i j}, i ≠ j →
      q i ∉ convexHull ℝ (negativeOrthant 2 ∪ {q j})) :
    InConvexPosition (Finset.univ.image q) := by
  classical
  have hcap := fin_concaveChain_negativeOrthantCap hn q hx hy hturn hanti
  intro z hzC
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hzC
  intro hk
  apply hcap k
  exact convexHull_mono Set.subset_union_right hk

theorem convex_planeTurn_nonneg (p q : Point 2) :
    Convex ℝ {z : Point 2 | 0 ≤ planeTurn p q z} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  calc
    0 ≤ a * planeTurn p q x + b * planeTurn p q y :=
      add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)
    _ = planeTurn p q (a • x + b • y) := by
      have hb' : b = 1 - a := by linarith
      rw [hb']
      simp only [planeTurn, planeX, planeY, PiLp.add_apply, PiLp.smul_apply]
      ring

/-- A chain whose every ordered triple turns left is in ordinary convex
position.  Endpoints are exposed by the first coordinate; an internal point
is separated by the line through its two neighboring points. -/
theorem fin_convexChain_inConvexPosition {n : ℕ} (hn : 2 ≤ n)
    (q : Fin n → Point 2)
    (hx : ∀ {i j}, i < j → planeX (q i) < planeX (q j))
    (hturn : ∀ {i j k}, i < j → j < k → 0 < planeTurn (q i) (q j) (q k)) :
    InConvexPosition (Finset.univ.image q) := by
  classical
  intro z hzC
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hzC
  by_cases hk0 : k.val = 0
  · let H : Set (Point 2) := {z | planeX (q k) < planeX z}
    have hconv : Convex ℝ H := by
      exact (convex_Ioi (planeX (q k))).linear_preimage
        { toFun := planeX
          map_add' := by intro x y; simp [planeX]
          map_smul' := by intro c x; simp [planeX] }
    intro hkHull
    have hsub : (↑((Finset.univ.image q).erase (q k)) : Set (Point 2)) ⊆ H := by
      intro w hw
      obtain ⟨hwne, hwC⟩ := Finset.mem_erase.mp hw
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hwC
      apply hx
      apply Fin.lt_iff_val_lt_val.mpr
      have : j.val ≠ 0 := by
        intro h
        apply hwne
        congr 1
        apply Fin.ext
        simpa [hk0] using h
      omega
    have := convexHull_min hsub hconv hkHull
    have hbad : planeX (q k) < planeX (q k) := by simpa [H] using this
    exact (lt_irrefl _ hbad)
  · by_cases hklast : k.val + 1 = n
    · let H : Set (Point 2) := {z | planeX z < planeX (q k)}
      have hconv : Convex ℝ H := by
        exact (convex_Iio (planeX (q k))).linear_preimage
          { toFun := planeX
            map_add' := by intro x y; simp [planeX]
            map_smul' := by intro c x; simp [planeX] }
      intro hkHull
      have hsub : (↑((Finset.univ.image q).erase (q k)) : Set (Point 2)) ⊆ H := by
        intro w hw
        obtain ⟨hwne, hwC⟩ := Finset.mem_erase.mp hw
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hwC
        apply hx
        apply Fin.lt_iff_val_lt_val.mpr
        have : j.val ≠ k.val := by
          intro h
          apply hwne
          congr 1
          exact Fin.ext h
        omega
      have := convexHull_min hsub hconv hkHull
      have hbad : planeX (q k) < planeX (q k) := by simpa [H] using this
      exact (lt_irrefl _ hbad)
    · let l : Fin n := ⟨k.val - 1, by omega⟩
      let r : Fin n := ⟨k.val + 1, by omega⟩
      have hlk : l < k := by
        apply Fin.lt_iff_val_lt_val.mpr
        dsimp [l]
        omega
      have hkr : k < r := by
        apply Fin.lt_iff_val_lt_val.mpr
        dsimp [r]
        omega
      intro hkHull
      have hsub : (↑((Finset.univ.image q).erase (q k)) : Set (Point 2)) ⊆
          {z | 0 ≤ planeTurn (q l) (q r) z} := by
        intro w hw
        obtain ⟨hwne, hwC⟩ := Finset.mem_erase.mp hw
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hwC
        rcases lt_trichotomy j k with hjk | hjk | hkj
        · by_cases hjl : j = l
          · subst j
            dsimp [planeTurn]
            nlinarith
          · have hjl' : j < l := by
              apply Fin.lt_iff_val_lt_val.mpr
              dsimp [l]
              have : j.val ≠ k.val - 1 := by
                intro h
                apply hjl
                exact Fin.ext (by simpa [l] using h)
              omega
            change 0 ≤ planeTurn (q l) (q r) (q j)
            rw [planeTurn_rotate]
            exact (hturn hjl' (hlk.trans hkr)).le
        · exact (hwne (congrArg q hjk)).elim
        · by_cases hjr : j = r
          · subst j
            dsimp [planeTurn]
            nlinarith
          · have hrj : r < j := by
              apply Fin.lt_iff_val_lt_val.mpr
              dsimp [r]
              have : j.val ≠ k.val + 1 := by
                intro h
                apply hjr
                exact Fin.ext (by simpa [r] using h)
              omega
            exact (hturn (hlk.trans hkr) hrj).le
      have hmem := convexHull_min hsub (convex_planeTurn_nonneg (q l) (q r)) hkHull
      have hkneg : planeTurn (q l) (q r) (q k) < 0 := by
        rw [planeTurn_swap_right]
        exact neg_neg_of_pos (hturn hlk hkr)
      exact (not_le_of_gt hkneg) hmem

/-- The projected version of the exposed-point part of `PCap`. -/
def ProjectedPCap (P : Set (Point 3))
    (π : Point 3 →ᵃ[ℝ] Point 2) (C : Finset (Point 3)) : Prop :=
  ∀ x ∈ C,
    π x ∉ convexHull ℝ
      (π '' P ∪ π '' (↑(C.erase x) : Set (Point 3)))

/-- Convex position after applying a (not necessarily injective globally)
linear projection. -/
def ProjectedConvexPosition
    (π : Point 3 →ᵃ[ℝ] Point 2) (C : Finset (Point 3)) : Prop :=
  ∀ x ∈ C,
    π x ∉ convexHull ℝ (π '' (↑(C.erase x) : Set (Point 3)))

/-- Convex position in the projected plane always lifts to convex position
upstairs.  No injectivity hypothesis is needed: the displayed projected
extreme-point certificates themselves rule out a collision. -/
theorem ProjectedConvexPosition.inConvexPosition
    {C : Finset (Point 3)} {π : Point 3 →ᵃ[ℝ] Point 2}
    (hC : ProjectedConvexPosition π C) : InConvexPosition C := by
  intro x hxC hxHull
  apply hC x hxC
  rw [← π.image_convexHull]
  exact ⟨x, hxHull, rfl⟩

/-- A projected `P`-cap lifts to an actual `P`-cap. -/
theorem ProjectedPCap.pcap
    {P : Set (Point 3)} {C : Finset (Point 3)}
    {π : Point 3 →ᵃ[ℝ] Point 2} (hC : ProjectedPCap P π C) :
    PCap P C := by
  refine ⟨?_, ?_⟩
  · intro x hxC hxHull
    apply hC x hxC
    apply convexHull_mono (Set.subset_union_right)
    rw [← π.image_convexHull]
    exact ⟨x, hxHull, rfl⟩
  · intro x hxC hxHull
    apply hC x hxC
    rw [← Set.image_union, ← π.image_convexHull]
    exact ⟨x, hxHull, rfl⟩

/-- A coloring by `m` colors whose color classes are chains. -/
def IsChainColoring {α : Type*} (r : α → α → Prop) {m : ℕ}
    (color : α → Fin m) : Prop :=
  ∀ {x y}, color x = color y → r x y ∨ r y x

/-! The finite matching-to-chain part of Dilworth's theorem. -/

structure IncreasingMatching (α : Type*) [PartialOrder α] (m : ℕ) where
  next : α → α ⊕ Fin m
  injective_next : Function.Injective next
  lt_of_next_eq : ∀ {x y}, next x = Sum.inl y → x < y

namespace IncreasingMatching

variable {α : Type*} [Fintype α] [PartialOrder α] {m : ℕ}

private theorem gt_wellFounded : WellFounded (fun y x : α => x < y) := by
  let ht : IsTrans α (fun y x : α => x < y) := ⟨by
    intro a b c hba hcb
    exact hcb.trans hba⟩
  let hi : Std.Irrefl (fun y x : α => x < y) := ⟨by
    intro a
    exact lt_irrefl a⟩
  exact @Finite.wellFounded_of_trans_of_irrefl α _ _ ht hi

/-- The unique forward trace of a point ends at a dummy color. -/
inductive TracesTo (M : IncreasingMatching α m) : α → ℕ → Fin m → Prop
  | stop {x : α} {c : Fin m} (h : M.next x = Sum.inr c) :
      TracesTo M x 0 c
  | step {x y : α} {n : ℕ} {c : Fin m}
      (hxy : M.next x = Sum.inl y) (hrest : TracesTo M y n c) :
      TracesTo M x (n + 1) c

theorem exists_trace (M : IncreasingMatching α m) :
    ∀ x, ∃ n c, TracesTo M x n c := by
  intro x
  let Q : α → Prop := fun x => ∃ n c, TracesTo M x n c
  change Q x
  refine (gt_wellFounded (α := α)).induction x ?_
  intro x ih
  cases hx : M.next x with
  | inl y =>
      obtain ⟨n, c, htrace⟩ := ih y (M.lt_of_next_eq hx)
      exact ⟨n + 1, c, TracesTo.step hx htrace⟩
  | inr c => exact ⟨0, c, TracesTo.stop hx⟩

theorem trace_unique (M : IncreasingMatching α m) {x : α}
    {n n' : ℕ} {c c' : Fin m}
    (h : TracesTo M x n c) (h' : TracesTo M x n' c') :
    n = n' ∧ c = c' := by
  induction h generalizing n' c' with
  | @stop x c hx =>
      cases h' with
      | stop hx' =>
          exact ⟨rfl, Sum.inr.inj (hx.symm.trans hx')⟩
      | step hy _ => exact (Sum.inr_ne_inl (hx.symm.trans hy)).elim
  | step hx hrest ih =>
      cases h' with
      | stop hy => exact (Sum.inl_ne_inr (hx.symm.trans hy)).elim
      | @step _ y' n' c' hy hrest' =>
          have hyy : _ = y' := Sum.inl.inj (hx.symm.trans hy)
          subst y'
          obtain ⟨hn, hc⟩ := ih hrest'
          exact ⟨congrArg (fun k => k + 1) hn, hc⟩

theorem trace_start_unique (M : IncreasingMatching α m) {x y : α}
    {n : ℕ} {c : Fin m} (hx : TracesTo M x n c) (hy : TracesTo M y n c) :
    x = y := by
  induction hx generalizing y with
  | stop hx =>
      cases hy with
      | stop hy => exact M.injective_next (hx.trans hy.symm)
  | step hx hrest ih =>
      cases hy with
      | step hy hrest' =>
          have htail := ih hrest'
          apply M.injective_next
          exact hx.trans <|
            (congrArg (Sum.inl : α → α ⊕ Fin m) htail).trans hy.symm

theorem le_of_traces (M : IncreasingMatching α m) {x y : α}
    {nx ny : ℕ} {c : Fin m} (hx : TracesTo M x nx c) (hy : TracesTo M y ny c)
    (hdepth : nx ≤ ny) : y ≤ x := by
  induction hy generalizing x nx with
  | stop hy =>
      have hnx : nx = 0 := Nat.eq_zero_of_le_zero hdepth
      subst nx
      have hxy := M.trace_start_unique hx (TracesTo.stop hy)
      simpa [hxy]
  | @step y y' ny c hy hrest ih =>
      by_cases heq : nx = ny + 1
      · subst nx
        have hxy := M.trace_start_unique hx (TracesTo.step hy hrest)
        simpa [hxy]
      · have hnx : nx ≤ ny := by omega
        exact (M.lt_of_next_eq hy).le.trans (ih hx hnx)

/-- Distance to the terminal dummy color, together with that color. -/
noncomputable def traceData (M : IncreasingMatching α m) (x : α) : ℕ × Fin m :=
  let h := M.exists_trace x
  (Classical.choose h, Classical.choose (Classical.choose_spec h))

noncomputable def depth (M : IncreasingMatching α m) (x : α) : ℕ :=
  (M.traceData x).1

noncomputable def terminal (M : IncreasingMatching α m) (x : α) : Fin m :=
  (M.traceData x).2

theorem traceData_spec (M : IncreasingMatching α m) (x : α) :
    TracesTo M x (M.depth x) (M.terminal x) := by
  simp only [depth, terminal, traceData]
  exact Classical.choose_spec (Classical.choose_spec (M.exists_trace x))

theorem traceData_eq_inl (M : IncreasingMatching α m) {x y : α}
    (h : M.next x = Sum.inl y) :
    M.traceData x = (M.depth y + 1, M.terminal y) := by
  have htrace : TracesTo M x (M.depth y + 1) (M.terminal y) :=
    TracesTo.step h (M.traceData_spec y)
  obtain ⟨hn, hc⟩ := M.trace_unique (M.traceData_spec x) htrace
  exact Prod.ext hn hc

theorem traceData_eq_inr (M : IncreasingMatching α m) {x : α} {c : Fin m}
    (h : M.next x = Sum.inr c) : M.traceData x = (0, c) := by
  have htrace : TracesTo M x 0 c := TracesTo.stop h
  obtain ⟨hn, hc⟩ := M.trace_unique (M.traceData_spec x) htrace
  exact Prod.ext hn hc

theorem depth_eq_inl (M : IncreasingMatching α m) {x y : α}
    (h : M.next x = Sum.inl y) : M.depth x = M.depth y + 1 := by
  rw [depth, traceData_eq_inl M h]

theorem terminal_eq_inl (M : IncreasingMatching α m) {x y : α}
    (h : M.next x = Sum.inl y) : M.terminal x = M.terminal y := by
  rw [terminal, traceData_eq_inl M h]

theorem depth_eq_inr (M : IncreasingMatching α m) {x : α} {c : Fin m}
    (h : M.next x = Sum.inr c) : M.depth x = 0 := by
  rw [depth, traceData_eq_inr M h]

theorem terminal_eq_inr (M : IncreasingMatching α m) {x : α} {c : Fin m}
    (h : M.next x = Sum.inr c) : M.terminal x = c := by
  rw [terminal, traceData_eq_inr M h]

theorem eq_of_depth_eq_of_terminal_eq (M : IncreasingMatching α m) :
    ∀ x y, M.depth x = M.depth y → M.terminal x = M.terminal y → x = y := by
  intro x y hdepth hterminal
  have hx := M.traceData_spec x
  rw [hdepth, hterminal] at hx
  exact M.trace_start_unique hx (M.traceData_spec y)

theorem le_of_depth_le_of_terminal_eq (M : IncreasingMatching α m) :
    ∀ x y, M.depth x ≤ M.depth y → M.terminal x = M.terminal y → y ≤ x := by
  intro x y hdepth hterminal
  have hx := M.traceData_spec x
  rw [hterminal] at hx
  exact M.le_of_traces hx (M.traceData_spec y) hdepth

theorem terminal_chainColoring (M : IncreasingMatching α m) :
    IsChainColoring (fun x y : α => x ≤ y) M.terminal := by
  intro x y hxy
  rcases le_total (M.depth x) (M.depth y) with h | h
  · exact Or.inr (M.le_of_depth_le_of_terminal_eq x y h hxy)
  · exact Or.inl (M.le_of_depth_le_of_terminal_eq y x h hxy.symm)

end IncreasingMatching

/-- The precise finite consequence of Dilworth used in Proposition 2.1:
if every antichain has at most `m` elements, the poset is the union of `m`
chains. -/
def HasDilworthChainCover {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) : Prop :=
  ∀ m : ℕ, 0 < m →
    (∀ A : Finset α, IsAntichain r (↑A : Set α) → A.card ≤ m) →
      ∃ color : α → Fin m, IsChainColoring r color

/-- The finite chain-cover theorem for partial orders.  The proof is the
standard Hall matching proof of Dilworth: minimal elements of a test set
use the `m` dummy right vertices, while every nonminimal element contributes
its own strict-successor right vertex.  Following the resulting increasing
matching partitions the poset into its terminal-color chains. -/
theorem finite_dilworth_partialOrder {α : Type*} [Fintype α] [DecidableEq α]
    [PartialOrder α] : HasDilworthChainCover (fun x y : α => x ≤ y) := by
  classical
  intro m hm hwidth
  let R : α → α ⊕ Fin m → Prop := fun x z =>
    match z with
    | Sum.inl y => x < y
    | Sum.inr _ => True
  have hHall : ∀ A : Finset α,
      A.card ≤ ({z | ∃ x ∈ A, R x z} : Finset (α ⊕ Fin m)).card := by
    intro A
    by_cases hA : A = ∅
    · simp [hA]
    let minima : Finset α := A.filter fun x => ¬ ∃ y ∈ A, y < x
    have hminAnti : IsAntichain (fun x y : α => x ≤ y)
        (↑minima : Set α) := by
      intro x hx y hy hxy hle
      simp only [minima, Finset.mem_coe, Finset.mem_filter] at hx hy
      apply hy.2
      exact ⟨x, hx.1, lt_of_le_of_ne hle hxy⟩
    have hminCard : minima.card ≤ m := hwidth minima hminAnti
    let rank : ↑minima → Fin m := fun x =>
      ⟨(Fintype.equivFin (↑minima) x).val,
        (Fintype.equivFin (↑minima) x).isLt.trans_le (by simpa using hminCard)⟩
    have hrank : Function.Injective rank := by
      intro x y hxy
      apply (Fintype.equivFin (↑minima)).injective
      apply Fin.ext
      simpa [rank] using congrArg Fin.val hxy
    let f : ↑A → α ⊕ Fin m := fun x =>
      if hx : x.1 ∈ minima then Sum.inr (rank ⟨x.1, hx⟩) else Sum.inl x.1
    have hfmem (x : ↑A) : f x ∈ ({z | ∃ y ∈ A, R y z} : Finset (α ⊕ Fin m)) := by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      by_cases hx : x.1 ∈ minima
      · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hA
        exact ⟨a, ha, by simp [f, hx, R]⟩
      · have hex : ∃ y ∈ A, y < x.1 := by
          simpa [minima, x.2] using hx
        obtain ⟨y, hyA, hyx⟩ := hex
        exact ⟨y, hyA, by simpa [f, hx, R] using hyx⟩
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : x.1 ∈ minima
      · by_cases hy : y.1 ∈ minima
        · have hr : rank ⟨x.1, hx⟩ = rank ⟨y.1, hy⟩ :=
            @Sum.inr.inj α (Fin m) _ _ (by simpa [f, hx, hy] using hxy)
          have hval : x.1 = y.1 :=
            congrArg (fun z : ↑minima => z.1) (hrank hr)
          exact Subtype.ext hval
        · have hbad : (Sum.inr (rank ⟨x.1, hx⟩) : α ⊕ Fin m) = Sum.inl y.1 := by
            simpa [f, hx, hy] using hxy
          exact (Sum.inr_ne_inl hbad).elim
      · by_cases hy : y.1 ∈ minima
        · have hbad : (Sum.inl x.1 : α ⊕ Fin m) = Sum.inr (rank ⟨y.1, hy⟩) := by
            simpa [f, hx, hy] using hxy
          exact (Sum.inl_ne_inr hbad).elim
        · have heq : (Sum.inl x.1 : α ⊕ Fin m) = Sum.inl y.1 := by
            simpa [f, hx, hy] using hxy
          exact Subtype.ext (@Sum.inl.inj α (Fin m) _ _ heq)
    let g : ↑A → ↑({z | ∃ y ∈ A, R y z} : Finset (α ⊕ Fin m)) :=
      fun x => ⟨f x, hfmem x⟩
    have hg : Function.Injective g := fun _ _ h => hf (congrArg Subtype.val h)
    rw [← Fintype.card_coe A,
      ← Fintype.card_coe ({z | ∃ y ∈ A, R y z} : Finset (α ⊕ Fin m))]
    exact Fintype.card_le_of_injective g hg
  obtain ⟨next, hnext, hR⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective R).mp hHall
  let M : IncreasingMatching α m :=
    { next := next
      injective_next := hnext
      lt_of_next_eq := by
        intro x y hxy
        have := hR x
        simpa [R, hxy] using this }
  exact ⟨M.terminal, M.terminal_chainColoring⟩

/-- Dilworth's finite chain-cover consequence for preorders.  Mutual
comparability is quotiented out by `Antisymmetrization`; a representative
order embedding transfers antichains to the original preorder, and the
resulting quotient chain coloring is pulled back. -/
theorem finite_dilworth_preorder {α : Type*} [Fintype α] [DecidableEq α]
    [Preorder α] : HasDilworthChainCover (fun x y : α => x ≤ y) := by
  classical
  intro m hm hwidth
  let β := Antisymmetrization α (fun x y : α => x ≤ y)
  letI : Fintype β := Fintype.ofSurjective
    (toAntisymmetrization (fun x y : α => x ≤ y)) fun q =>
      ⟨ofAntisymmetrization (fun x y : α => x ≤ y) q,
        toAntisymmetrization_ofAntisymmetrization (fun x y : α => x ≤ y) q⟩
  let e : β ↪o α := OrderEmbedding.ofAntisymmetrization α
  have hwidthβ (A : Finset β)
      (hA : IsAntichain (fun x y : β => x ≤ y) (↑A : Set β)) : A.card ≤ m := by
    let B : Finset α := A.map e.toEmbedding
    have hB : IsAntichain (fun x y : α => x ≤ y) (↑B : Set α) := by
      intro x hx y hy hxy hle
      simp only [B, Finset.mem_coe, Finset.mem_map] at hx hy
      obtain ⟨qx, hqx, rfl⟩ := hx
      obtain ⟨qy, hqy, hqyval⟩ := hy
      subst y
      have hqq : qx = qy := hA.eq hqx hqy (e.le_iff_le.mp hle)
      exact hxy (congrArg e hqq)
    have := hwidth B hB
    simpa [B] using this
  obtain ⟨color, hcolor⟩ :=
    finite_dilworth_partialOrder (α := β) m hm hwidthβ
  refine ⟨fun x => color (toAntisymmetrization (fun x y : α => x ≤ y) x), ?_⟩
  intro x y hxy
  rcases hcolor hxy with hle | hge
  · exact Or.inl (toAntisymmetrization_le_toAntisymmetrization_iff.mp hle)
  · exact Or.inr (toAntisymmetrization_le_toAntisymmetrization_iff.mp hge)

/-- Unbundled form, convenient when several preorders live on the same
finite carrier. -/
theorem finite_dilworth_of_isPreorder {α : Type*} [Fintype α] [DecidableEq α]
    (r : α → α → Prop) (hr : IsPreorder α r) : HasDilworthChainCover r := by
  letI : Preorder α :=
    { le := r
      le_refl := hr.refl
      le_trans := hr.trans }
  change HasDilworthChainCover (fun x y : α => x ≤ y)
  exact finite_dilworth_preorder (α := α)

/-- A family of finite preorders, one for every edge direction, with
the two properties used in the multi-order Dilworth argument. -/
structure MultiOrderDilworthData (α ι : Type*)
    [Fintype α] [DecidableEq α] [Fintype ι] where
  rel : ι → α → α → Prop
  preorder : ∀ i, IsPreorder α (rel i)
  separated : ∀ {x y}, x ≠ y →
    ∃ i, ¬ rel i x y ∧ ¬ rel i y x

/-- The exact iterated-Dilworth pigeonhole argument.  If each of `e`
orders had width at most `m`, color into `m` chains in every order.  The
resulting map into `m^e` color vectors cannot be injective, while the
separation property says that it must be injective. -/
theorem MultiOrderDilworthData.exists_large_antichain
    {α ι : Type*} [Fintype α] [DecidableEq α]
    [Fintype ι]
    (D : MultiOrderDilworthData α ι) {m : ℕ} (hm : 0 < m)
    (hcard : m ^ Fintype.card ι < Fintype.card α) :
    ∃ i : ι, ∃ A : Finset α,
      IsAntichain (D.rel i) (↑A : Set α) ∧ m < A.card := by
  classical
  by_contra h
  push Not at h
  have hbound (i : ι) :
      ∀ A : Finset α, IsAntichain (D.rel i) (↑A : Set α) → A.card ≤ m := by
    intro A hA
    exact h i A hA
  choose color hcolor using fun i =>
    finite_dilworth_of_isPreorder (D.rel i) (D.preorder i) m hm (hbound i)
  let signature : α → (∀ i : ι, Fin m) := fun x i => color i x
  have hsignature : Function.Injective signature := by
    intro x y hxy
    by_contra hne
    obtain ⟨i, hixy, hiyx⟩ := D.separated hne
    have hc : color i x = color i y := congrFun hxy i
    exact (hcolor i hc).elim hixy hiyx
  have hle : Fintype.card α ≤ m ^ Fintype.card ι := by
    simpa using Fintype.card_le_of_injective signature hsignature
  exact (Nat.not_le_of_lt hcard) hle

/-- All geometric inputs to Proposition 2.1, organized edge by edge.

`separated` is the projection-separation lemma combined with `PFree`, and `planar_dichotomy`
is the cups--caps theorem after projection. -/
structure ProjectionOrderCertificate
    (P : Set (Point 3)) (X : Finset (Point 3)) (ι : Type*)
    [Fintype ι] where
  projection : ι → Point 3 →ᵃ[ℝ] Point 2
  separated : PFree P X → ∀ {x y : ↑X}, x ≠ y →
    ∃ i, ¬ projectionLE P (projection i) x.1 y.1 ∧
      ¬ projectionLE P (projection i) y.1 x.1
  planar_dichotomy : ∀ i (A : Finset (↑X)) (a b : ℕ),
    2 ≤ a → 2 ≤ b →
    IsAntichain (fun x y : ↑X => projectionLE P (projection i) x.1 y.1)
      (↑A : Set (↑X)) →
    Nat.choose (a + b - 4) (a - 2) < A.card →
      (∃ C : Finset (↑X), C ⊆ A ∧ C.card = a ∧
        ProjectedPCap P (projection i) (C.map (Function.Embedding.subtype _))) ∨
      (∃ C : Finset (↑X), C ⊆ A ∧ C.card = b ∧
        ProjectedConvexPosition (projection i)
          (C.map (Function.Embedding.subtype _)))

private lemma polytope_ordered_pairwise_lt {I : List ℕ} (hI : Ordered I) :
    I.Pairwise (· < ·) := by
  induction I with
  | nil => simp
  | cons x tail ih =>
      cases tail with
      | nil => simp
      | cons y tail =>
          exact List.Pairwise.cons_cons_of_trans hI.1 (ih hI.2)

private lemma polytope_tightPath_get_consecutive
    {χ : ℕ → ℕ → ℕ → Bool} {c : Bool} {I : List ℕ}
    (hI : TightPath χ c I) (i : ℕ) (hi : i + 2 < I.length) :
    χ I[i] I[i + 1] I[i + 2] = c := by
  induction i generalizing I with
  | zero =>
      cases I with
      | nil => simp at hi
      | cons x tail =>
          cases tail with
          | nil => simp at hi
          | cons y tail =>
              cases tail with
              | nil => simp at hi
              | cons z tail => simpa [TightPath] using hI.1
  | succ i ih =>
      cases I with
      | nil => simp at hi
      | cons x tail =>
          cases tail with
          | nil => simp at hi
          | cons y tail =>
              cases tail with
              | nil => simp at hi
              | cons z tail =>
                  have hi' : i + 2 < (y :: z :: tail).length :=
                    Nat.lt_of_succ_lt_succ hi
                  have hh := ih hI.2 hi'
                  simpa using hh

/-- The generic edge projections of an oriented trihedral supply every
geometric input in the projection-certificate form of Proposition 2.1. -/
def OrientedTrihedral.GenericProjectionFamily.toProjectionOrderCertificate
    {T : OrientedTrihedral} {X : Finset (Point 3)}
    (G : T.GenericProjectionFamily X) :
    ProjectionOrderCertificate T.carrier X (Fin 3) := by
  classical
  refine {
    projection := G.projection
    separated := G.separated
    planar_dichotomy := ?_ }
  intro edge A a b ha hb hanti hcard
  have hApos : 0 < A.card := Nat.zero_lt_of_lt hcard
  let coordinate : ↥A → ℝ := fun x => planeX (G.projection edge x.1.1)
  have hcoordinate : Function.Injective coordinate := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    by_contra hne
    exact (G.planeX_ne edge (x := x.1.1) (y := y.1.1) x.1.2 y.1.2 hne) hxy
  letI : LinearOrder ↥A := LinearOrder.lift' coordinate hcoordinate
  let e : Fin A.card ≃o ↥A := Fintype.orderIsoFinOfCardEq ↥A (by simp)
  let u : ℕ → ↥X := fun j =>
    if hj : j < A.card then (e ⟨j, hj⟩).1 else (e ⟨0, hApos⟩).1
  let p : ℕ → Point 2 := fun j => G.projection edge (u j).1
  have huA {j : ℕ} (hj : j < A.card) : u j ∈ A := by
    change (if h : j < A.card then (e ⟨j, h⟩).1 else (e ⟨0, hApos⟩).1) ∈ A
    rw [dif_pos hj]
    exact (e ⟨j, hj⟩).2
  have hpX : ∀ j ∈ Finset.range A.card, ∀ k ∈ Finset.range A.card,
      j < k → planeX (p j) < planeX (p k) := by
    intro j hj k hk hjk
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    have he := e.strictMono (show (⟨j, hj'⟩ : Fin A.card) < ⟨k, hk'⟩ by exact hjk)
    change coordinate (e ⟨j, hj'⟩) < coordinate (e ⟨k, hk'⟩) at he
    simpa [coordinate, p, u, hj', hk'] using he
  have hpSlope : ∀ j ∈ Finset.range A.card, ∀ k ∈ Finset.range A.card,
      ∀ l ∈ Finset.range A.card, j < k → k < l →
        secantSlope (p j) (p k) ≠ secantSlope (p k) (p l) := by
    intro j hj k hk l hl hjk hkl
    have hj' := Finset.mem_range.mp hj
    have hk' := Finset.mem_range.mp hk
    have hl' := Finset.mem_range.mp hl
    apply G.slope_ne edge (u j).2 (u k).2 (u l).2
    · intro h
      exact (ne_of_lt (hpX j hj k hk hjk)) (congrArg (planeX ∘ G.projection edge) h)
    · intro h
      exact (ne_of_lt (hpX k hk l hl hkl)) (congrArg (planeX ∘ G.projection edge) h)
    · intro h
      exact (ne_of_lt (hpX j hj l hl (hjk.trans hkl)))
        (congrArg (planeX ∘ G.projection edge) h)
  have hchoose : Nat.choose (b + a - 4) (b - 2) =
      Nat.choose (a + b - 4) (a - 2) := by
    have hsum : a + b - 4 = (a - 2) + (b - 2) := by omega
    calc
      Nat.choose (b + a - 4) (b - 2) =
          Nat.choose (a + b - 4) (b - 2) := by congr 2 <;> omega
      _ = Nat.choose (a + b - 4) (a - 2) :=
        (Nat.choose_symm_of_eq_add hsum).symm
  have hcard' : Nat.choose (b + a - 4) (b - 2) <
      (Finset.range A.card).card := by
    simpa only [Finset.card_range, hchoose] using hcard
  rcases planar_cups_caps p (Finset.range A.card) b a hb ha hpX hpSlope hcard' with
    hcup | hcap
  · obtain ⟨I, hIS, hlen, hcup⟩ := hcup
    let castIndex : Fin b → Fin I.length := fun j =>
      ⟨j.1, by simpa [hlen] using j.2⟩
    let index : Fin b → ℕ := fun j => I.get (castIndex j)
    have hindex_mem (j : Fin b) : index j ∈ Finset.range A.card := by
      apply hIS
      exact List.get_mem I (castIndex j)
    have hindex_strict : StrictMono index := by
      intro j k hjk
      have hget := (polytope_ordered_pairwise_lt hcup.1).rel_get_of_lt
        (show castIndex j < castIndex k by exact hjk)
      simpa [index] using hget
    let c : Fin b → ↥X := fun j => u (index j)
    let q : Fin b → Point 2 := fun j => p (index j)
    have hcA (j : Fin b) : c j ∈ A := by
      exact huA (Finset.mem_range.mp (hindex_mem j))
    have hcinj : Function.Injective c := by
      intro j k hck
      have hj := Finset.mem_range.mp (hindex_mem j)
      have hk := Finset.mem_range.mp (hindex_mem k)
      have heq : e ⟨index j, hj⟩ = e ⟨index k, hk⟩ := by
        apply Subtype.ext
        simpa [c, u, hj, hk] using hck
      have hfin := e.injective heq
      apply hindex_strict.injective
      exact Fin.ext_iff.mp hfin
    have hqinj : Function.Injective q := by
      intro j k hq
      apply hcinj
      apply Subtype.ext
      by_contra hne
      exact (G.planeX_ne edge (x := (c j).1) (y := (c k).1)
        (c j).2 (c k).2 hne)
        (congrArg planeX hq)
    have hqx : ∀ {j k : Fin b}, j < k → planeX (q j) < planeX (q k) := by
      intro j k hjk
      exact hpX _ (hindex_mem j) _ (hindex_mem k) (hindex_strict hjk)
    let qNat : ℕ → Point 2 := fun j => if hj : j < b then q ⟨j, hj⟩ else 0
    have hqNatX : ∀ j k, j < k → k < b → planeX (qNat j) < planeX (qNat k) := by
      intro j k hjk hkb
      have hjb : j < b := hjk.trans hkb
      simpa [qNat, hjb, hkb] using
        hqx (show (⟨j, hjb⟩ : Fin b) < ⟨k, hkb⟩ by exact hjk)
    have hadj : ∀ j, j + 2 < b →
        0 < planeTurn (qNat j) (qNat (j + 1)) (qNat (j + 2)) := by
      intro j hj
      have hj0 : j < b := by omega
      have hj1 : j + 1 < b := by omega
      have hsraw := polytope_tightPath_get_consecutive hcup.2.2 j (by
        simpa [hlen] using hj)
      have hslope : secantSlope (q ⟨j, hj0⟩) (q ⟨j + 1, hj1⟩) <
          secantSlope (q ⟨j + 1, hj1⟩) (q ⟨j + 2, hj⟩) := by
        simpa [q, index, castIndex] using of_decide_eq_true hsraw
      have hturn := (slope_lt_slope_iff_turn_pos
        (hqx (show (⟨j, hj0⟩ : Fin b) < ⟨j + 1, hj1⟩ by
          change j < j + 1
          omega))
        (hqx (show (⟨j + 1, hj1⟩ : Fin b) < ⟨j + 2, hj⟩ by
          change j + 1 < j + 2
          omega))).1 hslope
      simpa [qNat, hj0, hj1, hj] using hturn
    have hturn : ∀ {j k l : Fin b}, j < k → k < l →
        0 < planeTurn (q j) (q k) (q l) := by
      intro j k l hjk hkl
      have h := adjacent_planeTurn_pos_all qNat b hqNatX hadj
        j.1 k.1 l.1 hjk hkl l.2
      simpa [qNat, j.2, k.2, l.2] using h
    have hconv := fin_convexChain_inConvexPosition hb q hqx hturn
    let C : Finset (↥X) := Finset.univ.image c
    have hCA : C ⊆ A := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
      exact hcA j
    have hCcard : C.card = b := by
      change (Finset.univ.image c).card = b
      rw [Finset.card_image_of_injective _ hcinj, Finset.card_univ,
        Fintype.card_fin]
    have hprojectedErase (j : Fin b) :
        G.projection edge ''
            (↑((C.map (Function.Embedding.subtype _)).erase (c j).1) : Set (Point 3)) ⊆
          (↑((Finset.univ.image q).erase (q j)) : Set (Point 2)) := by
      rintro z ⟨y, hy, rfl⟩
      obtain ⟨hyne, hyC⟩ := Finset.mem_erase.mp hy
      obtain ⟨s, hsC, rfl⟩ := Finset.mem_map.mp hyC
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hsC
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_image_of_mem q (Finset.mem_univ k)⟩
      have hkj : k ≠ j := by
        intro h
        subst k
        exact hyne rfl
      simpa [q, c, p] using hqinj.ne hkj
    right
    refine ⟨C, hCA, hCcard, ?_⟩
    intro x hx
    obtain ⟨s, hsC, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hsC
    intro hhull
    exact hconv (q j) (Finset.mem_image_of_mem q (Finset.mem_univ j))
      (convexHull_mono (hprojectedErase j) hhull)
  · obtain ⟨I, hIS, hlen, hcap⟩ := hcap
    let castIndex : Fin a → Fin I.length := fun j =>
      ⟨j.1, by simpa [hlen] using j.2⟩
    let index : Fin a → ℕ := fun j => I.get (castIndex j)
    have hindex_mem (j : Fin a) : index j ∈ Finset.range A.card := by
      apply hIS
      exact List.get_mem I (castIndex j)
    have hindex_strict : StrictMono index := by
      intro j k hjk
      have hget := (polytope_ordered_pairwise_lt hcap.1).rel_get_of_lt
        (show castIndex j < castIndex k by exact hjk)
      simpa [index] using hget
    let c : Fin a → ↥X := fun j => u (index j)
    let q : Fin a → Point 2 := fun j => p (index j)
    have hcA (j : Fin a) : c j ∈ A :=
      huA (Finset.mem_range.mp (hindex_mem j))
    have hcinj : Function.Injective c := by
      intro j k hck
      have hj := Finset.mem_range.mp (hindex_mem j)
      have hk := Finset.mem_range.mp (hindex_mem k)
      have heq : e ⟨index j, hj⟩ = e ⟨index k, hk⟩ := by
        apply Subtype.ext
        simpa [c, u, hj, hk] using hck
      have hfin := e.injective heq
      apply hindex_strict.injective
      exact Fin.ext_iff.mp hfin
    have hqinj : Function.Injective q := by
      intro j k hq
      apply hcinj
      apply Subtype.ext
      by_contra hne
      exact (G.planeX_ne edge (x := (c j).1) (y := (c k).1)
        (c j).2 (c k).2 hne)
        (congrArg planeX hq)
    have hqx : ∀ {j k : Fin a}, j < k → planeX (q j) < planeX (q k) := by
      intro j k hjk
      exact hpX _ (hindex_mem j) _ (hindex_mem k) (hindex_strict hjk)
    have hnotrel {j k : Fin a} (hjk : j ≠ k) :
        ¬ projectionLE T.carrier (G.projection edge) (c j).1 (c k).1 := by
      intro hrel
      have heq := hanti.eq (hcA j) (hcA k) hrel
      exact hjk (hcinj heq)
    have hqy : ∀ {j k : Fin a}, j < k → planeY (q k) < planeY (q j) := by
      intro j k hjk
      have hjk' : j ≠ k := ne_of_lt hjk
      have hpoint : (c j).1 ≠ (c k).1 := by
        intro h
        exact hjk' (hcinj (Subtype.ext h))
      have hyne := G.planeY_ne edge (x := (c j).1) (y := (c k).1)
        (c j).2 (c k).2 hpoint
      rcases lt_trichotomy (planeY (q j)) (planeY (q k)) with hy | hy | hy
      · exfalso
        apply hnotrel hjk'
        rw [projectionLE, G.image_carrier edge]
        exact mem_convexHull_negativeOrthant_of_both_lt (hqx hjk) hy
      · exact (hyne hy).elim
      · exact hy
    have hantiQ : ∀ {j k : Fin a}, j ≠ k →
        q j ∉ convexHull ℝ (negativeOrthant 2 ∪ {q k}) := by
      intro j k hjk hmem
      apply hnotrel hjk
      rw [projectionLE, G.image_carrier edge]
      exact hmem
    let qNat : ℕ → Point 2 := fun j => if hj : j < a then q ⟨j, hj⟩ else 0
    have hqNatX : ∀ j k, j < k → k < a → planeX (qNat j) < planeX (qNat k) := by
      intro j k hjk hka
      have hja : j < a := hjk.trans hka
      simpa [qNat, hja, hka] using
        hqx (show (⟨j, hja⟩ : Fin a) < ⟨k, hka⟩ by exact hjk)
    have hadj : ∀ j, j + 2 < a →
        planeTurn (qNat j) (qNat (j + 1)) (qNat (j + 2)) < 0 := by
      intro j hj
      have hj0 : j < a := by omega
      have hj1 : j + 1 < a := by omega
      have hsraw := polytope_tightPath_get_consecutive hcap.2.2.1 j (by
        simpa [hlen] using hj)
      have hnotSlope : ¬ secantSlope (q ⟨j, hj0⟩) (q ⟨j + 1, hj1⟩) <
          secantSlope (q ⟨j + 1, hj1⟩) (q ⟨j + 2, hj⟩) := by
        simpa [q, index, castIndex] using of_decide_eq_false hsraw
      have hneSlope : secantSlope (q ⟨j, hj0⟩) (q ⟨j + 1, hj1⟩) ≠
          secantSlope (q ⟨j + 1, hj1⟩) (q ⟨j + 2, hj⟩) := by
        apply hcap.2.2.2
        · exact List.get_mem I (castIndex ⟨j, hj0⟩)
        · exact List.get_mem I (castIndex ⟨j + 1, hj1⟩)
        · exact List.get_mem I (castIndex ⟨j + 2, hj⟩)
        · exact hindex_strict (show (⟨j, hj0⟩ : Fin a) < ⟨j + 1, hj1⟩ by
            change j < j + 1
            omega)
        · exact hindex_strict (show (⟨j + 1, hj1⟩ : Fin a) < ⟨j + 2, hj⟩ by
            change j + 1 < j + 2
            omega)
      have hslope : secantSlope (q ⟨j + 1, hj1⟩) (q ⟨j + 2, hj⟩) <
          secantSlope (q ⟨j, hj0⟩) (q ⟨j + 1, hj1⟩) :=
        lt_of_le_of_ne (le_of_not_gt hnotSlope) hneSlope.symm
      have hturn := (slope_gt_slope_iff_turn_neg
        (hqx (show (⟨j, hj0⟩ : Fin a) < ⟨j + 1, hj1⟩ by
          change j < j + 1
          omega))
        (hqx (show (⟨j + 1, hj1⟩ : Fin a) < ⟨j + 2, hj⟩ by
          change j + 1 < j + 2
          omega))).1 hslope
      simpa [qNat, hj0, hj1, hj] using hturn
    have hturn : ∀ {j k l : Fin a}, j < k → k < l →
        planeTurn (q j) (q k) (q l) < 0 := by
      intro j k l hjk hkl
      have h := adjacent_planeTurn_neg_all qNat a hqNatX hadj
        j.1 k.1 l.1 hjk hkl l.2
      simpa [qNat, j.2, k.2, l.2] using h
    have hnegcap := fin_concaveChain_negativeOrthantCap ha q hqx hqy hturn hantiQ
    let C : Finset (↥X) := Finset.univ.image c
    have hCA : C ⊆ A := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
      exact hcA j
    have hCcard : C.card = a := by
      change (Finset.univ.image c).card = a
      rw [Finset.card_image_of_injective _ hcinj, Finset.card_univ,
        Fintype.card_fin]
    have hprojectedErase (j : Fin a) :
        G.projection edge ''
            (↑((C.map (Function.Embedding.subtype _)).erase (c j).1) : Set (Point 3)) ⊆
          (↑((Finset.univ.image q).erase (q j)) : Set (Point 2)) := by
      rintro z ⟨y, hy, rfl⟩
      obtain ⟨hyne, hyC⟩ := Finset.mem_erase.mp hy
      obtain ⟨s, hsC, rfl⟩ := Finset.mem_map.mp hyC
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hsC
      apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_image_of_mem q (Finset.mem_univ k)⟩
      have hkj : k ≠ j := by
        intro h
        subst k
        exact hyne rfl
      simpa [q, c, p] using hqinj.ne hkj
    left
    refine ⟨C, hCA, hCcard, ?_⟩
    intro x hx
    obtain ⟨s, hsC, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hsC
    intro hhull
    apply hnegcap j
    apply convexHull_mono ?_ hhull
    intro z hz
    rcases hz with hzP | hzC
    · left
      rw [← G.image_carrier edge]
      exact hzP
    · exact Or.inr (hprojectedErase j hzC)

/-- Pohoata--Zakharov, Proposition 2.1, in projection-certificate form.
The cardinal threshold and its exponent are exactly those in the paper. -/
theorem pohoata_zakharov_prop_two_one
    {P : Set (Point 3)} {X : Finset (Point 3)} {ι : Type*}
    [Fintype ι]
    (cert : ProjectionOrderCertificate P X ι)
    (hfree : PFree P X) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : Nat.choose (a + b - 4) (a - 2) ^ Fintype.card ι < X.card) :
    (∃ C : Finset (Point 3), C ⊆ X ∧ C.card = a ∧ PCap P C) ∨
      (∃ C : Finset (Point 3), C ⊆ X ∧ C.card = b ∧
        InConvexPosition C) := by
  classical
  let m := Nat.choose (a + b - 4) (a - 2)
  have hindex : a - 2 ≤ a + b - 4 := by omega
  have hm : 0 < m := Nat.choose_pos hindex
  let D : MultiOrderDilworthData (↑X) ι :=
    { rel := fun i x y => projectionLE P (cert.projection i) x.1 y.1
      preorder := fun i =>
        { refl := fun x => (projectionLE_isPreorder P (cert.projection i)).refl x.1
          trans := fun x y z hxy hyz =>
            (projectionLE_isPreorder P (cert.projection i)).trans
              x.1 y.1 z.1 hxy hyz }
      separated := cert.separated hfree }
  have hcard' : m ^ Fintype.card ι < Fintype.card (↑X) := by
    simpa [m] using hcard
  obtain ⟨i, A, hAanti, hAcard⟩ := D.exists_large_antichain hm hcard'
  rcases cert.planar_dichotomy i A a b ha hb hAanti hAcard with hcap | hconv
  · left
    obtain ⟨C, hCA, hCa, hCcap⟩ := hcap
    refine ⟨C.map (Function.Embedding.subtype _), ?_, ?_, hCcap.pcap⟩
    · intro x hx
      simp only [Finset.mem_map] at hx
      obtain ⟨y, hyC, rfl⟩ := hx
      exact y.2
    · simpa using hCa
  · right
    obtain ⟨C, hCA, hCb, hCconv⟩ := hconv
    refine ⟨C.map (Function.Embedding.subtype _), ?_, ?_, hCconv.inConvexPosition⟩
    · intro x hx
      simp only [Finset.mem_map] at hx
      obtain ⟨y, hyC, rfl⟩ := hx
      exact y.2
    · simpa using hCb

/-- The specialization used later in the paper: after padding an edge list
of cardinality at most three, the sharp threshold is the cube of the planar
cups--caps number. -/
theorem pohoata_zakharov_prop_two_one_atMostThree_edges
    {P : Set (Point 3)} {X : Finset (Point 3)} {ι : Type*} [Fintype ι]
    (cert : ProjectionOrderCertificate P X ι)
    (hedges : Fintype.card ι ≤ 3)
    (hfree : PFree P X) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : Nat.choose (a + b - 4) (a - 2) ^ 3 < X.card) :
    (∃ C : Finset (Point 3), C ⊆ X ∧ C.card = a ∧ PCap P C) ∨
      (∃ C : Finset (Point 3), C ⊆ X ∧ C.card = b ∧
        InConvexPosition C) := by
  apply pohoata_zakharov_prop_two_one cert hfree ha hb
  have hindex : a - 2 ≤ a + b - 4 := by omega
  have hm : 0 < Nat.choose (a + b - 4) (a - 2) := Nat.choose_pos hindex
  exact (Nat.pow_le_pow_right hm hedges).trans_lt hcard

/-- A convenient padded form of the at-most-three-edge specialization,
with the edge directions indexed by `Fin 3`. -/
theorem pohoata_zakharov_prop_two_one_three_edges
    {P : Set (Point 3)} {X : Finset (Point 3)}
    (cert : ProjectionOrderCertificate P X (Fin 3))
    (hfree : PFree P X) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : Nat.choose (a + b - 4) (a - 2) ^ 3 < X.card) :
    (∃ C : Finset (Point 3), C ⊆ X ∧ C.card = a ∧ PCap P C) ∨
      (∃ C : Finset (Point 3), C ⊆ X ∧ C.card = b ∧
        InConvexPosition C) := by
  apply pohoata_zakharov_prop_two_one cert hfree ha hb
  simpa using hcard

end

end Erdos651
