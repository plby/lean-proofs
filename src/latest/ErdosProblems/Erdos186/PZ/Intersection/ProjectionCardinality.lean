/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ProgressionBox
import ErdosProblems.Erdos186.PZ.Intersection.DilationVolume

/-!
# Projection cardinality forces full rank

If the square step matrix of a progression is singular, its steps lie in a
rational hyperplane.  Deleting a coordinate on which a nonzero normal is
nonzero is injective on every dilate of the progression.  Containment of the
original progression in an axis-parallel box bounds the remaining
coordinates of the dilate, giving an explicit `d - 1` dimensional cardinal
bound.  A proper dilate whose displayed volume exceeds this bound therefore
forces the step matrix to be nonsingular.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Delete coordinate `j₀` from an `(d+1)`-dimensional lattice point. -/
def deleteCoordinate {d : ℕ} (j₀ : Fin (d + 1))
    (x : LatticePoint (d + 1)) : LatticePoint d :=
  fun j ↦ x (j₀.succAbove j)

/-- A singular square step matrix has a nonzero rational normal vector to
all its rows. -/
theorem exists_nonzero_rational_step_normal_of_det_eq_zero {d : ℕ}
    (P : GAP d d) (hdet : (stepMatrix P).det = 0) :
    ∃ u : Fin d → ℚ, u ≠ 0 ∧
      ∀ i, (∑ j, (P.steps i j : ℚ) * u j) = 0 := by
  let M : Matrix (Fin d) (Fin d) ℚ :=
    (stepMatrix P).map (Int.castRingHom ℚ)
  have hdetM : M.det = 0 := by
    rw [show M.det = ((stepMatrix P).det : ℚ) by
      exact ((Int.castRingHom ℚ).map_det (stepMatrix P)).symm]
    simp [hdet]
  obtain ⟨u, hu, hmul⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := M)).2 hdetM
  refine ⟨u, hu, ?_⟩
  intro i
  have hi := congrFun hmul i
  simpa [M, Matrix.mulVec, stepMatrix, dotProduct] using hi

/-- A rational normal annihilates the difference of two displayed points
of any dilate, since dilation changes neither the steps nor their span. -/
theorem rational_normal_coordPoint_sub_eq_zero {d r k : ℕ}
    (P : GAP d r) (u : Fin d → ℚ)
    (hu : ∀ i, (∑ j, (P.steps i j : ℚ) * u j) = 0)
    (n m : (P.dilate k).Coord) :
    (∑ j, u j *
      (((P.dilate k).coordPoint n j -
        (P.dilate k).coordPoint m j : ℤ) : ℚ)) = 0 := by
  simp only [GAP.coordPoint, GAP.dilate_steps]
  push_cast
  calc
    ∑ j, u j *
        ((↑((P.dilate k).offset j) +
            ∑ i, (n i : ℚ) * (P.steps i j : ℚ)) -
          (↑((P.dilate k).offset j) +
            ∑ i, (m i : ℚ) * (P.steps i j : ℚ))) =
        ∑ j, ∑ i,
          (((n i : ℚ) - (m i : ℚ)) *
            ((P.steps i j : ℚ) * u j)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show
        ↑((P.dilate k).offset j) +
              ∑ i, (n i : ℚ) * (P.steps i j : ℚ) -
            (↑((P.dilate k).offset j) +
              ∑ i, (m i : ℚ) * (P.steps i j : ℚ)) =
          (∑ i, (n i : ℚ) * (P.steps i j : ℚ)) -
            ∑ i, (m i : ℚ) * (P.steps i j : ℚ) by ring]
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i, (((n i : ℚ) - (m i : ℚ)) *
          ∑ j, ((P.steps i j : ℚ) * u j)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = 0 := by simp [hu]

/-- If a rational normal has a nonzero `j₀` coordinate, deletion of
`j₀` is injective on the carrier of every dilate. -/
theorem deleteCoordinate_injOn_dilate_carrier_of_normal {d r k : ℕ}
    (P : GAP (d + 1) r) (u : Fin (d + 1) → ℚ)
    (j₀ : Fin (d + 1)) (hj₀ : u j₀ ≠ 0)
    (hu : ∀ i, (∑ j, (P.steps i j : ℚ) * u j) = 0) :
    Set.InjOn (deleteCoordinate j₀) (P.dilate k).carrier := by
  intro x hx y hy hproj
  obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hx
  obtain ⟨m, rfl⟩ := GAP.mem_carrier_iff.mp hy
  have hnormal := rational_normal_coordPoint_sub_eq_zero P u hu n m
  rw [Fin.sum_univ_succAbove _ j₀] at hnormal
  have hother : ∀ j : Fin d,
      (P.dilate k).coordPoint n (j₀.succAbove j) =
        (P.dilate k).coordPoint m (j₀.succAbove j) := by
    intro j
    exact congrFun hproj j
  have hj : (P.dilate k).coordPoint n j₀ =
      (P.dilate k).coordPoint m j₀ := by
    have hzero :
        u j₀ *
          ((((P.dilate k).coordPoint n j₀ -
            (P.dilate k).coordPoint m j₀ : ℤ)) : ℚ) = 0 := by
      simpa [hother] using hnormal
    have hdiff :
        ((((P.dilate k).coordPoint n j₀ -
          (P.dilate k).coordPoint m j₀ : ℤ)) : ℚ) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hj₀
    exact_mod_cast (sub_eq_zero.mp (Int.cast_eq_zero.mp hdiff))
  funext j
  exact j₀.succAboveCases hj hother j

/-- Radius used to bound a dilated progression after projecting away one
coordinate.  Each of the `d+1` step directions contributes at most `k`
times the corresponding side length of the original containing box. -/
def projectionRadius {d : ℕ} (k : ℕ) (B : CFP.IntegerBox d)
    (j : Fin d) : ℕ :=
  d * k * (B.upper j - B.lower j).toNat

/-- The explicit projected box centered at `k * P.offset`. -/
def dilateProjectionBox {d : ℕ} (P : GAP (d + 1) (d + 1))
    (B : CFP.IntegerBox (d + 1)) (k : ℕ) (j₀ : Fin (d + 1)) :
    Finset (LatticePoint d) :=
  Fintype.piFinset fun j ↦
    Finset.Icc
      ((k : ℤ) * P.offset (j₀.succAbove j) -
        projectionRadius k B (j₀.succAbove j))
      ((k : ℤ) * P.offset (j₀.succAbove j) +
        projectionRadius k B (j₀.succAbove j))

/-- Cardinality of the projected bounding box. -/
theorem card_dilateProjectionBox {d : ℕ}
    (P : GAP (d + 1) (d + 1)) (B : CFP.IntegerBox (d + 1))
    (k : ℕ) (j₀ : Fin (d + 1)) :
    (dilateProjectionBox P B k j₀).card =
      ∏ j : Fin d,
        (2 * projectionRadius k B (j₀.succAbove j) + 1) := by
  classical
  rw [dilateProjectionBox, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro j _
  rw [Int.card_Icc]
  rw [show
    (k : ℤ) * P.offset (j₀.succAbove j) +
          projectionRadius k B (j₀.succAbove j) + 1 -
        ((k : ℤ) * P.offset (j₀.succAbove j) -
          projectionRadius k B (j₀.succAbove j)) =
      (2 * projectionRadius k B (j₀.succAbove j) + 1 : ℕ) by
        push_cast
        ring]
  exact Int.toNat_natCast _

/-- Every projected point of the dilated progression lies in the explicit
projected box coming from containment of the original progression. -/
theorem deleteCoordinate_dilate_carrier_subset_projectionBox {d k : ℕ}
    (P : GAP (d + 1) (d + 1)) (B : CFP.IntegerBox (d + 1))
    (t : LatticePoint (d + 1))
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (j₀ : Fin (d + 1)) :
    (P.dilate k).carrier.image (deleteCoordinate j₀) ⊆
      dilateProjectionBox P B k j₀ := by
  classical
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨n, rfl⟩ := GAP.mem_carrier_iff.mp hx
  rw [dilateProjectionBox, Fintype.mem_piFinset]
  intro j
  rw [Finset.mem_Icc]
  let q := j₀.succAbove j
  have hbase := hcontain (P.coordPoint_mem_carrier P.zeroCoord)
  obtain ⟨b, hbB, hb⟩ := CFP.mem_translate_iff.mp hbase
  have hbq := CFP.IntegerBox.mem_carrier_iff.mp hbB q
  have hside : 0 ≤ B.upper q - B.lower q := by omega
  have hsideNat : ((B.upper q - B.lower q).toNat : ℤ) =
      B.upper q - B.lower q := Int.toNat_of_nonneg hside
  have hterm : ∀ i : Fin (d + 1),
      |((n i : ℤ) * P.steps i q)| ≤
        (k : ℤ) * (B.upper q - B.lower q) := by
    intro i
    have hn : (n i : ℕ) ≤ k * (P.widths i - 1) := by
      have := (n i).isLt
      simpa only [GAP.dilate_widths, Nat.lt_add_one_iff] using this
    have hnZ : (n i : ℤ) ≤ (k * (P.widths i - 1) : ℕ) := by
      exact_mod_cast hn
    have hscaled := scaled_step_abs_le_box_side P B t hcontain i q
    calc
      |((n i : ℤ) * P.steps i q)| =
          (n i : ℤ) * |P.steps i q| := by
            rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℤ) ≤ (n i : ℤ))]
      _ ≤ ((k * (P.widths i - 1) : ℕ) : ℤ) * |P.steps i q| :=
        mul_le_mul_of_nonneg_right hnZ (abs_nonneg _)
      _ = (k : ℤ) *
          (((P.widths i - 1 : ℕ) : ℤ) * |P.steps i q|) := by
        push_cast
        ring
      _ ≤ (k : ℤ) * (B.upper q - B.lower q) :=
        mul_le_mul_of_nonneg_left hscaled (by positivity)
  have hsum :
      |∑ i, (n i : ℤ) * P.steps i q| ≤
        ((d + 1 : ℕ) : ℤ) *
          ((k : ℤ) * (B.upper q - B.lower q)) := by
    calc
      |∑ i, (n i : ℤ) * P.steps i q| ≤
          ∑ i, |((n i : ℤ) * P.steps i q)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin (d + 1),
          ((k : ℤ) * (B.upper q - B.lower q)) :=
        Finset.sum_le_sum fun i _ ↦ hterm i
      _ = ((d + 1 : ℕ) : ℤ) *
          ((k : ℤ) * (B.upper q - B.lower q)) := by simp
  have hradius :
      (projectionRadius k B q : ℤ) =
        ((d + 1 : ℕ) : ℤ) *
          ((k : ℤ) * (B.upper q - B.lower q)) := by
    simp only [projectionRadius, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      hsideNat]
    ring
  have hcoord :
      |(P.dilate k).coordPoint n q - (k : ℤ) * P.offset q| ≤
        (projectionRadius k B q : ℤ) := by
    simpa [GAP.coordPoint, hradius] using hsum
  constructor
  · dsimp only [q] at hcoord
    dsimp only [deleteCoordinate]
    rw [abs_le] at hcoord
    omega
  · dsimp only [q] at hcoord
    dsimp only [deleteCoordinate]
    rw [abs_le] at hcoord
    omega

/-- **Projection-cardinality full-rank criterion.**

For an ambient `(d+1)`-box, singularity would make some coordinate deletion
injective on the proper dilate.  Its cardinality would then be bounded by the
explicit product on the right.  Thus the displayed strict volume inequality
forces the square step matrix to be nonsingular. -/
theorem det_ne_zero_of_dilate_volume_gt_projection_bound {d k : ℕ}
    (P : GAP (d + 1) (d + 1)) (B : CFP.IntegerBox (d + 1))
    (t : LatticePoint (d + 1))
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (hproper : (P.dilate k).Proper)
    (hlarge : ∀ j₀ : Fin (d + 1),
      (∏ i, (k * (P.widths i - 1) + 1)) >
        ∏ j : Fin d,
          (2 * projectionRadius k B (j₀.succAbove j) + 1)) :
    (stepMatrix P).det ≠ 0 := by
  intro hdet
  obtain ⟨u, hu0, hu⟩ :=
    exists_nonzero_rational_step_normal_of_det_eq_zero P hdet
  have hex : ∃ j₀, u j₀ ≠ 0 := by
    by_contra h
    apply hu0
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨j₀, hj₀⟩ := hex
  have hinj := deleteCoordinate_injOn_dilate_carrier_of_normal
    (k := k) P u j₀ hj₀ hu
  have hcardImage :
      ((P.dilate k).carrier.image (deleteCoordinate j₀)).card =
        (P.dilate k).carrier.card := by
    exact Finset.card_image_iff.mpr hinj
  have hsubset := deleteCoordinate_dilate_carrier_subset_projectionBox
    (k := k) P B t hcontain j₀
  have hcard := Finset.card_le_card hsubset
  rw [hcardImage, P.dilate k |>.card_carrier_eq_volume hproper,
    card_dilateProjectionBox] at hcard
  exact (not_lt_of_ge hcard) (hlarge j₀)

/-- Source-facing form of the projection criterion.  Nondegeneracy supplies
the lower growth estimate
`k^(d+1) * volume(P) ≤ 2^(d+1) * |kP|`; the stated strict inequality then
forces the actual proper dilate to be larger than every possible projected
box. -/
theorem det_ne_zero_of_pow_mul_volume_gt_projection_bound {d k : ℕ}
    (P : GAP (d + 1) (d + 1)) (B : CFP.IntegerBox (d + 1))
    (t : LatticePoint (d + 1))
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (hnondegenerate : P.Nondegenerate)
    (hproper : (P.dilate k).Proper)
    (hlarge : ∀ j₀ : Fin (d + 1),
      2 ^ (d + 1) *
          (∏ j : Fin d,
            (2 * projectionRadius k B (j₀.succAbove j) + 1)) <
        k ^ (d + 1) * P.volume) :
    (stepMatrix P).det ≠ 0 := by
  apply det_ne_zero_of_dilate_volume_gt_projection_bound
    P B t hcontain hproper
  intro j₀
  let bound : ℕ :=
    ∏ j : Fin d, (2 * projectionRadius k B (j₀.succAbove j) + 1)
  have hgrowth :=
    pow_mul_volume_le_two_pow_mul_dilate_card P hnondegenerate hproper
  have hcard : bound < (P.dilate k).carrier.card := by
    by_contra hnot
    have hle : (P.dilate k).carrier.card ≤ bound := Nat.le_of_not_gt hnot
    have hupper :
        k ^ (d + 1) * P.volume ≤ 2 ^ (d + 1) * bound :=
      hgrowth.trans (Nat.mul_le_mul_left _ hle)
    exact (not_lt_of_ge hupper) (by simpa only [bound] using hlarge j₀)
  rw [(P.dilate k).card_carrier_eq_volume hproper] at hcard
  simpa only [bound, GAP.volume_dilate] using hcard

end

end Erdos186.PZ.Intersection
