/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ProjectionCardinality

/-!
# Coarse numerical form of the projection-cardinality criterion

This file bounds every coordinate-deletion box by one uniform polynomial
factor times the cardinality of the original containing integer box.  It
turns the coordinate-sensitive criterion in `ProjectionCardinality` into the
single natural-number inequality used by the source parameter hierarchy.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- For a nonempty integer interval, its cardinality is one plus its side
length. -/
theorem side_toNat_add_one_eq_intervalCard
    {lower upper : ℤ} (h : lower ≤ upper) :
    (upper - lower).toNat + 1 = (upper + 1 - lower).toNat := by
  have hcast :
      (((upper - lower).toNat + 1 : ℕ) : ℤ) =
        (((upper + 1 - lower).toNat : ℕ) : ℤ) := by
    push_cast
    rw [Int.toNat_of_nonneg (sub_nonneg.mpr h),
      Int.toNat_of_nonneg (by omega : 0 ≤ upper + 1 - lower)]
    omega
  exact_mod_cast hcast

/-- A box containing a translate of a GAP carrier is nonempty in every
coordinate. -/
theorem integerBox_lower_le_upper_of_gap_containment {d r : ℕ}
    (P : GAP d r) (B : CFP.IntegerBox d) (t : LatticePoint d)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier) :
    ∀ j, B.lower j ≤ B.upper j := by
  have hbase := hcontain (P.coordPoint_mem_carrier P.zeroCoord)
  obtain ⟨b, hbB, _hb⟩ := CFP.mem_translate_iff.mp hbase
  intro j
  exact (CFP.IntegerBox.mem_carrier_iff.mp hbB j).1.trans
    (CFP.IntegerBox.mem_carrier_iff.mp hbB j).2

/-- The product of the side cardinalities after deleting one coordinate is
at most the cardinality of the full box. -/
theorem prod_deleted_sideCard_le_box_card {d : ℕ}
    (B : CFP.IntegerBox (d + 1))
    (hB : ∀ j, B.lower j ≤ B.upper j) (j₀ : Fin (d + 1)) :
    (∏ j : Fin d,
        ((B.upper (j₀.succAbove j) - B.lower (j₀.succAbove j)).toNat + 1))
      ≤ B.carrier.card := by
  rw [B.card_carrier, Fin.prod_univ_succAbove _ j₀]
  simp_rw [side_toNat_add_one_eq_intervalCard (hB _)]
  have hfactor :
      1 ≤ (B.upper j₀ + 1 - B.lower j₀).toNat := by
    have hj := hB j₀
    have hpos : 0 < B.upper j₀ + 1 - B.lower j₀ := by omega
    rw [Nat.one_le_iff_ne_zero]
    intro hzero
    have hcast := Int.toNat_of_nonneg (le_of_lt hpos)
    rw [hzero] at hcast
    simp at hcast
    omega
  calc
    ∏ j : Fin d,
        (B.upper (j₀.succAbove j) + 1 -
          B.lower (j₀.succAbove j)).toNat =
        1 * ∏ j : Fin d,
          (B.upper (j₀.succAbove j) + 1 -
            B.lower (j₀.succAbove j)).toNat := by simp
    _ ≤ (B.upper j₀ + 1 - B.lower j₀).toNat *
        ∏ j : Fin d,
          (B.upper (j₀.succAbove j) + 1 -
            B.lower (j₀.succAbove j)).toNat :=
      Nat.mul_le_mul_right _ hfactor

/-- One projected coordinate factor is bounded by the uniform scale factor
times the corresponding original box-side cardinality. -/
theorem projection_factor_le_coarse {d k : ℕ}
    (B : CFP.IntegerBox (d + 1)) (j : Fin (d + 1)) :
    2 * projectionRadius k B j + 1 ≤
      (2 * (d + 1) * k + 1) *
        ((B.upper j - B.lower j).toNat + 1) := by
  let side := (B.upper j - B.lower j).toNat
  let scale := 2 * (d + 1) * k
  have hone : 1 ≤ scale + side + 1 := by omega
  calc
    2 * projectionRadius k B j + 1 = scale * side + 1 := by
      simp only [projectionRadius, scale, side]
      ring
    _ ≤ scale * side + (scale + side + 1) :=
      Nat.add_le_add_left hone _
    _ = (2 * (d + 1) * k + 1) *
        ((B.upper j - B.lower j).toNat + 1) := by
      simp only [scale, side]
      ring

/-- Uniform bound for every coordinate-deletion projection box. -/
theorem projection_product_le_coarse_mul_box_card {d k : ℕ}
    (P : GAP (d + 1) (d + 1)) (B : CFP.IntegerBox (d + 1))
    (t : LatticePoint (d + 1))
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (j₀ : Fin (d + 1)) :
    (∏ j : Fin d,
        (2 * projectionRadius k B (j₀.succAbove j) + 1)) ≤
      (2 * (d + 1) * k + 1) ^ d * B.carrier.card := by
  have hB := integerBox_lower_le_upper_of_gap_containment P B t hcontain
  calc
    (∏ j : Fin d,
        (2 * projectionRadius k B (j₀.succAbove j) + 1)) ≤
        ∏ j : Fin d,
          ((2 * (d + 1) * k + 1) *
            ((B.upper (j₀.succAbove j) -
              B.lower (j₀.succAbove j)).toNat + 1)) := by
      exact Finset.prod_le_prod (fun _j _hj ↦ Nat.zero_le _)
        (fun j _hj ↦ projection_factor_le_coarse B (j₀.succAbove j))
    _ = (2 * (d + 1) * k + 1) ^ d *
        ∏ j : Fin d,
          ((B.upper (j₀.succAbove j) -
            B.lower (j₀.succAbove j)).toNat + 1) := by
      rw [Finset.prod_mul_distrib]
      simp
    _ ≤ (2 * (d + 1) * k + 1) ^ d * B.carrier.card :=
      Nat.mul_le_mul_left _ (prod_deleted_sideCard_le_box_card B hB j₀)

/-- Coarse source-facing full-rank criterion.  This is the single numerical
inequality obtained after bounding every possible deleted-coordinate box by
the same polynomial factor. -/
theorem det_ne_zero_of_coarse_projection_bound {d k : ℕ}
    (P : GAP (d + 1) (d + 1)) (B : CFP.IntegerBox (d + 1))
    (t : LatticePoint (d + 1))
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (hnondegenerate : P.Nondegenerate)
    (hproper : (P.dilate k).Proper)
    (hlarge :
      2 ^ (d + 1) * (2 * (d + 1) * k + 1) ^ d * B.carrier.card <
        k ^ (d + 1) * P.volume) :
    (stepMatrix P).det ≠ 0 := by
  apply det_ne_zero_of_pow_mul_volume_gt_projection_bound
    P B t hcontain hnondegenerate hproper
  intro j₀
  calc
    2 ^ (d + 1) *
        (∏ j : Fin d,
          (2 * projectionRadius k B (j₀.succAbove j) + 1)) ≤
        2 ^ (d + 1) *
          ((2 * (d + 1) * k + 1) ^ d * B.carrier.card) :=
      Nat.mul_le_mul_left _
        (projection_product_le_coarse_mul_box_card P B t hcontain j₀)
    _ = 2 ^ (d + 1) * (2 * (d + 1) * k + 1) ^ d *
        B.carrier.card := by ring
    _ < k ^ (d + 1) * P.volume := hlarge

/-- The source hierarchy form.  The reference progression `S` controls the
box volume, while the selected progression `P` retains a `gamma` fraction of
`S`.  After extracting the common factor `k^d`, the single hierarchy
inequality `constant < k * gamma` implies the coarse projection bound and
hence full rank. -/
theorem det_ne_zero_of_controlled_box_gamma_hierarchy
    {d k ambient rank Q : ℕ}
    (P : GAP (d + 1) (d + 1)) (S : GAP ambient rank)
    (B : CFP.IntegerBox (d + 1)) (t : LatticePoint (d + 1))
    (gamma : ℝ)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (hnondegenerate : P.Nondegenerate)
    (hproper : (P.dilate k).Proper)
    (hk : 0 < k)
    (hbox : B.carrier.card ≤ Q * S.volume)
    (hvolume : gamma * (S.volume : ℝ) ≤ (P.volume : ℝ))
    (_hgamma : 0 < gamma)
    (hhierarchy :
      ((2 ^ (d + 1) * (2 * (d + 1) + 1) ^ d * Q : ℕ) : ℝ) <
        (k : ℝ) * gamma) :
    (stepMatrix P).det ≠ 0 := by
  let constant : ℕ :=
    2 ^ (d + 1) * (2 * (d + 1) + 1) ^ d * Q
  have hSvolume : 0 < S.volume := by
    rw [GAP.volume]
    exact Finset.prod_pos fun i _hi ↦ S.width_pos i
  have hfactor :
      2 * (d + 1) * k + 1 ≤ (2 * (d + 1) + 1) * k := by
    calc
      2 * (d + 1) * k + 1 ≤ 2 * (d + 1) * k + k :=
        Nat.add_le_add_left hk _
      _ = (2 * (d + 1) + 1) * k := by ring
  have hfactorPow :
      (2 * (d + 1) * k + 1) ^ d ≤
        ((2 * (d + 1) + 1) * k) ^ d :=
    Nat.pow_le_pow_left hfactor d
  have hupperNat :
      2 ^ (d + 1) * (2 * (d + 1) * k + 1) ^ d * B.carrier.card ≤
        constant * k ^ d * S.volume := by
    calc
      2 ^ (d + 1) * (2 * (d + 1) * k + 1) ^ d * B.carrier.card ≤
          2 ^ (d + 1) * ((2 * (d + 1) + 1) * k) ^ d *
            B.carrier.card :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hfactorPow)
      _ ≤ 2 ^ (d + 1) * ((2 * (d + 1) + 1) * k) ^ d *
          (Q * S.volume) :=
        Nat.mul_le_mul_left _ hbox
      _ = constant * k ^ d * S.volume := by
        simp only [constant, mul_pow]
        ring
  have hupperReal :
      ((2 ^ (d + 1) * (2 * (d + 1) * k + 1) ^ d *
        B.carrier.card : ℕ) : ℝ) ≤
        (constant : ℝ) * (k : ℝ) ^ d * (S.volume : ℝ) := by
    exact_mod_cast hupperNat
  have hpositive : 0 < (k : ℝ) ^ d * (S.volume : ℝ) := by
    exact mul_pos (pow_pos (by exact_mod_cast hk) _) (by exact_mod_cast hSvolume)
  have hhierarchy' : (constant : ℝ) < (k : ℝ) * gamma := by
    simpa only [constant] using hhierarchy
  have hstrict := mul_lt_mul_of_pos_right hhierarchy' hpositive
  have hlargeReal :
      ((2 ^ (d + 1) * (2 * (d + 1) * k + 1) ^ d *
        B.carrier.card : ℕ) : ℝ) <
        ((k ^ (d + 1) * P.volume : ℕ) : ℝ) := by
    calc
      ((2 ^ (d + 1) * (2 * (d + 1) * k + 1) ^ d *
          B.carrier.card : ℕ) : ℝ) ≤
          (constant : ℝ) * (k : ℝ) ^ d * (S.volume : ℝ) :=
        hupperReal
      _ < ((k : ℝ) * gamma) *
          ((k : ℝ) ^ d * (S.volume : ℝ)) := by
        simpa only [mul_assoc] using hstrict
      _ = (k : ℝ) ^ (d + 1) * (gamma * (S.volume : ℝ)) := by ring
      _ ≤ (k : ℝ) ^ (d + 1) * (P.volume : ℝ) :=
        mul_le_mul_of_nonneg_left hvolume (by positivity)
      _ = ((k ^ (d + 1) * P.volume : ℕ) : ℝ) := by norm_cast
  have hlarge :
      2 ^ (d + 1) * (2 * (d + 1) * k + 1) ^ d * B.carrier.card <
        k ^ (d + 1) * P.volume := by
    exact_mod_cast hlargeReal
  exact det_ne_zero_of_coarse_projection_bound P B t hcontain
    hnondegenerate hproper hlarge

/-- Dimension-positive form of the source hierarchy criterion.  This wrapper
avoids exposing a predecessor dimension in applications to a selected CFP
progression whose rank is known only abstractly to be positive. -/
theorem det_ne_zero_of_controlled_box_gamma_hierarchy_pos
    {d k ambient rank Q : ℕ} (hd : 0 < d)
    (P : GAP d d) (S : GAP ambient rank)
    (B : CFP.IntegerBox d) (t : LatticePoint d)
    (gamma : ℝ)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (hnondegenerate : P.Nondegenerate)
    (hproper : (P.dilate k).Proper)
    (hk : 0 < k)
    (hbox : B.carrier.card ≤ Q * S.volume)
    (hvolume : gamma * (S.volume : ℝ) ≤ (P.volume : ℝ))
    (hgamma : 0 < gamma)
    (hhierarchy :
      ((2 ^ d * (2 * d + 1) ^ (d - 1) * Q : ℕ) : ℝ) <
        (k : ℝ) * gamma) :
    (stepMatrix P).det ≠ 0 := by
  obtain ⟨n, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hd)
  exact det_ne_zero_of_controlled_box_gamma_hierarchy
    P S B t gamma hcontain hnondegenerate hproper hk hbox hvolume hgamma
      (by simpa using hhierarchy)

end

end Erdos186.PZ.Intersection
