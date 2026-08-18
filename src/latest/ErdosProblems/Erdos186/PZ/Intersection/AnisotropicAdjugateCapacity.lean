/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ActualStepInverse
import ErdosProblems.Erdos186.PZ.Intersection.AdjugateBounds
import ErdosProblems.Erdos186.PZ.Intersection.AdjugateHierarchy
import ErdosProblems.Erdos186.PZ.Intersection.AnisotropicRounding

/-!
# Anisotropic adjugate capacity for the rounding error box

The uniform adjugate estimate loses the source progression's separate
coordinate widths.  Here an adjugate entry is treated as the determinant of
the matrix obtained by deleting one displayed-step row and one ambient
coordinate column.  Its bound therefore contains exactly the other box
coordinate widths.  Multiplication by the rounding error in the deleted
coordinate restores one full anisotropic box product.

The second half of the file is Cramer's rule over `ℝ`.  Stating its numerical
premise over `ℝ` is important: the natural rounding multiplier is
`sqrt (d * |core|)`, and no coordinatewise ceiling is needed.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Product of the displayed widths after deleting row `i`. -/
def deletedWidthProduct {n : ℕ} (P : GAP (n + 1) (n + 1))
    (i : Fin (n + 1)) : ℕ :=
  ∏ k : Fin n, (P.widths (i.succAbove k) - 1)

/-- Product of the geometric side lengths after deleting ambient column
`j`.  These are differences of endpoints, rather than interval
cardinalities, because they are the quantities occurring in the determinant
bound. -/
def deletedBoxSideProduct {n : ℕ} (B : CFP.IntegerBox (n + 1))
    (j : Fin (n + 1)) : ℕ :=
  ∏ l : Fin n, (B.upper (j.succAbove l) - B.lower (j.succAbove l)).toNat

/-- For the canonical source control box, restoring the deleted source
coordinate width costs only the expected `(2m)^n` multiple of the source
progression volume. -/
theorem sourceWidth_mul_deletedBoxSideProduct_controlIntegerBox_le
    {ambient n : ℕ} (S : GAP ambient (n + 1)) (m : ℕ)
    (j : Fin (n + 1)) :
    (S.widths j - 1) *
        deletedBoxSideProduct (controlIntegerBox S m) j ≤
      (2 * m) ^ n * S.volume := by
  have hside (l : Fin n) :
      ((controlIntegerBox S m).upper (j.succAbove l) -
          (controlIntegerBox S m).lower (j.succAbove l)).toNat =
        2 * m * (S.widths (j.succAbove l) - 1) := by
    change
      (((m * (S.widths (j.succAbove l) - 1) : ℕ) : ℤ) -
        -((m * (S.widths (j.succAbove l) - 1) : ℕ) : ℤ)).toNat = _
    have hnonneg :
        0 ≤ (((m * (S.widths (j.succAbove l) - 1) : ℕ) : ℤ) -
          -((m * (S.widths (j.succAbove l) - 1) : ℕ) : ℤ)) := by
      have hw : (0 : ℤ) ≤
          ((m * (S.widths (j.succAbove l) - 1) : ℕ) : ℤ) := by
        exact Int.natCast_nonneg _
      omega
    have hcast :
        (((((m * (S.widths (j.succAbove l) - 1) : ℕ) : ℤ) -
          -((m * (S.widths (j.succAbove l) - 1) : ℕ) : ℤ)).toNat : ℕ) : ℤ) =
          ((2 * m * (S.widths (j.succAbove l) - 1) : ℕ) : ℤ) := by
      rw [Int.toNat_of_nonneg hnonneg]
      push_cast
      ring
    exact_mod_cast hcast
  have hdeleted :
      deletedBoxSideProduct (controlIntegerBox S m) j =
        (2 * m) ^ n *
          ∏ l : Fin n, (S.widths (j.succAbove l) - 1) := by
    unfold deletedBoxSideProduct
    simp_rw [hside]
    calc
      (∏ l : Fin n, 2 * m * (S.widths (j.succAbove l) - 1)) =
          (∏ _l : Fin n, 2 * m) *
            ∏ l : Fin n, (S.widths (j.succAbove l) - 1) := by
              rw [Finset.prod_mul_distrib]
      _ = (2 * m) ^ n *
          ∏ l : Fin n, (S.widths (j.succAbove l) - 1) := by simp
  rw [hdeleted]
  calc
    (S.widths j - 1) *
          ((2 * m) ^ n *
            ∏ l : Fin n, (S.widths (j.succAbove l) - 1)) =
        (2 * m) ^ n * ∏ l : Fin (n + 1), (S.widths l - 1) := by
      rw [Fin.prod_univ_succAbove (fun l ↦ S.widths l - 1) j]
      ring
    _ ≤ (2 * m) ^ n * ∏ l : Fin (n + 1), S.widths l := by
      apply Nat.mul_le_mul_left
      exact Finset.prod_le_prod (fun _l _hl ↦ Nat.zero_le _)
        (fun l _hl ↦ Nat.sub_le _ _)
    _ = (2 * m) ^ n * S.volume := by rfl

theorem deletedWidthProduct_eq_widthProductExcept {n : ℕ}
    (P : GAP (n + 1) (n + 1)) (i : Fin (n + 1)) :
    deletedWidthProduct P i = widthProductExcept P i := by
  unfold deletedWidthProduct widthProductExcept
  rw [show (Finset.univ : Finset (Fin (n + 1))).erase i =
      Finset.univ.map i.succAboveEmb by
    rw [Fin.univ_succAbove n i]
    simp]
  rw [Finset.prod_map]
  simp

/-- The cofactor in ambient column `j`, multiplied by all displayed widths
except row `i`, is controlled by the product of all box side lengths except
column `j`. -/
theorem adjugate_entry_mul_deletedWidthProduct_le_factorial_mul_deletedBoxSide
    {n : ℕ} (P : GAP (n + 1) (n + 1))
    (B : CFP.IntegerBox (n + 1)) (t : LatticePoint (n + 1))
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (i j : Fin (n + 1)) :
    ((stepMatrix P).adjugate j i).natAbs * deletedWidthProduct P i ≤
      n.factorial * deletedBoxSideProduct B j := by
  let A : Matrix (Fin n) (Fin n) ℤ :=
    (stepMatrix P).submatrix i.succAbove j.succAbove
  let s : Fin n → ℝ := fun k ↦
    (P.widths (i.succAbove k) - 1 : ℕ)
  let u : Fin n → ℝ := fun l ↦
    ((B.upper (j.succAbove l) - B.lower (j.succAbove l)).toNat : ℕ)
  have hB := integerBox_lower_le_upper_of_gap_containment P B t hcontain
  have hs : ∀ k, 0 ≤ s k := by
    intro k
    positivity
  have hentry : ∀ k l, s k * |(A k l : ℝ)| ≤ u l := by
    intro k l
    have hstep := scaled_step_abs_cast_le_box_side P B t hcontain
      (i.succAbove k) (j.succAbove l)
    have hnonneg :
        0 ≤ B.upper (j.succAbove l) - B.lower (j.succAbove l) :=
      sub_nonneg.mpr (hB _)
    have hu : u l =
        ((B.upper (j.succAbove l) - B.lower (j.succAbove l) : ℤ) : ℝ) := by
      dsimp only [u]
      exact_mod_cast Int.toNat_of_nonneg hnonneg
    rw [hu]
    simpa only [A, s, Matrix.submatrix_apply, stepMatrix] using hstep
  have hdet := natAbs_det_mul_prod_le A s u hs hentry
  have hadjugate :
      ((stepMatrix P).adjugate j i).natAbs = A.det.natAbs := by
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
    simp only [A, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg,
      Int.natAbs_one, one_pow, one_mul]
  have hprodS : (∏ k, s k) = (deletedWidthProduct P i : ℝ) := by
    simp only [s, deletedWidthProduct]
    norm_cast
  have hprodU : (∏ l, u l) = (deletedBoxSideProduct B j : ℝ) := by
    simp only [u, deletedBoxSideProduct, Nat.cast_prod]
  rw [← hadjugate, hprodS, hprodU] at hdet
  exact_mod_cast hdet

/-- If every deleted-column box product, after restoring the corresponding
rounding width, is bounded by `V`, then the full weighted adjugate column has
capacity `(n+1)! * V`. -/
theorem weighted_adjugate_mul_deletedWidthProduct_le_factorial_mul
    {n V : ℕ} (P : GAP (n + 1) (n + 1))
    (B : CFP.IntegerBox (n + 1)) (t : LatticePoint (n + 1))
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (errorWidth : Fin (n + 1) → ℕ)
    (hdeleted : ∀ j, errorWidth j * deletedBoxSideProduct B j ≤ V)
    (i : Fin (n + 1)) :
    (∑ j, errorWidth j * ((stepMatrix P).adjugate j i).natAbs) *
        deletedWidthProduct P i ≤
      (n + 1).factorial * V := by
  calc
    (∑ j, errorWidth j * ((stepMatrix P).adjugate j i).natAbs) *
          deletedWidthProduct P i =
        ∑ j, (errorWidth j * ((stepMatrix P).adjugate j i).natAbs) *
          deletedWidthProduct P i := by rw [Finset.sum_mul]
    _ ≤ ∑ _j : Fin (n + 1), n.factorial * V := by
      apply Finset.sum_le_sum
      intro j _hj
      calc
        (errorWidth j * ((stepMatrix P).adjugate j i).natAbs) *
              deletedWidthProduct P i =
            errorWidth j *
              (((stepMatrix P).adjugate j i).natAbs *
                deletedWidthProduct P i) := by ring
        _ ≤ errorWidth j *
              (n.factorial * deletedBoxSideProduct B j) := by
            exact Nat.mul_le_mul_left _
              (adjugate_entry_mul_deletedWidthProduct_le_factorial_mul_deletedBoxSide
                P B t hcontain i j)
        _ = n.factorial *
              (errorWidth j * deletedBoxSideProduct B j) := by ring
        _ ≤ n.factorial * V := Nat.mul_le_mul_left _ (hdeleted j)
    _ = (n + 1).factorial * V := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, Nat.factorial_succ]
      simp [Nat.add_mul, Nat.mul_assoc]

/-- Deleted-column box capacity and retained volume bound the anisotropically
weighted adjugate column.  The scalar `rho` is kept real so that it can later
be instantiated by the square-root rounding multiplier. -/
theorem anisotropic_adjugate_capacity_of_deleted_box_gamma_hierarchy
    {n ambient rank Q margin : ℕ}
    (P : GAP (n + 1) (n + 1)) (S : GAP ambient rank)
    (B : CFP.IntegerBox (n + 1)) (t : LatticePoint (n + 1))
    {radii : Fin (n + 1) → ℕ}
    (hcentered : P.Centered radii) (hnondegenerate : P.Nondegenerate)
    (errorWidth : Fin (n + 1) → ℕ)
    (hcontain : P.carrier ⊆ CFP.translate t B.carrier)
    (hdeleted : ∀ j,
      errorWidth j * deletedBoxSideProduct B j ≤ Q * S.volume)
    (hQ : 0 < Q)
    (gamma rho : ℝ) (hgamma : 0 < gamma) (hrho : 0 ≤ rho)
    (hvolume : gamma * (S.volume : ℝ) ≤ (P.volume : ℝ))
    (hdet : (stepMatrix P).det ≠ 0)
    (hhierarchy :
      rho * ((((n + 1).factorial * Q * 3 ^ (n + 1) : ℕ) : ℝ)) ≤
        gamma * margin) :
    ∀ i,
      ∑ j, (rho * (errorWidth j : ℝ)) *
          (((stepMatrix P).adjugate j i).natAbs : ℝ) ≤
        ((stepMatrix P).det.natAbs : ℝ) * (margin * radii i : ℕ) := by
  intro i
  let adjSum : ℕ :=
    ∑ j, errorWidth j * ((stepMatrix P).adjugate j i).natAbs
  let otherWidths : ℕ := deletedWidthProduct P i
  let constant : ℕ := (n + 1).factorial * Q * 3 ^ (n + 1)
  have hsum : adjSum * otherWidths ≤
      ((n + 1).factorial * Q) * S.volume := by
    calc
      adjSum * otherWidths ≤ (n + 1).factorial * (Q * S.volume) := by
        simpa only [adjSum, otherWidths] using
          weighted_adjugate_mul_deletedWidthProduct_le_factorial_mul
            P B t hcontain errorWidth hdeleted i
      _ = ((n + 1).factorial * Q) * S.volume := by ring
  have hvolume' :
      P.volume ≤ 3 ^ (n + 1) * radii i * otherWidths := by
    simpa only [otherWidths, ← deletedWidthProduct_eq_widthProductExcept]
      using centered_volume_le_three_pow_mul_radius_mul_widthProductExcept
        P hcentered hnondegenerate i
  have hotherWidths : 0 < otherWidths := by
    simp only [otherWidths, deletedWidthProduct]
    exact Finset.prod_pos fun k _hk ↦ by
      rw [hcentered.width_sub_one]
      have hkpos := hcentered.nondegenerate_iff.mp hnondegenerate
        (i.succAbove k)
      omega
  have hgamma_nonneg : 0 ≤ gamma := hgamma.le
  have hmul :
      (gamma * (adjSum : ℝ)) * (otherWidths : ℝ) ≤
        ((constant : ℝ) * radii i) * (otherWidths : ℝ) := by
    calc
      (gamma * (adjSum : ℝ)) * (otherWidths : ℝ) =
          gamma * ((adjSum * otherWidths : ℕ) : ℝ) := by
            push_cast
            ring
      _ ≤ gamma * ((((n + 1).factorial * Q) * S.volume : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hsum) hgamma_nonneg
      _ = ((((n + 1).factorial * Q : ℕ) : ℝ)) *
          (gamma * (S.volume : ℝ)) := by
            push_cast
            ring
      _ ≤ ((((n + 1).factorial * Q : ℕ) : ℝ)) * (P.volume : ℝ) :=
        mul_le_mul_of_nonneg_left hvolume (by positivity)
      _ ≤ ((((n + 1).factorial * Q : ℕ) : ℝ)) *
          ((3 ^ (n + 1) * radii i * otherWidths : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hvolume') (by positivity)
      _ = ((constant : ℝ) * radii i) * (otherWidths : ℝ) := by
        simp only [constant]
        push_cast
        ring
  have hotherWidthsReal : (0 : ℝ) < otherWidths := by
    exact_mod_cast hotherWidths
  have hadj : gamma * (adjSum : ℝ) ≤ (constant : ℝ) * radii i := by
    nlinarith
  have hconstant : 0 < constant := by
    simp only [constant]
    positivity
  have hmargin : (0 : ℝ) ≤ margin := by positivity
  have hadj' := mul_le_mul_of_nonneg_right hadj hmargin
  have hsum_nonneg : (0 : ℝ) ≤ adjSum := by positivity
  have hhierarchy' : rho * (constant : ℝ) ≤ gamma * margin := by
    simpa only [constant] using hhierarchy
  have hhierarchy'' :=
    mul_le_mul_of_nonneg_right hhierarchy' hsum_nonneg
  have hcapacity : rho * (adjSum : ℝ) ≤ (margin : ℝ) * radii i := by
    have hconstantReal : (0 : ℝ) < constant := by
      exact_mod_cast hconstant
    have hmulCapacity :
        (rho * (adjSum : ℝ)) * (constant : ℝ) ≤
          ((margin : ℝ) * radii i) * (constant : ℝ) := by
      calc
        (rho * (adjSum : ℝ)) * (constant : ℝ) =
            (rho * (constant : ℝ)) * (adjSum : ℝ) := by ring
        _ ≤ (gamma * margin) * (adjSum : ℝ) := hhierarchy''
        _ = (gamma * (adjSum : ℝ)) * margin := by ring
        _ ≤ ((constant : ℝ) * radii i) * margin := hadj'
        _ = ((margin : ℝ) * radii i) * (constant : ℝ) := by ring
    nlinarith
  calc
    ∑ j, (rho * (errorWidth j : ℝ)) *
        (((stepMatrix P).adjugate j i).natAbs : ℝ) =
        rho * (adjSum : ℝ) := by
          simp only [adjSum, Nat.cast_sum, Nat.cast_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _hj
          ring
    _ ≤ (margin : ℝ) * radii i := hcapacity
    _ = (1 : ℝ) * ((margin : ℝ) * radii i) := by ring
    _ ≤ ((stepMatrix P).det.natAbs : ℝ) *
        ((margin : ℝ) * radii i) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Int.natAbs_pos.mpr hdet
      · positivity
    _ = ((stepMatrix P).det.natAbs : ℝ) *
        (margin * radii i : ℕ) := by
      push_cast
      ring

/-- Real anisotropic Cramer capacity.  This is the exact numerical premise
needed to put every step-lattice point in the displayed margin dilate. -/
theorem mem_dilate_of_mem_stepLattice_of_anisotropic_adjugate_bound
    {d margin : ℕ} (P : GAP d d) {radii : Fin d → ℕ}
    (hP : P.Centered radii) (hdet : (stepMatrix P).det ≠ 0)
    (errorRadius : Fin d → ℝ)
    (hinverse : ∀ i,
      ∑ j, errorRadius j *
          (((stepMatrix P).adjugate j i).natAbs : ℝ) ≤
        ((stepMatrix P).det.natAbs : ℝ) * (margin * radii i : ℕ))
    {x : LatticePoint d} (hxL : x ∈ stepLattice P)
    (hx : ∀ j, |(x j : ℝ)| ≤ errorRadius j) :
    x ∈ (P.dilate margin).carrier := by
  obtain ⟨a, ha⟩ := exists_stepCoefficients_of_mem_stepLattice P hxL
  apply mem_dilate_of_stepCoefficients_le P hP a ha
  intro i
  have hcramer := det_mul_stepCoefficient_eq_sum_adjugate P a ha i
  have habsReal :
      (((stepMatrix P).det * a i).natAbs : ℝ) ≤
        ∑ j, errorRadius j *
          (((stepMatrix P).adjugate j i).natAbs : ℝ) := by
    rw [hcramer]
    calc
      (((∑ j, x j * (stepMatrix P).adjugate j i).natAbs : ℕ) : ℝ) =
          |((∑ j, x j * (stepMatrix P).adjugate j i : ℤ) : ℝ)| := by
            simp
      _ = |∑ j, (x j : ℝ) * ((stepMatrix P).adjugate j i : ℝ)| := by
            congr 1
            norm_cast
      _ ≤ ∑ j, |(x j : ℝ) * ((stepMatrix P).adjugate j i : ℝ)| :=
            Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |(x j : ℝ)| *
          (((stepMatrix P).adjugate j i).natAbs : ℝ) := by
            apply Finset.sum_congr rfl
            intro j _hj
            rw [abs_mul]
            simp
      _ ≤ ∑ j, errorRadius j *
          (((stepMatrix P).adjugate j i).natAbs : ℝ) := by
            apply Finset.sum_le_sum
            intro j _hj
            exact mul_le_mul_of_nonneg_right (hx j) (by positivity)
  have htotal := habsReal.trans (hinverse i)
  rw [Int.natAbs_mul] at htotal
  push_cast at htotal
  have hdetpos : (0 : ℝ) < (stepMatrix P).det.natAbs := by
    exact_mod_cast Int.natAbs_pos.mpr hdet
  have haReal : ((a i).natAbs : ℝ) ≤ (margin * radii i : ℕ) := by
    push_cast
    nlinarith
  have haNat : (a i).natAbs ≤ margin * radii i := by
    exact_mod_cast haReal
  have hcast : ((a i).natAbs : ℤ) ≤ (margin * radii i : ℕ) := by
    exact_mod_cast haNat
  simpa using hcast

/-- Wrapper in precisely the step-lattice-qualified form used as
`SideTarget.herrorBox`. -/
theorem anisotropic_errorBox_subset_dilate_of_adjugate_bound
    {d margin : ℕ} (P : GAP d d) {radii : Fin d → ℕ}
    (hP : P.Centered radii) (hdet : (stepMatrix P).det ≠ 0)
    (errorRadius : Fin d → ℝ)
    (hinverse : ∀ i,
      ∑ j, errorRadius j *
          (((stepMatrix P).adjugate j i).natAbs : ℝ) ≤
        ((stepMatrix P).det.natAbs : ℝ) * (margin * radii i : ℕ)) :
    ∀ e : LatticePoint d, e ∈ stepLattice P →
      (∀ j, |(e j : ℝ)| ≤ errorRadius j) →
      e ∈ (P.dilate margin).carrier := by
  intro e heL he
  exact mem_dilate_of_mem_stepLattice_of_anisotropic_adjugate_bound
    P hP hdet errorRadius hinverse heL he

/-- Enhanced-witness/rank-cast form of the anisotropic error-box theorem.
This has exactly the lattice and progression occurring in
`SideTarget.herrorBox`. -/
theorem enhancedWitness_anisotropic_errorBox_subset_dilate
    {d s D k loss margin : ℕ} {X : Finset (LatticePoint d)}
    (W : CFP.EnhancedCFPWitness X s D k loss) (hrank : W.rank = d)
    {radii : Fin d → ℕ}
    (hcentered : (rankCastGAP W.progression hrank).Centered radii)
    (hdet : (stepMatrix (rankCastGAP W.progression hrank)).det ≠ 0)
    (errorRadius : Fin d → ℝ)
    (hinverse : ∀ i,
      ∑ j, errorRadius j *
          (((stepMatrix (rankCastGAP W.progression hrank)).adjugate j i).natAbs : ℝ) ≤
        ((stepMatrix (rankCastGAP W.progression hrank)).det.natAbs : ℝ) *
          (margin * radii i : ℕ)) :
    ∀ e : LatticePoint d, e ∈ gapStepLattice W.progression →
      (∀ j, |(e j : ℝ)| ≤ errorRadius j) →
      e ∈ (W.progression.dilate margin).carrier := by
  intro e heL he
  have heL' : e ∈ stepLattice (rankCastGAP W.progression hrank) := by
    rw [rankCastGAP_stepLattice W.progression hrank]
    exact heL
  have he' := anisotropic_errorBox_subset_dilate_of_adjugate_bound
    (rankCastGAP W.progression hrank) hcentered hdet errorRadius hinverse
    e heL' he
  simpa only [rankCastGAP_dilate_carrier W.progression hrank] using he'

/-- Deleted-column capacity, retained volume, and the scalar hierarchy
produce the literal enhanced-witness `herrorBox` function. -/
theorem enhancedWitness_anisotropic_errorBox_of_deleted_box_gamma_hierarchy
    {n s D k loss margin ambient rank Q : ℕ}
    {X : Finset (LatticePoint (n + 1))}
    (W : CFP.EnhancedCFPWitness X s D k loss)
    (hrank : W.rank = n + 1)
    (S : GAP ambient rank) (B : CFP.IntegerBox (n + 1))
    (t : LatticePoint (n + 1)) {radii : Fin (n + 1) → ℕ}
    (hcentered : (rankCastGAP W.progression hrank).Centered radii)
    (errorWidth : Fin (n + 1) → ℕ)
    (hcontain : (rankCastGAP W.progression hrank).carrier ⊆
      CFP.translate t B.carrier)
    (hdeleted : ∀ j,
      errorWidth j * deletedBoxSideProduct B j ≤ Q * S.volume)
    (hQ : 0 < Q) (gamma rho : ℝ) (hgamma : 0 < gamma)
    (hrho : 0 ≤ rho)
    (hvolume : gamma * (S.volume : ℝ) ≤
      ((rankCastGAP W.progression hrank).volume : ℝ))
    (hdet :
      (stepMatrix (rankCastGAP W.progression hrank)).det ≠ 0)
    (hhierarchy :
      rho * ((((n + 1).factorial * Q * 3 ^ (n + 1) : ℕ) : ℝ)) ≤
        gamma * margin) :
    ∀ e : LatticePoint (n + 1),
      e ∈ gapStepLattice W.progression →
      (∀ j, |(e j : ℝ)| ≤ rho * (errorWidth j : ℝ)) →
      e ∈ (W.progression.dilate margin).carrier := by
  have hinverse :=
    anisotropic_adjugate_capacity_of_deleted_box_gamma_hierarchy
      (rankCastGAP W.progression hrank) S B t hcentered
      (rankCastGAP_nondegenerate hrank W.progression_nondegenerate)
      errorWidth hcontain hdeleted hQ gamma rho hgamma hrho hvolume hdet
      hhierarchy
  exact enhancedWitness_anisotropic_errorBox_subset_dilate
    W hrank hcentered hdet (fun j ↦ rho * (errorWidth j : ℝ)) hinverse

/-- Canonical-control-box specialization.  The coordinate error widths are
the original source GAP widths, so the deleted-column product estimate is
automatic. -/
theorem enhancedWitness_anisotropic_errorBox_of_sourceControlBox
    {n s D k loss margin ambient : ℕ}
    {X : Finset (LatticePoint (n + 1))}
    (W : CFP.EnhancedCFPWitness X s D k loss)
    (hrank : W.rank = n + 1) (S : GAP ambient (n + 1)) (m : ℕ)
    (hm : 0 < m) (t : LatticePoint (n + 1))
    {radii : Fin (n + 1) → ℕ}
    (hcentered : (rankCastGAP W.progression hrank).Centered radii)
    (hcontain : (rankCastGAP W.progression hrank).carrier ⊆
      CFP.translate t (controlIntegerBox S m).carrier)
    (gamma rho : ℝ) (hgamma : 0 < gamma) (hrho : 0 ≤ rho)
    (hvolume : gamma * (S.volume : ℝ) ≤
      ((rankCastGAP W.progression hrank).volume : ℝ))
    (hdet :
      (stepMatrix (rankCastGAP W.progression hrank)).det ≠ 0)
    (hhierarchy :
      rho * ((((n + 1).factorial * (2 * m) ^ n *
        3 ^ (n + 1) : ℕ) : ℝ)) ≤ gamma * margin) :
    ∀ e : LatticePoint (n + 1),
      e ∈ gapStepLattice W.progression →
      (∀ j, |(e j : ℝ)| ≤ rho * (S.widths j - 1 : ℕ)) →
      e ∈ (W.progression.dilate margin).carrier := by
  apply enhancedWitness_anisotropic_errorBox_of_deleted_box_gamma_hierarchy
    W hrank S (controlIntegerBox S m) t hcentered
      (fun j ↦ S.widths j - 1) hcontain
  · intro j
    exact sourceWidth_mul_deletedBoxSideProduct_controlIntegerBox_le S m j
  · positivity
  · exact hgamma
  · exact hrho
  · exact hvolume
  · exact hdet
  · simpa only using hhierarchy

/-- Anisotropic zonotope rounding in the packaged `IsZonotopePoint` form. -/
theorem zonotope_rounding_anisotropic {d : ℕ}
    (A : Finset (LatticePoint d)) (x : Fin d → ℝ)
    (width : Fin d → ℝ) (hx : Zonotope.IsZonotopePoint A x)
    (hwidth : ∀ i, 0 < width i)
    (hA : ∀ a ∈ A, ∀ i, |(a i : ℝ)| ≤ width i) :
    ∃ T : Finset (LatticePoint d), T ⊆ A ∧ ∀ i,
      |x i - ∑ a ∈ T, (a i : ℝ)| ≤
        Real.sqrt (((d * A.card : ℕ) : ℝ)) * width i := by
  obtain ⟨c, hc, hxc⟩ := hx
  obtain ⟨T, hTA, hT⟩ :=
    exists_subset_sum_approximation_anisotropic A c
      (fun a i ↦ (a i : ℝ)) width hc hwidth hA
  refine ⟨T, hTA, ?_⟩
  intro i
  rw [hxc i]
  exact hT i

/-- SideTarget residual absorption with the coordinatewise error widths
preserved.  Its last premise is the exact anisotropic `herrorBox` supplied
by the preceding enhanced-witness theorem. -/
theorem roundingErrorsAbsorbedBy_cfpTranslate_add_of_margin_stepLattice_anisotropic
    {d r structuredDilation margin coveredDilation : ℕ}
    (target core : Finset (LatticePoint d)) (width : Fin d → ℝ)
    (P : GAP d r) (hP : P.Symmetric)
    (translatePoint : LatticePoint d)
    (hwidth : ∀ i, 0 < width i)
    (hcore : ∀ x ∈ core, ∀ i, |(x i : ℝ)| ≤ width i)
    (hcoreL : ∀ x ∈ core, x ∈ gapStepLattice P)
    (htarget : ∀ z ∈ target,
      ∃ p ∈ CFP.translate translatePoint
          (P.dilate structuredDilation).carrier,
        ∃ x : LatticePoint d,
          Zonotope.IsZonotopePoint core (fun i ↦ (x i : ℝ)) ∧
          x ∈ gapStepLattice P ∧ z = p + x)
    (hscale : structuredDilation + margin ≤ coveredDilation)
    (herrorBox : ∀ e : LatticePoint d, e ∈ gapStepLattice P →
      (∀ i, |(e i : ℝ)| ≤
        Real.sqrt (((d * core.card : ℕ) : ℝ)) * width i) →
      e ∈ (P.dilate margin).carrier) :
    RoundingErrorsAbsorbedBy target core
      (CFP.translate translatePoint
        (P.dilate coveredDilation).carrier) := by
  intro z hz
  obtain ⟨p, hp, x, hxZ, hxL, rfl⟩ := htarget z hz
  obtain ⟨T, hTcore, hTerror⟩ :=
    zonotope_rounding_anisotropic core (fun i ↦ (x i : ℝ)) width hxZ
      hwidth hcore
  have hsumL : (∑ y ∈ T, y) ∈ gapStepLattice P := by
    exact AddSubgroup.sum_mem _ fun y hy ↦ hcoreL y (hTcore hy)
  have herrL : x - ∑ y ∈ T, y ∈ gapStepLattice P :=
    AddSubgroup.sub_mem _ hxL hsumL
  have herrMargin : x - ∑ y ∈ T, y ∈ (P.dilate margin).carrier := by
    apply herrorBox _ herrL
    intro i
    simpa [Finset.sum_apply] using hTerror i
  refine ⟨T, hTcore, ?_⟩
  rw [add_sub_assoc]
  exact add_mem_translate_dilate_of_margin P hP translatePoint hscale hp
    herrMargin

end

end Erdos186.PZ.Intersection
