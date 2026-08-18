/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientThickness
import ErdosProblems.Erdos186.PZ.Intersection.HighCoefficientReverseCoefficient
import ErdosProblems.Erdos186.PZ.Intersection.SourceAnisotropicCoreBounds
import ErdosProblems.Erdos186.PZ.Intersection.NegateWitness

/-!
# Center error for the high-coefficient side selections

The balanced convex-combination center is initially formed from the full
oriented pools.  CFP is instead applied to the subpools on which the
coefficient is at least `theta`.  This file bounds the resulting two losses:

* the omitted low-coefficient generators cost at most
  `|A| * scale * theta * sourceCoordinateWidth`; and
* the subsequent CFP discard, reserve, and translation cost is controlled by
  `canonicalRoundingCore_center_error`.

The reverse estimate is stated for the canonical negation of a witness
selected on `A₂ - a`, so both sides are directly usable with the source
selection package.
-/

namespace Erdos186.PZ.Intersection

open scoped BigOperators

noncomputable section

set_option autoImplicit false

/-- Scaling every coefficient scales the corresponding zonotope center. -/
theorem zonotopeCenter_mul_coefficient
    {d : ℕ} (S : Finset (LatticePoint d))
    (q : LatticePoint d → ℝ) (scale : ℝ) :
    zonotopeCenter S (fun x ↦ scale * q x) =
      fun i ↦ scale * zonotopeCenter S q i := by
  funext i
  simp only [zonotopeCenter]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

/-- Removing generators changes a weighted center by at most the sum of the
coordinatewise budgets of the removed generators. -/
theorem abs_zonotopeCenter_sub_le_card_sdiff_mul_of_abs
    {d : ℕ} {S T : Finset (LatticePoint d)}
    (hTS : T ⊆ S) (q : LatticePoint d → ℝ)
    {coefficientBound coordinateBound : ℝ}
    (hcoefficientBound : 0 ≤ coefficientBound)
    (hq : ∀ x ∈ S \ T, |q x| ≤ coefficientBound)
    (hcoord : ∀ x ∈ S, ∀ i, |(x i : ℝ)| ≤ coordinateBound)
    (i : Fin d) :
    |zonotopeCenter S q i - zonotopeCenter T q i| ≤
      ((S \ T).card : ℝ) * (coefficientBound * coordinateBound) := by
  change |(∑ x ∈ S, q x * (x i : ℝ)) -
      ∑ x ∈ T, q x * (x i : ℝ)| ≤ _
  rw [← Finset.sum_sdiff_eq_sub hTS]
  calc
    |∑ x ∈ S \ T, q x * (x i : ℝ)| ≤
        ∑ x ∈ S \ T, |q x * (x i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ S \ T, coefficientBound * coordinateBound := by
      apply Finset.sum_le_sum
      intro x hx
      rw [abs_mul]
      exact mul_le_mul (hq x hx)
        (hcoord x (Finset.mem_sdiff.mp hx).1 i) (abs_nonneg _)
        hcoefficientBound
    _ = ((S \ T).card : ℝ) *
        (coefficientBound * coordinateBound) := by simp

/-- A source coefficient box bounds every coordinate of either orientation
of every deviation from another point in the box. -/
theorem orientedTranslate_sourceCoordinateBound
    {ambient r : ℕ} (P : GAP ambient r)
    {X : Finset (LatticePoint r)} {a : LatticePoint r}
    (hX : X ⊆ (gapCoefficientBox P).carrier)
    (ha : a ∈ (gapCoefficientBox P).carrier)
    (orientation : Orientation) :
    ∀ y ∈ orientedTranslate orientation a X, ∀ i,
      |(y i : ℝ)| ≤ (sourceCoordinateWidth P : ℝ) := by
  intro y hy i
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
  have hdiff := Reduction.GAP.sub_mem_differenceCoefficientGAP_of_mem
    P (hX hx) ha
  have hbound :=
    abs_coordinate_le_sourceCoordinateWidth_of_mem_difference
      P (x - a) hdiff i
  cases orientation with
  | forward => exact hbound
  | reverse =>
      simpa only [orientedDeviation, Pi.sub_apply, Int.cast_sub,
        abs_sub_comm] using hbound

namespace ConvexPoolsData

variable {d : ℕ} {Acore : Finset (LatticePoint d)}
    {a₀ : realImage Acore} {c : realImage Acore → ℝ} {mu : ℝ}

/-- The forward scaled coefficients scale every restricted center, not only
the full pool center. -/
theorem zonotopeCenter_scaledForwardCoefficient
    (D : ConvexPoolsData Acore a₀ c mu)
    (S : Finset (LatticePoint d)) (scale : ℝ) :
    zonotopeCenter S (D.scaledForwardCoefficient scale) =
      fun i ↦ scale * zonotopeCenter S D.forwardCoefficient i := by
  exact zonotopeCenter_mul_coefficient S D.forwardCoefficient scale

/-- The reverse scaled coefficients obey the same scaling identity. -/
theorem zonotopeCenter_scaledReverseCoefficient
    (D : ConvexPoolsData Acore a₀ c mu)
    (S : Finset (LatticePoint d)) (scale : ℝ) :
    zonotopeCenter S (D.scaledReverseCoefficient scale) =
      fun i ↦ scale * zonotopeCenter S D.reverseCoefficient i := by
  exact zonotopeCenter_mul_coefficient S D.reverseCoefficient scale

/-- After uniform scaling, the two full oriented deviation pools retain the
same balanced center. -/
theorem zonotopeCenter_scaledForward_eq_scaledReverse
    (D : ConvexPoolsData Acore a₀ c mu) (scale : ℝ) :
    zonotopeCenter (orientedTranslate .forward D.a D.A₁)
        (D.scaledForwardCoefficient scale) =
      zonotopeCenter (orientedTranslate .reverse D.a D.A₂)
        (D.scaledReverseCoefficient scale) := by
  rw [D.zonotopeCenter_scaledForwardCoefficient,
    D.zonotopeCenter_scaledReverseCoefficient,
    D.zonotopeCenter_forward_eq_reverse]

/-- All generators in the full forward oriented pool inherit the scalar
source-coordinate bound. -/
theorem fullForward_sourceCoordinateBound
    (D : ConvexPoolsData Acore a₀ c mu)
    {ambient : ℕ} (P : GAP ambient d)
    (hAcore : Acore ⊆ (gapCoefficientBox P).carrier) :
    ∀ y ∈ orientedTranslate .forward D.a D.A₁, ∀ i,
      |(y i : ℝ)| ≤ (sourceCoordinateWidth P : ℝ) := by
  exact orientedTranslate_sourceCoordinateBound P
    ((D.A₁_subset_erase.trans (Finset.erase_subset _ _)).trans hAcore)
    (hAcore D.a_mem) Orientation.forward

/-- All generators in the full reverse oriented pool inherit the same scalar
source-coordinate bound. -/
theorem fullReverse_sourceCoordinateBound
    (D : ConvexPoolsData Acore a₀ c mu)
    {ambient : ℕ} (P : GAP ambient d)
    (hAcore : Acore ⊆ (gapCoefficientBox P).carrier) :
    ∀ y ∈ orientedTranslate .reverse D.a D.A₂, ∀ i,
      |(y i : ℝ)| ≤ (sourceCoordinateWidth P : ℝ) := by
  exact orientedTranslate_sourceCoordinateBound P
    ((D.A₂_subset_erase.trans (Finset.erase_subset _ _)).trans hAcore)
    (hAcore D.a_mem) Orientation.reverse

/-- Omitting the coefficients below `theta` from the forward oriented pool
costs at most `|Acore| * scale * theta * sourceCoordinateWidth` in each
coordinate. -/
theorem fullForward_sub_high_center_le
    (D : ConvexPoolsData Acore a₀ c mu)
    {ambient : ℕ} (P : GAP ambient d)
    (hAcore : Acore ⊆ (gapCoefficientBox P).carrier)
    {theta scale : ℝ} (htheta : 0 ≤ theta) (hscale : 0 ≤ scale)
    (i : Fin d) :
    |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
          (D.scaledForwardCoefficient scale) i -
        zonotopeCenter
          (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
          (D.scaledForwardCoefficient scale) i| ≤
      (Acore.card : ℝ) * scale * theta *
        (sourceCoordinateWidth P : ℝ) := by
  let S := orientedTranslate .forward D.a D.A₁
  let T := Reduction.identifiedTranslate (D.largeA₁ theta) D.a
  have hTS : T ⊆ S := by
    dsimp only [T, S]
    rw [← orientedTranslate_forward_eq_identifiedTranslate]
    exact Finset.image_mono (orientedDeviation .forward D.a)
      (D.largeA₁_subset theta)
  have hq : ∀ y ∈ S \ T,
      |D.scaledForwardCoefficient scale y| ≤ scale * theta := by
    intro y hy
    have hyS := (Finset.mem_sdiff.mp hy).1
    have hyT := (Finset.mem_sdiff.mp hy).2
    have hlow : D.forwardCoefficient y < theta := by
      by_contra hnot
      have hge : theta ≤ D.forwardCoefficient y := le_of_not_gt hnot
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hyS
      apply hyT
      change y ∈ Reduction.identifiedTranslate (D.largeA₁ theta) D.a
      rw [← orientedTranslate_forward_eq_identifiedTranslate]
      refine Finset.mem_image.mpr ⟨x, ?_, hxy⟩
      rw [largeA₁, largeCoefficientPool, Finset.mem_filter]
      refine ⟨hx, ?_⟩
      rw [← hxy] at hge
      simpa only [orientedDeviation, forwardCoefficient_deviation] using hge
    change |scale * D.forwardCoefficient y| ≤ scale * theta
    rw [abs_of_nonneg (mul_nonneg hscale
      (D.forwardCoefficient_bounds hyS).1)]
    exact mul_le_mul_of_nonneg_left hlow.le hscale
  have hwidth : 0 ≤ (sourceCoordinateWidth P : ℝ) := by positivity
  have homit := abs_zonotopeCenter_sub_le_card_sdiff_mul_of_abs
    hTS (D.scaledForwardCoefficient scale)
      (mul_nonneg hscale htheta) hq
      (D.fullForward_sourceCoordinateBound P hAcore) i
  have hcardNat : (S \ T).card ≤ Acore.card := by
    calc
      (S \ T).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
      _ = D.A₁.card := by simp only [S, card_orientedTranslate]
      _ ≤ Acore.card := Finset.card_le_card
        (D.A₁_subset_erase.trans (Finset.erase_subset _ _))
  have hcard : ((S \ T).card : ℝ) ≤ (Acore.card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
          (D.scaledForwardCoefficient scale) i -
        zonotopeCenter
          (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
          (D.scaledForwardCoefficient scale) i| ≤
        ((S \ T).card : ℝ) *
          ((scale * theta) * (sourceCoordinateWidth P : ℝ)) := by
      simpa only [S, T] using homit
    _ ≤ (Acore.card : ℝ) *
        ((scale * theta) * (sourceCoordinateWidth P : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (mul_nonneg hscale htheta) hwidth)
    _ = (Acore.card : ℝ) * scale * theta *
        (sourceCoordinateWidth P : ℝ) := by ring

/-- Reverse-side analogue of `fullForward_sub_high_center_le`. -/
theorem fullReverse_sub_high_center_le
    (D : ConvexPoolsData Acore a₀ c mu)
    {ambient : ℕ} (P : GAP ambient d)
    (hAcore : Acore ⊆ (gapCoefficientBox P).carrier)
    {theta scale : ℝ} (htheta : 0 ≤ theta) (hscale : 0 ≤ scale)
    (i : Fin d) :
    |zonotopeCenter (orientedTranslate .reverse D.a D.A₂)
          (D.scaledReverseCoefficient scale) i -
        zonotopeCenter
          (orientedTranslate .reverse D.a (D.largeA₂ theta))
          (D.scaledReverseCoefficient scale) i| ≤
      (Acore.card : ℝ) * scale * theta *
        (sourceCoordinateWidth P : ℝ) := by
  let S := orientedTranslate .reverse D.a D.A₂
  let T := orientedTranslate .reverse D.a (D.largeA₂ theta)
  have hTS : T ⊆ S := by
    dsimp only [T, S, orientedTranslate]
    exact Finset.image_mono (orientedDeviation .reverse D.a)
      (D.largeA₂_subset theta)
  have hq : ∀ y ∈ S \ T,
      |D.scaledReverseCoefficient scale y| ≤ scale * theta := by
    intro y hy
    have hyS := (Finset.mem_sdiff.mp hy).1
    have hyT := (Finset.mem_sdiff.mp hy).2
    have hlow : D.reverseCoefficient y < theta := by
      by_contra hnot
      have hge : theta ≤ D.reverseCoefficient y := le_of_not_gt hnot
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hyS
      apply hyT
      refine Finset.mem_image.mpr ⟨x, ?_, hxy⟩
      rw [largeA₂, largeCoefficientPool, Finset.mem_filter]
      refine ⟨hx, ?_⟩
      rw [← hxy] at hge
      simpa only [orientedDeviation, reverseCoefficient_deviation] using hge
    change |scale * D.reverseCoefficient y| ≤ scale * theta
    rw [abs_of_nonneg (mul_nonneg hscale
      (D.reverseCoefficient_bounds hyS).1)]
    exact mul_le_mul_of_nonneg_left hlow.le hscale
  have hwidth : 0 ≤ (sourceCoordinateWidth P : ℝ) := by positivity
  have homit := abs_zonotopeCenter_sub_le_card_sdiff_mul_of_abs
    hTS (D.scaledReverseCoefficient scale)
      (mul_nonneg hscale htheta) hq
      (D.fullReverse_sourceCoordinateBound P hAcore) i
  have hcardNat : (S \ T).card ≤ Acore.card := by
    calc
      (S \ T).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
      _ = D.A₂.card := by simp only [S, card_orientedTranslate]
      _ ≤ Acore.card := Finset.card_le_card
        (D.A₂_subset_erase.trans (Finset.erase_subset _ _))
  have hcard : ((S \ T).card : ℝ) ≤ (Acore.card : ℝ) := by
    exact_mod_cast hcardNat
  calc
    |zonotopeCenter (orientedTranslate .reverse D.a D.A₂)
          (D.scaledReverseCoefficient scale) i -
        zonotopeCenter
          (orientedTranslate .reverse D.a (D.largeA₂ theta))
          (D.scaledReverseCoefficient scale) i| ≤
        ((S \ T).card : ℝ) *
          ((scale * theta) * (sourceCoordinateWidth P : ℝ)) := by
      simpa only [S, T] using homit
    _ ≤ (Acore.card : ℝ) *
        ((scale * theta) * (sourceCoordinateWidth P : ℝ)) :=
      mul_le_mul_of_nonneg_right hcard
        (mul_nonneg (mul_nonneg hscale htheta) hwidth)
    _ = (Acore.card : ℝ) * scale * theta *
        (sourceCoordinateWidth P : ℝ) := by ring

/-- The common full balanced center is close to the forward high-coefficient
canonical CFP center. -/
theorem fullBalancedCenter_forward_center_error
    (D : ConvexPoolsData Acore a₀ c mu)
    {ambient : ℕ} (P : GAP ambient d)
    (hAcore : Acore ⊆ (gapCoefficientBox P).carrier)
    {theta scale : ℝ} (htheta : 0 ≤ theta) (hscale : 0 ≤ scale)
    (hhalf : scale * (mu * Acore.card)⁻¹ ≤ (1 : ℝ) / 2)
    {s Dmax k loss : ℕ}
    (W : CFP.EnhancedCFPWitness
      (Reduction.identifiedTranslate (D.largeA₁ theta) D.a)
      s Dmax k loss)
    (i : Fin d) :
    |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
          (D.scaledForwardCoefficient scale) i -
        (realVector W.translatePoint +
          zonotopeCenter (canonicalRoundingCore W)
            (D.scaledForwardCoefficient scale)) i| ≤
      (Acore.card : ℝ) * scale * theta *
          (sourceCoordinateWidth P : ℝ) +
        ((((loss + s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 * (sourceCoordinateWidth P : ℝ))) +
          (s : ℝ) * (sourceCoordinateWidth P : ℝ)) := by
  let T := Reduction.identifiedTranslate (D.largeA₁ theta) D.a
  have hTfull : T ⊆ orientedTranslate .forward D.a D.A₁ := by
    dsimp only [T]
    rw [← orientedTranslate_forward_eq_identifiedTranslate]
    exact Finset.image_mono (orientedDeviation .forward D.a)
      (D.largeA₁_subset theta)
  have hq : ∀ y ∈ T,
      0 ≤ D.scaledForwardCoefficient scale y ∧
        D.scaledForwardCoefficient scale y ≤ (1 : ℝ) / 2 := by
    intro y hy
    have hb := D.forwardCoefficient_bounds (hTfull hy)
    exact ⟨mul_nonneg hscale hb.1,
      (mul_le_mul_of_nonneg_left hb.2 hscale).trans hhalf⟩
  have hbound : ∀ y ∈ T, ∀ j,
      |(y j : ℝ)| ≤ (sourceCoordinateWidth P : ℝ) := by
    intro y hy j
    exact D.fullForward_sourceCoordinateBound P hAcore y (hTfull hy) j
  have hwidth : 0 ≤ (sourceCoordinateWidth P : ℝ) := by positivity
  have hround := canonicalRoundingCore_center_error W
    (D.scaledForwardCoefficient scale) hwidth hq hbound i
  have homit := D.fullForward_sub_high_center_le P hAcore
    htheta hscale i
  calc
    |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
          (D.scaledForwardCoefficient scale) i -
        (realVector W.translatePoint +
          zonotopeCenter (canonicalRoundingCore W)
            (D.scaledForwardCoefficient scale)) i| ≤
        |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
            (D.scaledForwardCoefficient scale) i -
          zonotopeCenter T (D.scaledForwardCoefficient scale) i| +
        |zonotopeCenter T (D.scaledForwardCoefficient scale) i -
          (realVector W.translatePoint +
            zonotopeCenter (canonicalRoundingCore W)
              (D.scaledForwardCoefficient scale)) i| := by
      exact abs_sub_le _ _ _
    _ ≤ (Acore.card : ℝ) * scale * theta *
          (sourceCoordinateWidth P : ℝ) +
        ((((loss + s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 * (sourceCoordinateWidth P : ℝ))) +
          (s : ℝ) * (sourceCoordinateWidth P : ℝ)) := by
      exact add_le_add (by simpa only [T] using homit)
        (by simpa only [T] using hround)

/-- The same common full balanced center is close to the reverse canonical
center obtained by negating a witness selected on `A₂ - a`. -/
theorem fullBalancedCenter_reverse_center_error
    (D : ConvexPoolsData Acore a₀ c mu)
    {ambient : ℕ} (P : GAP ambient d)
    (hAcore : Acore ⊆ (gapCoefficientBox P).carrier)
    {theta scale : ℝ} (htheta : 0 ≤ theta) (hscale : 0 ≤ scale)
    (hhalf : scale * (mu * Acore.card)⁻¹ ≤ (1 : ℝ) / 2)
    {s Dmax k loss : ℕ}
    (W : CFP.EnhancedCFPWitness
      (Reduction.identifiedTranslate (D.largeA₂ theta) D.a)
      s Dmax k loss)
    (i : Fin d) :
    let Wreverse := reverseEnhancedCFPWitnessOfIdentifiedTranslate
      D.a (D.largeA₂ theta) W
    |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
          (D.scaledForwardCoefficient scale) i -
        (realVector Wreverse.translatePoint +
          zonotopeCenter (canonicalRoundingCore Wreverse)
            (D.scaledReverseCoefficient scale)) i| ≤
      (Acore.card : ℝ) * scale * theta *
          (sourceCoordinateWidth P : ℝ) +
        ((((loss + s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 * (sourceCoordinateWidth P : ℝ))) +
          (s : ℝ) * (sourceCoordinateWidth P : ℝ)) := by
  let Wreverse := reverseEnhancedCFPWitnessOfIdentifiedTranslate
    D.a (D.largeA₂ theta) W
  let T := orientedTranslate .reverse D.a (D.largeA₂ theta)
  have hTfull : T ⊆ orientedTranslate .reverse D.a D.A₂ := by
    dsimp only [T, orientedTranslate]
    exact Finset.image_mono (orientedDeviation .reverse D.a)
      (D.largeA₂_subset theta)
  have hq : ∀ y ∈ T,
      0 ≤ D.scaledReverseCoefficient scale y ∧
        D.scaledReverseCoefficient scale y ≤ (1 : ℝ) / 2 := by
    intro y hy
    have hb := D.reverseCoefficient_bounds (hTfull hy)
    exact ⟨mul_nonneg hscale hb.1,
      (mul_le_mul_of_nonneg_left hb.2 hscale).trans hhalf⟩
  have hbound : ∀ y ∈ T, ∀ j,
      |(y j : ℝ)| ≤ (sourceCoordinateWidth P : ℝ) := by
    intro y hy j
    exact D.fullReverse_sourceCoordinateBound P hAcore y (hTfull hy) j
  have hwidth : 0 ≤ (sourceCoordinateWidth P : ℝ) := by positivity
  have hround := canonicalRoundingCore_center_error Wreverse
    (D.scaledReverseCoefficient scale) hwidth hq hbound i
  have homit := D.fullReverse_sub_high_center_le P hAcore
    htheta hscale i
  rw [D.zonotopeCenter_scaledForward_eq_scaledReverse scale]
  calc
    |zonotopeCenter (orientedTranslate .reverse D.a D.A₂)
          (D.scaledReverseCoefficient scale) i -
        (realVector Wreverse.translatePoint +
          zonotopeCenter (canonicalRoundingCore Wreverse)
            (D.scaledReverseCoefficient scale)) i| ≤
        |zonotopeCenter (orientedTranslate .reverse D.a D.A₂)
            (D.scaledReverseCoefficient scale) i -
          zonotopeCenter T (D.scaledReverseCoefficient scale) i| +
        |zonotopeCenter T (D.scaledReverseCoefficient scale) i -
          (realVector Wreverse.translatePoint +
            zonotopeCenter (canonicalRoundingCore Wreverse)
              (D.scaledReverseCoefficient scale)) i| := by
      exact abs_sub_le _ _ _
    _ ≤ (Acore.card : ℝ) * scale * theta *
          (sourceCoordinateWidth P : ℝ) +
        ((((loss + s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 * (sourceCoordinateWidth P : ℝ))) +
          (s : ℝ) * (sourceCoordinateWidth P : ℝ)) := by
      exact add_le_add (by simpa only [T] using homit)
        (by simpa only [T, Wreverse] using hround)

/-- Adapter for a forward witness already presented on the oriented
high-coefficient pool.  This has the same center and error as
`fullBalancedCenter_forward_center_error`, but avoids transporting the
witness through the equality between the two forward-translation notations. -/
theorem fullBalancedCenter_forwardOriented_center_error
    (D : ConvexPoolsData Acore a₀ c mu)
    {ambient : ℕ} (P : GAP ambient d)
    (hAcore : Acore ⊆ (gapCoefficientBox P).carrier)
    {theta scale : ℝ} (htheta : 0 ≤ theta) (hscale : 0 ≤ scale)
    (hhalf : scale * (mu * Acore.card)⁻¹ ≤ (1 : ℝ) / 2)
    {s Dmax k loss : ℕ}
    (W : CFP.EnhancedCFPWitness
      (orientedTranslate .forward D.a (D.largeA₁ theta))
      s Dmax k loss)
    (i : Fin d) :
    |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
          (D.scaledForwardCoefficient scale) i -
        (realVector W.translatePoint +
          zonotopeCenter (canonicalRoundingCore W)
            (D.scaledForwardCoefficient scale)) i| ≤
      (Acore.card : ℝ) * scale * theta *
          (sourceCoordinateWidth P : ℝ) +
        ((((loss + s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 * (sourceCoordinateWidth P : ℝ))) +
          (s : ℝ) * (sourceCoordinateWidth P : ℝ)) := by
  let T := orientedTranslate .forward D.a (D.largeA₁ theta)
  have hTfull : T ⊆ orientedTranslate .forward D.a D.A₁ := by
    dsimp only [T, orientedTranslate]
    exact Finset.image_mono (orientedDeviation .forward D.a)
      (D.largeA₁_subset theta)
  have hq : ∀ y ∈ T,
      0 ≤ D.scaledForwardCoefficient scale y ∧
        D.scaledForwardCoefficient scale y ≤ (1 : ℝ) / 2 := by
    intro y hy
    have hb := D.forwardCoefficient_bounds (hTfull hy)
    exact ⟨mul_nonneg hscale hb.1,
      (mul_le_mul_of_nonneg_left hb.2 hscale).trans hhalf⟩
  have hbound : ∀ y ∈ T, ∀ j,
      |(y j : ℝ)| ≤ (sourceCoordinateWidth P : ℝ) := by
    intro y hy j
    exact D.fullForward_sourceCoordinateBound P hAcore y (hTfull hy) j
  have hwidth : 0 ≤ (sourceCoordinateWidth P : ℝ) := by positivity
  have hround := canonicalRoundingCore_center_error W
    (D.scaledForwardCoefficient scale) hwidth hq hbound i
  have homit := D.fullForward_sub_high_center_le P hAcore
    htheta hscale i
  have homitOriented :
      |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
            (D.scaledForwardCoefficient scale) i -
          zonotopeCenter T (D.scaledForwardCoefficient scale) i| ≤
        (Acore.card : ℝ) * scale * theta *
          (sourceCoordinateWidth P : ℝ) := by
    simpa only [T, orientedTranslate_forward_eq_identifiedTranslate] using homit
  calc
    |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
          (D.scaledForwardCoefficient scale) i -
        (realVector W.translatePoint +
          zonotopeCenter (canonicalRoundingCore W)
            (D.scaledForwardCoefficient scale)) i| ≤
        |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
            (D.scaledForwardCoefficient scale) i -
          zonotopeCenter T (D.scaledForwardCoefficient scale) i| +
        |zonotopeCenter T (D.scaledForwardCoefficient scale) i -
          (realVector W.translatePoint +
            zonotopeCenter (canonicalRoundingCore W)
              (D.scaledForwardCoefficient scale)) i| := by
      exact abs_sub_le _ _ _
    _ ≤ (Acore.card : ℝ) * scale * theta *
          (sourceCoordinateWidth P : ℝ) +
        ((((loss + s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 * (sourceCoordinateWidth P : ℝ))) +
          (s : ℝ) * (sourceCoordinateWidth P : ℝ)) := by
      exact add_le_add homitOriented (by simpa only [T] using hround)

/-- Adapter for a reverse witness already presented on the oriented
high-coefficient pool.  Its left-hand side uses the forward full-pool
expression for the common balanced center. -/
theorem fullBalancedCenter_reverseOriented_center_error
    (D : ConvexPoolsData Acore a₀ c mu)
    {ambient : ℕ} (P : GAP ambient d)
    (hAcore : Acore ⊆ (gapCoefficientBox P).carrier)
    {theta scale : ℝ} (htheta : 0 ≤ theta) (hscale : 0 ≤ scale)
    (hhalf : scale * (mu * Acore.card)⁻¹ ≤ (1 : ℝ) / 2)
    {s Dmax k loss : ℕ}
    (W : CFP.EnhancedCFPWitness
      (orientedTranslate .reverse D.a (D.largeA₂ theta))
      s Dmax k loss)
    (i : Fin d) :
    |zonotopeCenter (orientedTranslate .forward D.a D.A₁)
          (D.scaledForwardCoefficient scale) i -
        (realVector W.translatePoint +
          zonotopeCenter (canonicalRoundingCore W)
            (D.scaledReverseCoefficient scale)) i| ≤
      (Acore.card : ℝ) * scale * theta *
          (sourceCoordinateWidth P : ℝ) +
        ((((loss + s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 * (sourceCoordinateWidth P : ℝ))) +
          (s : ℝ) * (sourceCoordinateWidth P : ℝ)) := by
  let T := orientedTranslate .reverse D.a (D.largeA₂ theta)
  have hTfull : T ⊆ orientedTranslate .reverse D.a D.A₂ := by
    dsimp only [T, orientedTranslate]
    exact Finset.image_mono (orientedDeviation .reverse D.a)
      (D.largeA₂_subset theta)
  have hq : ∀ y ∈ T,
      0 ≤ D.scaledReverseCoefficient scale y ∧
        D.scaledReverseCoefficient scale y ≤ (1 : ℝ) / 2 := by
    intro y hy
    have hb := D.reverseCoefficient_bounds (hTfull hy)
    exact ⟨mul_nonneg hscale hb.1,
      (mul_le_mul_of_nonneg_left hb.2 hscale).trans hhalf⟩
  have hbound : ∀ y ∈ T, ∀ j,
      |(y j : ℝ)| ≤ (sourceCoordinateWidth P : ℝ) := by
    intro y hy j
    exact D.fullReverse_sourceCoordinateBound P hAcore y (hTfull hy) j
  have hwidth : 0 ≤ (sourceCoordinateWidth P : ℝ) := by positivity
  have hround := canonicalRoundingCore_center_error W
    (D.scaledReverseCoefficient scale) hwidth hq hbound i
  have homit := D.fullReverse_sub_high_center_le P hAcore
    htheta hscale i
  rw [D.zonotopeCenter_scaledForward_eq_scaledReverse scale]
  calc
    |zonotopeCenter (orientedTranslate .reverse D.a D.A₂)
          (D.scaledReverseCoefficient scale) i -
        (realVector W.translatePoint +
          zonotopeCenter (canonicalRoundingCore W)
            (D.scaledReverseCoefficient scale)) i| ≤
        |zonotopeCenter (orientedTranslate .reverse D.a D.A₂)
            (D.scaledReverseCoefficient scale) i -
          zonotopeCenter T (D.scaledReverseCoefficient scale) i| +
        |zonotopeCenter T (D.scaledReverseCoefficient scale) i -
          (realVector W.translatePoint +
            zonotopeCenter (canonicalRoundingCore W)
              (D.scaledReverseCoefficient scale)) i| := by
      exact abs_sub_le _ _ _
    _ ≤ (Acore.card : ℝ) * scale * theta *
          (sourceCoordinateWidth P : ℝ) +
        ((((loss + s : ℕ) : ℝ) *
            ((1 : ℝ) / 2 * (sourceCoordinateWidth P : ℝ))) +
          (s : ℝ) * (sourceCoordinateWidth P : ℝ)) := by
      exact add_le_add (by simpa only [T] using homit)
        (by simpa only [T] using hround)

end ConvexPoolsData

end

end Erdos186.PZ.Intersection
