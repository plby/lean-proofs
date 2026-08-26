import ErdosProblems.Erdos1038.CircleDensityLayerCake

/-!
# Set energies of terminal shells

This file identifies the logarithmic set-energy of a terminal shell with
the four numerical two-arc energies used by `CircleTerminalShell`.
-/

set_option warningAsError false

open Metric Set MeasureTheory
open scoped ENNReal

namespace Erdos1038

noncomputable section

local notation "AngleCircle" => AddCircle (2 * Real.pi)

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Nonnegative logarithmic deficit between two measurable circle sets. -/
def circleSetLogDeficit (A B : Set AngleCircle) : ℝ≥0∞ :=
  ∫⁻ p in A ×ˢ B,
    ENNReal.ofReal (circleLogDeficitAt p.1 p.2) ∂(volume.prod volume)

lemma circleLogDeficitAt_add_add
    (a x y : AngleCircle) :
    circleLogDeficitAt (a + x) (a + y) = circleLogDeficitAt x y := by
  unfold circleLogDeficitAt
  rw [dist_add_left]

lemma circleSetLogDeficit_closedBalls_zero
    (r s d : ℝ) :
    circleSetLogDeficit
        (closedBall (0 : AngleCircle) r)
        (closedBall (d : AngleCircle) s) =
      circleLogTwoArcEnergy r s d := by
  unfold circleSetLogDeficit circleLogTwoArcEnergy
  change (∫⁻ p in closedBall (0 : AngleCircle) r ×ˢ
      closedBall (d : AngleCircle) s,
        Function.uncurry
          (fun x y ↦ ENNReal.ofReal (circleLogDeficitAt x y)) p
        ∂(volume.prod volume)) = _
  rw [setLIntegral_prod _
    measurable_uncurry_circleLogDeficitAt_ofReal.aemeasurable]
  rfl

/-- Simultaneously translating both sets leaves the deficit unchanged. -/
lemma circleSetLogDeficit_preimage_add
    (A B : Set AngleCircle) (a : AngleCircle)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    circleSetLogDeficit
        ((fun z ↦ a + z) ⁻¹' A)
        ((fun z ↦ a + z) ⁻¹' B) =
      circleSetLogDeficit A B := by
  let T : AngleCircle × AngleCircle → AngleCircle × AngleCircle :=
    Prod.map (fun z ↦ a + z) (fun z ↦ a + z)
  have hpreserving : MeasurePreserving T
      (volume.prod volume) (volume.prod volume) :=
    (measurePreserving_add_left volume a).prod
      (measurePreserving_add_left volume a)
  have hsets : T ⁻¹' (A ×ˢ B) =
      ((fun z ↦ a + z) ⁻¹' A) ×ˢ
        ((fun z ↦ a + z) ⁻¹' B) := by
    ext p
    rfl
  have htrans : Measurable (fun z : AngleCircle ↦ a + z) := by
    fun_prop
  unfold circleSetLogDeficit
  change (∫⁻ p in ((fun z ↦ a + z) ⁻¹' A) ×ˢ
        ((fun z ↦ a + z) ⁻¹' B),
      Function.uncurry
        (fun x y ↦ ENNReal.ofReal (circleLogDeficitAt x y)) p
        ∂(volume.prod volume)) = _
  calc
    _ = ∫⁻ p in ((fun z ↦ a + z) ⁻¹' A) ×ˢ
          ((fun z ↦ a + z) ⁻¹' B),
        Function.uncurry
          (fun x y ↦ ENNReal.ofReal (circleLogDeficitAt x y)) (T p)
          ∂(volume.prod volume) := by
      apply setLIntegral_congr_fun
        ((htrans hA).prod (htrans hB))
      intro p _hp
      exact congr_arg ENNReal.ofReal
        (circleLogDeficitAt_add_add a p.1 p.2).symm
    _ = ∫⁻ p in A ×ˢ B,
        Function.uncurry
          (fun x y ↦ ENNReal.ofReal (circleLogDeficitAt x y)) p
          ∂(volume.prod volume) := by
      rw [← hpreserving.setLIntegral_comp_preimage
        (hA.prod hB) measurable_uncurry_circleLogDeficitAt_ofReal]
      rw [hsets]

lemma circleSetLogDeficit_closedBalls_realCenters
    (r s c d : ℝ) :
    circleSetLogDeficit
        (closedBall (c : AngleCircle) r)
        (closedBall (d : AngleCircle) s) =
      circleLogTwoArcEnergy r s (d - c) := by
  have hpreC : (fun z : AngleCircle ↦ (c : AngleCircle) + z) ⁻¹'
      closedBall (c : AngleCircle) r = closedBall 0 r := by
    ext z
    simp [mem_closedBall]
  have hpreD : (fun z : AngleCircle ↦ (c : AngleCircle) + z) ⁻¹'
      closedBall (d : AngleCircle) s =
        closedBall ((d - c : ℝ) : AngleCircle) s := by
    ext z
    simp only [mem_preimage, mem_closedBall]
    have hcenter : (c : AngleCircle) + ((d - c : ℝ) : AngleCircle) =
        (d : AngleCircle) := by
      norm_num
    rw [← hcenter, dist_add_left]
  have htranslate := circleSetLogDeficit_preimage_add
    (closedBall (c : AngleCircle) r)
    (closedBall (d : AngleCircle) s) (c : AngleCircle)
    measurableSet_closedBall measurableSet_closedBall
  rw [hpreC, hpreD] at htranslate
  rw [← htranslate]
  exact circleSetLogDeficit_closedBalls_zero r s (d - c)

lemma circleLogDeficitAt_neg_neg (x y : AngleCircle) :
    circleLogDeficitAt (-x) (-y) = circleLogDeficitAt x y := by
  unfold circleLogDeficitAt
  rw [dist_neg_neg]

/-- Simultaneously reflecting both sets leaves the deficit unchanged. -/
lemma circleSetLogDeficit_preimage_neg
    (A B : Set AngleCircle) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    circleSetLogDeficit ((fun z ↦ -z) ⁻¹' A) ((fun z ↦ -z) ⁻¹' B) =
      circleSetLogDeficit A B := by
  let T : AngleCircle × AngleCircle → AngleCircle × AngleCircle :=
    Prod.map Neg.neg Neg.neg
  have hpreserving : MeasurePreserving T
      (volume.prod volume) (volume.prod volume) :=
    (Measure.measurePreserving_neg volume).prod
      (Measure.measurePreserving_neg volume)
  have hsets : T ⁻¹' (A ×ˢ B) =
      ((fun z ↦ -z) ⁻¹' A) ×ˢ ((fun z ↦ -z) ⁻¹' B) := by
    ext p
    rfl
  have hneg : Measurable (fun z : AngleCircle ↦ -z) := by fun_prop
  unfold circleSetLogDeficit
  change (∫⁻ p in ((fun z ↦ -z) ⁻¹' A) ×ˢ ((fun z ↦ -z) ⁻¹' B),
      Function.uncurry
        (fun x y ↦ ENNReal.ofReal (circleLogDeficitAt x y)) p
        ∂(volume.prod volume)) = _
  calc
    _ = ∫⁻ p in ((fun z ↦ -z) ⁻¹' A) ×ˢ ((fun z ↦ -z) ⁻¹' B),
        Function.uncurry
          (fun x y ↦ ENNReal.ofReal (circleLogDeficitAt x y)) (T p)
          ∂(volume.prod volume) := by
      apply setLIntegral_congr_fun ((hneg hA).prod (hneg hB))
      intro p _hp
      exact congr_arg ENNReal.ofReal
        (circleLogDeficitAt_neg_neg p.1 p.2).symm
    _ = ∫⁻ p in A ×ˢ B,
        Function.uncurry
          (fun x y ↦ ENNReal.ofReal (circleLogDeficitAt x y)) p
          ∂(volume.prod volume) := by
      rw [← hpreserving.setLIntegral_comp_preimage
        (hA.prod hB) measurable_uncurry_circleLogDeficitAt_ofReal]
      rw [hsets]

lemma circleLogTwoArcEnergy_neg_center (r s d : ℝ) :
    circleLogTwoArcEnergy r s (-d) = circleLogTwoArcEnergy r s d := by
  have hpreZero : (fun z : AngleCircle ↦ -z) ⁻¹'
      closedBall (0 : AngleCircle) r = closedBall 0 r := by
    ext z
    simp only [mem_preimage, mem_closedBall]
    have hd : dist (-z) (0 : AngleCircle) = dist z 0 := by
      simpa only [neg_zero] using! (dist_neg_neg z (0 : AngleCircle))
    rw [hd]
  have hpreD : (fun z : AngleCircle ↦ -z) ⁻¹'
      closedBall (d : AngleCircle) s = closedBall ((-d : ℝ) : AngleCircle) s := by
    ext z
    simp only [mem_preimage, mem_closedBall]
    have hd : dist (-z) (d : AngleCircle) =
        dist z ((-d : ℝ) : AngleCircle) := by
      convert! dist_neg_neg z ((-d : ℝ) : AngleCircle) using 1
      norm_num
    rw [hd]
  have hreflect := circleSetLogDeficit_preimage_neg
    (closedBall (0 : AngleCircle) r) (closedBall (d : AngleCircle) s)
    measurableSet_closedBall measurableSet_closedBall
  rw [hpreZero, hpreD, circleSetLogDeficit_closedBalls_zero,
    circleSetLogDeficit_closedBalls_zero] at hreflect
  exact hreflect

lemma circleLogTwoArcEnergy_abs_center (r s d : ℝ) :
    circleLogTwoArcEnergy r s |d| = circleLogTwoArcEnergy r s d := by
  rcases le_total 0 d with hd | hd
  · rw [abs_of_nonneg hd]
  · rw [abs_of_nonpos hd, circleLogTwoArcEnergy_neg_center]

lemma circleLogTwoArcEnergy_center_congr
    (r s d e : ℝ) (hcenter : (d : AngleCircle) = (e : AngleCircle)) :
    circleLogTwoArcEnergy r s d = circleLogTwoArcEnergy r s e := by
  unfold circleLogTwoArcEnergy
  rw [hcenter]

private lemma aedisjoint_prod_left
    {A₁ A₂ B : Set AngleCircle}
    (hA : AEDisjoint volume A₁ A₂) :
    AEDisjoint (volume.prod volume) (A₁ ×ˢ B) (A₂ ×ˢ B) := by
  unfold AEDisjoint
  rw [prod_inter_prod, Measure.prod_prod, hA.eq, zero_mul]

private lemma aedisjoint_prod_right
    {A B₁ B₂ : Set AngleCircle}
    (hB : AEDisjoint volume B₁ B₂) :
    AEDisjoint (volume.prod volume) (A ×ˢ B₁) (A ×ˢ B₂) := by
  unfold AEDisjoint
  rw [prod_inter_prod, Measure.prod_prod, hB.eq, mul_zero]

lemma circleSetLogDeficit_union_left
    {A₁ A₂ B : Set AngleCircle}
    (hA : AEDisjoint volume A₁ A₂)
    (hA₂ : NullMeasurableSet A₂ volume)
    (hB : NullMeasurableSet B volume) :
    circleSetLogDeficit (A₁ ∪ A₂) B =
      circleSetLogDeficit A₁ B + circleSetLogDeficit A₂ B := by
  have hsets : (A₁ ∪ A₂) ×ˢ B = (A₁ ×ˢ B) ∪ (A₂ ×ˢ B) := by
    ext p
    simp only [mem_prod, mem_union]
    tauto
  unfold circleSetLogDeficit
  rw [hsets, Measure.restrict_union₀ (aedisjoint_prod_left hA)
    (hA₂.prod hB), lintegral_add_measure]

lemma circleSetLogDeficit_union_right
    {A B₁ B₂ : Set AngleCircle}
    (hB : AEDisjoint volume B₁ B₂)
    (hA : NullMeasurableSet A volume)
    (hB₂ : NullMeasurableSet B₂ volume) :
    circleSetLogDeficit A (B₁ ∪ B₂) =
      circleSetLogDeficit A B₁ + circleSetLogDeficit A B₂ := by
  have hsets : A ×ˢ (B₁ ∪ B₂) = (A ×ˢ B₁) ∪ (A ×ˢ B₂) := by
    ext p
    simp only [mem_prod, mem_union]
    tauto
  unfold circleSetLogDeficit
  rw [hsets, Measure.restrict_union₀ (aedisjoint_prod_right hB)
    (hA.prod hB₂), lintegral_add_measure]

lemma circleSetLogDeficit_union_union
    {A₁ A₂ B₁ B₂ : Set AngleCircle}
    (hA : AEDisjoint volume A₁ A₂)
    (hB : AEDisjoint volume B₁ B₂)
    (hA₁m : MeasurableSet A₁) (hA₂m : MeasurableSet A₂)
    (hB₁m : MeasurableSet B₁) (hB₂m : MeasurableSet B₂) :
    circleSetLogDeficit (A₁ ∪ A₂) (B₁ ∪ B₂) =
      (circleSetLogDeficit A₁ B₁ + circleSetLogDeficit A₁ B₂) +
        (circleSetLogDeficit A₂ B₁ + circleSetLogDeficit A₂ B₂) := by
  rw [circleSetLogDeficit_union_left hA hA₂m.nullMeasurableSet
    (hB₁m.union hB₂m).nullMeasurableSet]
  rw [circleSetLogDeficit_union_right hB hA₁m.nullMeasurableSet
    hB₂m.nullMeasurableSet]
  rw [circleSetLogDeficit_union_right hB hA₂m.nullMeasurableSet
    hB₂m.nullMeasurableSet]

lemma circleLogTwoArcEnergy_eq_min_wrap
    (r s x : ℝ) :
    circleLogTwoArcEnergy r s x =
      circleLogTwoArcEnergy r s (min x (2 * Real.pi - x)) := by
  rcases le_total x Real.pi with hxpi | hpix
  · rw [min_eq_left (by linarith)]
  · rw [min_eq_right (by linarith)]
    have hcoe : (x : AngleCircle) =
        ((-(2 * Real.pi - x) : ℝ) : AngleCircle) := by
      calc
        (x : AngleCircle) =
            ((-(2 * Real.pi - x) + 2 * Real.pi : ℝ) : AngleCircle) := by
          congr 1
          ring
        _ = ((-(2 * Real.pi - x) : ℝ) : AngleCircle) :=
          AddCircle.coe_add_period (2 * Real.pi) _
    calc
      circleLogTwoArcEnergy r s x =
          circleLogTwoArcEnergy r s (-(2 * Real.pi - x)) :=
        circleLogTwoArcEnergy_center_congr r s _ _ hcoe
      _ = circleLogTwoArcEnergy r s (2 * Real.pi - x) :=
        circleLogTwoArcEnergy_neg_center r s _

lemma addCircle_norm_coe_eq_min_wrap
    (x : ℝ) (hx0 : 0 ≤ x) (hx2pi : x ≤ 2 * Real.pi) :
    ‖(x : AngleCircle)‖ = min x (2 * Real.pi - x) := by
  rcases le_total x Real.pi with hxpi | hpix
  · rw [min_eq_left (by linarith)]
    have hnorm := (AddCircle.norm_coe_eq_abs_iff
      (2 * Real.pi) (by positivity)).2 (by
        rw [abs_of_nonneg hx0, abs_of_pos Real.two_pi_pos]
        linarith)
    rwa [abs_of_nonneg hx0] at hnorm
  · rw [min_eq_right (by linarith)]
    have hcoe : (x : AngleCircle) =
        ((x - 2 * Real.pi : ℝ) : AngleCircle) := by
      calc
        (x : AngleCircle) =
            (((x - 2 * Real.pi) + 2 * Real.pi : ℝ) : AngleCircle) := by
          congr 1
          ring
        _ = ((x - 2 * Real.pi : ℝ) : AngleCircle) :=
          AddCircle.coe_add_period (2 * Real.pi) _
    rw [hcoe]
    have hshift0 : x - 2 * Real.pi ≤ 0 := by linarith
    have hnorm := (AddCircle.norm_coe_eq_abs_iff
      (2 * Real.pi) (by positivity)).2 (by
        rw [abs_of_nonpos hshift0, abs_of_pos Real.two_pi_pos]
        linarith)
    rw [hnorm, abs_of_nonpos hshift0]
    ring

lemma circleArcOverlap_self_eq_zero_of_separated
    {r d : ℝ} (hdiameter : 2 * r ≤ Real.pi)
    (hseparated : 2 * r ≤ d) :
    circleArcOverlap r r d = 0 := by
  have htail : r + r - d ≤ 0 := by linarith
  have hline : lineArcOverlap r r d = 0 := by
    unfold lineArcOverlap
    apply max_eq_left
    exact (min_le_right _ _).trans ((min_le_right _ _).trans htail)
  unfold circleArcOverlap
  rw [hline]
  exact max_eq_right (by linarith)

/-- Positive component of `[-upper,-lower] ∪ [lower,upper]`. -/
def terminalShellPositiveArc (lower upper : ℝ) : Set AngleCircle :=
  closedBall (((upper + lower) / 2 : ℝ) : AngleCircle)
    (terminalShellComponentRadius lower upper)

/-- Negative component of `[-upper,-lower] ∪ [lower,upper]`. -/
def terminalShellNegativeArc (lower upper : ℝ) : Set AngleCircle :=
  closedBall ((-((upper + lower) / 2) : ℝ) : AngleCircle)
    (terminalShellComponentRadius lower upper)

/-- Terminal shell as the union of its positive and negative arcs. -/
def terminalShellSet (lower upper : ℝ) : Set AngleCircle :=
  terminalShellPositiveArc lower upper ∪ terminalShellNegativeArc lower upper

lemma measurableSet_terminalShellPositiveArc (lower upper : ℝ) :
    MeasurableSet (terminalShellPositiveArc lower upper) :=
  measurableSet_closedBall

lemma measurableSet_terminalShellNegativeArc (lower upper : ℝ) :
    MeasurableSet (terminalShellNegativeArc lower upper) :=
  measurableSet_closedBall

lemma terminalShell_components_aedisjoint
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hlowerUpper : lower ≤ upper) (hupper : upper ≤ Real.pi) :
    AEDisjoint volume
      (terminalShellPositiveArc lower upper)
      (terminalShellNegativeArc lower upper) := by
  have hr0 : 0 ≤ terminalShellComponentRadius lower upper := by
    unfold terminalShellComponentRadius
    linarith
  have hrpi : terminalShellComponentRadius lower upper ≤ Real.pi := by
    unfold terminalShellComponentRadius
    linarith [Real.pi_pos]
  let center : ℝ := (upper + lower) / 2
  have hcenter0 : 0 ≤ 2 * center := by
    dsimp only [center]
    linarith
  have hcenter2pi : 2 * center ≤ 2 * Real.pi := by
    dsimp only [center]
    linarith
  have hdist : dist (center : AngleCircle) (-center : AngleCircle) =
      min (2 * center) (2 * Real.pi - 2 * center) := by
    have hgroup : (center : AngleCircle) - (-(center : AngleCircle)) =
        ((2 * center : ℝ) : AngleCircle) := by
      calc
        (center : AngleCircle) - (-(center : AngleCircle)) =
            (center : AngleCircle) + (center : AngleCircle) := by abel
        _ = ((center + center : ℝ) : AngleCircle) := by
          rw [AddCircle.coe_add]
        _ = ((2 * center : ℝ) : AngleCircle) := by
          congr 1
          ring
    calc
      dist (center : AngleCircle) (-center : AngleCircle) =
          ‖((2 * center : ℝ) : AngleCircle)‖ := by
        rw [dist_eq_norm, hgroup]
      _ = min (2 * center) (2 * Real.pi - 2 * center) :=
        addCircle_norm_coe_eq_min_wrap _ hcenter0 hcenter2pi
  have hdiameter : 2 * terminalShellComponentRadius lower upper ≤ Real.pi := by
    unfold terminalShellComponentRadius
    linarith
  have hseparated :
      2 * terminalShellComponentRadius lower upper ≤
        min (2 * center) (2 * Real.pi - 2 * center) := by
    apply le_min
    · dsimp only [center]
      unfold terminalShellComponentRadius
      linarith
    · dsimp only [center]
      unfold terminalShellComponentRadius
      linarith
  unfold AEDisjoint terminalShellPositiveArc terminalShellNegativeArc
  rw [volume_inter_addCircle_closedBalls hr0 hrpi hr0 hrpi]
  change ENNReal.ofReal
      (circleArcOverlap
        (terminalShellComponentRadius lower upper)
        (terminalShellComponentRadius lower upper)
        (dist (center : AngleCircle) (-center : AngleCircle))) = 0
  rw [hdist,
    circleArcOverlap_self_eq_zero_of_separated hdiameter hseparated,
    ENNReal.ofReal_zero]

lemma circleSetLogDeficit_terminalPositive_positive
    (lower₁ upper lower₂ : ℝ) :
    circleSetLogDeficit
        (terminalShellPositiveArc lower₁ upper)
        (terminalShellPositiveArc lower₂ upper) =
      circleLogTwoArcEnergy
        (terminalShellComponentRadius lower₁ upper)
        (terminalShellComponentRadius lower₂ upper)
        (terminalShellSameSignSeparation lower₁ lower₂) := by
  unfold terminalShellPositiveArc
  rw [circleSetLogDeficit_closedBalls_realCenters]
  rw [← circleLogTwoArcEnergy_abs_center]
  congr 1
  unfold terminalShellSameSignSeparation
  have hdiff :
      (upper + lower₂) / 2 - (upper + lower₁) / 2 =
        (lower₂ - lower₁) / 2 := by ring
  rw [hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_sub_comm]

lemma circleSetLogDeficit_terminalNegative_negative
    (lower₁ upper lower₂ : ℝ) :
    circleSetLogDeficit
        (terminalShellNegativeArc lower₁ upper)
        (terminalShellNegativeArc lower₂ upper) =
      circleLogTwoArcEnergy
        (terminalShellComponentRadius lower₁ upper)
        (terminalShellComponentRadius lower₂ upper)
        (terminalShellSameSignSeparation lower₁ lower₂) := by
  unfold terminalShellNegativeArc
  rw [circleSetLogDeficit_closedBalls_realCenters]
  rw [← circleLogTwoArcEnergy_abs_center]
  congr 1
  unfold terminalShellSameSignSeparation
  have hdiff :
      -((upper + lower₂) / 2) - -((upper + lower₁) / 2) =
        (lower₁ - lower₂) / 2 := by ring
  rw [hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

lemma circleSetLogDeficit_terminalPositive_negative
    (lower₁ upper lower₂ : ℝ) :
    circleSetLogDeficit
        (terminalShellPositiveArc lower₁ upper)
        (terminalShellNegativeArc lower₂ upper) =
      circleLogTwoArcEnergy
        (terminalShellComponentRadius lower₁ upper)
        (terminalShellComponentRadius lower₂ upper)
        (terminalShellOppositeSeparation lower₁ upper lower₂) := by
  unfold terminalShellPositiveArc terminalShellNegativeArc
  rw [circleSetLogDeficit_closedBalls_realCenters]
  let x : ℝ := upper + (lower₁ + lower₂) / 2
  have hcenter :
      -((upper + lower₂) / 2) - (upper + lower₁) / 2 = -x := by
    dsimp only [x]
    ring
  rw [hcenter, circleLogTwoArcEnergy_neg_center,
    circleLogTwoArcEnergy_eq_min_wrap]
  rfl

lemma circleSetLogDeficit_terminalNegative_positive
    (lower₁ upper lower₂ : ℝ) :
    circleSetLogDeficit
        (terminalShellNegativeArc lower₁ upper)
        (terminalShellPositiveArc lower₂ upper) =
      circleLogTwoArcEnergy
        (terminalShellComponentRadius lower₁ upper)
        (terminalShellComponentRadius lower₂ upper)
        (terminalShellOppositeSeparation lower₁ upper lower₂) := by
  unfold terminalShellPositiveArc terminalShellNegativeArc
  rw [circleSetLogDeficit_closedBalls_realCenters]
  let x : ℝ := upper + (lower₁ + lower₂) / 2
  have hcenter :
      (upper + lower₂) / 2 - -((upper + lower₁) / 2) = x := by
    dsimp only [x]
    ring
  rw [hcenter, circleLogTwoArcEnergy_eq_min_wrap]
  rfl

/-- Exact four-arc evaluation of the logarithmic deficit between two
terminal shells. -/
theorem circleSetLogDeficit_terminalShellSet
    {lower₁ upper lower₂ : ℝ}
    (hlower₁ : 0 ≤ lower₁) (hlower₂ : 0 ≤ lower₂)
    (hlower₁Upper : lower₁ ≤ upper)
    (hlower₂Upper : lower₂ ≤ upper)
    (hupper : upper ≤ Real.pi) :
    circleSetLogDeficit
        (terminalShellSet lower₁ upper)
        (terminalShellSet lower₂ upper) =
      terminalShellCrossDeficit lower₁ upper lower₂ := by
  unfold terminalShellSet
  rw [circleSetLogDeficit_union_union
    (terminalShell_components_aedisjoint
      hlower₁ hlower₁Upper hupper)
    (terminalShell_components_aedisjoint
      hlower₂ hlower₂Upper hupper)
    (measurableSet_terminalShellPositiveArc lower₁ upper)
    (measurableSet_terminalShellNegativeArc lower₁ upper)
    (measurableSet_terminalShellPositiveArc lower₂ upper)
    (measurableSet_terminalShellNegativeArc lower₂ upper)]
  rw [circleSetLogDeficit_terminalPositive_positive,
    circleSetLogDeficit_terminalPositive_negative,
    circleSetLogDeficit_terminalNegative_positive,
    circleSetLogDeficit_terminalNegative_negative]
  unfold terminalShellCrossDeficit
  simp only [two_mul]
  abel

lemma circleSetLogDeficit_congr
    {A A' B B' : Set AngleCircle}
    (hA : A =ᵐ[volume] A') (hB : B =ᵐ[volume] B') :
    circleSetLogDeficit A B = circleSetLogDeficit A' B' := by
  unfold circleSetLogDeficit
  rw [← Measure.prod_restrict, Measure.restrict_congr_set hA,
    Measure.restrict_congr_set hB, Measure.prod_restrict]

/-- Exact four-arc superlevel evaluation from an a.e. terminal-shell
description of each strict superlevel set. -/
theorem circleSuperlevelLogDeficit_eq_terminalShellCrossDeficit
    {f g : AngleCircle → ℝ} {t s lower₁ upper lower₂ : ℝ}
    (hF : {z | t < f z} =ᵐ[volume] terminalShellSet lower₁ upper)
    (hG : {z | s < g z} =ᵐ[volume] terminalShellSet lower₂ upper)
    (hlower₁ : 0 ≤ lower₁) (hlower₂ : 0 ≤ lower₂)
    (hlower₁Upper : lower₁ ≤ upper)
    (hlower₂Upper : lower₂ ≤ upper)
    (hupper : upper ≤ Real.pi) :
    circleSuperlevelLogDeficit f g t s =
      terminalShellCrossDeficit lower₁ upper lower₂ := by
  change circleSetLogDeficit {z | t < f z} {z | s < g z} = _
  rw [circleSetLogDeficit_congr hF hG]
  exact circleSetLogDeficit_terminalShellSet
    hlower₁ hlower₂ hlower₁Upper hlower₂Upper hupper

lemma coe_mem_terminalShellPositiveArc_iff
    {lower upper q : ℝ} (hlower : 0 ≤ lower)
    (hupper : upper ≤ Real.pi)
    (hq : q ∈ Ioo (-Real.pi) Real.pi) :
    (q : AngleCircle) ∈ terminalShellPositiveArc lower upper ↔
      q ∈ Icc lower upper := by
  let center : ℝ := (upper + lower) / 2
  let radius : ℝ := (upper - lower) / 2
  change q ∈ ((↑) : ℝ → AngleCircle) ⁻¹' closedBall (center : AngleCircle) radius ↔ _
  rw [AddCircle.coe_real_preimage_closedBall_eq_iUnion]
  simp only [mem_iUnion, mem_closedBall, Real.dist_eq]
  rcases hq with ⟨hqlo, hqhi⟩
  constructor
  · rintro ⟨z, hz⟩
    simp only [zsmul_eq_mul] at hz
    have hzBounds : center + (z : ℝ) * (2 * Real.pi) - radius ≤ q ∧
        q ≤ center + (z : ℝ) * (2 * Real.pi) + radius := by
      rw [abs_le] at hz
      constructor <;> linarith
    rcases lt_trichotomy z 0 with hzneg | rfl | hzpos
    · have hzle : (z : ℝ) ≤ -1 := by
        exact_mod_cast (Int.le_sub_one_of_lt hzneg)
      have hzmul : (z : ℝ) * (2 * Real.pi) ≤ -1 * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hzle (by positivity)
      exfalso
      dsimp only [center, radius] at hzBounds
      linarith [Real.pi_pos]
    · dsimp only [center, radius] at hzBounds
      constructor <;> linarith
    · have hzone : (1 : ℝ) ≤ z := by
        exact_mod_cast hzpos
      have hzmul : 1 * (2 * Real.pi) ≤ (z : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hzone (by positivity)
      exfalso
      dsimp only [center, radius] at hzBounds
      linarith [Real.pi_pos]
  · intro hqInterval
    rcases hqInterval with ⟨hqLower, hqUpper⟩
    refine ⟨0, ?_⟩
    norm_num
    dsimp only [center, radius]
    rw [abs_le]
    constructor <;> linarith

lemma coe_mem_terminalShellNegativeArc_iff
    {lower upper q : ℝ} (hlower : 0 ≤ lower)
    (hupper : upper ≤ Real.pi) (hq : q ∈ Ioo (-Real.pi) Real.pi) :
    (q : AngleCircle) ∈ terminalShellNegativeArc lower upper ↔
      q ∈ Icc (-upper) (-lower) := by
  have hqneg : -q ∈ Ioo (-Real.pi) Real.pi := by
    constructor <;> linarith [hq.1, hq.2]
  have hmem :
      ((q : AngleCircle) ∈ terminalShellNegativeArc lower upper) ↔
        (((-q : ℝ) : AngleCircle) ∈ terminalShellPositiveArc lower upper) := by
    unfold terminalShellNegativeArc terminalShellPositiveArc
    simp only [mem_closedBall]
    have hd : dist ((-q : ℝ) : AngleCircle)
        (((upper + lower) / 2 : ℝ) : AngleCircle) =
      dist (q : AngleCircle)
        ((-((upper + lower) / 2) : ℝ) : AngleCircle) := by
      convert! dist_neg_neg (q : AngleCircle)
        ((-((upper + lower) / 2) : ℝ) : AngleCircle) using 1
      norm_num
    rw [hd]
  rw [hmem, coe_mem_terminalShellPositiveArc_iff hlower hupper hqneg]
  constructor <;> intro h
  · constructor <;> linarith [h.1, h.2]
  · constructor <;> linarith [h.1, h.2]

lemma coe_mem_terminalShellSet_iff
    {lower upper q : ℝ} (hlower : 0 ≤ lower)
    (hupper : upper ≤ Real.pi) (hq : q ∈ Ioo (-Real.pi) Real.pi) :
    (q : AngleCircle) ∈ terminalShellSet lower upper ↔
      |q| ∈ Icc lower upper := by
  unfold terminalShellSet
  rw [mem_union, coe_mem_terminalShellPositiveArc_iff hlower hupper hq,
    coe_mem_terminalShellNegativeArc_iff hlower hupper hq]
  rcases le_total 0 q with hq0 | hq0
  · rw [abs_of_nonneg hq0]
    constructor
    · rintro (h | h)
      · exact h
      · constructor <;> linarith [h.1, h.2]
    · exact Or.inl
  · rw [abs_of_nonpos hq0]
    constructor
    · rintro (h | h)
      · constructor <;> linarith [h.1, h.2]
      · constructor <;> linarith [h.1, h.2]
    · intro h
      exact Or.inr ⟨by linarith [h.2], by linarith [h.1]⟩

lemma addCircle_dist_coe_zero_eq_abs
    {q : ℝ} (hq : q ∈ Ioo (-Real.pi) Real.pi) :
    dist (q : AngleCircle) 0 = |q| := by
  rcases hq with ⟨hqlo, hqhi⟩
  rw [dist_eq_norm, sub_zero]
  exact (AddCircle.norm_coe_eq_abs_iff
    (2 * Real.pi) (by positivity)).2 (by
      rw [abs_of_pos Real.two_pi_pos]
      exact abs_le.2 ⟨by linarith, by linarith⟩)

lemma mem_terminalShellSet_iff_dist_mem_Icc_of_ne_antipode
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hupper : upper ≤ Real.pi) {z : AngleCircle}
    (hz : z ≠ (Real.pi : AngleCircle)) :
    z ∈ terminalShellSet lower upper ↔
      dist z 0 ∈ Icc lower upper := by
  let qsub : Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) :=
    AddCircle.equivIoc (2 * Real.pi) (-Real.pi) z
  let q : ℝ := qsub.1
  have hqmem : q ∈ Ioc (-Real.pi) (-Real.pi + 2 * Real.pi) := qsub.2
  have hqcoe : (q : AngleCircle) = z := by
    change (AddCircle.equivIoc (2 * Real.pi) (-Real.pi)).symm qsub = z
    exact Equiv.symm_apply_apply _ _
  have hqne : q ≠ Real.pi := by
    intro hq
    apply hz
    rw [← hqcoe, hq]
  have hqoo : q ∈ Ioo (-Real.pi) Real.pi := by
    constructor
    · exact hqmem.1
    · have hqle : q ≤ Real.pi := by linarith [hqmem.2]
      exact lt_of_le_of_ne hqle hqne
  rw [← hqcoe, coe_mem_terminalShellSet_iff hlower hupper hqoo,
    addCircle_dist_coe_zero_eq_abs hqoo]

/-- A terminal shell is a.e. the radial annulus with the same endpoints.
The only discarded point is the choice of representative at the antipode. -/
theorem terminalShellSet_ae_eq_radial
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hupper : upper ≤ Real.pi) :
    terminalShellSet lower upper =ᵐ[volume]
      {z : AngleCircle | dist z 0 ∈ Icc lower upper} := by
  have hae : ∀ᵐ z ∂(volume : Measure AngleCircle),
      z ∉ ({(Real.pi : AngleCircle)} : Set AngleCircle) := by
    rw [ae_iff]
    simpa only [Classical.not_not] using!
      volume_angleCircle_singleton_zero (Real.pi : AngleCircle)
  filter_upwards [hae] with z hz
  apply propext
  exact mem_terminalShellSet_iff_dist_mem_Icc_of_ne_antipode
    hlower hupper (by simpa only [mem_singleton_iff] using! hz)

lemma volume_radial_level_zero
    {radius : ℝ} (hradius0 : 0 ≤ radius)
    (hradiusPi : radius ≤ Real.pi) :
    volume {z : AngleCircle | dist z 0 ∈ Icc radius radius} = 0 := by
  have hae := terminalShellSet_ae_eq_radial hradius0 hradiusPi
  calc
    volume {z : AngleCircle | dist z 0 ∈ Icc radius radius} =
        volume (terminalShellSet radius radius) := measure_congr hae.symm
    _ = 0 := by
      unfold terminalShellSet terminalShellPositiveArc
        terminalShellNegativeArc terminalShellComponentRadius
      simp only [sub_self, zero_div, closedBall_zero]
      rw [measure_union_null
        (volume_angleCircle_singleton_zero _)
        (volume_angleCircle_singleton_zero _)]

/-- The two half-arcs obtained by compressing a terminal shell into a
centered arc. -/
def centeredCompressionShellSet (lower upper : ℝ) : Set AngleCircle :=
  terminalShellSet 0 (upper - lower)

lemma centeredCompressionShellSet_ae_eq_closedBall
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hlowerUpper : lower ≤ upper) (hupper : upper ≤ Real.pi) :
    centeredCompressionShellSet lower upper =ᵐ[volume]
      closedBall (0 : AngleCircle) (upper - lower) := by
  have hradius0 : 0 ≤ upper - lower := sub_nonneg.mpr hlowerUpper
  have hradiusPi : upper - lower ≤ Real.pi := by linarith
  have hradial := terminalShellSet_ae_eq_radial
    (lower := 0) (upper := upper - lower) (le_refl 0) hradiusPi
  have hset : {z : AngleCircle | dist z 0 ∈ Icc 0 (upper - lower)} =
      closedBall (0 : AngleCircle) (upper - lower) := by
    ext z
    simp only [mem_ofPred_eq, mem_Icc, mem_closedBall]
    exact and_iff_right dist_nonneg
  unfold centeredCompressionShellSet
  rw [hset] at hradial
  exact hradial

/-- The four compressed half-arc interactions are exactly the energy of
the two full centered arcs. -/
theorem centeredTerminalShellCrossDeficit_eq_twoArcEnergy
    {lower₁ upper lower₂ : ℝ}
    (hlower₁ : 0 ≤ lower₁) (hlower₂ : 0 ≤ lower₂)
    (hlower₁Upper : lower₁ ≤ upper)
    (hlower₂Upper : lower₂ ≤ upper)
    (hupper : upper ≤ Real.pi) :
    centeredTerminalShellCrossDeficit lower₁ upper lower₂ =
      circleLogTwoArcEnergy (upper - lower₁) (upper - lower₂) 0 := by
  let Q : ℝ := upper - lower₁
  let R : ℝ := upper - lower₂
  have hQ0 : 0 ≤ Q := by dsimp only [Q]; linarith
  have hR0 : 0 ≤ R := by dsimp only [R]; linarith
  have hQpi : Q ≤ Real.pi := by dsimp only [Q]; linarith
  have hRpi : R ≤ Real.pi := by dsimp only [R]; linarith
  let Qpos := terminalShellPositiveArc 0 Q
  let Qneg := terminalShellNegativeArc 0 Q
  let Rpos := terminalShellPositiveArc 0 R
  let Rneg := terminalShellNegativeArc 0 R
  have hPP : circleSetLogDeficit Qpos Rpos =
      circleLogTwoArcEnergy
        (terminalShellComponentRadius lower₁ upper)
        (terminalShellComponentRadius lower₂ upper)
        (terminalShellSameSignSeparation lower₁ lower₂) := by
    dsimp only [Qpos, Rpos, terminalShellPositiveArc]
    rw [circleSetLogDeficit_closedBalls_realCenters]
    rw [← circleLogTwoArcEnergy_abs_center]
    congr 1
    · unfold terminalShellComponentRadius
      dsimp only [Q]
      ring
    · unfold terminalShellComponentRadius
      dsimp only [R]
      ring
    · unfold terminalShellSameSignSeparation
      dsimp only [Q, R]
      have hdiff :
          (upper - lower₂ + 0) / 2 - (upper - lower₁ + 0) / 2 =
            (lower₁ - lower₂) / 2 := by ring
      rw [hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hNN : circleSetLogDeficit Qneg Rneg =
      circleLogTwoArcEnergy
        (terminalShellComponentRadius lower₁ upper)
        (terminalShellComponentRadius lower₂ upper)
        (terminalShellSameSignSeparation lower₁ lower₂) := by
    dsimp only [Qneg, Rneg, terminalShellNegativeArc]
    rw [circleSetLogDeficit_closedBalls_realCenters]
    rw [← circleLogTwoArcEnergy_abs_center]
    congr 1
    · unfold terminalShellComponentRadius
      dsimp only [Q]
      ring
    · unfold terminalShellComponentRadius
      dsimp only [R]
      ring
    · unfold terminalShellSameSignSeparation
      dsimp only [Q, R]
      have hdiff :
          -((upper - lower₂ + 0) / 2) - -((upper - lower₁ + 0) / 2) =
            (lower₂ - lower₁) / 2 := by ring
      rw [hdiff, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_sub_comm]
  have hPN : circleSetLogDeficit Qpos Rneg =
      circleLogTwoArcEnergy
        (terminalShellComponentRadius lower₁ upper)
        (terminalShellComponentRadius lower₂ upper)
        (centeredCompressionOppositeSeparation lower₁ upper lower₂) := by
    dsimp only [Qpos, Rneg, terminalShellPositiveArc, terminalShellNegativeArc]
    rw [circleSetLogDeficit_closedBalls_realCenters]
    have hcenter :
        -((R + 0) / 2) - (Q + 0) / 2 =
          -(centeredCompressionOppositeSeparation lower₁ upper lower₂) := by
      unfold centeredCompressionOppositeSeparation
      dsimp only [Q, R]
      ring
    rw [hcenter, circleLogTwoArcEnergy_neg_center]
    congr 1
    · unfold terminalShellComponentRadius
      dsimp only [Q]
      ring
    · unfold terminalShellComponentRadius
      dsimp only [R]
      ring
  have hNP : circleSetLogDeficit Qneg Rpos =
      circleLogTwoArcEnergy
        (terminalShellComponentRadius lower₁ upper)
        (terminalShellComponentRadius lower₂ upper)
        (centeredCompressionOppositeSeparation lower₁ upper lower₂) := by
    dsimp only [Qneg, Rpos, terminalShellNegativeArc, terminalShellPositiveArc]
    rw [circleSetLogDeficit_closedBalls_realCenters]
    congr 1
    · unfold terminalShellComponentRadius
      dsimp only [Q]
      ring
    · unfold terminalShellComponentRadius
      dsimp only [R]
      ring
    · unfold centeredCompressionOppositeSeparation
      dsimp only [Q, R]
      ring
  have hsum : circleSetLogDeficit
      (centeredCompressionShellSet lower₁ upper)
      (centeredCompressionShellSet lower₂ upper) =
        centeredTerminalShellCrossDeficit lower₁ upper lower₂ := by
    unfold centeredCompressionShellSet terminalShellSet
    change circleSetLogDeficit (Qpos ∪ Qneg) (Rpos ∪ Rneg) = _
    rw [circleSetLogDeficit_union_union
      (terminalShell_components_aedisjoint
        (lower := 0) (upper := Q) (le_refl 0) hQ0 hQpi)
      (terminalShell_components_aedisjoint
        (lower := 0) (upper := R) (le_refl 0) hR0 hRpi)
      measurableSet_closedBall measurableSet_closedBall
      measurableSet_closedBall measurableSet_closedBall]
    rw [hPP, hPN, hNP, hNN]
    unfold centeredTerminalShellCrossDeficit
    simp only [two_mul]
    abel
  have hsets : circleSetLogDeficit
      (centeredCompressionShellSet lower₁ upper)
      (centeredCompressionShellSet lower₂ upper) =
        circleSetLogDeficit
          (closedBall (0 : AngleCircle) Q)
          (closedBall (0 : AngleCircle) R) := circleSetLogDeficit_congr
    (centeredCompressionShellSet_ae_eq_closedBall
      hlower₁ hlower₁Upper hupper)
    (centeredCompressionShellSet_ae_eq_closedBall
      hlower₂ hlower₂Upper hupper)
  calc
    centeredTerminalShellCrossDeficit lower₁ upper lower₂ =
        circleSetLogDeficit
          (centeredCompressionShellSet lower₁ upper)
          (centeredCompressionShellSet lower₂ upper) := hsum.symm
    _ = circleSetLogDeficit
          (closedBall (0 : AngleCircle) Q)
          (closedBall (0 : AngleCircle) R) := hsets
    _ = circleLogTwoArcEnergy Q R 0 := by
      simpa using! circleSetLogDeficit_closedBalls_zero Q R 0
    _ = circleLogTwoArcEnergy (upper - lower₁) (upper - lower₂) 0 := by
      rfl

/-- After the pointwise four-piece collapse, the centered double layer cake
is simply the double integral of the energies of the two full centered
arcs. -/
theorem centeredTerminalShellLayerCakeDeficit_eq_twoArcEnergy
    (lowerF lowerG : ℝ → ℝ) (upper : ℝ)
    (hlowerF0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ lowerF t)
    (hlowerG0 : ∀ s ∈ Ioi (0 : ℝ), 0 ≤ lowerG s)
    (hlowerFUpper : ∀ t ∈ Ioi (0 : ℝ), lowerF t ≤ upper)
    (hlowerGUpper : ∀ s ∈ Ioi (0 : ℝ), lowerG s ≤ upper)
    (hupper : upper ≤ Real.pi) :
    centeredTerminalShellLayerCakeDeficit lowerF lowerG upper =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
        circleLogTwoArcEnergy
          (upper - lowerF t) (upper - lowerG s) 0 := by
  unfold centeredTerminalShellLayerCakeDeficit
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  exact centeredTerminalShellCrossDeficit_eq_twoArcEnergy
    (hlowerF0 t ht) (hlowerG0 s hs)
    (hlowerFUpper t ht) (hlowerGUpper s hs) hupper

end

end Erdos1038
