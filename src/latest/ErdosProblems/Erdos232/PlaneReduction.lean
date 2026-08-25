/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.TorusSemantics
import Mathlib.MeasureTheory.Integral.Prod

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace Erdos232

noncomputable section

local instance planeReductionMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance planeReductionIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance planeReductionIsProbability :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Coordinate squares in the Euclidean plane -/

/-- The open axis-parallel square of coordinate half-width `r` centered at `c`. -/
def coordinateBox (c : Plane) (r : ℝ) : Set Plane :=
  {x | ∀ i, x i ∈ Ioo (c i - r) (c i + r)}

theorem measurableSet_coordinateBox (c : Plane) (r : ℝ) :
    MeasurableSet (coordinateBox c r) := by
  rw [coordinateBox, show {x : Plane | ∀ i, x i ∈ Ioo (c i - r) (c i + r)} =
      ⋂ i, (fun x : Plane ↦ x i) ⁻¹' Ioo (c i - r) (c i + r) by ext; simp]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_Ioo.preimage
      (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 ↦ ℝ) i).measurable

theorem volumeReal_coordinateBox (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (coordinateBox c r) = (2 * r) ^ 2 := by
  let Q : Set (Fin 2 → ℝ) := Set.pi Set.univ fun i ↦ Ioo (c i - r) (c i + r)
  have hpre : (@WithLp.toLp 2 (Fin 2 → ℝ)) ⁻¹' coordinateBox c r = Q := by
    ext x
    simp [coordinateBox, Q]
  have hmeasure : volume (coordinateBox c r) = volume Q := by
    rw [← hpre]
    exact ((PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
      (measurableSet_coordinateBox c r).nullMeasurableSet).symm
  rw [Measure.real, hmeasure, Real.volume_pi_Ioo_toReal]
  · simp only [Fin.prod_univ_two]
    ring
  · intro i
    linarith

theorem mem_coordinateBox_comm {c x : Plane} {r : ℝ} :
    x ∈ coordinateBox c r ↔ c ∈ coordinateBox x r := by
  simp only [coordinateBox, mem_setOf_eq, mem_Ioo]
  constructor <;> intro h i <;> specialize h i <;> constructor <;> linarith

theorem dist_lt_two_mul_of_mem_coordinateBox
    {c x : Plane} {r : ℝ} (hr : 0 < r) (hcx : c ∈ coordinateBox x r) :
    dist c x < 2 * r := by
  have h0 := hcx 0
  have h1 := hcx 1
  simp only [coordinateBox, mem_setOf_eq, mem_Ioo] at h0 h1
  have hsq : dist c x ^ 2 = (c 0 - x 0) ^ 2 + (c 1 - x 1) ^ 2 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_two]
  have hdist : 0 ≤ dist c x := dist_nonneg
  nlinarith [sq_nonneg (c 0 - x 0 - r), sq_nonneg (c 0 - x 0 + r),
    sq_nonneg (c 1 - x 1 - r), sq_nonneg (c 1 - x 1 + r)]

theorem center_mem_expanded_ball
    {c x : Plane} {r R : ℝ} (hr : 0 < r)
    (hxR : x ∈ ball (0 : Plane) R) (hcx : c ∈ coordinateBox x r) :
    c ∈ ball (0 : Plane) (R + 2 * r) := by
  rw [mem_ball] at hxR ⊢
  have hcx' := dist_lt_two_mul_of_mem_coordinateBox hr hcx
  calc
    dist c 0 ≤ dist c x + dist x 0 := dist_triangle _ _ _
    _ < 2 * r + R := add_lt_add hcx' hxR
    _ = R + 2 * r := by ring

/-! ## Cropping a coordinate square into a square torus -/

/-- Lower endpoint for the canonical representatives of the two unit circles. -/
def centeredFundamentalBase : Fin 2 → ℝ := fun _ ↦ -(1 / 2 : ℝ)

/-- The canonical representative in `(-1/2, 1/2]` of a point of the square torus. -/
def torusRepresentative (y : SquareTorus) : Fin 2 → ℝ :=
  (UnitAddTorus.measurableEquivPiIoc centeredFundamentalBase y).1

theorem measurable_torusRepresentative : Measurable torusRepresentative := by
  exact measurable_subtype_coe.comp
    (UnitAddTorus.measurableEquivPiIoc centeredFundamentalBase).measurable

theorem torusRepresentative_mem (y : SquareTorus) (i : Fin 2) :
    torusRepresentative y i ∈ Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ) := by
  change (AddCircle.equivIoc 1 (centeredFundamentalBase i) (y i)).1 ∈
    Ioc (-(1 / 2 : ℝ)) (1 / 2 : ℝ)
  have h := (AddCircle.equivIoc 1 (centeredFundamentalBase i) (y i)).2
  constructor
  · simpa only [centeredFundamentalBase] using h.1
  · calc
      (AddCircle.equivIoc 1 (centeredFundamentalBase i) (y i)).1 ≤
          centeredFundamentalBase i + 1 := h.2
      _ = 1 / 2 := by simp [centeredFundamentalBase]; norm_num

theorem coe_torusRepresentative (y : SquareTorus) (i : Fin 2) :
    (torusRepresentative y i : UnitAddCircle) = y i := by
  let e := UnitAddTorus.measurableEquivPiIoc centeredFundamentalBase
  have h := congrArg (fun q : SquareTorus ↦ q i) (e.symm_apply_apply y)
  simpa [e, torusRepresentative,
    UnitAddTorus.coe_symm_measurableEquivPiIoc_apply] using h

/-- Interpret a unit-square representative as a physical point in the square of side `L`
centered at `c`. -/
def torusPhysicalPoint (c : Plane) (L : ℝ) (y : SquareTorus) : Plane :=
  WithLp.toLp 2 (fun i ↦ c i + L * torusRepresentative y i)

@[simp] theorem torusPhysicalPoint_apply
    (c : Plane) (L : ℝ) (y : SquareTorus) (i : Fin 2) :
    torusPhysicalPoint c L y i = c i + L * torusRepresentative y i := rfl

theorem measurable_torusPhysicalPoint (c : Plane) (L : ℝ) :
    Measurable (torusPhysicalPoint c L) := by
  refine (PiLp.continuous_toLp (p := 2)
    (β := fun _ : Fin 2 ↦ ℝ)).measurable.comp ?_
  apply measurable_pi_lambda
  intro i
  exact measurable_const.add <| measurable_const.mul <|
    (measurable_pi_apply i).comp measurable_torusRepresentative

/-- The part of `A` in the coordinate square of half-width `r`, represented on a torus whose
physical period is `2(r+1)`.  The unit collar is what prevents wrap-around unit pairs. -/
def torusCrop (A : Set Plane) (c : Plane) (r : ℝ) : Set SquareTorus :=
  torusPhysicalPoint c (2 * (r + 1)) ⁻¹' (A ∩ coordinateBox c r)

theorem measurableSet_torusCrop {A : Set Plane} (hA : MeasurableSet A)
    (c : Plane) (r : ℝ) : MeasurableSet (torusCrop A c r) := by
  exact (hA.inter (measurableSet_coordinateBox c r)).preimage
    (measurable_torusPhysicalPoint c (2 * (r + 1)))

/-! ## The measure and distance properties of a crop -/

/-- The half-open coordinate fundamental domain used by `torusRepresentative`. -/
def centeredFundamentalBox : Set (Fin 2 → ℝ) :=
  {u | ∀ i, u i ∈ Ioc (centeredFundamentalBase i) (centeredFundamentalBase i + 1)}

theorem measurableSet_centeredFundamentalBox :
    MeasurableSet centeredFundamentalBox := by
  rw [centeredFundamentalBox, show
      {u : Fin 2 → ℝ | ∀ i, u i ∈ Ioc (centeredFundamentalBase i)
        (centeredFundamentalBase i + 1)} =
      ⋂ i, (fun u : Fin 2 → ℝ ↦ u i) ⁻¹'
        Ioc (centeredFundamentalBase i) (centeredFundamentalBase i + 1) by
      ext; simp]
  exact MeasurableSet.iInter fun i ↦
    measurableSet_Ioc.preimage (measurable_pi_apply i)

/-- The affine chart from the raw coordinate plane to the physical plane. -/
def rawAffinePoint (c : Plane) (L : ℝ) (u : Fin 2 → ℝ) : Plane :=
  WithLp.toLp 2 (fun i ↦ c i + L * u i)

@[simp] theorem rawAffinePoint_apply
    (c : Plane) (L : ℝ) (u : Fin 2 → ℝ) (i : Fin 2) :
    rawAffinePoint c L u i = c i + L * u i := rfl

theorem measurable_rawAffinePoint (c : Plane) (L : ℝ) :
    Measurable (rawAffinePoint c L) := by
  refine (PiLp.continuous_toLp (p := 2)
    (β := fun _ : Fin 2 ↦ ℝ)).measurable.comp ?_
  fun_prop

theorem torusPhysicalPoint_eq_rawAffinePoint
    (c : Plane) (L : ℝ) (y : SquareTorus) :
    torusPhysicalPoint c L y = rawAffinePoint c L (torusRepresentative y) := rfl

/-- Lebesgue measure under the affine coordinate chart. -/
theorem volume_rawAffinePoint_preimage {E : Set Plane} (hE : MeasurableSet E)
    (c : Plane) {L : ℝ} (hL : 0 < L) :
    volume (rawAffinePoint c L ⁻¹' E) =
      ENNReal.ofReal (L ^ 2)⁻¹ * volume E := by
  let T : (Fin 2 → ℝ) → Plane := WithLp.toLp 2
  let V : Set Plane := (fun v : Plane ↦ c + L • v) ⁻¹' E
  have hV : MeasurableSet V := by
    exact hE.preimage (by fun_prop)
  have hpre : rawAffinePoint c L ⁻¹' E = T ⁻¹' V := by
    ext u
    simp only [mem_preimage, V, T]
    rw [show rawAffinePoint c L u = c + L • WithLp.toLp 2 u by
      ext i
      rfl]
  calc
    volume (rawAffinePoint c L ⁻¹' E) = volume V := by
      rw [hpre]
      exact (PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
        hV.nullMeasurableSet
    _ = volume ((fun v : Plane ↦ L • v) ⁻¹'
        ((fun v : Plane ↦ c + v) ⁻¹' E)) := by rfl
    _ = ENNReal.ofReal (abs (L ^ Module.finrank ℝ Plane)⁻¹) *
        volume ((fun v : Plane ↦ c + v) ⁻¹' E) := by
      rw [Measure.addHaar_preimage_smul volume hL.ne']
    _ = ENNReal.ofReal (L ^ 2)⁻¹ * volume E := by
      rw [measure_preimage_add]
      simp [finrank_euclideanSpace_fin, abs_of_pos (sq_pos_of_pos hL)]

/-- The Haar mass of a torus crop is the physical mass of the crop divided by the
area of the physical fundamental square. -/
theorem volume_torusCrop {A : Set Plane} (hA : MeasurableSet A)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    volume (torusCrop A c r) =
      ENNReal.ofReal ((2 * (r + 1)) ^ 2)⁻¹ *
        volume (A ∩ coordinateBox c r) := by
  let L : ℝ := 2 * (r + 1)
  have hL : 0 < L := by dsimp [L]; linarith
  let E : Set Plane := A ∩ coordinateBox c r
  have hE : MeasurableSet E := hA.inter (measurableSet_coordinateBox c r)
  let e := UnitAddTorus.measurableEquivPiIoc centeredFundamentalBase
  let Q : Set centeredFundamentalBox :=
    {u | rawAffinePoint c L u.1 ∈ E}
  have hQ : MeasurableSet Q := by
    exact hE.preimage <| (measurable_rawAffinePoint c L).comp measurable_subtype_coe
  have hcrop : torusCrop A c r = e ⁻¹' Q := by
    ext y
    rfl
  have himage : ((↑) '' Q : Set (Fin 2 → ℝ)) = rawAffinePoint c L ⁻¹' E := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hu
      have hubox : rawAffinePoint c L u ∈ coordinateBox c r := hu.2
      have hfund : u ∈ centeredFundamentalBox := by
        intro i
        have hi := hubox i
        simp only [rawAffinePoint_apply, mem_Ioo] at hi
        simp only [centeredFundamentalBox, centeredFundamentalBase, mem_setOf_eq, mem_Ioc]
        constructor <;> norm_num at * <;> nlinarith
      exact ⟨⟨u, hfund⟩, hu, rfl⟩
  calc
    volume (torusCrop A c r) = volume (e ⁻¹' Q) := by rw [hcrop]
    _ = (Measure.comap Subtype.val volume) Q := by
      exact (UnitAddTorus.measurePreserving_equivPiIoc centeredFundamentalBase).measure_preimage
        hQ.nullMeasurableSet
    _ = volume ((↑) '' Q : Set (Fin 2 → ℝ)) := by
      exact comap_subtype_coe_apply measurableSet_centeredFundamentalBox volume Q
    _ = volume (rawAffinePoint c L ⁻¹' E) := by rw [himage]
    _ = ENNReal.ofReal (L ^ 2)⁻¹ * volume E :=
      volume_rawAffinePoint_preimage hE c hL
    _ = ENNReal.ofReal ((2 * (r + 1)) ^ 2)⁻¹ *
        volume (A ∩ coordinateBox c r) := by rfl

theorem volumeReal_torusCrop {A : Set Plane} (hA : MeasurableSet A)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    volume.real (torusCrop A c r) =
      volume.real (A ∩ coordinateBox c r) / (2 * (r + 1)) ^ 2 := by
  rw [Measure.real, volume_torusCrop hA c hr, ENNReal.toReal_mul]
  have hsq : 0 ≤ (2 * (r + 1)) ^ 2 := sq_nonneg _
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hsq), div_eq_inv_mul]
  rfl

/-- The real and imaginary coordinates of a complex displacement, indexed by `Fin 2`. -/
def complexCoordinate (z : ℂ) (i : Fin 2) : ℝ :=
  match i.val with
  | 0 => z.re
  | _ => z.im

theorem torusVector_apply (L : ℝ) (z : ℂ) (i : Fin 2) :
    torusVector L z i = (complexCoordinate z i / L : UnitAddCircle) := by
  fin_cases i <;> rfl

theorem complexCoordinate_sq_le_one {z : ℂ} (hz : Complex.normSq z = 1)
    (i : Fin 2) : complexCoordinate z i ^ 2 ≤ 1 := by
  fin_cases i <;> simp only [complexCoordinate, Complex.normSq_apply] at hz ⊢ <;>
    nlinarith [sq_nonneg z.re, sq_nonneg z.im]

theorem torusCrop_unitDistanceFree {A : Set Plane} (hfree : UnitDistanceFree A)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    TorusUnitDistanceFree (2 * (r + 1)) (torusCrop A c r) := by
  let L : ℝ := 2 * (r + 1)
  have hL : 0 < L := by dsimp [L]; linarith
  intro x z hz hxpair
  rcases hxpair with ⟨hx, hy⟩
  rcases hx with ⟨hxA, hxbox⟩
  rcases hy with ⟨hyA, hybox⟩
  let y : SquareTorus := x + torusVector L z
  have hcoordinate : ∀ i : Fin 2,
      torusPhysicalPoint c L y i - torusPhysicalPoint c L x i = complexCoordinate z i := by
    intro i
    let w : ℝ := complexCoordinate z i
    have hw_sq : w ^ 2 ≤ 1 := complexCoordinate_sq_le_one hz i
    have hw_lower : -1 ≤ w := by nlinarith [sq_nonneg (w + 1)]
    have hw_upper : w ≤ 1 := by nlinarith [sq_nonneg (w - 1)]
    have hcircle :
        (torusRepresentative y i : UnitAddCircle) =
          (torusRepresentative x i + w / L : ℝ) := by
      simp only [y, coe_torusRepresentative, Pi.add_apply, torusVector_apply,
        AddCircle.coe_add, w]
    have hzero :
        ((torusRepresentative y i - (torusRepresentative x i + w / L) : ℝ) :
          UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hcircle, sub_self]
    rcases (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp hzero with ⟨n, hn⟩
    have hn' : (n : ℝ) =
        torusRepresentative y i - (torusRepresentative x i + w / L) := by
      simpa using hn
    have hdiff :
        torusPhysicalPoint c L y i - torusPhysicalPoint c L x i =
          L * (n : ℝ) + w := by
      simp only [torusPhysicalPoint_apply]
      calc
        c i + L * torusRepresentative y i -
              (c i + L * torusRepresentative x i) =
            L * (torusRepresentative y i - torusRepresentative x i) := by ring
        _ = L * ((n : ℝ) + w / L) := by rw [hn']; ring
        _ = L * (n : ℝ) + w := by field_simp
    have hxb := hxbox i
    have hyb := hybox i
    simp only [coordinateBox, mem_setOf_eq, mem_Ioo] at hxb hyb
    have hdiff_lower : -2 * r <
        torusPhysicalPoint c L y i - torusPhysicalPoint c L x i := by linarith
    have hdiff_upper :
        torusPhysicalPoint c L y i - torusPhysicalPoint c L x i < 2 * r := by linarith
    have hn0 : n = 0 := by
      by_contra hn_ne
      rcases lt_or_gt_of_ne hn_ne with hnneg | hnpos
      · have hnle : n ≤ -1 := by omega
        have hnle' : (n : ℝ) ≤ -1 := by exact_mod_cast hnle
        rw [hdiff] at hdiff_lower
        dsimp [L] at hL ⊢
        nlinarith
      · have hnge : 1 ≤ n := by omega
        have hnge' : (1 : ℝ) ≤ n := by exact_mod_cast hnge
        rw [hdiff] at hdiff_upper
        dsimp [L] at hL ⊢
        nlinarith
    rw [hdiff, hn0]
    simp [w]
  have hdist_sq :
      dist (torusPhysicalPoint c L x) (torusPhysicalPoint c L y) ^ 2 = 1 := by
    rw [dist_eq_norm, EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two]
    have h0 := hcoordinate 0
    have h1 := hcoordinate 1
    change torusPhysicalPoint c L y 0 - torusPhysicalPoint c L x 0 = z.re at h0
    change torusPhysicalPoint c L y 1 - torusPhysicalPoint c L x 1 = z.im at h1
    change (torusPhysicalPoint c L x 0 - torusPhysicalPoint c L y 0) ^ 2 +
      (torusPhysicalPoint c L x 1 - torusPhysicalPoint c L y 1) ^ 2 = 1
    rw [show torusPhysicalPoint c L x 0 - torusPhysicalPoint c L y 0 = -z.re by linarith,
      show torusPhysicalPoint c L x 1 - torusPhysicalPoint c L y 1 = -z.im by linarith]
    simp only [neg_sq]
    simpa only [Complex.normSq_apply, pow_two] using hz
  have hdist : dist (torusPhysicalPoint c L x) (torusPhysicalPoint c L y) = 1 := by
    have hnonneg : 0 ≤ dist (torusPhysicalPoint c L x) (torusPhysicalPoint c L y) :=
      dist_nonneg
    nlinarith
  exact hfree hxA hyA hdist

/-! ## The local-to-global incidence estimate -/

theorem volume_coordinateBox (c : Plane) {r : ℝ} (hr : 0 ≤ r) :
    volume (coordinateBox c r) = ENNReal.ofReal ((2 * r) ^ 2) := by
  let Q : Set (Fin 2 → ℝ) := Set.pi Set.univ fun i ↦ Ioo (c i - r) (c i + r)
  have hpre : (@WithLp.toLp 2 (Fin 2 → ℝ)) ⁻¹' coordinateBox c r = Q := by
    ext x
    simp [coordinateBox, Q]
  have hmeasure : volume (coordinateBox c r) = volume Q := by
    rw [← hpre]
    exact ((PiLp.volume_preserving_toLp (Fin 2)).measure_preimage
      (measurableSet_coordinateBox c r).nullMeasurableSet).symm
  rw [hmeasure, Real.volume_pi_Ioo]
  simp only [Fin.prod_univ_two]
  have h0 : c 0 + r - (c 0 - r) = 2 * r := by ring
  have h1 : c 1 + r - (c 1 - r) = 2 * r := by ring
  rw [h0, h1]
  rw [← ENNReal.ofReal_mul (by linarith : 0 ≤ 2 * r)]
  congr 1
  ring

/-- The measurable set of pairs `(c,x)` in which `x` is a point of `A` in the radius-`R`
ball and `c` is a center in the expanded ball whose width-`r` coordinate box contains `x`. -/
def localIncidence (A : Set Plane) (R r : ℝ) : Set (Plane × Plane) :=
  {p | p.1 ∈ ball 0 (R + 2 * r) ∧ p.2 ∈ A ∩ ball 0 R ∧
    p.2 ∈ coordinateBox p.1 r}

theorem measurableSet_localIncidence {A : Set Plane} (hA : MeasurableSet A)
    (R r : ℝ) : MeasurableSet (localIncidence A R r) := by
  have hrel : MeasurableSet {p : Plane × Plane | p.2 ∈ coordinateBox p.1 r} := by
    rw [show {p : Plane × Plane | p.2 ∈ coordinateBox p.1 r} =
        ⋂ i, {p : Plane × Plane |
          p.1 i - r < p.2 i ∧ p.2 i < p.1 i + r} by
      ext p
      simp [coordinateBox]]
    apply MeasurableSet.iInter
    intro i
    measurability
  exact (measurableSet_ball.preimage measurable_fst).inter <|
    ((hA.inter measurableSet_ball).preimage measurable_snd).inter hrel

theorem localIncidence_right_fiber {A : Set Plane} {R r : ℝ} (hr : 0 < r)
    {x : Plane} (hx : x ∈ A ∩ ball (0 : Plane) R) :
    (fun c : Plane ↦ (c, x)) ⁻¹' localIncidence A R r = coordinateBox x r := by
  ext c
  constructor
  · intro hc
    exact (mem_coordinateBox_comm.mp hc.2.2)
  · intro hc
    exact ⟨center_mem_expanded_ball hr hx.2 hc,
      hx, mem_coordinateBox_comm.mpr hc⟩

theorem localIncidence_right_fiber_of_not_mem {A : Set Plane} {R r : ℝ}
    {x : Plane} (hx : x ∉ A ∩ ball (0 : Plane) R) :
    (fun c : Plane ↦ (c, x)) ⁻¹' localIncidence A R r = ∅ := by
  ext c
  constructor
  · intro hc
    exact (hx hc.2.1).elim
  · simp

theorem volume_localIncidence {A : Set Plane} (hA : MeasurableSet A)
    {R r : ℝ} (hr : 0 < r) :
    (volume.prod volume) (localIncidence A R r) =
      ENNReal.ofReal ((2 * r) ^ 2) * volume (A ∩ ball (0 : Plane) R) := by
  rw [Measure.prod_apply_symm (measurableSet_localIncidence hA R r)]
  have hfiber : ∀ x : Plane,
      volume ((fun c : Plane ↦ (c, x)) ⁻¹' localIncidence A R r) =
        (A ∩ ball (0 : Plane) R).indicator
          (fun _ ↦ ENNReal.ofReal ((2 * r) ^ 2)) x := by
    intro x
    by_cases hx : x ∈ A ∩ ball (0 : Plane) R
    · rw [localIncidence_right_fiber hr hx, volume_coordinateBox x hr.le,
        indicator_of_mem hx]
    · rw [localIncidence_right_fiber_of_not_mem hx, measure_empty,
        indicator_of_notMem hx]
  simp_rw [hfiber]
  rw [lintegral_indicator (hA.inter measurableSet_ball)]
  simp

theorem volume_inter_coordinateBox_ne_top (A : Set Plane) (c : Plane) {r : ℝ}
    (hr : 0 ≤ r) : volume (A ∩ coordinateBox c r) ≠ ∞ := by
  exact ne_of_lt <| (measure_mono inter_subset_right).trans_lt <| by
    rw [volume_coordinateBox c hr]
    exact ENNReal.ofReal_lt_top

/-- Integrating a uniform local square bound over all centers bounds the incidence set. -/
theorem volume_localIncidence_le_of_local_bound {A : Set Plane} (hA : MeasurableSet A)
    {R r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hlocal : ∀ c : Plane, volume.real (A ∩ coordinateBox c r) ≤ K) :
    (volume.prod volume) (localIncidence A R r) ≤
      ENNReal.ofReal K * volume (ball (0 : Plane) (R + 2 * r)) := by
  rw [Measure.prod_apply (measurableSet_localIncidence hA R r)]
  have hfiber : ∀ c : Plane,
      volume (Prod.mk c ⁻¹' localIncidence A R r) ≤
        (ball (0 : Plane) (R + 2 * r)).indicator (fun _ ↦ ENNReal.ofReal K) c := by
    intro c
    by_cases hc : c ∈ ball (0 : Plane) (R + 2 * r)
    · rw [indicator_of_mem hc]
      have hsubset : Prod.mk c ⁻¹' localIncidence A R r ⊆
          A ∩ coordinateBox c r := by
        intro x hx
        exact ⟨hx.2.1.1, hx.2.2⟩
      refine (measure_mono hsubset).trans ?_
      rw [ENNReal.le_ofReal_iff_toReal_le
        (volume_inter_coordinateBox_ne_top A c hr.le) hK]
      simpa only [measureReal_def] using hlocal c
    · rw [indicator_of_notMem hc]
      suffices Prod.mk c ⁻¹' localIncidence A R r = ∅ by simp [this]
      ext x
      constructor
      · intro hx
        exact (hc hx.1).elim
      · simp
  refine (lintegral_mono hfiber).trans_eq ?_
  rw [lintegral_indicator measurableSet_ball]
  simp

/-- The double-counting inequality behind the density reduction. -/
theorem localIncidence_real_inequality {A : Set Plane} (hA : MeasurableSet A)
    {R r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hlocal : ∀ c : Plane, volume.real (A ∩ coordinateBox c r) ≤ K) :
    (2 * r) ^ 2 * volume.real (A ∩ ball (0 : Plane) R) ≤
      K * volume.real (ball (0 : Plane) (R + 2 * r)) := by
  have h := volume_localIncidence_le_of_local_bound (R := R) hA hr hK hlocal
  rw [volume_localIncidence hA hr] at h
  have htop : ENNReal.ofReal K * volume (ball (0 : Plane) (R + 2 * r)) ≠ ∞ := by
    finiteness
  have hreal := ENNReal.toReal_mono htop h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg (2 * r)),
    ENNReal.toReal_ofReal hK, measureReal_def] using hreal

theorem volumeReal_ball (R : ℝ) (hR : 0 ≤ R) :
    volume.real (ball (0 : Plane) R) = R ^ 2 * Real.pi := by
  rw [measureReal_def, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul]
  simp [hR, Real.pi_pos.le]

/-- A local width-`r` square estimate gives a finite-radius ball-density estimate. -/
theorem ballDensity_le_of_local_bound {A : Set Plane} (hA : MeasurableSet A)
    {R r K : ℝ} (hR : 0 < R) (hr : 0 < r) (hK : 0 ≤ K)
    (hlocal : ∀ c : Plane, volume.real (A ∩ coordinateBox c r) ≤ K) :
    ballDensity A R ≤
      K / (2 * r) ^ 2 * ((R + 2 * r) / R) ^ 2 := by
  have hinc := localIncidence_real_inequality (R := R) hA hr hK hlocal
  have hcoef : 0 < (2 * r) ^ 2 := sq_pos_of_pos (mul_pos zero_lt_two hr)
  have hAvol : volume.real (A ∩ ball (0 : Plane) R) ≤
      (K * volume.real (ball (0 : Plane) (R + 2 * r))) / (2 * r) ^ 2 := by
    apply (le_div_iff₀ hcoef).2
    simpa only [mul_comm] using hinc
  have hden : 0 < volume.real (ball (0 : Plane) R) := by
    rw [volumeReal_ball R hR.le]
    positivity
  rw [ballDensity, show (volume (A ∩ ball (0 : Plane) R)).toReal =
      volume.real (A ∩ ball (0 : Plane) R) by rfl,
    show (volume (ball (0 : Plane) R)).toReal =
      volume.real (ball (0 : Plane) R) by rfl]
  apply (div_le_iff₀ hden).2
  refine hAvol.trans_eq ?_
  rw [volumeReal_ball R hR.le,
    volumeReal_ball (R + 2 * r) (by positivity)]
  field_simp

/-- Taking the radius of the observation ball to infinity removes the outer boundary loss. -/
theorem upperDensity_le_of_local_bound_at_scale {A : Set Plane} (hA : MeasurableSet A)
    {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hlocal : ∀ c : Plane, volume.real (A ∩ coordinateBox c r) ≤ K) :
    upperDensity A ≤ K / (2 * r) ^ 2 := by
  let C : ℝ := K / (2 * r) ^ 2
  let g : ℝ → ℝ := fun R ↦ C * (1 + (2 * r) / R) ^ 2
  have hzero : Tendsto (fun R : ℝ ↦ (2 * r) / R) atTop (nhds 0) :=
    (tendsto_id : Tendsto (fun R : ℝ ↦ R) atTop atTop).const_div_atTop (2 * r)
  have hg : Tendsto g atTop (nhds C) := by
    dsimp [g]
    convert tendsto_const_nhds.mul ((tendsto_const_nhds.add hzero).pow 2) using 1 <;>
      norm_num
  have hpoint : ballDensity A ≤ᶠ[atTop] g := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    have h := ballDensity_le_of_local_bound hA hR hr hK hlocal
    dsimp [g, C]
    convert h using 1
    field_simp
  rw [upperDensity]
  calc
    limsup (ballDensity A) atTop ≤ limsup g atTop :=
      limsup_le_limsup hpoint
        (isCoboundedUnder_le_of_le atTop (ballDensity_nonneg A)) hg.isBoundedUnder_le
    _ = C := hg.limsup_eq
    _ = K / (2 * r) ^ 2 := rfl

/-- If the same local density constant works at every scale, all collar loss vanishes. -/
theorem upperDensity_le_of_all_local_bounds {A : Set Plane} (hA : MeasurableSet A)
    {T : ℝ} (hT : 0 ≤ T)
    (hlocal : ∀ (c : Plane) {r : ℝ}, 0 < r →
      volume.real (A ∩ coordinateBox c r) ≤ T * (2 * (r + 1)) ^ 2) :
    upperDensity A ≤ T := by
  let f : ℝ → ℝ := fun r ↦ T * (1 + 1 / r) ^ 2
  have hzero : Tendsto (fun r : ℝ ↦ 1 / r) atTop (nhds 0) :=
    (tendsto_id : Tendsto (fun r : ℝ ↦ r) atTop atTop).const_div_atTop 1
  have hf : Tendsto f atTop (nhds T) := by
    dsimp [f]
    convert tendsto_const_nhds.mul ((tendsto_const_nhds.add hzero).pow 2) using 1 <;>
      norm_num
  apply ge_of_tendsto hf
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  have hscale := upperDensity_le_of_local_bound_at_scale hA hr
    (mul_nonneg hT (sq_nonneg _)) (fun c ↦ hlocal c hr)
  dsimp [f]
  rw [show T * (1 + 1 / r) ^ 2 =
      T * (2 * (r + 1)) ^ 2 / (2 * r) ^ 2 by
    field_simp]
  exact hscale

/-! ## Instantiating the local estimate with the exact torus certificate -/

/-- The exact torus certificate bounds every cropped coordinate square.  The factor
`(2 * (r + 1)) ^ 2` is the area of the padded period cell used to prevent wraparound
unit distances. -/
theorem volumeReal_inter_coordinateBox_le_dualTarget
    {A : Set Plane} (hA : MeasurableSet A) (hfree : UnitDistanceFree A)
    (c : Plane) {r : ℝ} (hr : 0 < r) :
    volume.real (A ∩ coordinateBox c r) ≤
      (246993028 / 1000000000 : ℝ) * (2 * (r + 1)) ^ 2 := by
  have hL : 0 < 2 * (r + 1) := by linarith
  have htorus := torus_density_le_dualTarget
    (measurableSet_torusCrop hA c r) hL
    (torusCrop_unitDistanceFree hfree c hr)
  rw [volumeReal_torusCrop hA c hr] at htorus
  exact (div_le_iff₀ (sq_pos_of_pos hL)).mp htorus

/-- Exact rational upper bound supplied by the formalized ACMVZ dual certificate. -/
theorem upperDensity_le_dualTarget {A : Set Plane} (hA : MeasurableSet A)
    (hfree : UnitDistanceFree A) :
    upperDensity A ≤ (246993028 / 1000000000 : ℝ) := by
  apply upperDensity_le_of_all_local_bounds hA (by norm_num)
  intro c r hr
  exact volumeReal_inter_coordinateBox_le_dualTarget hA hfree c hr

end

end Erdos232
