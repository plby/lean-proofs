import ErdosProblems.Erdos957.BisectorPolar
import ErdosProblems.Erdos957.TwoExtremeFrame

/-!
# Coherence of the shared middle at adjacent flat sources

If a unit hull edge and a third point form the supported equilateral
triangle used by Cases 2 and 4, then the third point lies in the open middle
cone of the bisector chart at either flat endpoint.  Consequently, when the
other endpoint is itself a source, its canonical phase-bin middle choice is
the same actual vertex.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957PartnerMiddle

open Erdos957
open Erdos957GeometryCore
open Erdos957HullGeometryBridge
open Erdos957BisectorFrame
open Erdos957BisectorPolar
open Erdos957TurnSum.HullOrderBridge

abbrev Point := Erdos957.Point

/-- The lower common unit point of the origin and a unit point whose polar
angle is a small negative number lies strictly in the downward open
sixty-degree cone. -/
private theorem inOpenMiddleCone_of_common_unit_polar
    {n z : ℝ × ℝ} {θ : ℝ}
    (hn : n = (Real.cos θ, Real.sin θ))
    (hθneg : θ < 0) (hθabs : |θ| ≤ Real.pi / 180)
    (hzUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin z = 1)
    (hnzUnit : Erdos957Cases13.sqDist n z = 1)
    (hzneg : z.2 < 0) :
    Erdos957Cases13.InOpenMiddleCone z := by
  subst n
  let c := Real.cos θ
  let s := Real.sin θ
  let d := c * z.2 - s * z.1
  have htrig : c ^ 2 + s ^ 2 = 1 := by
    dsimp [c, s]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hzSq : z.1 ^ 2 + z.2 ^ 2 = 1 := by
    simpa [Erdos957Cases13.sqDist, Erdos957Cases13.origin] using hzUnit
  have hnzSq : (c - z.1) ^ 2 + (s - z.2) ^ 2 = 1 := by
    simpa [Erdos957Cases13.sqDist, c, s] using hnzUnit
  have hdot : c * z.1 + s * z.2 = 1 / 2 := by
    nlinarith
  have hdSq : d ^ 2 = 3 / 4 := by
    dsimp [d]
    nlinarith [sq_nonneg (c * z.1 + s * z.2)]
  have hθlower : -Real.pi < θ := by
    have hsmall : -Real.pi / 180 ≤ θ := by
      have := neg_le_of_abs_le hθabs
      linarith
    nlinarith [Real.pi_pos]
  have hsneg : s < 0 := by
    exact Real.sin_neg_of_neg_of_neg_pi_lt hθneg hθlower
  have hθrational : |θ| ≤ (1 : ℝ) / 45 := by
    calc
      |θ| ≤ Real.pi / 180 := hθabs
      _ ≤ (1 : ℝ) / 45 := by nlinarith [Real.pi_le_four]
  have hsAbs : |s| ≤ (1 : ℝ) / 45 := by
    exact (Real.abs_sin_le_abs.trans hθrational)
  have hsLower : -(1 : ℝ) / 45 ≤ s := by
    have := neg_le_of_abs_le hsAbs
    linarith
  have hθfortyfive : |θ| ≤ Real.pi / 45 := by
    nlinarith [Real.pi_pos]
  have hcStrong : (399 / 400 : ℝ) < c := by
    calc
      (399 / 400 : ℝ) < Real.cos (Real.pi / 45) :=
        Erdos957Locality.three_nine_nine_div_four_hundred_lt_cos_pi_div_forty_five
      _ ≤ Real.cos |θ| := Real.cos_le_cos_of_nonneg_of_le_pi
        (abs_nonneg θ) (by nlinarith [Real.pi_pos]) hθfortyfive
      _ = c := by exact Real.cos_abs θ
  have hcPos : 0 < c := by
    linarith
  have hcLower : (4 / 5 : ℝ) < c := by linarith
  have hyFormula : z.2 = s / 2 + c * d := by
    have hidentity : s * (c * z.1 + s * z.2) +
        c * (c * z.2 - s * z.1) =
        (c ^ 2 + s ^ 2) * z.2 := by ring
    rw [htrig] at hidentity
    norm_num at hidentity
    rw [← hidentity, hdot]
    dsimp [d]
    ring
  have hdneg : d < 0 := by
    by_contra hnot
    have hdnonneg : 0 ≤ d := le_of_not_gt hnot
    have hdLower : (4 / 5 : ℝ) < d := by nlinarith
    have hprod : (4 / 5 : ℝ) * (4 / 5) < c * d := by
      exact mul_lt_mul hcLower hdLower.le (by norm_num) hcPos.le
    rw [hyFormula] at hzneg
    nlinarith
  have hsqrtPos : 0 < Erdos957Cases13.sqrtThree :=
    Erdos957Cases13.sqrtThree_pos
  have hsqrtSq : Erdos957Cases13.sqrtThree ^ 2 = 3 :=
    Erdos957Cases13.sqrtThree_sq
  have hd : d = -Erdos957Cases13.sqrtThree / 2 := by
    nlinarith only [hdSq, hsqrtSq, hsqrtPos, hdneg]
  have hxFormula : z.1 =
      c / 2 + s * Erdos957Cases13.sqrtThree / 2 := by
    have hidentity : c * (c * z.1 + s * z.2) -
        s * (c * z.2 - s * z.1) =
        (c ^ 2 + s ^ 2) * z.1 := by ring
    rw [htrig] at hidentity
    norm_num at hidentity
    dsimp [d] at hd ⊢
    rw [← hidentity, hdot, hd]
    ring
  have hyFormula' : z.2 =
      s / 2 - c * Erdos957Cases13.sqrtThree / 2 := by
    rw [hyFormula, hd]
    ring
  have hsProdNeg : Erdos957Cases13.sqrtThree * s < 0 :=
    mul_neg_of_pos_of_neg hsqrtPos hsneg
  have hsqrtOne : 1 ≤ Erdos957Cases13.sqrtThree := by
    nlinarith only [hsqrtSq, hsqrtPos]
  have hcScale : c ≤ Erdos957Cases13.sqrtThree * c := by
    have hprod : 0 ≤ (Erdos957Cases13.sqrtThree - 1) * c :=
      mul_nonneg (sub_nonneg.mpr hsqrtOne) hcPos.le
    nlinarith only [hprod]
  have hsumPos : 0 < Erdos957Cases13.sqrtThree * c + s := by
    nlinarith only [hcStrong, hsLower, hcScale]
  constructor
  · rw [hxFormula, hyFormula']
    nlinarith only [hsqrtSq, hsneg]
  · rw [hxFormula, hyFormula']
    have hdiff :
        Erdos957Cases13.sqrtThree *
            (c / 2 + s * Erdos957Cases13.sqrtThree / 2) -
          (s / 2 - c * Erdos957Cases13.sqrtThree / 2) =
            Erdos957Cases13.sqrtThree * c + s := by
      calc
        _ = Erdos957Cases13.sqrtThree * c +
            (Erdos957Cases13.sqrtThree ^ 2 - 1) * s / 2 := by ring
        _ = Erdos957Cases13.sqrtThree * c + s := by
          rw [hsqrtSq]
          ring
    linarith

private theorem right_neighbor_polar_unit
    {A : Finset Point} (hA : IsOneSeparated A)
    (O : CyclicHullOrder A) (L : LiftedCyclicHullOrder O)
    (partner : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hunit : (unitDistanceGraph A).Adj partner.1
      ((cyclicHullDataOfOrder O L).next partner).1) :
    let C := bisectorAlignedChartData O L
    let n := C.coord partner ((cyclicHullDataOfOrder O L).next partner).1
    n = (Real.cos (producedRightAngle L partner 0),
      Real.sin (producedRightAngle L partner 0)) := by
  let P := cyclicHullDataOfOrder O L
  let C := bisectorAlignedChartData O L
  let n := C.coord partner (P.next partner).1
  let r := producedRightRadius L partner 0
  let θ := producedRightAngle L partner 0
  have hp := producedRightPolar L partner 0
  simp only [CyclicHullData.AlignedChartData.rightOrbitCoord_zero] at hp
  change Erdos957Locality.IsPolarEdge (0, 0) n r θ at hp
  have hnUnit : n.1 ^ 2 + n.2 ^ 2 = 1 := by
    have hs := C.sqDist_coord partner partner.1 (P.next partner).1
    rw [C.coord_source, hunit] at hs
    simpa [Erdos957Cases13.sqDist, n] using hs
  have hrge : 1 ≤ r := producedRightRadius_ge_one L hA partner 0
  have htrig := Real.sin_sq_add_cos_sq θ
  have hr : r = 1 := by
    rcases hp with ⟨hx, hy⟩
    norm_num at hx hy
    rw [hx, hy] at hnUnit
    have hrsq : r ^ 2 = 1 := by
      calc
        r ^ 2 = r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by
          rw [htrig, mul_one]
        _ = (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by ring
        _ = 1 := hnUnit
    nlinarith only [hrsq, hrge]
  rcases hp with ⟨hx, hy⟩
  norm_num at hx hy
  change n = (Real.cos θ, Real.sin θ)
  apply Prod.ext
  · simpa [hr] using hx
  · simpa [hr] using hy

private theorem left_reflected_neighbor_polar_unit
    {A : Finset Point} (hA : IsOneSeparated A)
    (O : CyclicHullOrder A) (L : LiftedCyclicHullOrder O)
    (partner : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hunit : (unitDistanceGraph A).Adj partner.1
      ((cyclicHullDataOfOrder O L).next⁻¹ partner).1) :
    let C := bisectorAlignedChartData O L
    let p := C.coord partner ((cyclicHullDataOfOrder O L).next⁻¹ partner).1
    (-p.1, p.2) = (Real.cos (producedLeftAngle L partner 0),
      Real.sin (producedLeftAngle L partner 0)) := by
  let P := cyclicHullDataOfOrder O L
  let C := bisectorAlignedChartData O L
  let p := C.coord partner (P.next⁻¹ partner).1
  let n : ℝ × ℝ := (-p.1, p.2)
  let r := producedLeftRadius L partner 0
  let θ := producedLeftAngle L partner 0
  have hp := producedLeftPolar L partner 0
  simp only [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord_zero] at hp
  change Erdos957Locality.IsPolarEdge (0, 0) n r θ at hp
  have hnUnit : n.1 ^ 2 + n.2 ^ 2 = 1 := by
    have hs := C.sqDist_coord partner partner.1 (P.next⁻¹ partner).1
    rw [C.coord_source, hunit] at hs
    simpa [Erdos957Cases13.sqDist, n, p] using hs
  have hrge : 1 ≤ r := producedLeftRadius_ge_one L hA partner 0
  have htrig := Real.sin_sq_add_cos_sq θ
  have hr : r = 1 := by
    rcases hp with ⟨hx, hy⟩
    norm_num at hx hy
    rw [hx, hy] at hnUnit
    have hrsq : r ^ 2 = 1 := by
      calc
        r ^ 2 = r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by
          rw [htrig, mul_one]
        _ = (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 := by ring
        _ = 1 := hnUnit
    nlinarith only [hrsq, hrge]
  rcases hp with ⟨hx, hy⟩
  norm_num at hx hy
  change n = (Real.cos θ, Real.sin θ)
  apply Prod.ext
  · simpa [hr] using hx
  · simpa [hr] using hy

private theorem producedAngle_zero_neg_and_small
    {A : Finset Point} (O : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder O)
    (partner : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hflat : (cyclicHullDataOfOrder O L).IsFlat partner) :
    let θ := producedRightAngle L partner 0
    θ < 0 ∧ |θ| ≤ Real.pi / 180 := by
  let P := cyclicHullDataOfOrder O L
  have htpos : 0 < P.turn partner := by
    let e := indexEquivLiftedHull O
    let a := e.symm partner
    have hi : e a = partner := e.apply_symm_apply partner
    have hturn := incidentTurn_eq_producedTurn L a
    rw [hi] at hturn
    rw [← hturn]
    exact incidentTurn_pos L a
  have htlt : P.turn partner < Real.pi / 180 :=
    P.turn_lt_of_isFlat partner hflat
  rw [producedRightAngle_zero]
  constructor
  · nlinarith
  · rw [abs_of_nonpos (by linarith)]
    nlinarith [Real.pi_pos]

private theorem producedLeftAngle_zero_neg_and_small
    {A : Finset Point} (O : CyclicHullOrder A)
    (L : LiftedCyclicHullOrder O)
    (partner : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hflat : (cyclicHullDataOfOrder O L).IsFlat partner) :
    let θ := producedLeftAngle L partner 0
    θ < 0 ∧ |θ| ≤ Real.pi / 180 := by
  let P := cyclicHullDataOfOrder O L
  have htpos : 0 < P.turn partner := by
    let e := indexEquivLiftedHull O
    let a := e.symm partner
    have hi : e a = partner := e.apply_symm_apply partner
    have hturn := incidentTurn_eq_producedTurn L a
    rw [hi] at hturn
    rw [← hturn]
    exact incidentTurn_pos L a
  have htlt : P.turn partner < Real.pi / 180 :=
    P.turn_lt_of_isFlat partner hflat
  rw [producedLeftAngle_zero]
  constructor
  · nlinarith
  · rw [abs_of_nonpos (by linarith)]
    nlinarith [Real.pi_pos]

/-- If `next partner` and `middle` form the supported unit equilateral
triangle at a flat partner, then `middle` lies in the partner's produced
bisector middle cone. -/
theorem middle_in_partner_bisector_openCone_of_next
    {A : Finset Point} (hA : IsOneSeparated A)
    (O : CyclicHullOrder A) (L : LiftedCyclicHullOrder O)
    (partner : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hflat : (cyclicHullDataOfOrder O L).IsFlat partner)
    (middle : Erdos957GeometryCore.Vertex A)
    (hpartnerNext : (unitDistanceGraph A).Adj partner.1
      ((cyclicHullDataOfOrder O L).next partner).1)
    (hpartnerMiddle : (unitDistanceGraph A).Adj partner.1 middle)
    (hnextMiddle : (unitDistanceGraph A).Adj
      ((cyclicHullDataOfOrder O L).next partner).1 middle) :
    Erdos957Cases13.InOpenMiddleCone
      ((bisectorAlignedChartData O L).coord partner middle) := by
  let P := cyclicHullDataOfOrder O L
  let C := bisectorAlignedChartData O L
  let n := C.coord partner (P.next partner).1
  let z := C.coord partner middle
  let θ := producedRightAngle L partner 0
  have hn := right_neighbor_polar_unit hA O L partner hpartnerNext
  have hθ := producedAngle_zero_neg_and_small O L partner hflat
  have hzUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin z = 1 := by
    change Erdos957Cases13.sqDist (0, 0) (C.coord partner middle) = 1
    rw [← C.coord_source partner, C.sqDist_coord, hpartnerMiddle]
    norm_num
  have hnzUnit : Erdos957Cases13.sqDist n z = 1 := by
    rw [C.sqDist_coord, hnextMiddle]
    norm_num
  have hzneg : z.2 < 0 :=
    Erdos957BisectorFrame.bisectorAlignedChartData_coord_snd_neg
      O L partner middle hpartnerMiddle.ne.symm
  exact inOpenMiddleCone_of_common_unit_polar hn hθ.1 hθ.2
    hzUnit hnzUnit hzneg

/-- The reflected predecessor-side form of
`middle_in_partner_bisector_openCone_of_next`. -/
theorem middle_in_partner_bisector_openCone_of_previous
    {A : Finset Point} (hA : IsOneSeparated A)
    (O : CyclicHullOrder A) (L : LiftedCyclicHullOrder O)
    (partner : {p // p ∈ (cyclicHullDataOfOrder O L).H})
    (hflat : (cyclicHullDataOfOrder O L).IsFlat partner)
    (middle : Erdos957GeometryCore.Vertex A)
    (hpartnerPrevious : (unitDistanceGraph A).Adj partner.1
      ((cyclicHullDataOfOrder O L).next⁻¹ partner).1)
    (hpartnerMiddle : (unitDistanceGraph A).Adj partner.1 middle)
    (hpreviousMiddle : (unitDistanceGraph A).Adj
      ((cyclicHullDataOfOrder O L).next⁻¹ partner).1 middle) :
    Erdos957Cases13.InOpenMiddleCone
      ((bisectorAlignedChartData O L).coord partner middle) := by
  let P := cyclicHullDataOfOrder O L
  let C := bisectorAlignedChartData O L
  let p := C.coord partner (P.next⁻¹ partner).1
  let z₀ := C.coord partner middle
  let n : ℝ × ℝ := (-p.1, p.2)
  let z : ℝ × ℝ := (-z₀.1, z₀.2)
  let θ := producedLeftAngle L partner 0
  have hn := left_reflected_neighbor_polar_unit hA O L partner hpartnerPrevious
  have hθ := producedLeftAngle_zero_neg_and_small O L partner hflat
  have hzUnit : Erdos957Cases13.sqDist Erdos957Cases13.origin z = 1 := by
    have hs := C.sqDist_coord partner partner.1 middle
    rw [C.coord_source, hpartnerMiddle] at hs
    dsimp [Erdos957Cases13.sqDist, Erdos957Cases13.origin, z, z₀] at hs ⊢
    ring_nf at hs ⊢
    exact hs
  have hnzUnit : Erdos957Cases13.sqDist n z = 1 := by
    have hs := C.sqDist_coord partner (P.next⁻¹ partner).1 middle
    rw [hpreviousMiddle] at hs
    dsimp [Erdos957Cases13.sqDist, n, p, z, z₀] at hs ⊢
    ring_nf at hs ⊢
    exact hs
  have hzneg : z.2 < 0 := by
    dsimp [z, z₀]
    exact Erdos957BisectorFrame.bisectorAlignedChartData_coord_snd_neg
      O L partner middle hpartnerMiddle.ne.symm
  have hzCone := inOpenMiddleCone_of_common_unit_polar hn hθ.1 hθ.2
    hzUnit hnzUnit hzneg
  rcases hzCone with ⟨hleft, hright⟩
  constructor <;> dsimp [z, z₀] at hleft hright ⊢ <;> linarith

end Erdos957PartnerMiddle
