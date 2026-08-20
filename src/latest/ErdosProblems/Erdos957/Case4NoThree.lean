import ErdosProblems.Erdos957.CaseClassification


open scoped RealInnerProductSpace

noncomputable section

namespace Erdos957Case4NoThree

open Erdos957GeometryCore
open Erdos957GeometryLocalRows
open Erdos957CaseClassification

abbrev Point := Erdos957GeometryCore.Point

variable {A : Finset Point} {P : CyclicHullData A}
variable {W : DiameterWitnessData P} {F : P.FlatAlignedFrameData}

def pairDot (x y : ℝ × ℝ) : ℝ := x.1 * y.1 + x.2 * y.2

def pairEdgeTransform (e z : ℝ × ℝ) : ℝ × ℝ :=
  (pairDot e z, CyclicHullData.pairCross e z)

lemma pairEdgeTransform_sub (e p q : ℝ × ℝ) :
    CyclicHullData.pairSub (pairEdgeTransform e q) (pairEdgeTransform e p) =
      pairEdgeTransform e (CyclicHullData.pairSub q p) := by
  apply Prod.ext <;>
    simp [pairEdgeTransform, pairDot, CyclicHullData.pairCross,
      CyclicHullData.pairSub] <;> ring

lemma pairEdgeTransform_polar
    {e p q : ℝ × ℝ} {r α β : ℝ}
    (he : e = (Real.cos α, Real.sin α))
    (hpq : Erdos957Locality.IsPolarEdge p q r β) :
    Erdos957Locality.IsPolarEdge (pairEdgeTransform e p)
      (pairEdgeTransform e q) r (β - α) := by
  subst e
  rcases hpq with ⟨hx, hy⟩
  simp only [Erdos957Locality.IsPolarEdge, pairEdgeTransform, pairDot,
    CyclicHullData.pairCross] at hx hy ⊢
  constructor
  · rw [Real.cos_sub]
    calc
      _ = Real.cos α * (q.1 - p.1) + Real.sin α * (q.2 - p.2) := by ring
      _ = Real.cos α * (r * Real.cos β) +
          Real.sin α * (r * Real.sin β) := by rw [hx, hy]
      _ = _ := by ring
  · rw [Real.sin_sub]
    calc
      _ = Real.cos α * (q.2 - p.2) - Real.sin α * (q.1 - p.1) := by ring
      _ = Real.cos α * (r * Real.sin β) -
          Real.sin α * (r * Real.cos β) := by rw [hx, hy]
      _ = _ := by ring

private lemma polar_three_prefix_bounds
    (p : ℕ → ℝ × ℝ) (r θ : Fin 3 → ℝ)
    (hp0 : p 0 = (0, 0))
    (he : ∀ j : Fin 3,
      Erdos957Locality.IsPolarEdge (p j.1) (p (j.1 + 1)) (r j) (θ j))
    (hr : ∀ j : Fin 3, 1 ≤ r j)
    (ha : ∀ j : Fin 3, |θ j| ≤ Real.pi / 45)
    (k : Fin 3) :
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < (p (k.1 + 1)).1 ∧
      -(p (k.1 + 1)).2 ≤ (p (k.1 + 1)).1 / 10 := by
  have hx : ∀ j : Fin 3,
      (399 / 400 : ℝ) < (p (j.1 + 1)).1 - (p j.1).1 := by
    intro j
    exact Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (hr j) (ha j) (he j).1
  have hy : ∀ j : Fin 3,
      -((p (j.1 + 1)).2 - (p j.1).2) ≤
        ((p (j.1 + 1)).1 - (p j.1).1) / 10 := by
    intro j
    have hs :=
      Erdos957Locality.neg_sin_le_cos_div_ten_of_abs_le_pi_div_forty_five
        (ha j)
    have hm := mul_le_mul_of_nonneg_left hs (by linarith [hr j] : 0 ≤ r j)
    rcases he j with ⟨hejx, hejy⟩
    nlinarith
  fin_cases k
  · have hx0 := hx 0
    have hy0 := hy 0
    norm_num at hx0 hy0 ⊢
    rw [hp0] at hx0 hy0
    norm_num at hx0 hy0
    exact ⟨hx0, by linarith⟩
  · have hx0 := hx 0
    have hx1 := hx 1
    have hy0 := hy 0
    have hy1 := hy 1
    norm_num at hx0 hx1 hy0 hy1 ⊢
    rw [hp0] at hx0 hy0
    norm_num at hx0 hx1 hy0 hy1 ⊢
    constructor <;> linarith
  · have hx0 := hx 0
    have hx1 := hx 1
    have hx2 := hx 2
    have hy0 := hy 0
    have hy1 := hy 1
    have hy2 := hy 2
    norm_num at hx0 hx1 hx2 hy0 hy1 hy2 ⊢
    rw [hp0] at hx0 hy0
    norm_num at hx0 hx1 hx2 hy0 hy1 hy2 ⊢
    constructor <;> linarith

private lemma three_angles_plus_initial_near_horizontal
    {a b0 b1 b2 : ℝ}
    (ha : |a| ≤ Real.pi / 180)
    (hb0 : |b0| ≤ Real.pi / 180)
    (hb1 : |b1 - b0| ≤ Real.pi / 180)
    (hb2 : |b2 - b1| ≤ Real.pi / 180) :
    ∀ j : Fin 3, |![b0 + a, b1 + a, b2 + a] j| ≤ Real.pi / 45 := by
  have hab0 : |b0 + a| ≤ |b0| + |a| := abs_add_le _ _
  have hb1' : |b1| ≤ |b1 - b0| + |b0| := by
    calc
      |b1| = |(b1 - b0) + b0| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hab1 : |b1 + a| ≤ |b1| + |a| := abs_add_le _ _
  have hb2' : |b2| ≤ |b2 - b1| + |b1| := by
    calc
      |b2| = |(b2 - b1) + b1| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hab2 : |b2 + a| ≤ |b2| + |a| := abs_add_le _ _
  intro j
  fin_cases j <;> simp <;> nlinarith [Real.pi_pos]

private lemma three_angles_relative_initial_near_horizontal
    {b0 b1 b2 : ℝ}
    (hb1 : |b1 - b0| ≤ Real.pi / 180)
    (hb2 : |b2 - b1| ≤ Real.pi / 180) :
    ∀ j : Fin 3, |![0, b1 - b0, b2 - b0] j| ≤ Real.pi / 45 := by
  have hb20 : |b2 - b0| ≤ |b2 - b1| + |b1 - b0| := by
    calc
      |b2 - b0| = |(b2 - b1) + (b1 - b0)| := by congr 1 <;> ring
      _ ≤ _ := abs_add_le _ _
  intro j
  fin_cases j <;> simp <;> nlinarith [Real.pi_pos]

/-- The outgoing unit-edge chart is obtained from any aligned chart by
taking dot product with the aligned edge vector and the retained oriented
pair cross product.  This avoids choosing an angle for either chart. -/
lemma outgoingEdgePairCoord_eq_aligned
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (a q : Vertex A) (hunit : dist (source.1 : Point) (a : Point) = 1) :
    Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
        ((a : Point) - source.1) (q : Point) =
      (pairDot (C.coord source a) (C.coord source q),
        CyclicHullData.pairCross (C.coord source a) (C.coord source q)) := by
  let z := Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
    ((a : Point) - source.1) (q : Point)
  let ea := C.coord source a
  let eq := C.coord source q
  have hz0 := Erdos957EdgeFrame.sqDist_edgePairCoord hunit
    (source.1 : Point) (q : Point)
  have hz1 := Erdos957EdgeFrame.sqDist_edgePairCoord hunit
    (a : Point) (q : Point)
  have hC0 := C.sqDist_coord source source.1 q
  have hC1 := C.sqDist_coord source a q
  have hsource := C.coord_source source
  have hea : Erdos957Cases13.sqDist (C.coord source source.1) ea = 1 := by
    rw [C.sqDist_coord, hunit]
    norm_num
  have hcross := C.cross_displacements source source.1 a q
  have hedgeCross := Erdos957EdgeFrame.pairCross_edgePairCoord_displacements
    hunit (source.1 : Point) (a : Point) (q : Point)
  apply Prod.ext
  · simp only [Prod.fst]
    change z.1 = pairDot ea eq
    simp only [z, Erdos957EdgeFrame.edgePairCoord_self,
      Erdos957EdgeFrame.edgePairCoord_terminal hunit,
      Erdos957Cases13.sqDist, hsource, pairDot, ea, eq,
      CyclicHullData.pairSub] at hz0 hz1 hC0 hC1 hea ⊢
    nlinarith
  · simp only [Prod.snd]
    change z.2 = CyclicHullData.pairCross ea eq
    simp only [z, Erdos957EdgeFrame.edgePairCoord_self,
      Erdos957EdgeFrame.edgePairCoord_terminal hunit,
      Erdos957Cases13.sqDist, hsource, CyclicHullData.pairSub,
      CyclicHullData.pairCross, ea, eq] at hcross hedgeCross ⊢
    nlinarith

/-- The terminal chart on `pred → source` uses the negative of the aligned
source-to-predecessor displacement. -/
lemma terminalEdgePairCoord_eq_aligned
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (pred q : Vertex A) (hunit : dist (pred : Point) (source.1 : Point) = 1) :
    Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
        ((source.1 : Point) - pred) (q : Point) =
      pairEdgeTransform
        (-(C.coord source pred).1, -(C.coord source pred).2)
        (C.coord source q) := by
  have h := outgoingEdgePairCoord_eq_aligned C source pred q
    (by simpa [dist_comm] using hunit)
  calc
    _ = (-(Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
          ((pred : Point) - source.1) (q : Point)).1,
        -(Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
          ((pred : Point) - source.1) (q : Point)).2) := by
          apply Prod.ext <;>
            simp [Erdos957EdgeFrame.edgePairCoord, PiLp.sub_apply] <;> ring
    _ = _ := by
      rw [h]
      apply Prod.ext <;>
        simp [pairEdgeTransform, pairDot, CyclicHullData.pairCross] <;> ring

/-- Prefix bounds in the incoming terminal-edge chart when the incident
Case-4 side is the predecessor. -/
theorem previous_terminal_away_prefix_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hi : P.IsFlat source)
    (hunit : dist ((P.next⁻¹ source).1 : Point) (source.1 : Point) = 1)
    (k : Fin 3) :
    let q := ((P.next ^ (k.1 + 1)) source).1
    let z := (Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      (P.next⁻¹ source).1.1 source.1.1 hunit).toCanonical q
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < z 0 ∧
      -z 1 ≤ z 0 / 10 := by
  let pred := P.next⁻¹ source
  let e : ℝ × ℝ :=
    (-((F.chart.coord source pred.1).1),
      -((F.chart.coord source pred.1).2))
  let p : ℕ → ℝ × ℝ := fun n ↦
    pairEdgeTransform e (F.chart.rightOrbitCoord P source n)
  obtain ⟨hl0, -, -, -⟩ := F.leftFlatAngles source hi
  obtain ⟨hr0, hr1, hr2, -⟩ := F.rightFlatAngles source hi
  have hleftPolar := F.leftPolar source 0
  have hleftNorm :
      (F.chart.leftOrbitReflectedCoord P source 1).1 ^ 2 +
          (F.chart.leftOrbitReflectedCoord P source 1).2 ^ 2 = 1 := by
    have hs := F.chart.sqDist_coord source pred.1 source.1
    rw [show dist (pred.1 : Point) (source.1 : Point) = 1 by simpa [pred]] at hs
    simp only [Erdos957Cases13.sqDist, F.chart.coord_source,
      sub_zero, neg_sq, one_pow] at hs
    simpa [pred, CyclicHullData.AlignedChartData.leftOrbitReflectedCoord] using hs
  have hleftRadius : F.leftRadius source 0 = 1 := by
    rcases hleftPolar with ⟨hx, hy⟩
    have htrig := Real.sin_sq_add_cos_sq (F.leftAngle source 0)
    have hrad := F.leftRadius_ge_one source 0
    norm_num at hx hy
    have hrsq : F.leftRadius source 0 ^ 2 = 1 := by
      calc
        _ = F.leftRadius source 0 ^ 2 *
            (Real.sin (F.leftAngle source 0) ^ 2 +
              Real.cos (F.leftAngle source 0) ^ 2) := by rw [htrig]; ring
        _ = (F.chart.leftOrbitReflectedCoord P source 1).1 ^ 2 +
            (F.chart.leftOrbitReflectedCoord P source 1).2 ^ 2 := by
              rw [hx, hy]
              ring
        _ = 1 := hleftNorm
    nlinarith
  have he : e =
      (Real.cos (-F.leftAngle source 0),
        Real.sin (-F.leftAngle source 0)) := by
    rcases F.leftPolar source 0 with ⟨hx, hy⟩
    norm_num at hx hy
    rw [hleftRadius] at hx hy
    norm_num at hx hy
    simp only [e, CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
      pow_one] at hx hy ⊢
    rw [Real.cos_neg, Real.sin_neg]
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> linarith
  have hp0 : p 0 = (0, 0) := by
    simp [p, pairEdgeTransform, pairDot, CyclicHullData.pairCross]
  have hp : ∀ j : Fin 3,
      Erdos957Locality.IsPolarEdge (p j.1) (p (j.1 + 1))
        (F.rightRadius source j.castSucc)
        (![F.rightAngle source 0 + F.leftAngle source 0,
          F.rightAngle source 1 + F.leftAngle source 0,
          F.rightAngle source 2 + F.leftAngle source 0] j) := by
    intro j
    have h := pairEdgeTransform_polar he (F.rightPolar source j.castSucc)
    fin_cases j <;> simpa [p] using h
  have hbounds := polar_three_prefix_bounds p
    (fun j ↦ F.rightRadius source j.castSucc)
    (fun j ↦ ![F.rightAngle source 0 + F.leftAngle source 0,
      F.rightAngle source 1 + F.leftAngle source 0,
      F.rightAngle source 2 + F.leftAngle source 0] j)
    hp0 hp
    (fun j ↦ F.rightRadius_ge_one source j.castSucc)
    (three_angles_plus_initial_near_horizontal hl0 hr0 hr1 hr2) k
  change ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) <
      (Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
        ((source.1 : Point) - pred.1) (((P.next ^ (k.1 + 1)) source).1 : Point)).1 ∧
    -(Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
        ((source.1 : Point) - pred.1) (((P.next ^ (k.1 + 1)) source).1 : Point)).2 ≤
      (Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
        ((source.1 : Point) - pred.1) (((P.next ^ (k.1 + 1)) source).1 : Point)).1 / 10
  rw [terminalEdgePairCoord_eq_aligned F.chart source pred.1
    ((P.next ^ (k.1 + 1)) source).1 hunit]
  simpa only [p, e,
    CyclicHullData.AlignedChartData.rightOrbitCoord] using hbounds

/-- The second edge on the away prefix advances by almost one unit in the
incoming terminal chart.  This is the per-edge fact hidden inside
`previous_terminal_away_prefix_bounds`; exposing it avoids losing the edge
direction when two adjacent Case-4 pictures are compared. -/
theorem previous_terminal_away_second_edge_fst_increment_gt
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hi : P.IsFlat source)
    (hunit : dist ((P.next⁻¹ source).1 : Point) (source.1 : Point) = 1) :
    (399 / 400 : ℝ) <
      ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
        (P.next⁻¹ source).1.1 source.1.1 hunit).toCanonical
          ((P.next ^ 2) source).1) 0 -
      ((Erdos957EdgeFrame.terminalUnitEdgeRigidChart
        (P.next⁻¹ source).1.1 source.1.1 hunit).toCanonical
          (P.next source).1) 0 := by
  let pred := P.next⁻¹ source
  let e : ℝ × ℝ :=
    (-((F.chart.coord source pred.1).1),
      -((F.chart.coord source pred.1).2))
  let p : ℕ → ℝ × ℝ := fun n ↦
    pairEdgeTransform e (F.chart.rightOrbitCoord P source n)
  obtain ⟨hl0, -, -, -⟩ := F.leftFlatAngles source hi
  obtain ⟨hr0, hr1, hr2, -⟩ := F.rightFlatAngles source hi
  have hleftPolar := F.leftPolar source 0
  have hleftNorm :
      (F.chart.leftOrbitReflectedCoord P source 1).1 ^ 2 +
          (F.chart.leftOrbitReflectedCoord P source 1).2 ^ 2 = 1 := by
    have hs := F.chart.sqDist_coord source pred.1 source.1
    rw [show dist (pred.1 : Point) (source.1 : Point) = 1 by simpa [pred]] at hs
    simp only [Erdos957Cases13.sqDist, F.chart.coord_source,
      sub_zero, neg_sq, one_pow] at hs
    simpa [pred, CyclicHullData.AlignedChartData.leftOrbitReflectedCoord] using hs
  have hleftRadius : F.leftRadius source 0 = 1 := by
    rcases hleftPolar with ⟨hx, hy⟩
    have htrig := Real.sin_sq_add_cos_sq (F.leftAngle source 0)
    have hrad := F.leftRadius_ge_one source 0
    norm_num at hx hy
    have hrsq : F.leftRadius source 0 ^ 2 = 1 := by
      calc
        _ = F.leftRadius source 0 ^ 2 *
            (Real.sin (F.leftAngle source 0) ^ 2 +
              Real.cos (F.leftAngle source 0) ^ 2) := by rw [htrig]; ring
        _ = (F.chart.leftOrbitReflectedCoord P source 1).1 ^ 2 +
            (F.chart.leftOrbitReflectedCoord P source 1).2 ^ 2 := by
              rw [hx, hy]
              ring
        _ = 1 := hleftNorm
    nlinarith
  have he : e =
      (Real.cos (-F.leftAngle source 0),
        Real.sin (-F.leftAngle source 0)) := by
    rcases F.leftPolar source 0 with ⟨hx, hy⟩
    norm_num at hx hy
    rw [hleftRadius] at hx hy
    norm_num at hx hy
    simp only [e, CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
      pow_one] at hx hy ⊢
    rw [Real.cos_neg, Real.sin_neg]
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> linarith
  have hp : ∀ j : Fin 3,
      Erdos957Locality.IsPolarEdge (p j.1) (p (j.1 + 1))
        (F.rightRadius source j.castSucc)
        (![F.rightAngle source 0 + F.leftAngle source 0,
          F.rightAngle source 1 + F.leftAngle source 0,
          F.rightAngle source 2 + F.leftAngle source 0] j) := by
    intro j
    have h := pairEdgeTransform_polar he (F.rightPolar source j.castSucc)
    fin_cases j <;> simpa [p] using h
  have ha := three_angles_plus_initial_near_horizontal hl0 hr0 hr1 hr2
  have hx :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.rightRadius_ge_one source (1 : Fin 4)) (ha (1 : Fin 3))
      (hp (1 : Fin 3)).1
  change (399 / 400 : ℝ) <
    (Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
      ((source.1 : Point) - pred.1) (((P.next ^ 2) source).1 : Point)).1 -
    (Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
      ((source.1 : Point) - pred.1) ((P.next source).1 : Point)).1
  rw [terminalEdgePairCoord_eq_aligned F.chart source pred.1
      ((P.next ^ 2) source).1 hunit,
    terminalEdgePairCoord_eq_aligned F.chart source pred.1
      (P.next source).1 hunit]
  norm_num at hx
  simpa only [p, e, CyclicHullData.AlignedChartData.rightOrbitCoord,
    pow_one] using hx

lemma reflectedSuccessorCoord_eq_aligned
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (hunit : dist (source.1 : Point) ((P.next source).1 : Point) = 1)
    (q : Vertex A) :
    let e := ((C.coord source (P.next source).1).1,
      -((C.coord source (P.next source).1).2))
    let qr := (-((C.coord source q).1), (C.coord source q).2)
    (Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
      P source hunit).toCanonical q =
      Erdos957Cases24.point (pairEdgeTransform e qr).1
        (pairEdgeTransform e qr).2 := by
  let out := Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
    (((P.next source).1 : Point) - source.1) (q : Point)
  have hout := outgoingEdgePairCoord_eq_aligned C source (P.next source).1 q hunit
  rw [Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart_toCanonical]
  apply Erdos957Cases24.point_ext
  · simp only [Erdos957EdgeFrame.edgePointCoord_apply_zero,
      Erdos957Cases24.point_apply_zero]
    change -out.1 = _
    dsimp only [out]
    rw [hout]
    simp [pairEdgeTransform, pairDot, CyclicHullData.pairCross]
    ring
  · simp only [Erdos957EdgeFrame.edgePointCoord_apply_one,
      Erdos957Cases24.point_apply_one]
    change out.2 = _
    dsimp only [out]
    rw [hout]
    simp [pairEdgeTransform, pairDot, CyclicHullData.pairCross]

/-- Prefix bounds in the reflected outgoing-edge chart when the incident
Case-4 side is the successor. -/
theorem next_reflected_away_prefix_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hi : P.IsFlat source)
    (hunit : dist (source.1 : Point) ((P.next source).1 : Point) = 1)
    (k : Fin 3) :
    let q := (((P.next⁻¹) ^ (k.1 + 1)) source).1
    let z := (Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
      P source hunit).toCanonical q
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < z 0 ∧
      -z 1 ≤ z 0 / 10 := by
  let succ := P.next source
  let e : ℝ × ℝ :=
    ((F.chart.coord source succ.1).1,
      -((F.chart.coord source succ.1).2))
  let p : ℕ → ℝ × ℝ := fun n ↦
    pairEdgeTransform e (F.chart.leftOrbitReflectedCoord P source n)
  obtain ⟨hr0, -, -, -⟩ := F.rightFlatAngles source hi
  obtain ⟨hl0, hl1, hl2, -⟩ := F.leftFlatAngles source hi
  have hrightPolar := F.rightPolar source 0
  have hrightNorm :
      (F.chart.rightOrbitCoord P source 1).1 ^ 2 +
          (F.chart.rightOrbitCoord P source 1).2 ^ 2 = 1 := by
    have hs := F.chart.sqDist_coord source succ.1 source.1
    rw [show dist (succ.1 : Point) (source.1 : Point) = 1 by
      simpa [succ, dist_comm] using hunit] at hs
    simp only [Erdos957Cases13.sqDist, F.chart.coord_source,
      sub_zero, one_pow] at hs
    simpa [succ, CyclicHullData.AlignedChartData.rightOrbitCoord] using hs
  have hrightRadius : F.rightRadius source 0 = 1 := by
    rcases hrightPolar with ⟨hx, hy⟩
    have htrig := Real.sin_sq_add_cos_sq (F.rightAngle source 0)
    have hrad := F.rightRadius_ge_one source 0
    norm_num at hx hy
    have hrsq : F.rightRadius source 0 ^ 2 = 1 := by
      calc
        _ = F.rightRadius source 0 ^ 2 *
            (Real.sin (F.rightAngle source 0) ^ 2 +
              Real.cos (F.rightAngle source 0) ^ 2) := by rw [htrig]; ring
        _ = (F.chart.rightOrbitCoord P source 1).1 ^ 2 +
            (F.chart.rightOrbitCoord P source 1).2 ^ 2 := by
              rw [hx, hy]
              ring
        _ = 1 := hrightNorm
    nlinarith
  have he : e =
      (Real.cos (-F.rightAngle source 0),
        Real.sin (-F.rightAngle source 0)) := by
    rcases F.rightPolar source 0 with ⟨hx, hy⟩
    norm_num at hx hy
    rw [hrightRadius] at hx hy
    norm_num at hx hy
    simp only [e, succ, CyclicHullData.AlignedChartData.rightOrbitCoord,
      pow_one] at hx hy ⊢
    rw [Real.cos_neg, Real.sin_neg]
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> linarith
  have hp0 : p 0 = (0, 0) := by
    simp [p, pairEdgeTransform, pairDot, CyclicHullData.pairCross]
  have hp : ∀ j : Fin 3,
      Erdos957Locality.IsPolarEdge (p j.1) (p (j.1 + 1))
        (F.leftRadius source j.castSucc)
        (![F.leftAngle source 0 + F.rightAngle source 0,
          F.leftAngle source 1 + F.rightAngle source 0,
          F.leftAngle source 2 + F.rightAngle source 0] j) := by
    intro j
    have h := pairEdgeTransform_polar he (F.leftPolar source j.castSucc)
    fin_cases j <;> simpa [p] using h
  have hbounds := polar_three_prefix_bounds p
    (fun j ↦ F.leftRadius source j.castSucc)
    (fun j ↦ ![F.leftAngle source 0 + F.rightAngle source 0,
      F.leftAngle source 1 + F.rightAngle source 0,
      F.leftAngle source 2 + F.rightAngle source 0] j)
    hp0 hp
    (fun j ↦ F.leftRadius_ge_one source j.castSucc)
    (three_angles_plus_initial_near_horizontal hr0 hl0 hl1 hl2) k
  dsimp only
  rw [reflectedSuccessorCoord_eq_aligned F.chart source hunit
    (((P.next⁻¹) ^ (k.1 + 1)) source).1]
  simpa only [p, e, succ,
    CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
    Erdos957Cases24.point_apply_zero,
    Erdos957Cases24.point_apply_one] using hbounds

/-- Reflected-successor analogue of
`previous_terminal_away_second_edge_fst_increment_gt`. -/
theorem next_reflected_away_second_edge_fst_increment_gt
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hi : P.IsFlat source)
    (hunit : dist (source.1 : Point) ((P.next source).1 : Point) = 1) :
    (399 / 400 : ℝ) <
      ((Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
        P source hunit).toCanonical (((P.next⁻¹) ^ 2) source).1) 0 -
      ((Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
        P source hunit).toCanonical (P.next⁻¹ source).1) 0 := by
  let succ := P.next source
  let e : ℝ × ℝ :=
    ((F.chart.coord source succ.1).1,
      -((F.chart.coord source succ.1).2))
  let p : ℕ → ℝ × ℝ := fun n ↦
    pairEdgeTransform e (F.chart.leftOrbitReflectedCoord P source n)
  obtain ⟨hr0, -, -, -⟩ := F.rightFlatAngles source hi
  obtain ⟨hl0, hl1, hl2, -⟩ := F.leftFlatAngles source hi
  have hrightPolar := F.rightPolar source 0
  have hrightNorm :
      (F.chart.rightOrbitCoord P source 1).1 ^ 2 +
          (F.chart.rightOrbitCoord P source 1).2 ^ 2 = 1 := by
    have hs := F.chart.sqDist_coord source succ.1 source.1
    rw [show dist (succ.1 : Point) (source.1 : Point) = 1 by
      simpa [succ, dist_comm] using hunit] at hs
    simp only [Erdos957Cases13.sqDist, F.chart.coord_source,
      sub_zero, one_pow] at hs
    simpa [succ, CyclicHullData.AlignedChartData.rightOrbitCoord] using hs
  have hrightRadius : F.rightRadius source 0 = 1 := by
    rcases hrightPolar with ⟨hx, hy⟩
    have htrig := Real.sin_sq_add_cos_sq (F.rightAngle source 0)
    have hrad := F.rightRadius_ge_one source 0
    norm_num at hx hy
    have hrsq : F.rightRadius source 0 ^ 2 = 1 := by
      calc
        _ = F.rightRadius source 0 ^ 2 *
            (Real.sin (F.rightAngle source 0) ^ 2 +
              Real.cos (F.rightAngle source 0) ^ 2) := by rw [htrig]; ring
        _ = (F.chart.rightOrbitCoord P source 1).1 ^ 2 +
            (F.chart.rightOrbitCoord P source 1).2 ^ 2 := by
              rw [hx, hy]
              ring
        _ = 1 := hrightNorm
    nlinarith
  have he : e =
      (Real.cos (-F.rightAngle source 0),
        Real.sin (-F.rightAngle source 0)) := by
    rcases F.rightPolar source 0 with ⟨hx, hy⟩
    norm_num at hx hy
    rw [hrightRadius] at hx hy
    norm_num at hx hy
    simp only [e, succ, CyclicHullData.AlignedChartData.rightOrbitCoord,
      pow_one] at hx hy ⊢
    rw [Real.cos_neg, Real.sin_neg]
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> linarith
  have hp : ∀ j : Fin 3,
      Erdos957Locality.IsPolarEdge (p j.1) (p (j.1 + 1))
        (F.leftRadius source j.castSucc)
        (![F.leftAngle source 0 + F.rightAngle source 0,
          F.leftAngle source 1 + F.rightAngle source 0,
          F.leftAngle source 2 + F.rightAngle source 0] j) := by
    intro j
    have h := pairEdgeTransform_polar he (F.leftPolar source j.castSucc)
    fin_cases j <;> simpa [p] using h
  have ha := three_angles_plus_initial_near_horizontal hr0 hl0 hl1 hl2
  have hx :=
    Erdos957Locality.horizontal_increment_gt_three_nine_nine_div_four_hundred
      (F.leftRadius_ge_one source (1 : Fin 4)) (ha (1 : Fin 3))
      (hp (1 : Fin 3)).1
  rw [reflectedSuccessorCoord_eq_aligned F.chart source hunit
      (((P.next⁻¹) ^ 2) source).1,
    reflectedSuccessorCoord_eq_aligned F.chart source hunit
      (P.next⁻¹ source).1]
  norm_num at hx
  simpa only [p, e, succ,
    CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
    Erdos957Cases24.point_apply_zero, pow_one] using hx

/-! ## Continuing through the incident endpoint -/

/-- In the terminal chart on `pred → source`, the reflected backward orbit
has the same positive longitudinal projection as the negative of the actual
terminal-chart coordinate. -/
lemma terminalCoord_neg_fst_eq_reflectedTransform_fst
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (q : Vertex A)
    (hunit : dist ((P.next⁻¹ source).1 : Point) (source.1 : Point) = 1) :
    -(Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
        ((source.1 : Point) - (P.next⁻¹ source).1) (q : Point)).1 =
      (pairEdgeTransform (C.leftOrbitReflectedCoord P source 1)
        (-(C.coord source q).1, (C.coord source q).2)).1 := by
  have hcoord := congrArg Prod.fst
    (terminalEdgePairCoord_eq_aligned C source (P.next⁻¹ source).1 q hunit)
  rw [hcoord]
  simp only [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord,
    pow_one]
  simp [pairEdgeTransform, pairDot, CyclicHullData.pairCross]
  ring

/-- The two hull vertices beyond the incident predecessor continue almost
one unit per step to the negative side of the normalized terminal chart. -/
theorem previous_terminal_incident_prefix_metric_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hi : P.IsFlat source)
    (hunit : dist ((P.next⁻¹ source).1 : Point) (source.1 : Point) = 1)
    (k : Fin 3) :
    let q := (((P.next⁻¹) ^ (k.1 + 1)) source).1
    let z := (Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      (P.next⁻¹ source).1.1 source.1.1 hunit).toCanonical q
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < -z 0 ∧
      -z 1 ≤ (-z 0) / 10 := by
  let p : ℕ → ℝ × ℝ := fun n ↦
    pairEdgeTransform (F.chart.leftOrbitReflectedCoord P source 1)
      (F.chart.leftOrbitReflectedCoord P source n)
  obtain ⟨_hl0, hl1, hl2, _hl3⟩ := F.leftFlatAngles source hi
  have hnorm :
      (F.chart.leftOrbitReflectedCoord P source 1).1 ^ 2 +
          (F.chart.leftOrbitReflectedCoord P source 1).2 ^ 2 = 1 := by
    have hs := F.chart.sqDist_coord source (P.next⁻¹ source).1 source.1
    rw [hunit] at hs
    simp only [Erdos957Cases13.sqDist, F.chart.coord_source,
      sub_zero, neg_sq, one_pow] at hs
    simpa [CyclicHullData.AlignedChartData.leftOrbitReflectedCoord] using hs
  have hradius : F.leftRadius source 0 = 1 := by
    rcases F.leftPolar source 0 with ⟨hx, hy⟩
    have htrig := Real.sin_sq_add_cos_sq (F.leftAngle source 0)
    have hrad := F.leftRadius_ge_one source 0
    norm_num at hx hy
    have hrsq : F.leftRadius source 0 ^ 2 = 1 := by
      calc
        _ = F.leftRadius source 0 ^ 2 *
            (Real.sin (F.leftAngle source 0) ^ 2 +
              Real.cos (F.leftAngle source 0) ^ 2) := by rw [htrig]; ring
        _ = (F.chart.leftOrbitReflectedCoord P source 1).1 ^ 2 +
            (F.chart.leftOrbitReflectedCoord P source 1).2 ^ 2 := by
              rw [hx, hy]
              ring
        _ = 1 := hnorm
    nlinarith
  have he : F.chart.leftOrbitReflectedCoord P source 1 =
      (Real.cos (F.leftAngle source 0),
        Real.sin (F.leftAngle source 0)) := by
    rcases F.leftPolar source 0 with ⟨hx, hy⟩
    norm_num at hx hy
    rw [hradius] at hx hy
    norm_num at hx hy
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> linarith
  have hp0 : p 0 = (0, 0) := by
    simp [p, pairEdgeTransform, pairDot, CyclicHullData.pairCross]
  have hp : ∀ j : Fin 3,
      Erdos957Locality.IsPolarEdge (p j.1) (p (j.1 + 1))
        (F.leftRadius source j.castSucc)
        (![0, F.leftAngle source 1 - F.leftAngle source 0,
          F.leftAngle source 2 - F.leftAngle source 0] j) := by
    intro j
    have h := pairEdgeTransform_polar he (F.leftPolar source j.castSucc)
    fin_cases j <;> simpa [p] using h
  have hbounds := polar_three_prefix_bounds p
    (fun j ↦ F.leftRadius source j.castSucc)
    (fun j ↦ ![0, F.leftAngle source 1 - F.leftAngle source 0,
      F.leftAngle source 2 - F.leftAngle source 0] j)
    hp0 hp
    (fun j ↦ F.leftRadius_ge_one source j.castSucc)
    (three_angles_relative_initial_near_horizontal hl1 hl2) k
  constructor
  · change ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) <
      -(Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
        ((source.1 : Point) - (P.next⁻¹ source).1)
        ((((P.next⁻¹) ^ (k.1 + 1)) source).1 : Point)).1
    rw [terminalCoord_neg_fst_eq_reflectedTransform_fst F.chart source
      (((P.next⁻¹) ^ (k.1 + 1)) source).1 hunit]
    simpa only [p,
      CyclicHullData.AlignedChartData.leftOrbitReflectedCoord] using hbounds.1
  · have hcoord := terminalEdgePairCoord_eq_aligned F.chart source
      (P.next⁻¹ source).1 (((P.next⁻¹) ^ (k.1 + 1)) source).1 hunit
    change
      -(Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
        ((source.1 : Point) - (P.next⁻¹ source).1)
        ((((P.next⁻¹) ^ (k.1 + 1)) source).1 : Point)).2 ≤
      (-(Erdos957EdgeFrame.edgePairCoord (source.1 : Point)
        ((source.1 : Point) - (P.next⁻¹ source).1)
        ((((P.next⁻¹) ^ (k.1 + 1)) source).1 : Point)).1) / 10
    rw [hcoord]
    convert hbounds.2 using 1 <;>
      simp [p, pairEdgeTransform, pairDot,
        CyclicHullData.pairCross,
        CyclicHullData.AlignedChartData.leftOrbitReflectedCoord] <;> ring

/-- Longitudinal projection retained for existing callers. -/
theorem previous_terminal_incident_prefix_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hi : P.IsFlat source)
    (hunit : dist ((P.next⁻¹ source).1 : Point) (source.1 : Point) = 1)
    (k : Fin 3) :
    let q := (((P.next⁻¹) ^ (k.1 + 1)) source).1
    let z := (Erdos957EdgeFrame.terminalUnitEdgeRigidChart
      (P.next⁻¹ source).1.1 source.1.1 hunit).toCanonical q
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < -z 0 :=
  (previous_terminal_incident_prefix_metric_bounds F source hi hunit k).1

/-- In the reflected successor chart, the negative horizontal coordinate
of a forward-orbit vertex is its longitudinal projection onto the first
forward hull edge. -/
lemma reflectedSuccessorCoord_neg_fst_eq_rightTransform_fst
    (C : P.AlignedChartData) (source : {p // p ∈ P.H})
    (q : Vertex A)
    (hunit : dist (source.1 : Point) ((P.next source).1 : Point) = 1) :
    -((Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
        P source hunit).toCanonical q) 0 =
      (pairEdgeTransform (C.rightOrbitCoord P source 1)
        (C.coord source q)).1 := by
  rw [reflectedSuccessorCoord_eq_aligned C source hunit q]
  simp only [Erdos957Cases24.point_apply_zero,
    CyclicHullData.AlignedChartData.rightOrbitCoord, pow_one]
  simp [pairEdgeTransform, pairDot, CyclicHullData.pairCross]
  ring

/-- Successor-side analogue of
`previous_terminal_incident_prefix_bounds`. -/
theorem next_reflected_incident_prefix_metric_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hi : P.IsFlat source)
    (hunit : dist (source.1 : Point) ((P.next source).1 : Point) = 1)
    (k : Fin 3) :
    let q := ((P.next ^ (k.1 + 1)) source).1
    let z := (Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
      P source hunit).toCanonical q
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < -z 0 ∧
      -z 1 ≤ (-z 0) / 10 := by
  let p : ℕ → ℝ × ℝ := fun n ↦
    pairEdgeTransform (F.chart.rightOrbitCoord P source 1)
      (F.chart.rightOrbitCoord P source n)
  obtain ⟨_hr0, hr1, hr2, _hr3⟩ := F.rightFlatAngles source hi
  have hnorm :
      (F.chart.rightOrbitCoord P source 1).1 ^ 2 +
          (F.chart.rightOrbitCoord P source 1).2 ^ 2 = 1 := by
    have hs := F.chart.sqDist_coord source (P.next source).1 source.1
    rw [show dist ((P.next source).1 : Point) (source.1 : Point) = 1 by
      simpa [dist_comm] using hunit] at hs
    simp only [Erdos957Cases13.sqDist, F.chart.coord_source,
      sub_zero, one_pow] at hs
    simpa [CyclicHullData.AlignedChartData.rightOrbitCoord] using hs
  have hradius : F.rightRadius source 0 = 1 := by
    rcases F.rightPolar source 0 with ⟨hx, hy⟩
    have htrig := Real.sin_sq_add_cos_sq (F.rightAngle source 0)
    have hrad := F.rightRadius_ge_one source 0
    norm_num at hx hy
    have hrsq : F.rightRadius source 0 ^ 2 = 1 := by
      calc
        _ = F.rightRadius source 0 ^ 2 *
            (Real.sin (F.rightAngle source 0) ^ 2 +
              Real.cos (F.rightAngle source 0) ^ 2) := by rw [htrig]; ring
        _ = (F.chart.rightOrbitCoord P source 1).1 ^ 2 +
            (F.chart.rightOrbitCoord P source 1).2 ^ 2 := by
              rw [hx, hy]
              ring
        _ = 1 := hnorm
    nlinarith
  have he : F.chart.rightOrbitCoord P source 1 =
      (Real.cos (F.rightAngle source 0),
        Real.sin (F.rightAngle source 0)) := by
    rcases F.rightPolar source 0 with ⟨hx, hy⟩
    norm_num at hx hy
    rw [hradius] at hx hy
    norm_num at hx hy
    apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> linarith
  have hp0 : p 0 = (0, 0) := by
    simp [p, pairEdgeTransform, pairDot, CyclicHullData.pairCross]
  have hp : ∀ j : Fin 3,
      Erdos957Locality.IsPolarEdge (p j.1) (p (j.1 + 1))
        (F.rightRadius source j.castSucc)
        (![0, F.rightAngle source 1 - F.rightAngle source 0,
          F.rightAngle source 2 - F.rightAngle source 0] j) := by
    intro j
    have h := pairEdgeTransform_polar he (F.rightPolar source j.castSucc)
    fin_cases j <;> simpa [p] using h
  have hbounds := polar_three_prefix_bounds p
    (fun j ↦ F.rightRadius source j.castSucc)
    (fun j ↦ ![0, F.rightAngle source 1 - F.rightAngle source 0,
      F.rightAngle source 2 - F.rightAngle source 0] j)
    hp0 hp
    (fun j ↦ F.rightRadius_ge_one source j.castSucc)
    (three_angles_relative_initial_near_horizontal hr1 hr2) k
  constructor
  · change ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) <
      -((Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
        P source hunit).toCanonical
          ((P.next ^ (k.1 + 1)) source).1) 0
    rw [reflectedSuccessorCoord_neg_fst_eq_rightTransform_fst
      F.chart source ((P.next ^ (k.1 + 1)) source).1 hunit]
    simpa only [p, CyclicHullData.AlignedChartData.rightOrbitCoord]
      using hbounds.1
  · have hcoord := reflectedSuccessorCoord_eq_aligned F.chart source hunit
      ((P.next ^ (k.1 + 1)) source).1
    change
      -((Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
        P source hunit).toCanonical
          ((P.next ^ (k.1 + 1)) source).1) 1 ≤
      (-((Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
        P source hunit).toCanonical
          ((P.next ^ (k.1 + 1)) source).1) 0) / 10
    rw [hcoord]
    convert hbounds.2 using 1 <;>
      simp [p, pairEdgeTransform, pairDot,
        CyclicHullData.pairCross,
        CyclicHullData.AlignedChartData.rightOrbitCoord] <;> ring

/-- Longitudinal projection retained for existing callers. -/
theorem next_reflected_incident_prefix_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (hi : P.IsFlat source)
    (hunit : dist (source.1 : Point) ((P.next source).1 : Point) = 1)
    (k : Fin 3) :
    let q := ((P.next ^ (k.1 + 1)) source).1
    let z := (Erdos957TwoExtremeAligned.reflectedSuccessorUnitEdgeRigidChart
      P source hunit).toCanonical q
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < -z 0 :=
  (next_reflected_incident_prefix_metric_bounds F source hi hunit k).1

/-- The first three hull vertices continuing away from the incident
two-extreme edge, expressed without choosing its reflected orientation. -/
def awayHullVertex (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (side : CyclicSide) (k : Fin 3) : {p // p ∈ P.H} :=
  match side with
  | .previous => (P.next ^ (k.1 + 1)) source
  | .next => ((P.next⁻¹) ^ (k.1 + 1)) source

/-- The first three vertices reached by continuing through the incident
two-extreme endpoint rather than away from it. -/
def incidentHullVertex (P : CyclicHullData A) (source : {p // p ∈ P.H})
    (side : CyclicSide) (k : Fin 3) : {p // p ∈ P.H} :=
  match side with
  | .previous => ((P.next⁻¹) ^ (k.1 + 1)) source
  | .next => (P.next ^ (k.1 + 1)) source

/-- The away-prefix estimate depends only on the literal side-normalized
frame specification.  This is the formula-level form used by exceptional
Case-2 and Case-4 descriptors, which intentionally do not retain a second
copy of the two-extreme witness. -/
theorem sideNormalizedFrame_away_prefix_metric_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (side : CyclicSide) (frame : Erdos957Case24Bridge.Framed.RigidChart)
    (spec : ActualCase24Rows.SideNormalizedFrameSpec P source side frame)
    (hi : P.IsFlat source) (k : Fin 3) :
    let z := frame.toCanonical (awayHullVertex P source side k).1
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < z 0 ∧
      -z 1 ≤ z 0 / 10 := by
  cases spec with
  | previous hside hunit hframe =>
      rw [hside]
      simp only [awayHullVertex]
      rw [hframe]
      exact previous_terminal_away_prefix_bounds F source hi hunit k
  | next hside hunit hframe =>
      rw [hside]
      simp only [awayHullVertex]
      rw [hframe]
      exact next_reflected_away_prefix_bounds F source hi hunit k

/-- The second away hull edge has almost-unit positive longitudinal
projection in either literal side-normalized frame. -/
theorem sideNormalizedFrame_away_second_edge_fst_increment_gt
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (side : CyclicSide) (frame : Erdos957Case24Bridge.Framed.RigidChart)
    (spec : ActualCase24Rows.SideNormalizedFrameSpec P source side frame)
    (hi : P.IsFlat source) :
    (399 / 400 : ℝ) <
      (frame.toCanonical (awayHullVertex P source side 1).1) 0 -
        (frame.toCanonical (awayHullVertex P source side 0).1) 0 := by
  cases spec with
  | previous hside hunit hframe =>
      rw [hside]
      simp only [awayHullVertex]
      rw [hframe]
      exact previous_terminal_away_second_edge_fst_increment_gt
        F source hi hunit
  | next hside hunit hframe =>
      rw [hside]
      simp only [awayHullVertex]
      rw [hframe]
      exact next_reflected_away_second_edge_fst_increment_gt
        F source hi hunit

/-- Formula-level incident-continuation estimate. -/
theorem sideNormalizedFrame_incident_prefix_bound
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (side : CyclicSide) (frame : Erdos957Case24Bridge.Framed.RigidChart)
    (spec : ActualCase24Rows.SideNormalizedFrameSpec P source side frame)
    (hi : P.IsFlat source) (k : Fin 3) :
    let z := frame.toCanonical (incidentHullVertex P source side k).1
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < -z 0 := by
  cases spec with
  | previous hside hunit hframe =>
      rw [hside]
      simp only [incidentHullVertex]
      rw [hframe]
      exact previous_terminal_incident_prefix_bounds F source hi hunit k
  | next hside hunit hframe =>
      rw [hside]
      simp only [incidentHullVertex]
      rw [hframe]
      exact next_reflected_incident_prefix_bounds F source hi hunit k

/-- The incident continuation is shallow as well as longitudinally
negative in the side-normalized chart.  This is the second component
already computed by the polar-prefix proof above, exposed for collision
geometry. -/
theorem sideNormalizedFrame_incident_prefix_metric_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (side : CyclicSide) (frame : Erdos957Case24Bridge.Framed.RigidChart)
    (spec : ActualCase24Rows.SideNormalizedFrameSpec P source side frame)
    (hi : P.IsFlat source) (k : Fin 3) :
    let z := frame.toCanonical (incidentHullVertex P source side k).1
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < -z 0 ∧
      -z 1 ≤ (-z 0) / 10 := by
  cases spec with
  | previous hside hunit hframe =>
      rw [hside]
      simp only [incidentHullVertex]
      rw [hframe]
      exact previous_terminal_incident_prefix_metric_bounds
        F source hi hunit k
  | next hside hunit hframe =>
      rw [hside]
      simp only [incidentHullVertex]
      rw [hframe]
      exact next_reflected_incident_prefix_metric_bounds
        F source hi hunit k

/-- Reflection-safe negative-side prefix control through the incident
endpoint of a two-extreme normalized frame. -/
theorem normalizedFrame_incident_prefix_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (hi : P.IsFlat source) (k : Fin 3) :
    let z := N.frame.toCanonical (incidentHullVertex P source T.side k).1
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < -z 0 := by
  exact sideNormalizedFrame_incident_prefix_bound F source T.side
    N.frame N.frame_spec hi k

/-- Reflection-safe full incident-prefix metric estimate. -/
theorem normalizedFrame_incident_prefix_metric_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (hi : P.IsFlat source) (k : Fin 3) :
    let z := N.frame.toCanonical (incidentHullVertex P source T.side k).1
    ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < -z 0 ∧
      -z 1 ≤ (-z 0) / 10 := by
  exact sideNormalizedFrame_incident_prefix_metric_bounds F source T.side
    N.frame N.frame_spec hi k

/-- Reflection-safe normalized-edge prefix control.  The away orbit lies
in a shallow inward cone, advances by almost one unit per hull edge, and is
strictly below the supporting edge. -/
theorem normalizedFrame_away_prefix_bounds
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (hi : P.IsFlat source) (k : Fin 3) :
    let z := N.frame.toCanonical (awayHullVertex P source T.side k).1
    z 1 < 0 ∧
      ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < z 0 ∧
      -z 1 ≤ z 0 / 10 := by
  have hmetric :
      ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) <
          (N.frame.toCanonical (awayHullVertex P source T.side k).1) 0 ∧
        -(N.frame.toCanonical (awayHullVertex P source T.side k).1) 1 ≤
          (N.frame.toCanonical (awayHullVertex P source T.side k).1) 0 / 10 := by
    cases N.frame_spec with
    | previous hside hunit hframe =>
        rw [hside]
        simp only [awayHullVertex]
        rw [hframe]
        exact previous_terminal_away_prefix_bounds F source hi hunit k
    | next hside hunit hframe =>
        rw [hside]
        simp only [awayHullVertex]
        rw [hframe]
        exact next_reflected_away_prefix_bounds F source hi hunit k
  let z := N.frame.toCanonical (awayHullVertex P source T.side k).1
  have hzMem : z ∈ N.frame.image A := by
    exact Finset.mem_image.mpr
      ⟨(awayHullVertex P source T.side k).1,
        (awayHullVertex P source T.side k).1.property, rfl⟩
  have hzNotEndpoints :
      z ∉ ({Erdos957Cases24.Case2.uPrev,
        Erdos957Cases24.Case2.u} : Finset Point) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor
    · intro hz
      have hx := hmetric.1
      have hpos : (0 : ℝ) <
          ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) := by positivity
      change ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < z 0 at hx
      rw [show z = Erdos957Cases24.Case2.uPrev by exact hz] at hx
      norm_num [Erdos957Cases24.Case2.uPrev] at hx
      linarith
    · intro hz
      have hx := hmetric.1
      have hpos : (0 : ℝ) <
          ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) := by positivity
      change ((k.1 + 1 : ℕ) : ℝ) * (399 / 400 : ℝ) < z 0 at hx
      rw [show z = Erdos957Cases24.Case2.u by exact hz] at hx
      norm_num [Erdos957Cases24.Case2.u] at hx
      linarith
  exact ⟨N.strict_support z hzMem hzNotEndpoints, hmetric⟩

/-- Reflection-safe almost-unit longitudinal increment along the second
away hull edge. -/
theorem normalizedFrame_away_second_edge_fst_increment_gt
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (hi : P.IsFlat source) :
    (399 / 400 : ℝ) <
      (N.frame.toCanonical (awayHullVertex P source T.side 1).1) 0 -
        (N.frame.toCanonical (awayHullVertex P source T.side 0).1) 0 := by
  exact sideNormalizedFrame_away_second_edge_fst_increment_gt
    F source T.side N.frame N.frame_spec hi

lemma normalizedFrame_away_second_fst_gt_three_halves
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (hi : P.IsFlat source) :
    (3 / 2 : ℝ) <
      (N.frame.toCanonical (awayHullVertex P source T.side 1).1) 0 := by
  have h := (normalizedFrame_away_prefix_bounds F source middle T N hi 1).2.1
  norm_num at h ⊢
  linarith

lemma normalizedFrame_away_third_fst_gt_five_halves
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (hi : P.IsFlat source) :
    (5 / 2 : ℝ) <
      (N.frame.toCanonical (awayHullVertex P source T.side 2).1) 0 := by
  have h := (normalizedFrame_away_prefix_bounds F source middle T N hi 2).2.1
  norm_num at h ⊢
  linarith

lemma normalizedFrame_incident_second_fst_lt_neg_three_halves
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (hi : P.IsFlat source) :
    (N.frame.toCanonical (incidentHullVertex P source T.side 1).1) 0 <
      -(3 / 2 : ℝ) := by
  have h := normalizedFrame_incident_prefix_bounds F source middle T N hi 1
  norm_num at h ⊢
  linarith

lemma normalizedFrame_incident_third_fst_lt_neg_five_halves
    (F : P.FlatAlignedFrameData) (source : {p // p ∈ P.H})
    (middle : Vertex A)
    (T : TwoExtremeCyclicWitness P source middle)
    (N : ActualCase24Rows.TwoExtremeNormalizedFrame source middle T)
    (hi : P.IsFlat source) :
    (N.frame.toCanonical (incidentHullVertex P source T.side 2).1) 0 <
      -(5 / 2 : ℝ) := by
  have h := normalizedFrame_incident_prefix_bounds F source middle T N hi 2
  norm_num at h ⊢
  linarith

end Erdos957Case4NoThree
