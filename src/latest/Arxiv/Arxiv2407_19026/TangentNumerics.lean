import Arxiv.Arxiv2407_19026.TangentRounds

open LeanCert.Core LeanCert.Engine LeanCert.Validity

noncomputable section

namespace Arxiv2407_19026

/-!
# Certified numerics for the three tangent-envelope rounds

The formulas below remove the cancelling `z * log z` terms and extend
continuously to `z = 0`.  The numerical layer is checked by rational affine
interval arithmetic; no floating-point result enters a theorem.
-/

def tangentCorrectionSlope (β z : ℝ) : ℝ :=
  (-(1 / 4 : ℝ) + 2 * β * z + (6 / 25 : ℝ) * z ^ 2 -
    (-(1 / 4 : ℝ) * z + β * z ^ 2 + (2 / 25 : ℝ) * z ^ 3)) *
    Real.exp (-z)

def tangentCorrectionSlopeDeriv (β z : ℝ) : ℝ :=
  let p :=
    (-(1 / 4 : ℝ) + 2 * β * z + (6 / 25 : ℝ) * z ^ 2 -
      (-(1 / 4 : ℝ) * z + β * z ^ 2 + (2 / 25 : ℝ) * z ^ 3))
  let p' :=
    2 * β + (12 / 25 : ℝ) * z -
      (-(1 / 4 : ℝ) + 2 * β * z + (6 / 25 : ℝ) * z ^ 2)
  (p' - p) * Real.exp (-z)

def tangentMuPrime (z : ℝ) : ℝ :=
  (1 - z) * Real.exp (-z)

def tangentBlue (β z : ℝ) : ℝ :=
  z * Real.exp
    (-Real.log (1 + z) - tangentCorrectionSlope β z)

def tangentBluePrime (β z : ℝ) : ℝ :=
  let e :=
    Real.exp (-Real.log (1 + z) - tangentCorrectionSlope β z)
  e * (1 - z *
    ((1 + z)⁻¹ + tangentCorrectionSlopeDeriv β z))

def tangentXCoord (β z : ℝ) : ℝ :=
  let p := 1 - tangentBlue β z
  let om := 1 - optimizationM z
  Real.exp (Real.log p * Real.exp (-Real.log om)) * om

def tangentXLog (β z : ℝ) : ℝ :=
  let p := 1 - tangentBlue β z
  let om := 1 - optimizationM z
  Real.log p * Real.exp (-Real.log om) + Real.log om

def tangentXLogPrime (β z : ℝ) : ℝ :=
  let p := 1 - tangentBlue β z
  let om := 1 - optimizationM z
  (-tangentBluePrime β z * p⁻¹ * om⁻¹ +
      Real.log p * tangentMuPrime z * (om⁻¹) ^ 2 -
      tangentMuPrime z * om⁻¹)

def tangentALog (β t : ℝ) : ℝ :=
  -Real.log (1 + t) +
    t ^ 2 *
      (1 / 4 + β + (4 / 25 - β) * t - (2 / 25) * t ^ 2) *
      Real.exp (-t)

def tangentALogPrime (β t : ℝ) : ℝ :=
  let q :=
    1 / 4 + β + (4 / 25 - β) * t - (2 / 25) * t ^ 2
  let qDeriv := 4 / 25 - β - (4 / 25) * t
  (-(1 + t)⁻¹ +
    Real.exp (-t) *
      (2 * t * q + t ^ 2 * qDeriv - t ^ 2 * q))

def tangentBLog (β t : ℝ) : ℝ :=
  Real.log t - Real.log (1 + t) - tangentCorrectionSlope β t

def tangentA (β t : ℝ) : ℝ :=
  Real.exp (tangentALog β t)

def tangentB (β t : ℝ) : ℝ :=
  t * Real.exp
    (-Real.log (1 + t) - tangentCorrectionSlope β t)

def tangentSmallT (z : ℝ) : ℝ := (11 / 5) * z

def tangentSmallYLogOverZ (β z : ℝ) : ℝ :=
  Real.log (11 / 5 : ℝ) -
    Real.log (1 + tangentSmallT z) -
    tangentCorrectionSlope β (tangentSmallT z)

def tangentSmallYLogOverZPrime (β z : ℝ) : ℝ :=
  -(11 / 5 : ℝ) *
    ((1 + tangentSmallT z)⁻¹ +
      tangentCorrectionSlopeDeriv β (tangentSmallT z))

def tangentSmallCoordLog (β₀ β₁ z : ℝ) : ℝ :=
  tangentALog β₀ (tangentSmallT z) - tangentXLog β₁ z

def tangentSmallCoordLogPrime (β₀ β₁ z : ℝ) : ℝ :=
  (11 / 5 : ℝ) *
      tangentALogPrime β₀ (tangentSmallT z) -
    tangentXLogPrime β₁ z

def tangentCleanBookMargin (β z logYOverZ : ℝ) : ℝ :=
  (1 + z) * Real.log (1 + z) + ramseyCorrection β z +
    (tangentXLog β z - z ^ 2 + z * logYOverZ) / 2

def tangentSmallBookMargin (β₀ β₁ z : ℝ) : ℝ :=
  tangentCleanBookMargin β₁ z (tangentSmallYLogOverZ β₀ z)

def tangentSmallBookMarginPrime (β₀ β₁ z : ℝ) : ℝ :=
  Real.log (1 + z) + 1 + tangentCorrectionSlope β₁ z +
    (tangentXLogPrime β₁ z - 2 * z +
      tangentSmallYLogOverZ β₀ z +
      z * tangentSmallYLogOverZPrime β₀ z) / 2

def tangentRatHorner (u : ℝ) : List ℚ → ℝ
  | [] => 0
  | a :: as => (a : ℝ) + u * tangentRatHorner u as

def tangentLocalPoly (a : ℚ) (cs : List ℚ) (z : ℝ) : ℝ :=
  tangentRatHorner (z - (a : ℝ)) cs

namespace TangentAffine

def z : Expr := .var 0
def c (q : ℚ) : Expr := .const q
def add := Expr.add
def mul := Expr.mul
def neg := Expr.neg
def sub := Expr.sub
def div := Expr.div
def pow := Expr.pow

def correctionSlope (β : ℚ) (x : Expr) : Expr :=
  mul
    (sub
      (add
        (add (c (-1 / 4)) (mul (c (2 * β)) x))
        (mul (c (6 / 25)) (pow x 2)))
      (add
        (add (mul (c (-1 / 4)) x)
          (mul (c β) (pow x 2)))
        (mul (c (2 / 25)) (pow x 3))))
    (.exp (neg x))

def correctionSlopeDeriv (β : ℚ) (x : Expr) : Expr :=
  let p :=
    sub
      (add
        (add (c (-1 / 4)) (mul (c (2 * β)) x))
        (mul (c (6 / 25)) (pow x 2)))
      (add
        (add (mul (c (-1 / 4)) x)
          (mul (c β) (pow x 2)))
        (mul (c (2 / 25)) (pow x 3)))
  let pp :=
    sub
      (add (c (2 * β)) (mul (c (12 / 25)) x))
      (add
        (add (c (-1 / 4)) (mul (c (2 * β)) x))
        (mul (c (6 / 25)) (pow x 2)))
  mul (sub pp p) (.exp (neg x))

def invPos (x : Expr) : Expr := .exp (neg (.log x))

def μ : Expr := mul z (.exp (neg z))
def μ' : Expr := mul (sub (c 1) z) (.exp (neg z))

def blue (β : ℚ) : Expr :=
  mul z
    (.exp (add (neg (.log (add (c 1) z)))
      (neg (correctionSlope β z))))

def xcoord (β : ℚ) : Expr :=
  let p := sub (c 1) (blue β)
  let om := sub (c 1) μ
  mul (.exp (mul (.log p) (.exp (neg (.log om))))) om

def blue' (β : ℚ) : Expr :=
  let e :=
    .exp (add (neg (.log (add (c 1) z)))
      (neg (correctionSlope β z)))
  mul e
    (sub (c 1)
      (mul z
        (add (invPos (add (c 1) z))
          (correctionSlopeDeriv β z))))

def xlog (β : ℚ) : Expr :=
  let p := sub (c 1) (blue β)
  let om := sub (c 1) μ
  add (mul (.log p) (invPos om)) (.log om)

def xlog' (β : ℚ) : Expr :=
  let p := sub (c 1) (blue β)
  let om := sub (c 1) μ
  add
    (add
      (neg (mul (mul (blue' β) (invPos p)) (invPos om)))
      (mul (mul (.log p) μ') (pow (invPos om) 2)))
    (neg (mul μ' (invPos om)))

def tangentA (β : ℚ) (t : Expr) : Expr :=
  .exp
    (add (neg (.log (add (c 1) t)))
      (mul
        (mul (pow t 2)
          (add
            (add (c (1 / 4 + β))
              (mul (c (4 / 25 - β)) t))
            (mul (c (-2 / 25)) (pow t 2))))
        (.exp (neg t))))

def tangentB (β : ℚ) (t : Expr) : Expr :=
  mul t
    (.exp (add (neg (.log (add (c 1) t)))
      (neg (correctionSlope β t))))

def smallT : Expr := mul (c (11 / 5)) z
def tangentALog' (β : ℚ) (t : Expr) : Expr :=
  let q :=
    add
      (add (c (1 / 4 + β))
        (mul (c (4 / 25 - β)) t))
      (mul (c (-2 / 25)) (pow t 2))
  let q' := add (c (4 / 25 - β)) (mul (c (-4 / 25)) t)
  add
    (neg (invPos (add (c 1) t)))
    (mul (.exp (neg t))
      (add
        (add (mul (mul (c 2) t) q)
          (mul (pow t 2) q'))
        (neg (mul (pow t 2) q))))

def smallCoordSlope (β₀ β₁ : ℚ) : Expr :=
  sub
    (mul (c (11 / 5)) (tangentALog' β₀ smallT))
    (xlog' β₁)

def smallYLogOverZ (β₀ : ℚ) : Expr :=
  add
    (add (.log (c (11 / 5)))
      (neg (.log (add (c 1) smallT))))
    (neg (correctionSlope β₀ smallT))

def smallYLogOverZ' (β₀ : ℚ) : Expr :=
  neg
    (mul (c (11 / 5))
      (add (invPos (add (c 1) smallT))
        (correctionSlopeDeriv β₀ smallT)))

def smallBookSlope (β₀ β₁ : ℚ) : Expr :=
  add
    (add (add (.log (add (c 1) z)) (c 1))
      (correctionSlope β₁ z))
    (mul (c (1 / 2))
      (add
        (add (xlog' β₁) (mul (c (-2)) z))
        (add (smallYLogOverZ β₀)
          (mul z (smallYLogOverZ' β₀)))))

def correction (β : ℚ) : Expr :=
  mul
    (add
      (add (mul (c (-1 / 4)) z)
        (mul (c β) (pow z 2)))
      (mul (c (2 / 25)) (pow z 3)))
    (.exp (neg z))

def smallBook (β₀ β₁ : ℚ) : Expr :=
  add
    (add
      (mul (add (c 1) z) (.log (add (c 1) z)))
      (correction β₁))
    (mul (c (1 / 2))
      (add
        (add (xlog β₁) (neg (pow z 2)))
        (mul z (smallYLogOverZ β₀))))

def tangentALog (β : ℚ) (t : Expr) : Expr :=
  add (neg (.log (add (c 1) t)))
    (mul
      (mul (pow t 2)
        (add
          (add (c (1 / 4 + β))
            (mul (c (4 / 25 - β)) t))
          (mul (c (-2 / 25)) (pow t 2))))
      (.exp (neg t)))

def tangentBLog (β : ℚ) (t : Expr) : Expr :=
  add
    (add (.log t) (neg (.log (add (c 1) t))))
    (neg (correctionSlope β t))

def book (β : ℚ) (logYOverZ : Expr) : Expr :=
  add
    (add
      (mul (add (c 1) z) (.log (add (c 1) z)))
      (correction β))
    (mul (c (1 / 2))
      (add
        (add (xlog β) (neg (pow z 2)))
        (mul z logYOverZ)))

def horner (u : Expr) : List ℚ → Expr
  | [] => c 0
  | a :: as => add (c a) (mul u (horner u as))

def localPoly (a : ℚ) (cs : List ℚ) : Expr :=
  horner (sub z (c a)) cs

def r1ForwardCs : List ℚ :=
  [0.274490108077, 3.302195468460, 6.687108111306,
    8.679389702659, -85.276932241203]

def r1Back1Cs : List ℚ :=
  [0.997224373628, -4.138257629610, 11.931757071320,
    -19.405108055379, 12.549969336367]

def r1Back2Cs : List ℚ :=
  [0.493416422305, -1.185241317679, 2.802647111662,
    -4.238178100101, 2.992854989390]

def r2ForwardCs : List ℚ :=
  [0.272671664930, 3.281031479722, 6.023919414222,
    17.105674743961, -100.108877722336]

def r2Back1Cs : List ℚ :=
  [0.996001897210, -4.339468302776, 13.622329818021,
    -25.579883472595, 21.367656389184]

def r2Back2Cs : List ℚ :=
  [0.474024338617, -1.116399977009, 2.624394464499,
    -3.958323029657, 2.797575799256]

def r3ForwardCs : List ℚ :=
  [0.272018416919, 3.272807039320, 5.803332614784,
    19.695196275375, -103.812755085672]

def r3Back1Cs : List ℚ :=
  [0.996045172700, -4.409659888029, 14.226551855229,
    -27.833995842000, 24.607338805699]

def r3Back2Cs : List ℚ :=
  [0.468088971947, -1.094667543400, 2.566461506069,
    -3.865045090594, 2.730992772736]

def r1ForwardT : Expr := localPoly (1 / 10) r1ForwardCs
def r1Back1T : Expr := localPoly (387 / 1000) r1Back1Cs
def r1Back2T : Expr := localPoly (3 / 5) r1Back2Cs
def r2ForwardT : Expr := localPoly (1 / 10) r2ForwardCs
def r2Back1T : Expr := localPoly (189 / 500) r2Back1Cs
def r2Back2T : Expr := localPoly (3 / 5) r2Back2Cs
def r3ForwardT : Expr := localPoly (1 / 10) r3ForwardCs
def r3Back1T : Expr := localPoly (3 / 8) r3Back1Cs
def r3Back2T : Expr := localPoly (3 / 5) r3Back2Cs

def forwardCoord (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  sub (tangentA β₀ t) (xcoord β₁)

def forwardLogCoord (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  sub (tangentALog β₀ t) (xlog β₁)

def forwardBook (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  book β₁ (add (tangentBLog β₀ t) (neg (.log z)))

def plateauLow (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  sub (xcoord β₁) (tangentB β₀ t)

def plateauLogLow (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  sub (xlog β₁) (tangentBLog β₀ t)

def plateauHigh (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  sub (tangentA β₀ t) (xcoord β₁)

def plateauLogHigh (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  sub (tangentALog β₀ t) (xlog β₁)

def plateauBook (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  book β₁
    (add
      (add
        (add (tangentALog β₀ t) (tangentBLog β₀ t))
        (neg (xlog β₁)))
      (neg (.log z)))

def backwardCoord (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  sub (tangentB β₀ t) (xcoord β₁)

def backwardLogCoord (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  sub (tangentBLog β₀ t) (xlog β₁)

def backwardBook (β₀ β₁ : ℚ) (t : Expr) : Expr :=
  book β₁ (add (tangentALog β₀ t) (neg (.log z)))

def cfg : AffineConfig where
  taylorDepth := 10
  maxNoiseSymbols := 0

def bpsSlope : List ℚ :=
  (List.range 10).map (fun n => (n + 1 : ℚ) / 100)

def bpsBookSlope : List ℚ :=
  (List.range 20).map (fun n => (n + 1 : ℚ) / 1000)

def bpsBook : List ℚ :=
  (List.range 80).map (fun n => (n + 21 : ℚ) / 1000)

def fineBreakpoints (start count : ℕ) : List ℚ :=
  (List.range count).map (fun n => (n + start + 1 : ℚ) / 10000)

def mediumBreakpoints (start count : ℕ) : List ℚ :=
  (List.range count).map (fun n => (n + start + 1 : ℚ) / 1000)

end TangentAffine

lemma tangentCorrectionSlope_eq (β z : ℝ) :
    tangentCorrectionSlope β z =
      (-(1 / 4 : ℝ) + 2 * β * z + (6 / 25 : ℝ) * z ^ 2 -
        (-(1 / 4 : ℝ) * z + β * z ^ 2 + (2 / 25 : ℝ) * z ^ 3)) *
        Real.exp (-z) := rfl

lemma tangentBlue_eq_exp_neg_slope
    {β z : ℝ} (hz : 0 < z) :
    tangentBlue β z = Real.exp (-optimizedRamseySlope β z) := by
  calc
    tangentBlue β z =
        Real.exp (Real.log z) *
          Real.exp
            (-Real.log (1 + z) - tangentCorrectionSlope β z) := by
      rw [Real.exp_log hz]
      rfl
    _ = Real.exp
          (Real.log z +
            (-Real.log (1 + z) - tangentCorrectionSlope β z)) := by
      rw [Real.exp_add]
    _ = Real.exp (-optimizedRamseySlope β z) := by
      congr 1
      unfold optimizedRamseySlope tangentCorrectionSlope
      rw [add_comm z 1]
      ring

lemma tangentBlue_lt_one
    {β z : ℝ} (hβ : 0 ≤ β) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    tangentBlue β z < 1 := by
  rcases hz0.eq_or_lt with rfl | hz
  · norm_num [tangentBlue]
  rw [tangentBlue_eq_exp_neg_slope hz, Real.exp_lt_one_iff]
  linarith [optimizedRamseySlope_pos hβ hz hz1]

lemma optimizationM_lt_one_of_Icc
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    optimizationM z < 1 := by
  rcases hz0.eq_or_lt with rfl | hz
  · norm_num [optimizationM]
  have he0 : 0 < Real.exp (-z) := Real.exp_pos _
  have he1 : Real.exp (-z) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  unfold optimizationM
  exact mul_lt_one_of_nonneg_of_lt_one_right hz1 he0.le he1

lemma tangentXCoord_eq_optimizationX
    {β z : ℝ} (hβ : 0 ≤ β) (hz : 0 < z) (hz1 : z ≤ 1) :
    tangentXCoord β z = optimizationX β z := by
  have hb1 : tangentBlue β z < 1 :=
    tangentBlue_lt_one hβ hz.le hz1
  have hp : 0 < optimizationP β z := by
    rw [optimizationP, ← tangentBlue_eq_exp_neg_slope hz]
    linarith
  have hom : 0 < 1 - optimizationM z :=
    sub_pos.mpr (optimizationM_lt_one_of_Icc hz.le hz1)
  rw [← optimizationXExp_eq hp]
  unfold tangentXCoord optimizationXExp
  rw [show 1 - tangentBlue β z = optimizationP β z by
    rw [optimizationP, ← tangentBlue_eq_exp_neg_slope hz]]
  dsimp only
  rw [Real.exp_neg, Real.exp_log hom, div_eq_mul_inv]

lemma tangentXLog_exp
    {β z : ℝ} (hβ : 0 ≤ β) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.exp (tangentXLog β z) = tangentXCoord β z := by
  have hp : 0 < 1 - tangentBlue β z :=
    sub_pos.mpr (tangentBlue_lt_one hβ hz0 hz1)
  have hom : 0 < 1 - optimizationM z :=
    sub_pos.mpr (optimizationM_lt_one_of_Icc hz0 hz1)
  unfold tangentXLog tangentXCoord
  rw [Real.exp_add, Real.exp_log hom]

lemma tangentALog_eq_tangentExponent
    {β t : ℝ} :
    tangentALog β t =
      t * optimizedRamseySlope β t -
        optimizedRamseyExponent β t := by
  unfold tangentALog optimizedRamseySlope optimizedRamseyExponent
    ramseyEntropy ramseyCorrection
  ring_nf

lemma tangentA_eq_tangentRegionX
    {β t : ℝ} :
    tangentA β t =
      tangentRegionX (optimizedRamseyExponent β)
        (optimizedRamseySlope β) t := by
  unfold tangentA tangentRegionX
  rw [tangentALog_eq_tangentExponent]

lemma tangentB_eq_tangentRegionY
    {β t : ℝ} (ht : 0 < t) :
    tangentB β t =
      tangentRegionY (optimizedRamseySlope β) t := by
  change tangentBlue β t =
    Real.exp (-optimizedRamseySlope β t)
  rw [tangentBlue_eq_exp_neg_slope (β := β) ht]

lemma tangentBLog_exp
    {β t : ℝ} (ht : 0 < t) :
    Real.exp (tangentBLog β t) = tangentB β t := by
  calc
    Real.exp (tangentBLog β t) =
        Real.exp (Real.log t) *
          Real.exp
            (-Real.log (1 + t) - tangentCorrectionSlope β t) := by
      rw [← Real.exp_add]
      unfold tangentBLog
      congr 1
      ring
    _ = tangentB β t := by
      rw [Real.exp_log ht]
      rfl

lemma tangentA_exp (β t : ℝ) :
    Real.exp (tangentALog β t) = tangentA β t := rfl

lemma tangentCleanBookMargin_eq
    {β z logYOverZ : ℝ}
    (hβ : 0 ≤ β) (hz : 0 < z) (hz1 : z ≤ 1) :
    tangentCleanBookMargin β z logYOverZ =
      tangentRoundBookMargin β z
        (tangentXCoord β z) (z * Real.exp logYOverZ) := by
  have hom : 0 < 1 - optimizationM z :=
    sub_pos.mpr (optimizationM_lt_one_of_Icc hz.le hz1)
  have hxlog :
      Real.log (tangentXCoord β z) = tangentXLog β z := by
    rw [← tangentXLog_exp hβ hz.le hz1, Real.log_exp]
  have hmlog :
      Real.log (optimizationM z) = Real.log z - z := by
    unfold optimizationM
    rw [Real.log_mul hz.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hylog :
      Real.log (z * Real.exp logYOverZ) =
        Real.log z + logYOverZ := by
    rw [Real.log_mul hz.ne' (Real.exp_ne_zero _), Real.log_exp]
  rw [tangentCleanBookMargin, tangentRoundBookMargin,
    hxlog, hmlog, hylog]
  unfold optimizedRamseyExponent ramseyEntropy
  ring_nf

lemma hasDerivAt_tangentCorrectionSlope (β z : ℝ) :
    HasDerivAt (tangentCorrectionSlope β)
      (tangentCorrectionSlopeDeriv β z) z := by
  unfold tangentCorrectionSlope tangentCorrectionSlopeDeriv
  convert
    (((((hasDerivAt_const z (-(1 / 4 : ℝ))).add
          ((hasDerivAt_const z (2 * β)).mul (hasDerivAt_id z))).add
        ((hasDerivAt_const z (6 / 25 : ℝ)).mul
          ((hasDerivAt_id z).pow 2))).sub
      ((((hasDerivAt_const z (-(1 / 4 : ℝ))).mul
          (hasDerivAt_id z)).add
        ((hasDerivAt_const z β).mul ((hasDerivAt_id z).pow 2))).add
        ((hasDerivAt_const z (2 / 25 : ℝ)).mul
          ((hasDerivAt_id z).pow 3)))).mul
      (hasDerivAt_id z).neg.exp) using 1
  all_goals try rfl
  all_goals
    simp only [Function.id_def, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply, Pi.neg_apply]
  ring

lemma hasDerivAt_optimizationM_tangent (z : ℝ) :
    HasDerivAt optimizationM (tangentMuPrime z) z := by
  unfold optimizationM tangentMuPrime
  convert (hasDerivAt_id z).mul (hasDerivAt_id z).neg.exp using 1
  all_goals try rfl
  simp only [Function.id_def, Pi.neg_apply]
  ring

lemma hasDerivAt_tangentBlue
    (β : ℝ) {z : ℝ} (hplus : 1 + z ≠ 0) :
    HasDerivAt (tangentBlue β) (tangentBluePrime β z) z := by
  have harg := (hasDerivAt_id z).const_add 1
  have hlog := harg.log (by
    simpa [Function.id_def, add_comm] using hplus)
  have hexponent :=
    hlog.neg.sub (hasDerivAt_tangentCorrectionSlope β z)
  have hexp := hexponent.exp
  unfold tangentBlue tangentBluePrime
  convert (hasDerivAt_id z).mul hexp using 1
  all_goals try rfl
  simp only [Function.id_def, Pi.sub_apply, Pi.neg_apply]
  rw [inv_eq_one_div]
  field_simp [hplus]
  ring

lemma hasDerivAt_tangentXLog
    (β : ℝ) {z : ℝ}
    (hp : 0 < 1 - tangentBlue β z)
    (hom : 0 < 1 - optimizationM z)
    (hplus : 1 + z ≠ 0) :
    HasDerivAt (tangentXLog β) (tangentXLogPrime β z) z := by
  have hb := hasDerivAt_tangentBlue β hplus
  have hpDeriv := (hasDerivAt_const z (1 : ℝ)).sub hb
  have hm := hasDerivAt_optimizationM_tangent z
  have homDeriv := (hasDerivAt_const z (1 : ℝ)).sub hm
  have hlogp := hpDeriv.log hp.ne'
  have hlogom := homDeriv.log hom.ne'
  have hinvom := hlogom.neg.exp
  unfold tangentXLog tangentXLogPrime
  convert (hlogp.mul hinvom).add hlogom using 1
  all_goals try rfl
  all_goals
    simp only [Pi.sub_apply, Pi.neg_apply]
  rw [Real.exp_neg, Real.exp_log hom]
  field_simp [hp.ne', hom.ne']
  ring

lemma hasDerivAt_tangentALog (β t : ℝ)
    (hplus : 1 + t ≠ 0) :
    HasDerivAt (tangentALog β) (tangentALogPrime β t) t := by
  have harg := (hasDerivAt_id t).const_add 1
  have hlog := harg.log (by
    simpa [Function.id_def, add_comm] using hplus)
  have hq :=
    ((hasDerivAt_const t (1 / 4 + β : ℝ)).add
      ((hasDerivAt_const t (4 / 25 - β : ℝ)).mul
        (hasDerivAt_id t))).sub
      ((hasDerivAt_const t (2 / 25 : ℝ)).mul
        ((hasDerivAt_id t).pow 2))
  have hpoly := ((hasDerivAt_id t).pow 2).mul hq
  have hterm := hpoly.mul (hasDerivAt_id t).neg.exp
  have hraw := hlog.neg.add hterm
  unfold tangentALog tangentALogPrime
  convert hraw using 1
  all_goals try rfl
  all_goals
    try simp only [Function.id_def, Pi.add_apply, Pi.sub_apply, Pi.mul_apply,
      Pi.pow_apply, Pi.neg_apply]
  all_goals
    try field_simp [hplus]
    try ring

lemma hasDerivAt_tangentSmallCoordLog
    (β₀ β₁ : ℝ) {z : ℝ}
    (hp : 0 < 1 - tangentBlue β₁ z)
    (hom : 0 < 1 - optimizationM z)
    (hzplus : 1 + z ≠ 0)
    (htplus : 1 + tangentSmallT z ≠ 0) :
    HasDerivAt (tangentSmallCoordLog β₀ β₁)
      (tangentSmallCoordLogPrime β₀ β₁ z) z := by
  have ht :
      HasDerivAt tangentSmallT (11 / 5 : ℝ) z := by
    have hraw := (hasDerivAt_id z).mul_const (11 / 5 : ℝ)
    have hfun :
        tangentSmallT = fun y : ℝ ↦ id y * (11 / 5 : ℝ) := by
      funext x
      simp [tangentSmallT]
      ring
    rw [hfun]
    simpa using hraw
  have hA :=
    (hasDerivAt_tangentALog β₀ (tangentSmallT z) htplus).comp z ht
  have hX := hasDerivAt_tangentXLog β₁ hp hom hzplus
  have hfun :
      tangentSmallCoordLog β₀ β₁ =
        tangentALog β₀ ∘ tangentSmallT - tangentXLog β₁ := by
    funext x
    rfl
  have hcoeff :
      tangentSmallCoordLogPrime β₀ β₁ z =
        tangentALogPrime β₀ (tangentSmallT z) * (11 / 5) -
          tangentXLogPrime β₁ z := by
    unfold tangentSmallCoordLogPrime
    ring
  rw [hfun, hcoeff]
  exact hA.sub hX

lemma hasDerivAt_tangentSmallYLogOverZ
    (β : ℝ) {z : ℝ}
    (htplus : 1 + tangentSmallT z ≠ 0) :
    HasDerivAt (tangentSmallYLogOverZ β)
      (tangentSmallYLogOverZPrime β z) z := by
  have ht :
      HasDerivAt tangentSmallT (11 / 5 : ℝ) z := by
    have hraw := (hasDerivAt_id z).mul_const (11 / 5 : ℝ)
    have hfun :
        tangentSmallT = fun y : ℝ ↦ id y * (11 / 5 : ℝ) := by
      funext x
      simp [tangentSmallT]
      ring
    rw [hfun]
    simpa using hraw
  have harg := ht.const_add 1
  have hlog := harg.log (by
    simpa [Function.id_def, add_comm] using htplus)
  have hc :=
    (hasDerivAt_tangentCorrectionSlope β (tangentSmallT z)).comp z ht
  have hraw :=
    ((hasDerivAt_const z (Real.log (11 / 5 : ℝ))).sub hlog).sub hc
  have hcoeff :
      -(11 / 5 : ℝ) / (1 + tangentSmallT z) -
          tangentCorrectionSlopeDeriv β (tangentSmallT z) * (11 / 5) =
        tangentSmallYLogOverZPrime β z := by
    unfold tangentSmallYLogOverZPrime
    rw [inv_eq_one_div]
    field_simp [htplus]
    ring
  rw [← hcoeff]
  have hfun :
      tangentSmallYLogOverZ β =
        ((fun x : ℝ ↦ Real.log (11 / 5 : ℝ)) -
          fun y ↦ Real.log (1 + tangentSmallT y)) -
          tangentCorrectionSlope β ∘ tangentSmallT := by
    funext x
    rfl
  rw [hfun]
  have hcoeffRaw :
      -(11 / 5 : ℝ) / (1 + tangentSmallT z) -
          tangentCorrectionSlopeDeriv β (tangentSmallT z) * (11 / 5) =
        0 - (11 / 5 : ℝ) / (1 + tangentSmallT z) -
          tangentCorrectionSlopeDeriv β (tangentSmallT z) * (11 / 5) := by
    ring
  rw [hcoeffRaw]
  exact hraw

lemma hasDerivAt_tangentSmallBookMargin
    (β₀ β₁ : ℝ) {z : ℝ}
    (hp : 0 < 1 - tangentBlue β₁ z)
    (hom : 0 < 1 - optimizationM z)
    (hzplus : 1 + z ≠ 0)
    (htplus : 1 + tangentSmallT z ≠ 0) :
    HasDerivAt (tangentSmallBookMargin β₀ β₁)
      (tangentSmallBookMarginPrime β₀ β₁ z) z := by
  have hzarg := (hasDerivAt_id z).const_add 1
  have hzlog := hzarg.log (by
    simpa [Function.id_def, add_comm] using hzplus)
  have hmain := hzarg.mul hzlog
  have hX := hasDerivAt_tangentXLog β₁ hp hom hzplus
  have hY := hasDerivAt_tangentSmallYLogOverZ β₀ htplus
  have hbracket :=
    ((hX.sub ((hasDerivAt_id z).pow 2)).add
      ((hasDerivAt_id z).mul hY)).div_const 2
  unfold tangentSmallBookMargin tangentCleanBookMargin
    tangentSmallBookMarginPrime
  convert (hmain.add (hasDerivAt_ramseyCorrection β₁)).add hbracket
    using 1
  all_goals try rfl
  all_goals
    simp only [Function.id_def]
  unfold tangentCorrectionSlope
  field_simp [hzplus]
  ring

namespace TangentAffine

lemma eval_correctionSlope (β : ℚ) (x : Expr) (ρ : Nat → ℝ) :
    Expr.eval ρ (correctionSlope β x) =
      tangentCorrectionSlope (β : ℝ) (Expr.eval ρ x) := by
  simp [correctionSlope, tangentCorrectionSlope, c, add, mul, neg, sub,
    pow, Expr.eval]
  ring

lemma eval_correctionSlopeDeriv (β : ℚ) (x : Expr) (ρ : Nat → ℝ) :
    Expr.eval ρ (correctionSlopeDeriv β x) =
      tangentCorrectionSlopeDeriv (β : ℝ) (Expr.eval ρ x) := by
  simp [correctionSlopeDeriv, tangentCorrectionSlopeDeriv, c, add, mul,
    neg, sub, pow, Expr.eval]
  ring

lemma eval_invPos (x : Expr) (ρ : Nat → ℝ) :
    Expr.eval ρ (invPos x) =
      Real.exp (-Real.log (Expr.eval ρ x)) := by
  rfl

lemma eval_mu (t : ℝ) :
    Expr.eval (fun _ ↦ t) μ = optimizationM t := by
  simp [μ, z, mul, neg, optimizationM, Expr.eval]

lemma eval_muPrime (t : ℝ) :
    Expr.eval (fun _ ↦ t) μ' = tangentMuPrime t := by
  simp [μ', z, c, mul, neg, sub, tangentMuPrime, Expr.eval]

lemma eval_blue (β : ℚ) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (blue β) =
      tangentBlue (β : ℝ) t := by
  simp only [blue, z, c, add, mul, neg, Expr.eval_var,
    Expr.eval_const, Expr.eval_add, Expr.eval_mul, Expr.eval_neg,
    Expr.eval_exp, Expr.eval_log, eval_correctionSlope]
  unfold Arxiv2407_19026.tangentBlue
  congr 2
  ring_nf

lemma eval_xcoord (β : ℚ) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (xcoord β) =
      tangentXCoord (β : ℝ) t := by
  simp [xcoord, c, mul, neg, sub, eval_blue, eval_mu,
    tangentXCoord, Expr.eval]

lemma eval_bluePrime (β : ℚ) (t : ℝ) (hplus : 0 < 1 + t) :
    Expr.eval (fun _ ↦ t) (blue' β) =
      tangentBluePrime (β : ℝ) t := by
  simp only [blue', mul, add, neg, c, z, sub, Expr.eval_mul, Expr.eval,
    Rat.cast_one, eval_correctionSlope, Expr.eval_sub, eval_invPos,
    eval_correctionSlopeDeriv, tangentBluePrime]
  rw [Real.exp_neg, Real.exp_log hplus]
  congr 2

lemma eval_xlog (β : ℚ) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (xlog β) =
      tangentXLog (β : ℝ) t := by
  simp [xlog, c, add, mul, sub, eval_blue, eval_mu, eval_invPos,
    tangentXLog, Expr.eval]

lemma eval_xlogPrime (β : ℚ) (t : ℝ)
    (hp : 0 < 1 - tangentBlue (β : ℝ) t)
    (hom : 0 < 1 - optimizationM t)
    (hplus : 0 < 1 + t) :
    Expr.eval (fun _ ↦ t) (xlog' β) =
      tangentXLogPrime (β : ℝ) t := by
  simp [xlog', c, add, mul, neg, sub, pow, eval_blue,
    eval_bluePrime _ _ hplus,
    eval_mu, eval_muPrime, eval_invPos, tangentXLogPrime, Expr.eval,
    Real.exp_neg, Real.exp_log hp, Real.exp_log hom]
  ring

lemma eval_tangentA (β : ℚ) (x : Expr) (ρ : Nat → ℝ) :
    Expr.eval ρ (tangentA β x) =
      Arxiv2407_19026.tangentA (β : ℝ) (Expr.eval ρ x) := by
  simp only [tangentA, c, add, mul, neg, pow, Expr.eval_const,
    Expr.eval_add, Expr.eval_mul, Expr.eval_neg, Expr.eval_exp,
    Expr.eval_log, Expr.eval_pow]
  unfold Arxiv2407_19026.tangentA Arxiv2407_19026.tangentALog
  congr 2
  · norm_num
  · rw [Rat.cast_add, Rat.cast_sub]
    norm_num
    ring_nf
    simp

lemma eval_tangentB (β : ℚ) (x : Expr) (ρ : Nat → ℝ) :
    Expr.eval ρ (tangentB β x) =
      Arxiv2407_19026.tangentB (β : ℝ) (Expr.eval ρ x) := by
  simp only [tangentB, c, add, mul, neg, Expr.eval_const,
    Expr.eval_add, Expr.eval_mul, Expr.eval_neg, Expr.eval_exp,
    Expr.eval_log, eval_correctionSlope]
  unfold Arxiv2407_19026.tangentB
  congr 2
  ring_nf

lemma eval_tangentALogPrime (β : ℚ) (x : Expr) (ρ : Nat → ℝ)
    (hplus : 0 < 1 + Expr.eval ρ x) :
    Expr.eval ρ (tangentALog' β x) =
      Arxiv2407_19026.tangentALogPrime
        (β : ℝ) (Expr.eval ρ x) := by
  simp only [tangentALog', add, neg, c, mul, one_div, pow,
    Expr.eval_add, Expr.eval, eval_invPos, Rat.cast_one, Rat.cast_ofNat,
    Rat.cast_add, Rat.cast_inv, Rat.cast_sub, Rat.cast_div, Rat.cast_neg,
    Expr.eval_pow, tangentALogPrime]
  rw [Real.exp_neg, Real.exp_log hplus]
  ring

lemma eval_smallT (t : ℝ) :
    Expr.eval (fun _ ↦ t) smallT = tangentSmallT t := by
  simp [smallT, tangentSmallT, z, c, mul, Expr.eval]

lemma eval_smallCoordSlope (β₀ β₁ : ℚ) (t : ℝ)
    (hp : 0 < 1 - tangentBlue (β₁ : ℝ) t)
    (hom : 0 < 1 - optimizationM t)
    (hplus : 0 < 1 + t)
    (htplus : 0 < 1 + tangentSmallT t) :
    Expr.eval (fun _ ↦ t) (smallCoordSlope β₀ β₁) =
      tangentSmallCoordLogPrime (β₀ : ℝ) (β₁ : ℝ) t := by
  have htplus' :
      0 < 1 + Expr.eval (fun _ ↦ t) smallT := by
    simpa [eval_smallT] using htplus
  have hA :=
    eval_tangentALogPrime β₀ smallT (fun _ ↦ t) htplus'
  have hX := eval_xlogPrime β₁ t hp hom hplus
  unfold smallCoordSlope
  simp [c, mul, sub, hA, hX, eval_smallT,
    tangentSmallCoordLogPrime, Expr.eval]

lemma eval_smallYLogOverZ (β₀ : ℚ) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (smallYLogOverZ β₀) =
      tangentSmallYLogOverZ (β₀ : ℝ) t := by
  simp [smallYLogOverZ, c, add, neg, eval_smallT,
    eval_correctionSlope, tangentSmallYLogOverZ, Expr.eval]
  ring

lemma eval_smallYLogOverZPrime (β₀ : ℚ) (t : ℝ)
    (ht : 0 < 1 + tangentSmallT t) :
    Expr.eval (fun _ ↦ t) (smallYLogOverZ' β₀) =
      tangentSmallYLogOverZPrime (β₀ : ℝ) t := by
  simp [smallYLogOverZ', c, add, mul, neg, eval_smallT,
    eval_correctionSlopeDeriv, eval_invPos,
    tangentSmallYLogOverZPrime, Expr.eval, Real.exp_neg,
    Real.exp_log ht]

lemma eval_smallBookSlope (β₀ β₁ : ℚ) (t : ℝ)
    (hp : 0 < 1 - tangentBlue (β₁ : ℝ) t)
    (hom : 0 < 1 - optimizationM t)
    (hplus : 0 < 1 + t)
    (ht : 0 < 1 + tangentSmallT t) :
    Expr.eval (fun _ ↦ t) (smallBookSlope β₀ β₁) =
      tangentSmallBookMarginPrime (β₀ : ℝ) (β₁ : ℝ) t := by
  simp [smallBookSlope, z, c, add, mul,
    eval_correctionSlope, eval_xlogPrime _ _ hp hom hplus,
    eval_smallYLogOverZ, eval_smallYLogOverZPrime _ _ ht,
    tangentSmallBookMarginPrime, Expr.eval]
  ring

lemma eval_correction (β : ℚ) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (correction β) =
      ramseyCorrection (β : ℝ) t := by
  simp [correction, ramseyCorrection, z, c, add, mul, neg, pow,
    Expr.eval]
  ring

lemma eval_smallBook (β₀ β₁ : ℚ) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (smallBook β₀ β₁) =
      tangentSmallBookMargin (β₀ : ℝ) (β₁ : ℝ) t := by
  simp [smallBook, z, c, add, mul, neg, pow, eval_xlog,
    eval_smallYLogOverZ, eval_correction, tangentSmallBookMargin,
    tangentCleanBookMargin, Expr.eval]
  ring

lemma eval_tangentALog (β : ℚ) (x : Expr) (ρ : Nat → ℝ) :
    Expr.eval ρ (tangentALog β x) =
      Arxiv2407_19026.tangentALog (β : ℝ) (Expr.eval ρ x) := by
  simp only [tangentALog, c, add, mul, neg, pow, Expr.eval_const,
    Expr.eval_add, Expr.eval_mul, Expr.eval_neg, Expr.eval_exp,
    Expr.eval_log, Expr.eval_pow]
  unfold Arxiv2407_19026.tangentALog
  push_cast
  ring

lemma eval_tangentBLog (β : ℚ) (x : Expr) (ρ : Nat → ℝ) :
    Expr.eval ρ (tangentBLog β x) =
      Arxiv2407_19026.tangentBLog (β : ℝ) (Expr.eval ρ x) := by
  simp [tangentBLog, Arxiv2407_19026.tangentBLog, c, add, neg,
    eval_correctionSlope, Expr.eval]
  ring

lemma eval_book (β : ℚ) (L : Expr) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (book β L) =
      tangentCleanBookMargin (β : ℝ) t
        (Expr.eval (fun _ ↦ t) L) := by
  simp [book, tangentCleanBookMargin, z, c, add, mul, neg, pow,
    eval_xlog, eval_correction, Expr.eval]
  ring

lemma eval_horner (u : Expr) (cs : List ℚ) (ρ : Nat → ℝ) :
    Expr.eval ρ (horner u cs) =
      tangentRatHorner (Expr.eval ρ u) cs := by
  induction cs with
  | nil => simp [horner, tangentRatHorner, c]
  | cons a as ih =>
      simp [horner, tangentRatHorner, c, add, mul, ih]

lemma eval_localPoly (a : ℚ) (cs : List ℚ) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (localPoly a cs) =
      tangentLocalPoly a cs t := by
  simp [localPoly, tangentLocalPoly, eval_horner, z, c, sub,
    Expr.eval]

lemma eval_forwardLogCoord (β₀ β₁ : ℚ) (T : Expr) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (forwardLogCoord β₀ β₁ T) =
      Arxiv2407_19026.tangentALog (β₀ : ℝ)
          (Expr.eval (fun _ ↦ t) T) -
        tangentXLog (β₁ : ℝ) t := by
  simp [forwardLogCoord, sub, eval_tangentALog, eval_xlog]

lemma eval_forwardBook (β₀ β₁ : ℚ) (T : Expr) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (forwardBook β₀ β₁ T) =
      tangentCleanBookMargin (β₁ : ℝ) t
        (Arxiv2407_19026.tangentBLog (β₀ : ℝ)
            (Expr.eval (fun _ ↦ t) T) -
          Real.log t) := by
  simp [forwardBook, add, neg, eval_book, eval_tangentBLog, z,
    Expr.eval]
  ring_nf

lemma eval_plateauLogLow (β₀ β₁ : ℚ) (T : Expr) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (plateauLogLow β₀ β₁ T) =
      tangentXLog (β₁ : ℝ) t -
        Arxiv2407_19026.tangentBLog (β₀ : ℝ)
          (Expr.eval (fun _ ↦ t) T) := by
  simp [plateauLogLow, sub, eval_xlog, eval_tangentBLog]

lemma eval_plateauLogHigh (β₀ β₁ : ℚ) (T : Expr) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (plateauLogHigh β₀ β₁ T) =
      Arxiv2407_19026.tangentALog (β₀ : ℝ)
          (Expr.eval (fun _ ↦ t) T) -
        tangentXLog (β₁ : ℝ) t := by
  simp [plateauLogHigh, sub, eval_tangentALog, eval_xlog]

lemma eval_plateauBook (β₀ β₁ : ℚ) (T : Expr) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (plateauBook β₀ β₁ T) =
      tangentCleanBookMargin (β₁ : ℝ) t
        (Arxiv2407_19026.tangentALog (β₀ : ℝ)
            (Expr.eval (fun _ ↦ t) T) +
          Arxiv2407_19026.tangentBLog (β₀ : ℝ)
            (Expr.eval (fun _ ↦ t) T) -
          tangentXLog (β₁ : ℝ) t - Real.log t) := by
  simp [plateauBook, add, neg, eval_book, eval_tangentALog,
    eval_tangentBLog, eval_xlog, z, Expr.eval]
  ring_nf

lemma eval_backwardLogCoord (β₀ β₁ : ℚ) (T : Expr) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (backwardLogCoord β₀ β₁ T) =
      Arxiv2407_19026.tangentBLog (β₀ : ℝ)
          (Expr.eval (fun _ ↦ t) T) -
        tangentXLog (β₁ : ℝ) t := by
  simp [backwardLogCoord, sub, eval_tangentBLog, eval_xlog]

lemma eval_backwardBook (β₀ β₁ : ℚ) (T : Expr) (t : ℝ) :
    Expr.eval (fun _ ↦ t) (backwardBook β₀ β₁ T) =
      tangentCleanBookMargin (β₁ : ℝ) t
        (Arxiv2407_19026.tangentALog (β₀ : ℝ)
            (Expr.eval (fun _ ↦ t) T) -
          Real.log t) := by
  simp [backwardBook, add, neg, eval_book, eval_tangentALog, z,
    Expr.eval]
  ring_nf

end TangentAffine

end Arxiv2407_19026
