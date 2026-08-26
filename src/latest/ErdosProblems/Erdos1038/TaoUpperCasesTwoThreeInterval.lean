import ErdosProblems.Erdos1038.TaoUpperCasesTwoThreeAnalysis
import ErdosProblems.Erdos1038.RationalInterval

/-!
# Checked interval evaluators for Tao's Cases 2 and 3

These evaluators use only rational arithmetic together with the proved
logarithm and square-root enclosures from `RationalInterval`.  The absolute
value node deliberately fails on intervals crossing zero; singular points
are handled analytically in the surrounding proof rather than by an
unsound floating-point convention.
-/

namespace Erdos1038

noncomputable section

namespace RatInterval

/-- Exact absolute-value hull when an interval has a certified weak sign. -/
def abs? (I : RatInterval) : Option RatInterval :=
  if 0 ≤ I.lo then some I
  else if I.hi ≤ 0 then some (neg I)
  else none

theorem abs_contains {I J : RatInterval} {x : ℝ}
    (hx : I.Contains x) (h : abs? I = some J) :
    J.Contains |x| := by
  by_cases hlo : 0 ≤ I.lo
  · rw [abs?, if_pos hlo] at h
    cases h
    have hloReal : (0 : ℝ) ≤ (I.lo : ℝ) := by exact_mod_cast hlo
    rw [abs_of_nonneg (hloReal.trans hx.1)]
    exact hx
  · rw [abs?, if_neg hlo] at h
    by_cases hhi : I.hi ≤ 0
    · rw [if_pos hhi] at h
      cases h
      have hhiReal : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hhi
      rw [abs_of_nonpos (hx.2.trans hhiReal)]
      exact neg_contains hx
    · simp only [if_neg hhi, reduceCtorEq] at h

end RatInterval

/-- Compositional interval evaluation of `x - x log |x|`. -/
def evalTaoLogPrimitiveInterval
    (precision : Nat) (X : RatInterval) : Option RatInterval := do
  let AX ← RatInterval.abs? X
  let LX ← RatInterval.log? precision AX
  pure (RatInterval.sub X (RatInterval.mul X LX))

theorem evalTaoLogPrimitiveInterval_contains
    {precision : Nat} {X R : RatInterval} {x : ℝ}
    (hX : X.Contains x)
    (hEval : evalTaoLogPrimitiveInterval precision X = some R) :
    R.Contains (taoLogPrimitive x) := by
  cases hAX : RatInterval.abs? X with
  | none => simp [evalTaoLogPrimitiveInterval, hAX] at hEval
  | some AX =>
      cases hLX : RatInterval.log? precision AX with
      | none => simp [evalTaoLogPrimitiveInterval, hAX, hLX] at hEval
      | some LX =>
          simp [evalTaoLogPrimitiveInterval, hAX, hLX] at hEval
          subst R
          have hAbs := RatInterval.abs_contains hX hAX
          have hLog := RatInterval.log_contains hAbs hLX
          have hMul := RatInterval.mul_contains hX hLog
          simpa only [taoLogPrimitive] using!
            RatInterval.sub_contains hX hMul

/-- Fully executable enclosure of the scalar function (2.5). -/
def evalTaoCaseTwoPotentialInterval
    (precision : Nat) (T : RatInterval) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let logT ← RatInterval.log? precision T
  let FM ← evalTaoLogPrimitiveInterval precision (RatInterval.sub M T)
  let Fa ← evalTaoLogPrimitiveInterval precision
    (RatInterval.sub (RatInterval.point (1134371 / 500000)) T)
  pure (RatInterval.add (RatInterval.neg logT)
    (RatInterval.mul (RatInterval.point (7233 / 10000))
      (RatInterval.sub FM Fa)))

theorem evalTaoCaseTwoPotentialInterval_contains
    {precision : Nat} {T R : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hEval : evalTaoCaseTwoPotentialInterval precision T = some R) :
    R.Contains (taoCaseTwoPotential t) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseTwoPotentialInterval, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      cases hlogT : RatInterval.log? precision T with
      | none =>
          simp [evalTaoCaseTwoPotentialInterval, hS, hlogT] at hEval
      | some logT =>
          cases hFM : evalTaoLogPrimitiveInterval precision
              (RatInterval.sub M T) with
          | none =>
              simp [evalTaoCaseTwoPotentialInterval, hS, hlogT,
                M, hFM] at hEval
          | some FM =>
              let XA := RatInterval.sub
                (RatInterval.point (1134371 / 500000)) T
              cases hFa : evalTaoLogPrimitiveInterval precision XA with
              | none =>
                  simp [evalTaoCaseTwoPotentialInterval, hS, hlogT,
                    XA, hFa] at hEval
              | some Fa =>
                  simp [evalTaoCaseTwoPotentialInterval, hS, hlogT,
                    M, hFM, XA, hFa] at hEval
                  subst R
                  have hTwo := RatInterval.point_contains (2 : Rat)
                  have hSContains := RatInterval.sqrt_contains
                    (RatInterval.point_contains (2 : Rat)) hS
                  have hM : M.Contains taoUpperEdge := by
                    simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                      RatInterval.mul_contains hTwo hSContains
                  have hMT := RatInterval.sub_contains hM hT
                  have hFMContains := evalTaoLogPrimitiveInterval_contains
                    hMT hFM
                  have hARat := RatInterval.point_contains
                    (1134371 / 500000 : Rat)
                  have hAReal :
                      (RatInterval.point (1134371 / 500000)).Contains
                        taoCaseTwoLeftEndpoint := by
                    simpa only [taoCaseTwoLeftEndpoint, Rat.cast_div,
                      Rat.cast_ofNat] using! hARat
                  have hXA := RatInterval.sub_contains hAReal hT
                  have hFaContains := evalTaoLogPrimitiveInterval_contains
                    hXA hFa
                  have hlogContains := RatInterval.log_contains hT hlogT
                  have hWeightRat := RatInterval.point_contains
                    (7233 / 10000 : Rat)
                  have hWeight :
                      (RatInterval.point (7233 / 10000)).Contains
                        taoCaseTwoA := by
                    simpa only [taoCaseTwoA, Rat.cast_div,
                      Rat.cast_ofNat] using! hWeightRat
                  have hValue := RatInterval.add_contains
                    (RatInterval.neg_contains hlogContains)
                    (RatInterval.mul_contains hWeight
                      (RatInterval.sub_contains hFMContains hFaContains))
                  simpa only [taoCaseTwoPotential] using! hValue

/-- Fully executable enclosure of the derivative of (2.5). -/
def evalTaoCaseTwoDerivativeInterval
    (precision : Nat) (T : RatInterval) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let invT ← RatInterval.inv? T
  let absM ← RatInterval.abs? (RatInterval.sub M T)
  let logM ← RatInterval.log? precision absM
  let absA ← RatInterval.abs?
    (RatInterval.sub (RatInterval.point (1134371 / 500000)) T)
  let logA ← RatInterval.log? precision absA
  pure (RatInterval.add (RatInterval.neg invT)
    (RatInterval.mul (RatInterval.point (7233 / 10000))
      (RatInterval.sub logM logA)))

theorem evalTaoCaseTwoDerivativeInterval_contains
    {precision : Nat} {T R : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hEval : evalTaoCaseTwoDerivativeInterval precision T = some R) :
    R.Contains (taoCaseTwoPotentialDerivative t) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseTwoDerivativeInterval, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      cases hInvT : RatInterval.inv? T with
      | none =>
          simp [evalTaoCaseTwoDerivativeInterval, hS, hInvT] at hEval
      | some invT =>
          cases hAbsM : RatInterval.abs? (RatInterval.sub M T) with
          | none =>
              simp [evalTaoCaseTwoDerivativeInterval, hS, hInvT,
                M, hAbsM] at hEval
          | some absM =>
              cases hLogM : RatInterval.log? precision absM with
              | none =>
                  simp [evalTaoCaseTwoDerivativeInterval, hS, hInvT,
                    M, hAbsM, hLogM] at hEval
              | some logM =>
                  let XA := RatInterval.sub
                    (RatInterval.point (1134371 / 500000)) T
                  cases hAbsA : RatInterval.abs? XA with
                  | none =>
                      simp [evalTaoCaseTwoDerivativeInterval, hS, hInvT,
                        XA, hAbsA] at hEval
                  | some absA =>
                      cases hLogA : RatInterval.log? precision absA with
                      | none =>
                          simp [evalTaoCaseTwoDerivativeInterval, hS,
                            hInvT, XA, hAbsA,
                            hLogA] at hEval
                      | some logA =>
                          simp [evalTaoCaseTwoDerivativeInterval, hS,
                            hInvT, M, hAbsM, hLogM, XA, hAbsA,
                            hLogA] at hEval
                          subst R
                          have hTwo := RatInterval.point_contains (2 : Rat)
                          have hSContains := RatInterval.sqrt_contains
                            (RatInterval.point_contains (2 : Rat)) hS
                          have hM : M.Contains taoUpperEdge := by
                            simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                              RatInterval.mul_contains hTwo hSContains
                          have hMT := RatInterval.sub_contains hM hT
                          have hAbsMContains :=
                            RatInterval.abs_contains hMT hAbsM
                          have hLogMContains := RatInterval.log_contains
                            hAbsMContains hLogM
                          have hARat := RatInterval.point_contains
                            (1134371 / 500000 : Rat)
                          have hAReal :
                              (RatInterval.point (1134371 / 500000)).Contains
                                taoCaseTwoLeftEndpoint := by
                            simpa only [taoCaseTwoLeftEndpoint, Rat.cast_div,
                              Rat.cast_ofNat] using! hARat
                          have hXA := RatInterval.sub_contains hAReal hT
                          have hAbsAContains :=
                            RatInterval.abs_contains hXA hAbsA
                          have hLogAContains := RatInterval.log_contains
                            hAbsAContains hLogA
                          have hInvContains :=
                            RatInterval.inv_contains hT hInvT
                          have hWeightRat := RatInterval.point_contains
                            (7233 / 10000 : Rat)
                          have hWeight :
                              (RatInterval.point (7233 / 10000)).Contains
                                taoCaseTwoA := by
                            simpa only [taoCaseTwoA, Rat.cast_div,
                              Rat.cast_ofNat] using! hWeightRat
                          have hValue := RatInterval.add_contains
                            (RatInterval.neg_contains hInvContains)
                            (RatInterval.mul_contains hWeight
                              (RatInterval.sub_contains hLogMContains
                                hLogAContains))
                          simpa only [taoCaseTwoPotentialDerivative,
                            neg_div, one_div, one_mul] using! hValue

theorem taoCaseTwoPotential_neg_of_interval_certificate
    {precision : Nat} {T : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hcert : ∃ R, evalTaoCaseTwoPotentialInterval precision T = some R ∧
      R.hi < 0) :
    taoCaseTwoPotential t < 0 := by
  obtain ⟨R, hEval, hhi⟩ := hcert
  have hContains := evalTaoCaseTwoPotentialInterval_contains hT hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

/-- Enclosure of the supporting tangent at a rational point, evaluated at
the left endpoint `a = 2.268742` of the concave middle segment. -/
def evalTaoCaseTwoLeftTangentInterval
    (precision : Nat) (q : Rat) : Option RatInterval := do
  let P ← evalTaoCaseTwoPotentialInterval precision (RatInterval.point q)
  let D ← evalTaoCaseTwoDerivativeInterval precision (RatInterval.point q)
  pure (RatInterval.add P
    (RatInterval.mul D
      (RatInterval.point ((1134371 / 500000) - q))))

theorem evalTaoCaseTwoLeftTangentInterval_contains
    {precision : Nat} {q : Rat} {R : RatInterval}
    (hEval : evalTaoCaseTwoLeftTangentInterval precision q = some R) :
    R.Contains
      (taoCaseTwoPotential (q : ℝ) +
        taoCaseTwoPotentialDerivative (q : ℝ) *
          (taoCaseTwoLeftEndpoint - (q : ℝ))) := by
  cases hP : evalTaoCaseTwoPotentialInterval precision
      (RatInterval.point q) with
  | none => simp [evalTaoCaseTwoLeftTangentInterval, hP] at hEval
  | some P =>
      cases hD : evalTaoCaseTwoDerivativeInterval precision
          (RatInterval.point q) with
      | none =>
          simp [evalTaoCaseTwoLeftTangentInterval, hP, hD] at hEval
      | some D =>
          simp [evalTaoCaseTwoLeftTangentInterval, hP, hD] at hEval
          subst R
          have hQ := RatInterval.point_contains q
          have hPContains := evalTaoCaseTwoPotentialInterval_contains hQ hP
          have hDContains := evalTaoCaseTwoDerivativeInterval_contains hQ hD
          have hDeltaRat := RatInterval.point_contains
            ((1134371 / 500000 : Rat) - q)
          have hDelta :
              (RatInterval.point ((1134371 / 500000) - q)).Contains
                (taoCaseTwoLeftEndpoint - (q : ℝ)) := by
            simpa only [taoCaseTwoLeftEndpoint, Rat.cast_sub,
              Rat.cast_div, Rat.cast_ofNat] using! hDeltaRat
          exact RatInterval.add_contains hPContains
            (RatInterval.mul_contains hDContains hDelta)

/-- Specialized enclosure at the density's left endpoint.  The vanishing
primitive is simplified before interval evaluation. -/
def evalTaoCaseTwoPotentialAtLeftEndpoint
    (precision : Nat) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let A0 := RatInterval.point (1134371 / 500000)
  let logA ← RatInterval.log? precision A0
  let FM ← evalTaoLogPrimitiveInterval precision (RatInterval.sub M A0)
  pure (RatInterval.add (RatInterval.neg logA)
    (RatInterval.mul (RatInterval.point (7233 / 10000)) FM))

theorem evalTaoCaseTwoPotentialAtLeftEndpoint_contains
    {precision : Nat} {R : RatInterval}
    (hEval : evalTaoCaseTwoPotentialAtLeftEndpoint precision = some R) :
    R.Contains (taoCaseTwoPotential taoCaseTwoLeftEndpoint) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseTwoPotentialAtLeftEndpoint, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      let A0 := RatInterval.point (1134371 / 500000)
      cases hlogA : RatInterval.log? precision A0 with
      | none =>
          simp [evalTaoCaseTwoPotentialAtLeftEndpoint, hS, A0,
            hlogA] at hEval
      | some logA =>
          cases hFM : evalTaoLogPrimitiveInterval precision
              (RatInterval.sub M A0) with
          | none =>
              simp [evalTaoCaseTwoPotentialAtLeftEndpoint, hS, M,
                A0, hlogA, hFM] at hEval
          | some FM =>
              simp [evalTaoCaseTwoPotentialAtLeftEndpoint, hS, M,
                A0, hlogA, hFM] at hEval
              subst R
              have hSContains := RatInterval.sqrt_contains
                (RatInterval.point_contains (2 : Rat)) hS
              have hM : M.Contains taoUpperEdge := by
                simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                  RatInterval.mul_contains
                    (RatInterval.point_contains (2 : Rat)) hSContains
              have hARat := RatInterval.point_contains
                (1134371 / 500000 : Rat)
              have hA : A0.Contains taoCaseTwoLeftEndpoint := by
                simpa only [A0, taoCaseTwoLeftEndpoint, Rat.cast_div,
                  Rat.cast_ofNat] using! hARat
              have hlogContains := RatInterval.log_contains hA hlogA
              have hFMContains := evalTaoLogPrimitiveInterval_contains
                (RatInterval.sub_contains hM hA) hFM
              have hWeightRat := RatInterval.point_contains
                (7233 / 10000 : Rat)
              have hWeight :
                  (RatInterval.point (7233 / 10000)).Contains
                    taoCaseTwoA := by
                simpa only [taoCaseTwoA, Rat.cast_div,
                  Rat.cast_ofNat] using! hWeightRat
              have hValue := RatInterval.add_contains
                (RatInterval.neg_contains hlogContains)
                (RatInterval.mul_contains hWeight hFMContains)
              have hzero :
                  taoLogPrimitive
                    (taoCaseTwoLeftEndpoint - taoCaseTwoLeftEndpoint) = 0 := by
                rw [sub_self, taoLogPrimitive_zero]
              simpa only [taoCaseTwoPotential, hzero, sub_zero] using! hValue

/-- Specialized enclosure at `M = 2 * sqrt 2`; again the vanishing
primitive is simplified exactly. -/
def evalTaoCaseTwoPotentialAtUpperEdge
    (precision : Nat) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let logM ← RatInterval.log? precision M
  let Fa ← evalTaoLogPrimitiveInterval precision
    (RatInterval.sub (RatInterval.point (1134371 / 500000)) M)
  pure (RatInterval.sub (RatInterval.neg logM)
    (RatInterval.mul (RatInterval.point (7233 / 10000)) Fa))

theorem evalTaoCaseTwoPotentialAtUpperEdge_contains
    {precision : Nat} {R : RatInterval}
    (hEval : evalTaoCaseTwoPotentialAtUpperEdge precision = some R) :
    R.Contains (taoCaseTwoPotential taoUpperEdge) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseTwoPotentialAtUpperEdge, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      cases hlogM : RatInterval.log? precision M with
      | none =>
          simp [evalTaoCaseTwoPotentialAtUpperEdge, hS, M,
            hlogM] at hEval
      | some logM =>
          let XA := RatInterval.sub
            (RatInterval.point (1134371 / 500000)) M
          cases hFa : evalTaoLogPrimitiveInterval precision XA with
          | none =>
              simp [evalTaoCaseTwoPotentialAtUpperEdge, hS, M,
                hlogM, XA, hFa] at hEval
          | some Fa =>
              simp [evalTaoCaseTwoPotentialAtUpperEdge, hS, M,
                hlogM, XA, hFa] at hEval
              subst R
              have hSContains := RatInterval.sqrt_contains
                (RatInterval.point_contains (2 : Rat)) hS
              have hM : M.Contains taoUpperEdge := by
                simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                  RatInterval.mul_contains
                    (RatInterval.point_contains (2 : Rat)) hSContains
              have hlogContains := RatInterval.log_contains hM hlogM
              have hARat := RatInterval.point_contains
                (1134371 / 500000 : Rat)
              have hA :
                  (RatInterval.point (1134371 / 500000)).Contains
                    taoCaseTwoLeftEndpoint := by
                simpa only [taoCaseTwoLeftEndpoint, Rat.cast_div,
                  Rat.cast_ofNat] using! hARat
              have hFaContains := evalTaoLogPrimitiveInterval_contains
                (RatInterval.sub_contains hA hM) hFa
              have hWeightRat := RatInterval.point_contains
                (7233 / 10000 : Rat)
              have hWeight :
                  (RatInterval.point (7233 / 10000)).Contains
                    taoCaseTwoA := by
                simpa only [taoCaseTwoA, Rat.cast_div,
                  Rat.cast_ofNat] using! hWeightRat
              have hValue := RatInterval.sub_contains
                (RatInterval.neg_contains hlogContains)
                (RatInterval.mul_contains hWeight hFaContains)
              have hzero : taoLogPrimitive (taoUpperEdge - taoUpperEdge) = 0 := by
                rw [sub_self, taoLogPrimitive_zero]
              convert! hValue using 1
              unfold taoCaseTwoPotential
              rw [hzero]
              ring

/-- Fully executable enclosure of the scalar function (2.6). -/
def evalTaoCaseThreePotentialInterval
    (precision : Nat) (T : RatInterval) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let logT ← RatInterval.log? precision T
  let FM ← evalTaoLogPrimitiveInterval precision (RatInterval.sub M T)
  let Fa ← evalTaoLogPrimitiveInterval precision
    (RatInterval.sub (RatInterval.point (163 / 100)) T)
  let Fb ← evalTaoLogPrimitiveInterval precision
    (RatInterval.sub (RatInterval.point (1919 / 1000)) T)
  let absM ← RatInterval.abs? (RatInterval.sub M T)
  let logM ← RatInterval.log? precision absM
  pure (RatInterval.sub
    (RatInterval.add
      (RatInterval.add (RatInterval.neg logT)
        (RatInterval.mul (RatInterval.point (192829 / 1000000))
          (RatInterval.sub FM Fa)))
      (RatInterval.mul (RatInterval.point (28 / 125))
        (RatInterval.sub FM Fb)))
    (RatInterval.mul (RatInterval.point (31 / 200)) logM))

end

end Erdos1038
