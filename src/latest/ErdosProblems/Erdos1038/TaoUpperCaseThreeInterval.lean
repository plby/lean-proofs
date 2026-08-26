import ErdosProblems.Erdos1038.TaoUpperCaseThreeAnalysis
import ErdosProblems.Erdos1038.TaoUpperCasesTwoThreeInterval

/-!
# Checked interval enclosures for Tao's Case 3

This module supplies the semantic bridges for the executable potential,
derivative, endpoint, and supporting-tangent enclosures used by the final
Case 3 certificate.
-/

namespace Erdos1038

noncomputable section

theorem evalTaoCaseThreePotentialInterval_contains
    {precision : Nat} {T R : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hEval : evalTaoCaseThreePotentialInterval precision T = some R) :
    R.Contains (taoCaseThreePotential t) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseThreePotentialInterval, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      cases hlogT : RatInterval.log? precision T with
      | none =>
          simp [evalTaoCaseThreePotentialInterval, hS, hlogT] at hEval
      | some logT =>
          cases hFM : evalTaoLogPrimitiveInterval precision
              (RatInterval.sub M T) with
          | none =>
              simp [evalTaoCaseThreePotentialInterval, hS, M,
                hlogT, hFM] at hEval
          | some FM =>
              let XA := RatInterval.sub (RatInterval.point (163 / 100)) T
              cases hFa : evalTaoLogPrimitiveInterval precision XA with
              | none =>
                  simp [evalTaoCaseThreePotentialInterval, hS,
                    hlogT, XA, hFa] at hEval
              | some Fa =>
                  let XB := RatInterval.sub
                    (RatInterval.point (1919 / 1000)) T
                  cases hFb : evalTaoLogPrimitiveInterval precision XB with
                  | none =>
                      simp [evalTaoCaseThreePotentialInterval, hS,
                        hlogT, XA, hFa, XB, hFb] at hEval
                  | some Fb =>
                      cases hAbsM : RatInterval.abs?
                          (RatInterval.sub M T) with
                      | none =>
                          simp [evalTaoCaseThreePotentialInterval, hS, M,
                            hlogT, hFM, XA, hFa, XB, hFb,
                            hAbsM] at hEval
                      | some absM =>
                          cases hLogM : RatInterval.log? precision absM with
                          | none =>
                              simp [evalTaoCaseThreePotentialInterval, hS,
                                M, hlogT, hFM, XA, hFa, XB, hFb,
                                hAbsM, hLogM] at hEval
                          | some logM =>
                              simp [evalTaoCaseThreePotentialInterval, hS,
                                M, hlogT, hFM, XA, hFa, XB, hFb,
                                hAbsM, hLogM] at hEval
                              subst R
                              have hSContains := RatInterval.sqrt_contains
                                (RatInterval.point_contains (2 : Rat)) hS
                              have hM : M.Contains taoUpperEdge := by
                                simpa only [M, taoUpperEdge,
                                  Rat.cast_ofNat] using!
                                  RatInterval.mul_contains
                                    (RatInterval.point_contains (2 : Rat))
                                    hSContains
                              have hMT := RatInterval.sub_contains hM hT
                              have hFMContains :=
                                evalTaoLogPrimitiveInterval_contains hMT hFM
                              have hA :
                                  (RatInterval.point (163 / 100)).Contains
                                    taoCaseThreeLeftA := by
                                simpa only [taoCaseThreeLeftA, Rat.cast_div,
                                  Rat.cast_ofNat] using!
                                  RatInterval.point_contains (163 / 100 : Rat)
                              have hB :
                                  (RatInterval.point (1919 / 1000)).Contains
                                    taoCaseThreeLeftB := by
                                simpa only [taoCaseThreeLeftB, Rat.cast_div,
                                  Rat.cast_ofNat] using!
                                  RatInterval.point_contains
                                    (1919 / 1000 : Rat)
                              have hFaContains :=
                                evalTaoLogPrimitiveInterval_contains
                                  (RatInterval.sub_contains hA hT) hFa
                              have hFbContains :=
                                evalTaoLogPrimitiveInterval_contains
                                  (RatInterval.sub_contains hB hT) hFb
                              have hlogTContains :=
                                RatInterval.log_contains hT hlogT
                              have hlogMContains := RatInterval.log_contains
                                (RatInterval.abs_contains hMT hAbsM) hLogM
                              have hWeightA :
                                  (RatInterval.point
                                    (192829 / 1000000)).Contains
                                      taoCaseThreeA := by
                                simpa only [taoCaseThreeA, Rat.cast_div,
                                  Rat.cast_ofNat] using!
                                  RatInterval.point_contains
                                    (192829 / 1000000 : Rat)
                              have hWeightB :
                                  (RatInterval.point (28 / 125)).Contains
                                    taoCaseThreeB := by
                                simpa only [taoCaseThreeB, Rat.cast_div,
                                  Rat.cast_ofNat] using!
                                  RatInterval.point_contains (28 / 125 : Rat)
                              have hWeightC :
                                  (RatInterval.point (31 / 200)).Contains
                                    taoCaseThreeC := by
                                simpa only [taoCaseThreeC, Rat.cast_div,
                                  Rat.cast_ofNat] using!
                                  RatInterval.point_contains (31 / 200 : Rat)
                              have hValue := RatInterval.sub_contains
                                (RatInterval.add_contains
                                  (RatInterval.add_contains
                                    (RatInterval.neg_contains hlogTContains)
                                    (RatInterval.mul_contains hWeightA
                                      (RatInterval.sub_contains hFMContains
                                        hFaContains)))
                                  (RatInterval.mul_contains hWeightB
                                    (RatInterval.sub_contains hFMContains
                                      hFbContains)))
                                (RatInterval.mul_contains hWeightC
                                  hlogMContains)
                              simpa only [taoCaseThreePotential] using! hValue

theorem taoCaseThreePotential_neg_of_interval_certificate
    {precision : Nat} {T : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hcert : ∃ R,
      evalTaoCaseThreePotentialInterval precision T = some R ∧ R.hi < 0) :
    taoCaseThreePotential t < 0 := by
  obtain ⟨R, hEval, hhi⟩ := hcert
  have hContains := evalTaoCaseThreePotentialInterval_contains hT hEval
  have hhiReal : (R.hi : ℝ) < 0 := by exact_mod_cast hhi
  exact hContains.2.trans_lt hhiReal

/-- Executable enclosure of the first derivative of the Case 3 scalar. -/
def evalTaoCaseThreeDerivativeInterval
    (precision : Nat) (T : RatInterval) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let invT ← RatInterval.inv? T
  let MT := RatInterval.sub M T
  let absM ← RatInterval.abs? MT
  let logM ← RatInterval.log? precision absM
  let absA ← RatInterval.abs?
    (RatInterval.sub (RatInterval.point (163 / 100)) T)
  let logA ← RatInterval.log? precision absA
  let absB ← RatInterval.abs?
    (RatInterval.sub (RatInterval.point (1919 / 1000)) T)
  let logB ← RatInterval.log? precision absB
  let invM ← RatInterval.inv? MT
  pure (RatInterval.add
    (RatInterval.add
      (RatInterval.add (RatInterval.neg invT)
        (RatInterval.mul (RatInterval.point (192829 / 1000000))
          (RatInterval.sub logM logA)))
      (RatInterval.mul (RatInterval.point (28 / 125))
        (RatInterval.sub logM logB)))
    (RatInterval.mul (RatInterval.point (31 / 200)) invM))

theorem evalTaoCaseThreeDerivativeInterval_contains
    {precision : Nat} {T R : RatInterval} {t : ℝ}
    (hT : T.Contains t)
    (hEval : evalTaoCaseThreeDerivativeInterval precision T = some R) :
    R.Contains (taoCaseThreePotentialDerivative t) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseThreeDerivativeInterval, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      cases hInvT : RatInterval.inv? T with
      | none =>
          simp [evalTaoCaseThreeDerivativeInterval, hS, hInvT] at hEval
      | some invT =>
          let MT := RatInterval.sub M T
          cases hAbsM : RatInterval.abs? MT with
          | none =>
              simp [evalTaoCaseThreeDerivativeInterval, hS, M, MT,
                hInvT, hAbsM] at hEval
          | some absM =>
              cases hLogM : RatInterval.log? precision absM with
              | none =>
                  simp [evalTaoCaseThreeDerivativeInterval, hS, M, MT,
                    hInvT, hAbsM, hLogM] at hEval
              | some logM =>
                  let XA := RatInterval.sub
                    (RatInterval.point (163 / 100)) T
                  cases hAbsA : RatInterval.abs? XA with
                  | none =>
                      simp [evalTaoCaseThreeDerivativeInterval, hS,
                        hInvT, XA, hAbsA] at hEval
                  | some absA =>
                      cases hLogA : RatInterval.log? precision absA with
                      | none =>
                          simp [evalTaoCaseThreeDerivativeInterval, hS,
                            hInvT, XA, hAbsA,
                            hLogA] at hEval
                      | some logA =>
                          let XB := RatInterval.sub
                            (RatInterval.point (1919 / 1000)) T
                          cases hAbsB : RatInterval.abs? XB with
                          | none =>
                              simp [evalTaoCaseThreeDerivativeInterval,
                                hS, hInvT, XA,
                                hAbsA, XB, hAbsB] at hEval
                          | some absB =>
                              cases hLogB : RatInterval.log? precision absB with
                              | none =>
                                  simp [evalTaoCaseThreeDerivativeInterval,
                                    hS, hInvT, XA,
                                    hAbsA, XB, hAbsB,
                                    hLogB] at hEval
                              | some logB =>
                                  cases hInvM : RatInterval.inv? MT with
                                  | none =>
                                      simp [evalTaoCaseThreeDerivativeInterval,
                                        hS, M, MT, hInvT, hAbsM,
                                        XA, hAbsA, hLogA, XB, hAbsB,
                                        hLogB, hInvM] at hEval
                                  | some invM =>
                                      simp [evalTaoCaseThreeDerivativeInterval,
                                        hS, M, MT, hInvT, hAbsM, hLogM,
                                        XA, hAbsA, hLogA, XB, hAbsB,
                                        hLogB, hInvM] at hEval
                                      subst R
                                      have hSContains :=
                                        RatInterval.sqrt_contains
                                          (RatInterval.point_contains
                                            (2 : Rat)) hS
                                      have hM : M.Contains taoUpperEdge := by
                                        simpa only [M, taoUpperEdge,
                                          Rat.cast_ofNat] using!
                                          RatInterval.mul_contains
                                            (RatInterval.point_contains
                                              (2 : Rat)) hSContains
                                      have hMT := RatInterval.sub_contains hM hT
                                      have hA :
                                          (RatInterval.point (163 / 100)).Contains
                                            taoCaseThreeLeftA := by
                                        simpa only [taoCaseThreeLeftA,
                                          Rat.cast_div, Rat.cast_ofNat] using!
                                          RatInterval.point_contains
                                            (163 / 100 : Rat)
                                      have hB :
                                          (RatInterval.point
                                            (1919 / 1000)).Contains
                                              taoCaseThreeLeftB := by
                                        simpa only [taoCaseThreeLeftB,
                                          Rat.cast_div, Rat.cast_ofNat] using!
                                          RatInterval.point_contains
                                            (1919 / 1000 : Rat)
                                      have hlogMContains :=
                                        RatInterval.log_contains
                                          (RatInterval.abs_contains hMT hAbsM)
                                          hLogM
                                      have hlogAContains :=
                                        RatInterval.log_contains
                                          (RatInterval.abs_contains
                                            (RatInterval.sub_contains hA hT)
                                            hAbsA) hLogA
                                      have hlogBContains :=
                                        RatInterval.log_contains
                                          (RatInterval.abs_contains
                                            (RatInterval.sub_contains hB hT)
                                            hAbsB) hLogB
                                      have hInvTContains :=
                                        RatInterval.inv_contains hT hInvT
                                      have hInvMContains :=
                                        RatInterval.inv_contains hMT hInvM
                                      have hWeightA :
                                          (RatInterval.point
                                            (192829 / 1000000)).Contains
                                              taoCaseThreeA := by
                                        simpa only [taoCaseThreeA,
                                          Rat.cast_div, Rat.cast_ofNat] using!
                                          RatInterval.point_contains
                                            (192829 / 1000000 : Rat)
                                      have hWeightB :
                                          (RatInterval.point (28 / 125)).Contains
                                            taoCaseThreeB := by
                                        simpa only [taoCaseThreeB,
                                          Rat.cast_div, Rat.cast_ofNat] using!
                                          RatInterval.point_contains
                                            (28 / 125 : Rat)
                                      have hWeightC :
                                          (RatInterval.point (31 / 200)).Contains
                                            taoCaseThreeC := by
                                        simpa only [taoCaseThreeC,
                                          Rat.cast_div, Rat.cast_ofNat] using!
                                          RatInterval.point_contains
                                            (31 / 200 : Rat)
                                      have hValue := RatInterval.add_contains
                                        (RatInterval.add_contains
                                          (RatInterval.add_contains
                                            (RatInterval.neg_contains
                                              hInvTContains)
                                            (RatInterval.mul_contains hWeightA
                                              (RatInterval.sub_contains
                                                hlogMContains
                                                hlogAContains)))
                                          (RatInterval.mul_contains hWeightB
                                            (RatInterval.sub_contains
                                              hlogMContains hlogBContains)))
                                        (RatInterval.mul_contains hWeightC
                                          hInvMContains)
                                      simpa only [taoCaseThreePotentialDerivative,
                                        neg_div, one_div, one_mul] using! hValue

/-- Endpoint-specialized enclosure at `a = 1.63`, simplifying the
vanishing `F(a-a)` term before evaluation. -/
def evalTaoCaseThreePotentialAtLeftA
    (precision : Nat) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let A0 := RatInterval.point (163 / 100)
  let B0 := RatInterval.point (1919 / 1000)
  let logA ← RatInterval.log? precision A0
  let FM ← evalTaoLogPrimitiveInterval precision (RatInterval.sub M A0)
  let FB ← evalTaoLogPrimitiveInterval precision (RatInterval.sub B0 A0)
  let absM ← RatInterval.abs? (RatInterval.sub M A0)
  let logM ← RatInterval.log? precision absM
  pure (RatInterval.sub
    (RatInterval.add
      (RatInterval.add (RatInterval.neg logA)
        (RatInterval.mul (RatInterval.point (192829 / 1000000)) FM))
      (RatInterval.mul (RatInterval.point (28 / 125))
        (RatInterval.sub FM FB)))
    (RatInterval.mul (RatInterval.point (31 / 200)) logM))

theorem evalTaoCaseThreePotentialAtLeftA_contains
    {precision : Nat} {R : RatInterval}
    (hEval : evalTaoCaseThreePotentialAtLeftA precision = some R) :
    R.Contains (taoCaseThreePotential taoCaseThreeLeftA) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseThreePotentialAtLeftA, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      let A0 := RatInterval.point (163 / 100)
      let B0 := RatInterval.point (1919 / 1000)
      cases hlogA : RatInterval.log? precision A0 with
      | none =>
          simp [evalTaoCaseThreePotentialAtLeftA, hS, A0, hlogA] at hEval
      | some logA =>
          cases hFM : evalTaoLogPrimitiveInterval precision
              (RatInterval.sub M A0) with
          | none =>
              simp [evalTaoCaseThreePotentialAtLeftA, hS, M, A0,
                hlogA, hFM] at hEval
          | some FM =>
              cases hFB : evalTaoLogPrimitiveInterval precision
                  (RatInterval.sub B0 A0) with
              | none =>
                  simp [evalTaoCaseThreePotentialAtLeftA, hS, A0,
                    B0, hlogA, hFB] at hEval
              | some FB =>
                  cases hAbsM : RatInterval.abs?
                      (RatInterval.sub M A0) with
                  | none =>
                      simp [evalTaoCaseThreePotentialAtLeftA, hS, M, A0,
                        B0, hlogA, hFM, hFB, hAbsM] at hEval
                  | some absM =>
                      cases hLogM : RatInterval.log? precision absM with
                      | none =>
                          simp [evalTaoCaseThreePotentialAtLeftA, hS, M,
                            A0, B0, hlogA, hFM, hFB, hAbsM,
                            hLogM] at hEval
                      | some logM =>
                          simp [evalTaoCaseThreePotentialAtLeftA, hS, M,
                            A0, B0, hlogA, hFM, hFB, hAbsM,
                            hLogM] at hEval
                          subst R
                          have hSContains := RatInterval.sqrt_contains
                            (RatInterval.point_contains (2 : Rat)) hS
                          have hM : M.Contains taoUpperEdge := by
                            simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                              RatInterval.mul_contains
                                (RatInterval.point_contains (2 : Rat))
                                hSContains
                          have hA : A0.Contains taoCaseThreeLeftA := by
                            simpa only [A0, taoCaseThreeLeftA, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (163 / 100 : Rat)
                          have hB : B0.Contains taoCaseThreeLeftB := by
                            simpa only [B0, taoCaseThreeLeftB, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (1919 / 1000 : Rat)
                          have hFMContains :=
                            evalTaoLogPrimitiveInterval_contains
                              (RatInterval.sub_contains hM hA) hFM
                          have hFBContains :=
                            evalTaoLogPrimitiveInterval_contains
                              (RatInterval.sub_contains hB hA) hFB
                          have hlogAContains :=
                            RatInterval.log_contains hA hlogA
                          have hlogMContains := RatInterval.log_contains
                            (RatInterval.abs_contains
                              (RatInterval.sub_contains hM hA) hAbsM) hLogM
                          have hWeightA :
                              (RatInterval.point
                                (192829 / 1000000)).Contains
                                  taoCaseThreeA := by
                            simpa only [taoCaseThreeA, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (192829 / 1000000 : Rat)
                          have hWeightB :
                              (RatInterval.point (28 / 125)).Contains
                                taoCaseThreeB := by
                            simpa only [taoCaseThreeB, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (28 / 125 : Rat)
                          have hWeightC :
                              (RatInterval.point (31 / 200)).Contains
                                taoCaseThreeC := by
                            simpa only [taoCaseThreeC, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (31 / 200 : Rat)
                          have hValue := RatInterval.sub_contains
                            (RatInterval.add_contains
                              (RatInterval.add_contains
                                (RatInterval.neg_contains hlogAContains)
                                (RatInterval.mul_contains hWeightA
                                  hFMContains))
                              (RatInterval.mul_contains hWeightB
                                (RatInterval.sub_contains hFMContains
                                  hFBContains)))
                            (RatInterval.mul_contains hWeightC hlogMContains)
                          convert! hValue using 1
                          unfold taoCaseThreePotential
                          rw [sub_self, taoLogPrimitive_zero]
                          ring

/-- Endpoint-specialized enclosure at `b = 1.919`, simplifying the
vanishing `F(b-b)` term before evaluation. -/
def evalTaoCaseThreePotentialAtLeftB
    (precision : Nat) : Option RatInterval := do
  let S ← RatInterval.sqrt? precision (RatInterval.point 2)
  let M := RatInterval.mul (RatInterval.point 2) S
  let A0 := RatInterval.point (163 / 100)
  let B0 := RatInterval.point (1919 / 1000)
  let logB ← RatInterval.log? precision B0
  let FM ← evalTaoLogPrimitiveInterval precision (RatInterval.sub M B0)
  let FA ← evalTaoLogPrimitiveInterval precision (RatInterval.sub A0 B0)
  let absM ← RatInterval.abs? (RatInterval.sub M B0)
  let logM ← RatInterval.log? precision absM
  pure (RatInterval.sub
    (RatInterval.add
      (RatInterval.add (RatInterval.neg logB)
        (RatInterval.mul (RatInterval.point (192829 / 1000000))
          (RatInterval.sub FM FA)))
      (RatInterval.mul (RatInterval.point (28 / 125)) FM))
    (RatInterval.mul (RatInterval.point (31 / 200)) logM))

theorem evalTaoCaseThreePotentialAtLeftB_contains
    {precision : Nat} {R : RatInterval}
    (hEval : evalTaoCaseThreePotentialAtLeftB precision = some R) :
    R.Contains (taoCaseThreePotential taoCaseThreeLeftB) := by
  cases hS : RatInterval.sqrt? precision (RatInterval.point 2) with
  | none => simp [evalTaoCaseThreePotentialAtLeftB, hS] at hEval
  | some S =>
      let M := RatInterval.mul (RatInterval.point 2) S
      let A0 := RatInterval.point (163 / 100)
      let B0 := RatInterval.point (1919 / 1000)
      cases hlogB : RatInterval.log? precision B0 with
      | none =>
          simp [evalTaoCaseThreePotentialAtLeftB, hS, B0, hlogB] at hEval
      | some logB =>
          cases hFM : evalTaoLogPrimitiveInterval precision
              (RatInterval.sub M B0) with
          | none =>
              simp [evalTaoCaseThreePotentialAtLeftB, hS, M, B0,
                hlogB, hFM] at hEval
          | some FM =>
              cases hFA : evalTaoLogPrimitiveInterval precision
                  (RatInterval.sub A0 B0) with
              | none =>
                  simp [evalTaoCaseThreePotentialAtLeftB, hS, A0,
                    B0, hlogB, hFA] at hEval
              | some FA =>
                  cases hAbsM : RatInterval.abs?
                      (RatInterval.sub M B0) with
                  | none =>
                      simp [evalTaoCaseThreePotentialAtLeftB, hS, M, A0,
                        B0, hlogB, hFM, hFA, hAbsM] at hEval
                  | some absM =>
                      cases hLogM : RatInterval.log? precision absM with
                      | none =>
                          simp [evalTaoCaseThreePotentialAtLeftB, hS, M,
                            A0, B0, hlogB, hFM, hFA, hAbsM,
                            hLogM] at hEval
                      | some logM =>
                          simp [evalTaoCaseThreePotentialAtLeftB, hS, M,
                            A0, B0, hlogB, hFM, hFA, hAbsM,
                            hLogM] at hEval
                          subst R
                          have hSContains := RatInterval.sqrt_contains
                            (RatInterval.point_contains (2 : Rat)) hS
                          have hM : M.Contains taoUpperEdge := by
                            simpa only [M, taoUpperEdge, Rat.cast_ofNat] using!
                              RatInterval.mul_contains
                                (RatInterval.point_contains (2 : Rat))
                                hSContains
                          have hA : A0.Contains taoCaseThreeLeftA := by
                            simpa only [A0, taoCaseThreeLeftA, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (163 / 100 : Rat)
                          have hB : B0.Contains taoCaseThreeLeftB := by
                            simpa only [B0, taoCaseThreeLeftB, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (1919 / 1000 : Rat)
                          have hFMContains :=
                            evalTaoLogPrimitiveInterval_contains
                              (RatInterval.sub_contains hM hB) hFM
                          have hFAContains :=
                            evalTaoLogPrimitiveInterval_contains
                              (RatInterval.sub_contains hA hB) hFA
                          have hlogBContains :=
                            RatInterval.log_contains hB hlogB
                          have hlogMContains := RatInterval.log_contains
                            (RatInterval.abs_contains
                              (RatInterval.sub_contains hM hB) hAbsM) hLogM
                          have hWeightA :
                              (RatInterval.point
                                (192829 / 1000000)).Contains
                                  taoCaseThreeA := by
                            simpa only [taoCaseThreeA, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (192829 / 1000000 : Rat)
                          have hWeightB :
                              (RatInterval.point (28 / 125)).Contains
                                taoCaseThreeB := by
                            simpa only [taoCaseThreeB, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (28 / 125 : Rat)
                          have hWeightC :
                              (RatInterval.point (31 / 200)).Contains
                                taoCaseThreeC := by
                            simpa only [taoCaseThreeC, Rat.cast_div,
                              Rat.cast_ofNat] using! RatInterval.point_contains
                                (31 / 200 : Rat)
                          have hValue := RatInterval.sub_contains
                            (RatInterval.add_contains
                              (RatInterval.add_contains
                                (RatInterval.neg_contains hlogBContains)
                                (RatInterval.mul_contains hWeightA
                                  (RatInterval.sub_contains hFMContains
                                    hFAContains)))
                              (RatInterval.mul_contains hWeightB hFMContains))
                            (RatInterval.mul_contains hWeightC hlogMContains)
                          convert! hValue using 1
                          unfold taoCaseThreePotential
                          rw [sub_self, taoLogPrimitive_zero]
                          ring

/-- Supporting tangent at a rational interior point, evaluated at a
rational abscissa. -/
def evalTaoCaseThreeTangentInterval
    (precision : Nat) (q x : Rat) : Option RatInterval := do
  let P ← evalTaoCaseThreePotentialInterval precision (RatInterval.point q)
  let D ← evalTaoCaseThreeDerivativeInterval precision (RatInterval.point q)
  pure (RatInterval.add P
    (RatInterval.mul D (RatInterval.point (x - q))))

theorem evalTaoCaseThreeTangentInterval_contains
    {precision : Nat} {q x : Rat} {R : RatInterval}
    (hEval : evalTaoCaseThreeTangentInterval precision q x = some R) :
    R.Contains (taoCaseThreePotential (q : ℝ) +
      taoCaseThreePotentialDerivative (q : ℝ) * ((x : ℝ) - (q : ℝ))) := by
  cases hP : evalTaoCaseThreePotentialInterval precision
      (RatInterval.point q) with
  | none => simp [evalTaoCaseThreeTangentInterval, hP] at hEval
  | some P =>
      cases hD : evalTaoCaseThreeDerivativeInterval precision
          (RatInterval.point q) with
      | none =>
          simp [evalTaoCaseThreeTangentInterval, hP, hD] at hEval
      | some D =>
          simp [evalTaoCaseThreeTangentInterval, hP, hD] at hEval
          subst R
          exact RatInterval.add_contains
            (evalTaoCaseThreePotentialInterval_contains
              (RatInterval.point_contains q) hP)
            (RatInterval.mul_contains
              (evalTaoCaseThreeDerivativeInterval_contains
                (RatInterval.point_contains q) hD)
              (by simpa only [Rat.cast_sub] using!
                RatInterval.point_contains (x - q)))

end

end Erdos1038
