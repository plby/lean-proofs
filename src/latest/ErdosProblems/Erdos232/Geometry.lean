/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateData

namespace Erdos232

/-- The exact 23-point configuration, represented in the complex plane. -/
noncomputable def configurationPoint (i : Fin 23) : ℂ :=
  match i.val with
  | 0 => ⟨0, 0⟩
  | 1 => ⟨1, 0⟩
  | 2 => ⟨(1 / 2 : ℝ), (1 / 2 : ℝ) * Real.sqrt 3⟩
  | 3 => ⟨(3 / 2 : ℝ), (1 / 2 : ℝ) * Real.sqrt 3⟩
  | 4 => ⟨(5 / 6 : ℝ), (1 / 6 : ℝ) * Real.sqrt 11⟩
  | 5 => ⟨-(1 / 12 : ℝ) * Real.sqrt 33 + (5 / 12 : ℝ), (5 / 12 : ℝ) * Real.sqrt 3 + (1 / 12 : ℝ) * Real.sqrt 11⟩
  | 6 => ⟨-(1 / 12 : ℝ) * Real.sqrt 33 + (5 / 4 : ℝ), (5 / 12 : ℝ) * Real.sqrt 3 + (1 / 4 : ℝ) * Real.sqrt 11⟩
  | 7 => ⟨(1 / 12 : ℝ) * Real.sqrt 33 + (13 / 12 : ℝ), (1 / 12 : ℝ) * Real.sqrt 3 - (1 / 12 : ℝ) * Real.sqrt 11⟩
  | 8 => ⟨(1 / 12 : ℝ) * Real.sqrt 33 + (1 / 4 : ℝ), (1 / 12 : ℝ) * Real.sqrt 3 - (1 / 4 : ℝ) * Real.sqrt 11⟩
  | 9 => ⟨-(1 / 12 : ℝ) * Real.sqrt 33 + (13 / 12 : ℝ), -(1 / 12 : ℝ) * Real.sqrt 3 - (1 / 12 : ℝ) * Real.sqrt 11⟩
  | 10 => ⟨(2 / 3 : ℝ), (1 / 2 : ℝ) * Real.sqrt 3 - (1 / 6 : ℝ) * Real.sqrt 11⟩
  | 11 => ⟨-(1 / 12 : ℝ) * Real.sqrt 33 + (7 / 12 : ℝ), (5 / 12 : ℝ) * Real.sqrt 3 - (1 / 12 : ℝ) * Real.sqrt 11⟩
  | 12 => ⟨-(1 / 6 : ℝ) * Real.sqrt 33 + (5 / 6 : ℝ), -(1 / 6 : ℝ) * Real.sqrt 3 + (1 / 6 : ℝ) * Real.sqrt 11⟩
  | 13 => ⟨(1 / 12 : ℝ) * Real.sqrt 33 + (7 / 12 : ℝ), (7 / 12 : ℝ) * Real.sqrt 3 - (1 / 12 : ℝ) * Real.sqrt 11⟩
  | 14 => ⟨-(1 / 12 : ℝ) * Real.sqrt 33 + (1 / 12 : ℝ), -(1 / 12 : ℝ) * Real.sqrt 3 - (1 / 12 : ℝ) * Real.sqrt 11⟩
  | 15 => ⟨-(1 / 6 : ℝ) * Real.sqrt 33 + (2 / 3 : ℝ), (1 / 3 : ℝ) * Real.sqrt 3 - (1 / 6 : ℝ) * Real.sqrt 11⟩
  | 16 => ⟨-(1 / 12 : ℝ) * Real.sqrt 33 + (19 / 12 : ℝ), (5 / 12 : ℝ) * Real.sqrt 3 - (1 / 12 : ℝ) * Real.sqrt 11⟩
  | 17 => ⟨(1 / 3 : ℝ), (1 / 2 : ℝ) * Real.sqrt 3 + (1 / 6 : ℝ) * Real.sqrt 11⟩
  | 18 => ⟨-(1 / 12 : ℝ) * Real.sqrt 33 + (3 / 4 : ℝ), -(1 / 12 : ℝ) * Real.sqrt 3 + (1 / 4 : ℝ) * Real.sqrt 11⟩
  | 19 => ⟨-(1 / 6 : ℝ) * Real.sqrt 33 + 1, -(1 / 6 : ℝ) * Real.sqrt 3⟩
  | 20 => ⟨(7 / 6 : ℝ), -(1 / 6 : ℝ) * Real.sqrt 11⟩
  | 21 => ⟨-(1 / 6 : ℝ) * Real.sqrt 33 + (4 / 3 : ℝ), (1 / 3 : ℝ) * Real.sqrt 3 + (1 / 6 : ℝ) * Real.sqrt 11⟩
  | _ => ⟨-(1 / 4 : ℝ) * Real.sqrt 33 + (19 / 12 : ℝ), (1 / 4 : ℝ) * Real.sqrt 3 - (1 / 12 : ℝ) * Real.sqrt 11⟩

/-- Index of the squared distance between two configuration points in `dualSquaredDistance`.
The diagonal is assigned the harmless default label zero. -/
def configurationDistanceLabel (i j : Fin 23) : Fin 27 :=
  match i.val with
  | 0 =>
    match j.val with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 14
    | 4 => 0
    | 5 => 0
    | 6 => 14
    | 7 => 5
    | 8 => 0
    | 9 => 1
    | 10 => 1
    | 11 => 24
    | 12 => 21
    | 13 => 10
    | 14 => 4
    | 15 => 21
    | 16 => 2
    | 17 => 8
    | 18 => 1
    | 19 => 21
    | 20 => 10
    | 21 => 2
    | _ => 3
  | 1 =>
    match j.val with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 0
    | 4 => 4
    | 5 => 8
    | 6 => 5
    | 7 => 4
    | 8 => 1
    | 9 => 4
    | 10 => 24
    | 11 => 0
    | 12 => 6
    | 13 => 1
    | 14 => 8
    | 15 => 10
    | 16 => 24
    | 17 => 5
    | 18 => 0
    | 19 => 0
    | 20 => 4
    | 21 => 10
    | _ => 19
  | 2 =>
    match j.val with
    | 0 => 0
    | 1 => 0
    | 2 => 0
    | 3 => 0
    | 4 => 24
    | 5 => 4
    | 6 => 1
    | 7 => 8
    | 8 => 5
    | 9 => 10
    | 10 => 4
    | 11 => 4
    | 12 => 19
    | 13 => 4
    | 14 => 5
    | 15 => 6
    | 16 => 1
    | 17 => 4
    | 18 => 21
    | 19 => 26
    | 20 => 5
    | 21 => 21
    | _ => 22
  | 3 =>
    match j.val with
    | 0 => 14
    | 1 => 0
    | 2 => 0
    | 3 => 0
    | 4 => 1
    | 5 => 5
    | 6 => 0
    | 7 => 0
    | 8 => 14
    | 9 => 5
    | 10 => 0
    | 11 => 8
    | 12 => 14
    | 13 => 24
    | 14 => 11
    | 15 => 7
    | 16 => 4
    | 17 => 10
    | 18 => 26
    | 19 => 25
    | 20 => 8
    | 21 => 6
    | _ => 13
  | 4 =>
    match j.val with
    | 0 => 0
    | 1 => 4
    | 2 => 24
    | 3 => 1
    | 4 => 0
    | 5 => 0
    | 6 => 0
    | 7 => 0
    | 8 => 26
    | 9 => 0
    | 10 => 21
    | 11 => 1
    | 12 => 0
    | 13 => 21
    | 14 => 5
    | 15 => 26
    | 16 => 21
    | 17 => 0
    | 18 => 4
    | 19 => 6
    | 20 => 6
    | 21 => 1
    | _ => 22
  | 5 =>
    match j.val with
    | 0 => 0
    | 1 => 8
    | 2 => 4
    | 3 => 5
    | 4 => 0
    | 5 => 0
    | 6 => 0
    | 7 => 7
    | 8 => 25
    | 9 => 5
    | 10 => 0
    | 11 => 4
    | 12 => 1
    | 13 => 6
    | 14 => 8
    | 15 => 0
    | 16 => 10
    | 17 => 4
    | 18 => 24
    | 19 => 10
    | 20 => 7
    | 21 => 24
    | _ => 19
  | 6 =>
    match j.val with
    | 0 => 14
    | 1 => 5
    | 2 => 1
    | 3 => 0
    | 4 => 0
    | 5 => 0
    | 6 => 0
    | 7 => 25
    | 8 => 9
    | 9 => 7
    | 10 => 26
    | 11 => 10
    | 12 => 5
    | 13 => 19
    | 14 => 11
    | 15 => 25
    | 16 => 6
    | 17 => 24
    | 18 => 0
    | 19 => 7
    | 20 => 12
    | 21 => 4
    | _ => 13
  | 7 =>
    match j.val with
    | 0 => 5
    | 1 => 4
    | 2 => 8
    | 3 => 0
    | 4 => 0
    | 5 => 7
    | 6 => 25
    | 7 => 0
    | 8 => 0
    | 9 => 0
    | 10 => 0
    | 11 => 5
    | 12 => 14
    | 13 => 0
    | 14 => 7
    | 15 => 25
    | 16 => 1
    | 17 => 7
    | 18 => 13
    | 19 => 13
    | 20 => 4
    | 21 => 14
    | _ => 15
  | 8 =>
    match j.val with
    | 0 => 0
    | 1 => 1
    | 2 => 5
    | 3 => 14
    | 4 => 26
    | 5 => 25
    | 6 => 9
    | 7 => 0
    | 8 => 0
    | 9 => 21
    | 10 => 0
    | 11 => 10
    | 12 => 16
    | 13 => 8
    | 14 => 6
    | 15 => 26
    | 16 => 2
    | 17 => 12
    | 18 => 15
    | 19 => 22
    | 20 => 24
    | 21 => 17
    | _ => 18
  | 9 =>
    match j.val with
    | 0 => 1
    | 1 => 4
    | 2 => 10
    | 3 => 5
    | 4 => 0
    | 5 => 5
    | 6 => 7
    | 7 => 0
    | 8 => 21
    | 9 => 0
    | 10 => 1
    | 11 => 0
    | 12 => 0
    | 13 => 26
    | 14 => 0
    | 15 => 0
    | 16 => 0
    | 17 => 25
    | 18 => 6
    | 19 => 4
    | 20 => 4
    | 21 => 5
    | _ => 1
  | 10 =>
    match j.val with
    | 0 => 1
    | 1 => 24
    | 2 => 4
    | 3 => 0
    | 4 => 21
    | 5 => 0
    | 6 => 26
    | 7 => 0
    | 8 => 0
    | 9 => 1
    | 10 => 0
    | 11 => 4
    | 12 => 22
    | 13 => 4
    | 14 => 10
    | 15 => 0
    | 16 => 24
    | 17 => 6
    | 18 => 20
    | 19 => 19
    | 20 => 0
    | 21 => 19
    | _ => 20
  | 11 =>
    match j.val with
    | 0 => 24
    | 1 => 0
    | 2 => 4
    | 3 => 8
    | 4 => 1
    | 5 => 4
    | 6 => 10
    | 7 => 5
    | 8 => 10
    | 9 => 0
    | 10 => 4
    | 11 => 0
    | 12 => 21
    | 13 => 0
    | 14 => 0
    | 15 => 4
    | 16 => 0
    | 17 => 0
    | 18 => 21
    | 19 => 1
    | 20 => 8
    | 21 => 1
    | _ => 21
  | 12 =>
    match j.val with
    | 0 => 21
    | 1 => 6
    | 2 => 19
    | 3 => 14
    | 4 => 0
    | 5 => 1
    | 6 => 5
    | 7 => 14
    | 8 => 16
    | 9 => 0
    | 10 => 22
    | 11 => 21
    | 12 => 0
    | 13 => 16
    | 14 => 1
    | 15 => 21
    | 16 => 26
    | 17 => 26
    | 18 => 4
    | 19 => 4
    | 20 => 13
    | 21 => 0
    | _ => 21
  | 13 =>
    match j.val with
    | 0 => 10
    | 1 => 1
    | 2 => 4
    | 3 => 24
    | 4 => 21
    | 5 => 6
    | 6 => 19
    | 7 => 0
    | 8 => 8
    | 9 => 26
    | 10 => 4
    | 11 => 0
    | 12 => 16
    | 13 => 0
    | 14 => 25
    | 15 => 13
    | 16 => 21
    | 17 => 0
    | 18 => 22
    | 19 => 15
    | 20 => 10
    | 21 => 22
    | _ => 23
  | 14 =>
    match j.val with
    | 0 => 4
    | 1 => 8
    | 2 => 5
    | 3 => 11
    | 4 => 5
    | 5 => 8
    | 6 => 11
    | 7 => 7
    | 8 => 6
    | 9 => 0
    | 10 => 10
    | 11 => 0
    | 12 => 1
    | 13 => 25
    | 14 => 0
    | 15 => 24
    | 16 => 14
    | 17 => 7
    | 18 => 10
    | 19 => 24
    | 20 => 5
    | 21 => 14
    | _ => 22
  | 15 =>
    match j.val with
    | 0 => 21
    | 1 => 10
    | 2 => 6
    | 3 => 7
    | 4 => 26
    | 5 => 0
    | 6 => 25
    | 7 => 25
    | 8 => 26
    | 9 => 0
    | 10 => 0
    | 11 => 4
    | 12 => 21
    | 13 => 13
    | 14 => 24
    | 15 => 0
    | 16 => 8
    | 17 => 13
    | 18 => 19
    | 19 => 24
    | 20 => 5
    | 21 => 10
    | _ => 24
  | 16 =>
    match j.val with
    | 0 => 2
    | 1 => 24
    | 2 => 1
    | 3 => 4
    | 4 => 21
    | 5 => 10
    | 6 => 6
    | 7 => 1
    | 8 => 2
    | 9 => 0
    | 10 => 24
    | 11 => 0
    | 12 => 26
    | 13 => 21
    | 14 => 14
    | 15 => 8
    | 16 => 0
    | 17 => 26
    | 18 => 19
    | 19 => 10
    | 20 => 0
    | 21 => 0
    | _ => 0
  | 17 =>
    match j.val with
    | 0 => 8
    | 1 => 5
    | 2 => 4
    | 3 => 10
    | 4 => 0
    | 5 => 4
    | 6 => 24
    | 7 => 7
    | 8 => 12
    | 9 => 25
    | 10 => 6
    | 11 => 0
    | 12 => 26
    | 13 => 0
    | 14 => 7
    | 15 => 13
    | 16 => 26
    | 17 => 0
    | 18 => 1
    | 19 => 14
    | 20 => 12
    | 21 => 21
    | _ => 16
  | 18 =>
    match j.val with
    | 0 => 1
    | 1 => 0
    | 2 => 21
    | 3 => 26
    | 4 => 4
    | 5 => 24
    | 6 => 0
    | 7 => 13
    | 8 => 15
    | 9 => 6
    | 10 => 20
    | 11 => 21
    | 12 => 4
    | 13 => 22
    | 14 => 10
    | 15 => 19
    | 16 => 19
    | 17 => 1
    | 18 => 0
    | 19 => 0
    | 20 => 13
    | 21 => 24
    | _ => 20
  | 19 =>
    match j.val with
    | 0 => 21
    | 1 => 0
    | 2 => 26
    | 3 => 25
    | 4 => 6
    | 5 => 10
    | 6 => 7
    | 7 => 13
    | 8 => 22
    | 9 => 4
    | 10 => 19
    | 11 => 1
    | 12 => 4
    | 13 => 15
    | 14 => 24
    | 15 => 24
    | 16 => 10
    | 17 => 14
    | 18 => 0
    | 19 => 0
    | 20 => 6
    | 21 => 8
    | _ => 24
  | 20 =>
    match j.val with
    | 0 => 10
    | 1 => 4
    | 2 => 5
    | 3 => 8
    | 4 => 6
    | 5 => 7
    | 6 => 12
    | 7 => 4
    | 8 => 24
    | 9 => 4
    | 10 => 0
    | 11 => 8
    | 12 => 13
    | 13 => 10
    | 14 => 5
    | 15 => 5
    | 16 => 0
    | 17 => 12
    | 18 => 13
    | 19 => 6
    | 20 => 0
    | 21 => 25
    | _ => 26
  | 21 =>
    match j.val with
    | 0 => 2
    | 1 => 10
    | 2 => 21
    | 3 => 6
    | 4 => 1
    | 5 => 24
    | 6 => 4
    | 7 => 14
    | 8 => 17
    | 9 => 5
    | 10 => 19
    | 11 => 1
    | 12 => 0
    | 13 => 22
    | 14 => 14
    | 15 => 10
    | 16 => 0
    | 17 => 21
    | 18 => 24
    | 19 => 8
    | 20 => 25
    | 21 => 0
    | _ => 0
  | _ =>
    match j.val with
    | 0 => 3
    | 1 => 19
    | 2 => 22
    | 3 => 13
    | 4 => 22
    | 5 => 19
    | 6 => 13
    | 7 => 15
    | 8 => 18
    | 9 => 1
    | 10 => 20
    | 11 => 21
    | 12 => 21
    | 13 => 23
    | 14 => 22
    | 15 => 24
    | 16 => 0
    | 17 => 16
    | 18 => 20
    | 19 => 24
    | 20 => 26
    | 21 => 0
    | _ => 0

macro "geometry_arith" : tactic => `(tactic| (
   have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
   have h11 : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
   have h33 : Real.sqrt 33 ^ 2 = 33 := Real.sq_sqrt (by norm_num)
   have hprod : Real.sqrt 33 = Real.sqrt 3 * Real.sqrt 11 := by
     convert Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3) (11 : ℝ) using 1 <;> norm_num
   norm_num [configurationPoint, configurationDistanceLabel, dualSquaredDistance,
     Complex.normSq_apply]
   try nlinarith))

private theorem configurationDistanceLabel_comm (i j : Fin 23) :
    configurationDistanceLabel i j = configurationDistanceLabel j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem configuration_normSq_reverse {i j : Fin 23}
    (h : Complex.normSq (configurationPoint i - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel i j)) :
    Complex.normSq (configurationPoint j - configurationPoint i) =
      dualSquaredDistance (configurationDistanceLabel j i) := by
  calc
    Complex.normSq (configurationPoint j - configurationPoint i) =
        Complex.normSq (configurationPoint i - configurationPoint j) := by
      rw [← neg_sub (configurationPoint i) (configurationPoint j), Complex.normSq_neg]
    _ = dualSquaredDistance (configurationDistanceLabel i j) := h
    _ = dualSquaredDistance (configurationDistanceLabel j i) := by
      rw [configurationDistanceLabel_comm]

private theorem configuration_normSq_00_01 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (1 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (1 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_02 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (2 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (2 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_03 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (3 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (3 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_04 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (4 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (4 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_05 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (5 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (5 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_06 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (6 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (6 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_07 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (7 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (7 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_08 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (8 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (8 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_09 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (9 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (9 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_10 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (10 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (10 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_11 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_12 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_13 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_14 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_15 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_16 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_17 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_18 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_19 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_20 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_21 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_00_22 :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_02 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (2 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (2 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_03 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (3 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (3 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_04 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (4 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (4 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_05 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (5 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (5 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_06 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (6 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (6 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_07 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (7 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (7 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_08 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (8 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (8 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_09 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (9 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (9 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_10 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (10 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (10 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_11 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_12 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_13 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_14 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_15 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_16 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_17 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_18 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_19 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_20 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_21 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_01_22 :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_03 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (3 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (3 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_04 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (4 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (4 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_05 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (5 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (5 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_06 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (6 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (6 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_07 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (7 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (7 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_08 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (8 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (8 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_09 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (9 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (9 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_10 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (10 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (10 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_11 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_12 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_13 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_14 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_15 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_16 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_17 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_18 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_19 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_20 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_21 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_02_22 :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_04 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (4 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (4 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_05 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (5 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (5 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_06 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (6 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (6 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_07 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (7 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (7 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_08 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (8 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (8 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_09 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (9 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (9 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_10 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (10 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (10 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_11 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_12 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_13 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_14 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_15 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_16 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_17 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_18 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_19 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_20 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_21 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_03_22 :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_05 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (5 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (5 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_06 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (6 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (6 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_07 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (7 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (7 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_08 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (8 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (8 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_09 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (9 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (9 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_10 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (10 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (10 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_11 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_12 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_13 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_14 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_15 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_16 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_17 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_18 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_19 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_20 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_21 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_04_22 :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_06 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (6 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (6 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_07 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (7 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (7 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_08 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (8 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (8 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_09 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (9 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (9 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_10 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (10 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (10 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_11 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_12 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_13 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_14 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_15 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_16 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_17 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_18 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_19 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_20 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_21 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_05_22 :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_07 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (7 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (7 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_08 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (8 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (8 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_09 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (9 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (9 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_10 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (10 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (10 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_11 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_12 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_13 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_14 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_15 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_16 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_17 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_18 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_19 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_20 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_21 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_06_22 :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_08 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (8 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (8 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_09 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (9 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (9 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_10 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (10 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (10 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_11 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_12 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_13 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_14 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_15 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_16 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_17 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_18 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_19 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_20 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_21 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_07_22 :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_09 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (9 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (9 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_10 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (10 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (10 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_11 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_12 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_13 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_14 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_15 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_16 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_17 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_18 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_19 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_20 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_21 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_08_22 :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_10 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (10 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (10 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_11 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_12 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_13 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_14 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_15 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_16 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_17 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_18 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_19 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_20 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_21 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_09_22 :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_11 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (11 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (11 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_12 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_13 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_14 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_15 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_16 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_17 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_18 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_19 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_20 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_21 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_10_22 :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_12 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (12 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (12 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_13 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_14 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_15 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_16 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_17 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_18 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_19 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_20 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_21 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_11_22 :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_12_13 :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint (13 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) (13 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_12_14 :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_12_15 :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_12_16 :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_12_17 :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_12_18 :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_12_19 :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_12_20 :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_12_21 :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_12_22 :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_13_14 :
    Complex.normSq (configurationPoint (13 : Fin 23) - configurationPoint (14 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (13 : Fin 23) (14 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_13_15 :
    Complex.normSq (configurationPoint (13 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (13 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_13_16 :
    Complex.normSq (configurationPoint (13 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (13 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_13_17 :
    Complex.normSq (configurationPoint (13 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (13 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_13_18 :
    Complex.normSq (configurationPoint (13 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (13 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_13_19 :
    Complex.normSq (configurationPoint (13 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (13 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_13_20 :
    Complex.normSq (configurationPoint (13 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (13 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_13_21 :
    Complex.normSq (configurationPoint (13 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (13 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_13_22 :
    Complex.normSq (configurationPoint (13 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (13 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_14_15 :
    Complex.normSq (configurationPoint (14 : Fin 23) - configurationPoint (15 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (14 : Fin 23) (15 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_14_16 :
    Complex.normSq (configurationPoint (14 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (14 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_14_17 :
    Complex.normSq (configurationPoint (14 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (14 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_14_18 :
    Complex.normSq (configurationPoint (14 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (14 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_14_19 :
    Complex.normSq (configurationPoint (14 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (14 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_14_20 :
    Complex.normSq (configurationPoint (14 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (14 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_14_21 :
    Complex.normSq (configurationPoint (14 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (14 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_14_22 :
    Complex.normSq (configurationPoint (14 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (14 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_15_16 :
    Complex.normSq (configurationPoint (15 : Fin 23) - configurationPoint (16 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (15 : Fin 23) (16 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_15_17 :
    Complex.normSq (configurationPoint (15 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (15 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_15_18 :
    Complex.normSq (configurationPoint (15 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (15 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_15_19 :
    Complex.normSq (configurationPoint (15 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (15 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_15_20 :
    Complex.normSq (configurationPoint (15 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (15 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_15_21 :
    Complex.normSq (configurationPoint (15 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (15 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_15_22 :
    Complex.normSq (configurationPoint (15 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (15 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_16_17 :
    Complex.normSq (configurationPoint (16 : Fin 23) - configurationPoint (17 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (16 : Fin 23) (17 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_16_18 :
    Complex.normSq (configurationPoint (16 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (16 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_16_19 :
    Complex.normSq (configurationPoint (16 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (16 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_16_20 :
    Complex.normSq (configurationPoint (16 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (16 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_16_21 :
    Complex.normSq (configurationPoint (16 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (16 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_16_22 :
    Complex.normSq (configurationPoint (16 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (16 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_17_18 :
    Complex.normSq (configurationPoint (17 : Fin 23) - configurationPoint (18 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (17 : Fin 23) (18 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_17_19 :
    Complex.normSq (configurationPoint (17 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (17 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_17_20 :
    Complex.normSq (configurationPoint (17 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (17 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_17_21 :
    Complex.normSq (configurationPoint (17 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (17 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_17_22 :
    Complex.normSq (configurationPoint (17 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (17 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_18_19 :
    Complex.normSq (configurationPoint (18 : Fin 23) - configurationPoint (19 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (18 : Fin 23) (19 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_18_20 :
    Complex.normSq (configurationPoint (18 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (18 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_18_21 :
    Complex.normSq (configurationPoint (18 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (18 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_18_22 :
    Complex.normSq (configurationPoint (18 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (18 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_19_20 :
    Complex.normSq (configurationPoint (19 : Fin 23) - configurationPoint (20 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (19 : Fin 23) (20 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_19_21 :
    Complex.normSq (configurationPoint (19 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (19 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_19_22 :
    Complex.normSq (configurationPoint (19 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (19 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_20_21 :
    Complex.normSq (configurationPoint (20 : Fin 23) - configurationPoint (21 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (20 : Fin 23) (21 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_20_22 :
    Complex.normSq (configurationPoint (20 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (20 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_21_22 :
    Complex.normSq (configurationPoint (21 : Fin 23) - configurationPoint (22 : Fin 23)) =
      dualSquaredDistance (configurationDistanceLabel (21 : Fin 23) (22 : Fin 23)) := by
  geometry_arith

private theorem configuration_normSq_from_00 (j : Fin 23)
    (hij : (0 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (0 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (0 : Fin 23) j) := by
  fin_cases j
  · simp at hij
  · exact configuration_normSq_00_01
  · exact configuration_normSq_00_02
  · exact configuration_normSq_00_03
  · exact configuration_normSq_00_04
  · exact configuration_normSq_00_05
  · exact configuration_normSq_00_06
  · exact configuration_normSq_00_07
  · exact configuration_normSq_00_08
  · exact configuration_normSq_00_09
  · exact configuration_normSq_00_10
  · exact configuration_normSq_00_11
  · exact configuration_normSq_00_12
  · exact configuration_normSq_00_13
  · exact configuration_normSq_00_14
  · exact configuration_normSq_00_15
  · exact configuration_normSq_00_16
  · exact configuration_normSq_00_17
  · exact configuration_normSq_00_18
  · exact configuration_normSq_00_19
  · exact configuration_normSq_00_20
  · exact configuration_normSq_00_21
  · exact configuration_normSq_00_22

private theorem configuration_normSq_from_01 (j : Fin 23)
    (hij : (1 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (1 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (1 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_01
  · simp at hij
  · exact configuration_normSq_01_02
  · exact configuration_normSq_01_03
  · exact configuration_normSq_01_04
  · exact configuration_normSq_01_05
  · exact configuration_normSq_01_06
  · exact configuration_normSq_01_07
  · exact configuration_normSq_01_08
  · exact configuration_normSq_01_09
  · exact configuration_normSq_01_10
  · exact configuration_normSq_01_11
  · exact configuration_normSq_01_12
  · exact configuration_normSq_01_13
  · exact configuration_normSq_01_14
  · exact configuration_normSq_01_15
  · exact configuration_normSq_01_16
  · exact configuration_normSq_01_17
  · exact configuration_normSq_01_18
  · exact configuration_normSq_01_19
  · exact configuration_normSq_01_20
  · exact configuration_normSq_01_21
  · exact configuration_normSq_01_22

private theorem configuration_normSq_from_02 (j : Fin 23)
    (hij : (2 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (2 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (2 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_02
  · exact configuration_normSq_reverse configuration_normSq_01_02
  · simp at hij
  · exact configuration_normSq_02_03
  · exact configuration_normSq_02_04
  · exact configuration_normSq_02_05
  · exact configuration_normSq_02_06
  · exact configuration_normSq_02_07
  · exact configuration_normSq_02_08
  · exact configuration_normSq_02_09
  · exact configuration_normSq_02_10
  · exact configuration_normSq_02_11
  · exact configuration_normSq_02_12
  · exact configuration_normSq_02_13
  · exact configuration_normSq_02_14
  · exact configuration_normSq_02_15
  · exact configuration_normSq_02_16
  · exact configuration_normSq_02_17
  · exact configuration_normSq_02_18
  · exact configuration_normSq_02_19
  · exact configuration_normSq_02_20
  · exact configuration_normSq_02_21
  · exact configuration_normSq_02_22

private theorem configuration_normSq_from_03 (j : Fin 23)
    (hij : (3 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (3 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (3 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_03
  · exact configuration_normSq_reverse configuration_normSq_01_03
  · exact configuration_normSq_reverse configuration_normSq_02_03
  · simp at hij
  · exact configuration_normSq_03_04
  · exact configuration_normSq_03_05
  · exact configuration_normSq_03_06
  · exact configuration_normSq_03_07
  · exact configuration_normSq_03_08
  · exact configuration_normSq_03_09
  · exact configuration_normSq_03_10
  · exact configuration_normSq_03_11
  · exact configuration_normSq_03_12
  · exact configuration_normSq_03_13
  · exact configuration_normSq_03_14
  · exact configuration_normSq_03_15
  · exact configuration_normSq_03_16
  · exact configuration_normSq_03_17
  · exact configuration_normSq_03_18
  · exact configuration_normSq_03_19
  · exact configuration_normSq_03_20
  · exact configuration_normSq_03_21
  · exact configuration_normSq_03_22

private theorem configuration_normSq_from_04 (j : Fin 23)
    (hij : (4 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (4 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (4 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_04
  · exact configuration_normSq_reverse configuration_normSq_01_04
  · exact configuration_normSq_reverse configuration_normSq_02_04
  · exact configuration_normSq_reverse configuration_normSq_03_04
  · simp at hij
  · exact configuration_normSq_04_05
  · exact configuration_normSq_04_06
  · exact configuration_normSq_04_07
  · exact configuration_normSq_04_08
  · exact configuration_normSq_04_09
  · exact configuration_normSq_04_10
  · exact configuration_normSq_04_11
  · exact configuration_normSq_04_12
  · exact configuration_normSq_04_13
  · exact configuration_normSq_04_14
  · exact configuration_normSq_04_15
  · exact configuration_normSq_04_16
  · exact configuration_normSq_04_17
  · exact configuration_normSq_04_18
  · exact configuration_normSq_04_19
  · exact configuration_normSq_04_20
  · exact configuration_normSq_04_21
  · exact configuration_normSq_04_22

private theorem configuration_normSq_from_05 (j : Fin 23)
    (hij : (5 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (5 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (5 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_05
  · exact configuration_normSq_reverse configuration_normSq_01_05
  · exact configuration_normSq_reverse configuration_normSq_02_05
  · exact configuration_normSq_reverse configuration_normSq_03_05
  · exact configuration_normSq_reverse configuration_normSq_04_05
  · simp at hij
  · exact configuration_normSq_05_06
  · exact configuration_normSq_05_07
  · exact configuration_normSq_05_08
  · exact configuration_normSq_05_09
  · exact configuration_normSq_05_10
  · exact configuration_normSq_05_11
  · exact configuration_normSq_05_12
  · exact configuration_normSq_05_13
  · exact configuration_normSq_05_14
  · exact configuration_normSq_05_15
  · exact configuration_normSq_05_16
  · exact configuration_normSq_05_17
  · exact configuration_normSq_05_18
  · exact configuration_normSq_05_19
  · exact configuration_normSq_05_20
  · exact configuration_normSq_05_21
  · exact configuration_normSq_05_22

private theorem configuration_normSq_from_06 (j : Fin 23)
    (hij : (6 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (6 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (6 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_06
  · exact configuration_normSq_reverse configuration_normSq_01_06
  · exact configuration_normSq_reverse configuration_normSq_02_06
  · exact configuration_normSq_reverse configuration_normSq_03_06
  · exact configuration_normSq_reverse configuration_normSq_04_06
  · exact configuration_normSq_reverse configuration_normSq_05_06
  · simp at hij
  · exact configuration_normSq_06_07
  · exact configuration_normSq_06_08
  · exact configuration_normSq_06_09
  · exact configuration_normSq_06_10
  · exact configuration_normSq_06_11
  · exact configuration_normSq_06_12
  · exact configuration_normSq_06_13
  · exact configuration_normSq_06_14
  · exact configuration_normSq_06_15
  · exact configuration_normSq_06_16
  · exact configuration_normSq_06_17
  · exact configuration_normSq_06_18
  · exact configuration_normSq_06_19
  · exact configuration_normSq_06_20
  · exact configuration_normSq_06_21
  · exact configuration_normSq_06_22

private theorem configuration_normSq_from_07 (j : Fin 23)
    (hij : (7 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (7 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (7 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_07
  · exact configuration_normSq_reverse configuration_normSq_01_07
  · exact configuration_normSq_reverse configuration_normSq_02_07
  · exact configuration_normSq_reverse configuration_normSq_03_07
  · exact configuration_normSq_reverse configuration_normSq_04_07
  · exact configuration_normSq_reverse configuration_normSq_05_07
  · exact configuration_normSq_reverse configuration_normSq_06_07
  · simp at hij
  · exact configuration_normSq_07_08
  · exact configuration_normSq_07_09
  · exact configuration_normSq_07_10
  · exact configuration_normSq_07_11
  · exact configuration_normSq_07_12
  · exact configuration_normSq_07_13
  · exact configuration_normSq_07_14
  · exact configuration_normSq_07_15
  · exact configuration_normSq_07_16
  · exact configuration_normSq_07_17
  · exact configuration_normSq_07_18
  · exact configuration_normSq_07_19
  · exact configuration_normSq_07_20
  · exact configuration_normSq_07_21
  · exact configuration_normSq_07_22

private theorem configuration_normSq_from_08 (j : Fin 23)
    (hij : (8 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (8 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (8 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_08
  · exact configuration_normSq_reverse configuration_normSq_01_08
  · exact configuration_normSq_reverse configuration_normSq_02_08
  · exact configuration_normSq_reverse configuration_normSq_03_08
  · exact configuration_normSq_reverse configuration_normSq_04_08
  · exact configuration_normSq_reverse configuration_normSq_05_08
  · exact configuration_normSq_reverse configuration_normSq_06_08
  · exact configuration_normSq_reverse configuration_normSq_07_08
  · simp at hij
  · exact configuration_normSq_08_09
  · exact configuration_normSq_08_10
  · exact configuration_normSq_08_11
  · exact configuration_normSq_08_12
  · exact configuration_normSq_08_13
  · exact configuration_normSq_08_14
  · exact configuration_normSq_08_15
  · exact configuration_normSq_08_16
  · exact configuration_normSq_08_17
  · exact configuration_normSq_08_18
  · exact configuration_normSq_08_19
  · exact configuration_normSq_08_20
  · exact configuration_normSq_08_21
  · exact configuration_normSq_08_22

private theorem configuration_normSq_from_09 (j : Fin 23)
    (hij : (9 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (9 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (9 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_09
  · exact configuration_normSq_reverse configuration_normSq_01_09
  · exact configuration_normSq_reverse configuration_normSq_02_09
  · exact configuration_normSq_reverse configuration_normSq_03_09
  · exact configuration_normSq_reverse configuration_normSq_04_09
  · exact configuration_normSq_reverse configuration_normSq_05_09
  · exact configuration_normSq_reverse configuration_normSq_06_09
  · exact configuration_normSq_reverse configuration_normSq_07_09
  · exact configuration_normSq_reverse configuration_normSq_08_09
  · simp at hij
  · exact configuration_normSq_09_10
  · exact configuration_normSq_09_11
  · exact configuration_normSq_09_12
  · exact configuration_normSq_09_13
  · exact configuration_normSq_09_14
  · exact configuration_normSq_09_15
  · exact configuration_normSq_09_16
  · exact configuration_normSq_09_17
  · exact configuration_normSq_09_18
  · exact configuration_normSq_09_19
  · exact configuration_normSq_09_20
  · exact configuration_normSq_09_21
  · exact configuration_normSq_09_22

private theorem configuration_normSq_from_10 (j : Fin 23)
    (hij : (10 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (10 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (10 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_10
  · exact configuration_normSq_reverse configuration_normSq_01_10
  · exact configuration_normSq_reverse configuration_normSq_02_10
  · exact configuration_normSq_reverse configuration_normSq_03_10
  · exact configuration_normSq_reverse configuration_normSq_04_10
  · exact configuration_normSq_reverse configuration_normSq_05_10
  · exact configuration_normSq_reverse configuration_normSq_06_10
  · exact configuration_normSq_reverse configuration_normSq_07_10
  · exact configuration_normSq_reverse configuration_normSq_08_10
  · exact configuration_normSq_reverse configuration_normSq_09_10
  · simp at hij
  · exact configuration_normSq_10_11
  · exact configuration_normSq_10_12
  · exact configuration_normSq_10_13
  · exact configuration_normSq_10_14
  · exact configuration_normSq_10_15
  · exact configuration_normSq_10_16
  · exact configuration_normSq_10_17
  · exact configuration_normSq_10_18
  · exact configuration_normSq_10_19
  · exact configuration_normSq_10_20
  · exact configuration_normSq_10_21
  · exact configuration_normSq_10_22

private theorem configuration_normSq_from_11 (j : Fin 23)
    (hij : (11 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (11 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (11 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_11
  · exact configuration_normSq_reverse configuration_normSq_01_11
  · exact configuration_normSq_reverse configuration_normSq_02_11
  · exact configuration_normSq_reverse configuration_normSq_03_11
  · exact configuration_normSq_reverse configuration_normSq_04_11
  · exact configuration_normSq_reverse configuration_normSq_05_11
  · exact configuration_normSq_reverse configuration_normSq_06_11
  · exact configuration_normSq_reverse configuration_normSq_07_11
  · exact configuration_normSq_reverse configuration_normSq_08_11
  · exact configuration_normSq_reverse configuration_normSq_09_11
  · exact configuration_normSq_reverse configuration_normSq_10_11
  · simp at hij
  · exact configuration_normSq_11_12
  · exact configuration_normSq_11_13
  · exact configuration_normSq_11_14
  · exact configuration_normSq_11_15
  · exact configuration_normSq_11_16
  · exact configuration_normSq_11_17
  · exact configuration_normSq_11_18
  · exact configuration_normSq_11_19
  · exact configuration_normSq_11_20
  · exact configuration_normSq_11_21
  · exact configuration_normSq_11_22

private theorem configuration_normSq_from_12 (j : Fin 23)
    (hij : (12 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (12 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (12 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_12
  · exact configuration_normSq_reverse configuration_normSq_01_12
  · exact configuration_normSq_reverse configuration_normSq_02_12
  · exact configuration_normSq_reverse configuration_normSq_03_12
  · exact configuration_normSq_reverse configuration_normSq_04_12
  · exact configuration_normSq_reverse configuration_normSq_05_12
  · exact configuration_normSq_reverse configuration_normSq_06_12
  · exact configuration_normSq_reverse configuration_normSq_07_12
  · exact configuration_normSq_reverse configuration_normSq_08_12
  · exact configuration_normSq_reverse configuration_normSq_09_12
  · exact configuration_normSq_reverse configuration_normSq_10_12
  · exact configuration_normSq_reverse configuration_normSq_11_12
  · simp at hij
  · exact configuration_normSq_12_13
  · exact configuration_normSq_12_14
  · exact configuration_normSq_12_15
  · exact configuration_normSq_12_16
  · exact configuration_normSq_12_17
  · exact configuration_normSq_12_18
  · exact configuration_normSq_12_19
  · exact configuration_normSq_12_20
  · exact configuration_normSq_12_21
  · exact configuration_normSq_12_22

private theorem configuration_normSq_from_13 (j : Fin 23)
    (hij : (13 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (13 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (13 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_13
  · exact configuration_normSq_reverse configuration_normSq_01_13
  · exact configuration_normSq_reverse configuration_normSq_02_13
  · exact configuration_normSq_reverse configuration_normSq_03_13
  · exact configuration_normSq_reverse configuration_normSq_04_13
  · exact configuration_normSq_reverse configuration_normSq_05_13
  · exact configuration_normSq_reverse configuration_normSq_06_13
  · exact configuration_normSq_reverse configuration_normSq_07_13
  · exact configuration_normSq_reverse configuration_normSq_08_13
  · exact configuration_normSq_reverse configuration_normSq_09_13
  · exact configuration_normSq_reverse configuration_normSq_10_13
  · exact configuration_normSq_reverse configuration_normSq_11_13
  · exact configuration_normSq_reverse configuration_normSq_12_13
  · simp at hij
  · exact configuration_normSq_13_14
  · exact configuration_normSq_13_15
  · exact configuration_normSq_13_16
  · exact configuration_normSq_13_17
  · exact configuration_normSq_13_18
  · exact configuration_normSq_13_19
  · exact configuration_normSq_13_20
  · exact configuration_normSq_13_21
  · exact configuration_normSq_13_22

private theorem configuration_normSq_from_14 (j : Fin 23)
    (hij : (14 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (14 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (14 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_14
  · exact configuration_normSq_reverse configuration_normSq_01_14
  · exact configuration_normSq_reverse configuration_normSq_02_14
  · exact configuration_normSq_reverse configuration_normSq_03_14
  · exact configuration_normSq_reverse configuration_normSq_04_14
  · exact configuration_normSq_reverse configuration_normSq_05_14
  · exact configuration_normSq_reverse configuration_normSq_06_14
  · exact configuration_normSq_reverse configuration_normSq_07_14
  · exact configuration_normSq_reverse configuration_normSq_08_14
  · exact configuration_normSq_reverse configuration_normSq_09_14
  · exact configuration_normSq_reverse configuration_normSq_10_14
  · exact configuration_normSq_reverse configuration_normSq_11_14
  · exact configuration_normSq_reverse configuration_normSq_12_14
  · exact configuration_normSq_reverse configuration_normSq_13_14
  · simp at hij
  · exact configuration_normSq_14_15
  · exact configuration_normSq_14_16
  · exact configuration_normSq_14_17
  · exact configuration_normSq_14_18
  · exact configuration_normSq_14_19
  · exact configuration_normSq_14_20
  · exact configuration_normSq_14_21
  · exact configuration_normSq_14_22

private theorem configuration_normSq_from_15 (j : Fin 23)
    (hij : (15 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (15 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (15 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_15
  · exact configuration_normSq_reverse configuration_normSq_01_15
  · exact configuration_normSq_reverse configuration_normSq_02_15
  · exact configuration_normSq_reverse configuration_normSq_03_15
  · exact configuration_normSq_reverse configuration_normSq_04_15
  · exact configuration_normSq_reverse configuration_normSq_05_15
  · exact configuration_normSq_reverse configuration_normSq_06_15
  · exact configuration_normSq_reverse configuration_normSq_07_15
  · exact configuration_normSq_reverse configuration_normSq_08_15
  · exact configuration_normSq_reverse configuration_normSq_09_15
  · exact configuration_normSq_reverse configuration_normSq_10_15
  · exact configuration_normSq_reverse configuration_normSq_11_15
  · exact configuration_normSq_reverse configuration_normSq_12_15
  · exact configuration_normSq_reverse configuration_normSq_13_15
  · exact configuration_normSq_reverse configuration_normSq_14_15
  · simp at hij
  · exact configuration_normSq_15_16
  · exact configuration_normSq_15_17
  · exact configuration_normSq_15_18
  · exact configuration_normSq_15_19
  · exact configuration_normSq_15_20
  · exact configuration_normSq_15_21
  · exact configuration_normSq_15_22

private theorem configuration_normSq_from_16 (j : Fin 23)
    (hij : (16 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (16 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (16 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_16
  · exact configuration_normSq_reverse configuration_normSq_01_16
  · exact configuration_normSq_reverse configuration_normSq_02_16
  · exact configuration_normSq_reverse configuration_normSq_03_16
  · exact configuration_normSq_reverse configuration_normSq_04_16
  · exact configuration_normSq_reverse configuration_normSq_05_16
  · exact configuration_normSq_reverse configuration_normSq_06_16
  · exact configuration_normSq_reverse configuration_normSq_07_16
  · exact configuration_normSq_reverse configuration_normSq_08_16
  · exact configuration_normSq_reverse configuration_normSq_09_16
  · exact configuration_normSq_reverse configuration_normSq_10_16
  · exact configuration_normSq_reverse configuration_normSq_11_16
  · exact configuration_normSq_reverse configuration_normSq_12_16
  · exact configuration_normSq_reverse configuration_normSq_13_16
  · exact configuration_normSq_reverse configuration_normSq_14_16
  · exact configuration_normSq_reverse configuration_normSq_15_16
  · simp at hij
  · exact configuration_normSq_16_17
  · exact configuration_normSq_16_18
  · exact configuration_normSq_16_19
  · exact configuration_normSq_16_20
  · exact configuration_normSq_16_21
  · exact configuration_normSq_16_22

private theorem configuration_normSq_from_17 (j : Fin 23)
    (hij : (17 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (17 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (17 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_17
  · exact configuration_normSq_reverse configuration_normSq_01_17
  · exact configuration_normSq_reverse configuration_normSq_02_17
  · exact configuration_normSq_reverse configuration_normSq_03_17
  · exact configuration_normSq_reverse configuration_normSq_04_17
  · exact configuration_normSq_reverse configuration_normSq_05_17
  · exact configuration_normSq_reverse configuration_normSq_06_17
  · exact configuration_normSq_reverse configuration_normSq_07_17
  · exact configuration_normSq_reverse configuration_normSq_08_17
  · exact configuration_normSq_reverse configuration_normSq_09_17
  · exact configuration_normSq_reverse configuration_normSq_10_17
  · exact configuration_normSq_reverse configuration_normSq_11_17
  · exact configuration_normSq_reverse configuration_normSq_12_17
  · exact configuration_normSq_reverse configuration_normSq_13_17
  · exact configuration_normSq_reverse configuration_normSq_14_17
  · exact configuration_normSq_reverse configuration_normSq_15_17
  · exact configuration_normSq_reverse configuration_normSq_16_17
  · simp at hij
  · exact configuration_normSq_17_18
  · exact configuration_normSq_17_19
  · exact configuration_normSq_17_20
  · exact configuration_normSq_17_21
  · exact configuration_normSq_17_22

private theorem configuration_normSq_from_18 (j : Fin 23)
    (hij : (18 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (18 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (18 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_18
  · exact configuration_normSq_reverse configuration_normSq_01_18
  · exact configuration_normSq_reverse configuration_normSq_02_18
  · exact configuration_normSq_reverse configuration_normSq_03_18
  · exact configuration_normSq_reverse configuration_normSq_04_18
  · exact configuration_normSq_reverse configuration_normSq_05_18
  · exact configuration_normSq_reverse configuration_normSq_06_18
  · exact configuration_normSq_reverse configuration_normSq_07_18
  · exact configuration_normSq_reverse configuration_normSq_08_18
  · exact configuration_normSq_reverse configuration_normSq_09_18
  · exact configuration_normSq_reverse configuration_normSq_10_18
  · exact configuration_normSq_reverse configuration_normSq_11_18
  · exact configuration_normSq_reverse configuration_normSq_12_18
  · exact configuration_normSq_reverse configuration_normSq_13_18
  · exact configuration_normSq_reverse configuration_normSq_14_18
  · exact configuration_normSq_reverse configuration_normSq_15_18
  · exact configuration_normSq_reverse configuration_normSq_16_18
  · exact configuration_normSq_reverse configuration_normSq_17_18
  · simp at hij
  · exact configuration_normSq_18_19
  · exact configuration_normSq_18_20
  · exact configuration_normSq_18_21
  · exact configuration_normSq_18_22

private theorem configuration_normSq_from_19 (j : Fin 23)
    (hij : (19 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (19 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (19 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_19
  · exact configuration_normSq_reverse configuration_normSq_01_19
  · exact configuration_normSq_reverse configuration_normSq_02_19
  · exact configuration_normSq_reverse configuration_normSq_03_19
  · exact configuration_normSq_reverse configuration_normSq_04_19
  · exact configuration_normSq_reverse configuration_normSq_05_19
  · exact configuration_normSq_reverse configuration_normSq_06_19
  · exact configuration_normSq_reverse configuration_normSq_07_19
  · exact configuration_normSq_reverse configuration_normSq_08_19
  · exact configuration_normSq_reverse configuration_normSq_09_19
  · exact configuration_normSq_reverse configuration_normSq_10_19
  · exact configuration_normSq_reverse configuration_normSq_11_19
  · exact configuration_normSq_reverse configuration_normSq_12_19
  · exact configuration_normSq_reverse configuration_normSq_13_19
  · exact configuration_normSq_reverse configuration_normSq_14_19
  · exact configuration_normSq_reverse configuration_normSq_15_19
  · exact configuration_normSq_reverse configuration_normSq_16_19
  · exact configuration_normSq_reverse configuration_normSq_17_19
  · exact configuration_normSq_reverse configuration_normSq_18_19
  · simp at hij
  · exact configuration_normSq_19_20
  · exact configuration_normSq_19_21
  · exact configuration_normSq_19_22

private theorem configuration_normSq_from_20 (j : Fin 23)
    (hij : (20 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (20 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (20 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_20
  · exact configuration_normSq_reverse configuration_normSq_01_20
  · exact configuration_normSq_reverse configuration_normSq_02_20
  · exact configuration_normSq_reverse configuration_normSq_03_20
  · exact configuration_normSq_reverse configuration_normSq_04_20
  · exact configuration_normSq_reverse configuration_normSq_05_20
  · exact configuration_normSq_reverse configuration_normSq_06_20
  · exact configuration_normSq_reverse configuration_normSq_07_20
  · exact configuration_normSq_reverse configuration_normSq_08_20
  · exact configuration_normSq_reverse configuration_normSq_09_20
  · exact configuration_normSq_reverse configuration_normSq_10_20
  · exact configuration_normSq_reverse configuration_normSq_11_20
  · exact configuration_normSq_reverse configuration_normSq_12_20
  · exact configuration_normSq_reverse configuration_normSq_13_20
  · exact configuration_normSq_reverse configuration_normSq_14_20
  · exact configuration_normSq_reverse configuration_normSq_15_20
  · exact configuration_normSq_reverse configuration_normSq_16_20
  · exact configuration_normSq_reverse configuration_normSq_17_20
  · exact configuration_normSq_reverse configuration_normSq_18_20
  · exact configuration_normSq_reverse configuration_normSq_19_20
  · simp at hij
  · exact configuration_normSq_20_21
  · exact configuration_normSq_20_22

private theorem configuration_normSq_from_21 (j : Fin 23)
    (hij : (21 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (21 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (21 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_21
  · exact configuration_normSq_reverse configuration_normSq_01_21
  · exact configuration_normSq_reverse configuration_normSq_02_21
  · exact configuration_normSq_reverse configuration_normSq_03_21
  · exact configuration_normSq_reverse configuration_normSq_04_21
  · exact configuration_normSq_reverse configuration_normSq_05_21
  · exact configuration_normSq_reverse configuration_normSq_06_21
  · exact configuration_normSq_reverse configuration_normSq_07_21
  · exact configuration_normSq_reverse configuration_normSq_08_21
  · exact configuration_normSq_reverse configuration_normSq_09_21
  · exact configuration_normSq_reverse configuration_normSq_10_21
  · exact configuration_normSq_reverse configuration_normSq_11_21
  · exact configuration_normSq_reverse configuration_normSq_12_21
  · exact configuration_normSq_reverse configuration_normSq_13_21
  · exact configuration_normSq_reverse configuration_normSq_14_21
  · exact configuration_normSq_reverse configuration_normSq_15_21
  · exact configuration_normSq_reverse configuration_normSq_16_21
  · exact configuration_normSq_reverse configuration_normSq_17_21
  · exact configuration_normSq_reverse configuration_normSq_18_21
  · exact configuration_normSq_reverse configuration_normSq_19_21
  · exact configuration_normSq_reverse configuration_normSq_20_21
  · simp at hij
  · exact configuration_normSq_21_22

private theorem configuration_normSq_from_22 (j : Fin 23)
    (hij : (22 : Fin 23) ≠ j) :
    Complex.normSq (configurationPoint (22 : Fin 23) - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel (22 : Fin 23) j) := by
  fin_cases j
  · exact configuration_normSq_reverse configuration_normSq_00_22
  · exact configuration_normSq_reverse configuration_normSq_01_22
  · exact configuration_normSq_reverse configuration_normSq_02_22
  · exact configuration_normSq_reverse configuration_normSq_03_22
  · exact configuration_normSq_reverse configuration_normSq_04_22
  · exact configuration_normSq_reverse configuration_normSq_05_22
  · exact configuration_normSq_reverse configuration_normSq_06_22
  · exact configuration_normSq_reverse configuration_normSq_07_22
  · exact configuration_normSq_reverse configuration_normSq_08_22
  · exact configuration_normSq_reverse configuration_normSq_09_22
  · exact configuration_normSq_reverse configuration_normSq_10_22
  · exact configuration_normSq_reverse configuration_normSq_11_22
  · exact configuration_normSq_reverse configuration_normSq_12_22
  · exact configuration_normSq_reverse configuration_normSq_13_22
  · exact configuration_normSq_reverse configuration_normSq_14_22
  · exact configuration_normSq_reverse configuration_normSq_15_22
  · exact configuration_normSq_reverse configuration_normSq_16_22
  · exact configuration_normSq_reverse configuration_normSq_17_22
  · exact configuration_normSq_reverse configuration_normSq_18_22
  · exact configuration_normSq_reverse configuration_normSq_19_22
  · exact configuration_normSq_reverse configuration_normSq_20_22
  · exact configuration_normSq_reverse configuration_normSq_21_22
  · simp at hij

theorem configuration_normSq (i j : Fin 23) (hij : i ≠ j) :
    Complex.normSq (configurationPoint i - configurationPoint j) =
      dualSquaredDistance (configurationDistanceLabel i j) := by
  fin_cases i
  · exact configuration_normSq_from_00 j hij
  · exact configuration_normSq_from_01 j hij
  · exact configuration_normSq_from_02 j hij
  · exact configuration_normSq_from_03 j hij
  · exact configuration_normSq_from_04 j hij
  · exact configuration_normSq_from_05 j hij
  · exact configuration_normSq_from_06 j hij
  · exact configuration_normSq_from_07 j hij
  · exact configuration_normSq_from_08 j hij
  · exact configuration_normSq_from_09 j hij
  · exact configuration_normSq_from_10 j hij
  · exact configuration_normSq_from_11 j hij
  · exact configuration_normSq_from_12 j hij
  · exact configuration_normSq_from_13 j hij
  · exact configuration_normSq_from_14 j hij
  · exact configuration_normSq_from_15 j hij
  · exact configuration_normSq_from_16 j hij
  · exact configuration_normSq_from_17 j hij
  · exact configuration_normSq_from_18 j hij
  · exact configuration_normSq_from_19 j hij
  · exact configuration_normSq_from_20 j hij
  · exact configuration_normSq_from_21 j hij
  · exact configuration_normSq_from_22 j hij

end Erdos232
