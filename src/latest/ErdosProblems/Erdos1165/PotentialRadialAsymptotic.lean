/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.PotentialAxis
import ErdosProblems.Erdos1165.PotentialRadialMass
import ErdosProblems.Erdos1165.PotentialEuclideanGeometry
import ErdosProblems.Erdos1165.PotentialAsymptotic
import Mathlib.Analysis.Complex.Norm

/-!
# Radial asymptotic for the planar potential kernel

This file combines the exact coordinate-axis evaluation with the uniform
near-radius Fourier comparison.  It identifies the classical constant and
proves an inverse-radius remainder, first in diagonal coordinates and then
for every nonzero point of the lattice (both parity classes).
-/

open Real
open scoped BigOperators

namespace Erdos1165
namespace PotentialRadialAsymptotic

open EndpointDiagonal PotentialAxis PotentialAsymptotic PotentialConvergence
open PotentialEuclideanGeometry PotentialFourierIntegral PotentialRadialMass

/-- The classical constant in the planar simple-random-walk potential
kernel, written in terms of the diagonal-axis constant. -/
noncomputable def cPotential : ℝ := cDiag - Real.log 2 / Real.pi

/-- The same constant in its standard closed form. -/
theorem cPotential_eq :
    cPotential = (2 * Real.eulerMascheroniConstant + 3 * Real.log 2) / Real.pi := by
  unfold cPotential cDiag
  field_simp
  ring

private lemma radiusSq_le_two_mul_max_sq (d e : ℕ) :
    radiusSq d e ≤ 2 * (max d e) ^ 2 := by
  unfold radiusSq
  have hd : d ≤ max d e := le_max_left _ _
  have he : e ≤ max d e := le_max_right _ _
  nlinarith [Nat.pow_le_pow_left hd 2, Nat.pow_le_pow_left he 2]

private lemma sqrt_radiusSq_geometry (d e : ℕ) :
    let R := max d e
    let Q := radiusSq d e
    let m := Nat.sqrt Q
    R ≤ m ∧ m ≤ 2 * R ∧
      |(Q : ℝ) - ((m ^ 2 : ℕ) : ℝ)| ≤ (8 : ℝ) * R := by
  dsimp only
  let R := max d e
  let Q := radiusSq d e
  let m := Nat.sqrt Q
  have hRlo : R ^ 2 ≤ Q := by
    dsimp [R, Q, radiusSq]
    rcases max_cases d e with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      exact Nat.le_add_right _ _
    · rw [h]
      exact Nat.le_add_left _ _
  have hmlo : R ≤ m := by
    dsimp [m]
    exact Nat.le_sqrt'.2 hRlo
  have hQhi : Q ≤ (2 * R) ^ 2 := by
    have h := radiusSq_le_two_mul_max_sq d e
    dsimp [Q, R]
    nlinarith
  have hmhi : m ≤ 2 * R := by
    dsimp [m]
    have h := Nat.sqrt_le_sqrt hQhi
    simpa using h
  have hmSq : m ^ 2 ≤ Q := by
    dsimp [m]
    exact Nat.sqrt_le' Q
  have hQlt : Q < (m + 1) ^ 2 := by
    dsimp [m]
    exact Nat.lt_succ_sqrt' Q
  have hgapNat : Q - m ^ 2 ≤ 8 * R := by
    have : Q ≤ m ^ 2 + 2 * m := by nlinarith [hQlt]
    omega
  have hcast : ((Q - m ^ 2 : ℕ) : ℝ) ≤ (8 : ℝ) * R := by
    exact_mod_cast hgapNat
  refine ⟨hmlo, hmhi, ?_⟩
  rw [abs_of_nonneg]
  · rw [← Nat.cast_sub hmSq]
    exact hcast
  · have hmSqR : ((m ^ 2 : ℕ) : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hmSq
    exact sub_nonneg.mpr hmSqR

private lemma abs_log_natSqrt_sub_log_sqrt_le {Q R : ℕ}
    (hR : 0 < R) (hRlo : R ^ 2 ≤ Q) :
    |Real.log (Nat.sqrt Q : ℝ) - Real.log (Real.sqrt (Q : ℝ))| ≤
      1 / (R : ℝ) := by
  let m := Nat.sqrt Q
  let r := Real.sqrt (Q : ℝ)
  have hmNat : R ≤ m := Nat.le_sqrt'.2 hRlo
  have hm : (0 : ℝ) < m := by exact_mod_cast (hR.trans_le hmNat)
  have hmR : (R : ℝ) ≤ m := by exact_mod_cast hmNat
  have hmr : (m : ℝ) ≤ r := by
    dsimp [m, r]
    exact Real.nat_sqrt_le_real_sqrt
  have hrlt : r < (m : ℝ) + 1 := by
    dsimp [m, r]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Real.real_sqrt_lt_nat_sqrt_succ (a := Q))
  have hlog : Real.log (m : ℝ) ≤ Real.log r :=
    Real.log_le_log hm hmr
  rw [abs_of_nonpos (sub_nonpos.mpr hlog)]
  have hratioPos : 0 < r / (m : ℝ) := div_pos (hm.trans_le hmr) hm
  have hlogRatio : Real.log r - Real.log (m : ℝ) = Real.log (r / (m : ℝ)) := by
    rw [Real.log_div (hm.trans_le hmr).ne' hm.ne']
  rw [neg_sub, hlogRatio]
  calc
    Real.log (r / (m : ℝ)) ≤ r / (m : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos hratioPos
    _ ≤ 1 / (m : ℝ) := by
      apply (sub_le_iff_le_add).2
      rw [div_le_iff₀ hm]
      calc
        r ≤ (m : ℝ) + 1 := hrlt.le
        _ = (1 / (m : ℝ) + 1) * m := by field_simp
          <;> ring
    _ ≤ 1 / (R : ℝ) := by
      exact one_div_le_one_div_of_le (by exact_mod_cast hR) hmR

/-- Sharp radial asymptotic in the nonnegative diagonal coordinates. -/
theorem abs_fourierPotential_sub_log_diagonalRadius_sub_cDiag_le
    {d e : ℕ} (hR : 2 ≤ max d e) :
    |fourierPotential d e - (2 / Real.pi) * Real.log (diagonalRadius d e) -
        cDiag| ≤ 1611010000 / (max d e : ℝ) := by
  let R := max d e
  let Q := radiusSq d e
  let m := Nat.sqrt Q
  have hRpos : 0 < R := by dsimp [R]; omega
  have hgeom := sqrt_radiusSq_geometry d e
  change R ≤ m ∧ m ≤ 2 * R ∧
      |(Q : ℝ) - ((m ^ 2 : ℕ) : ℝ)| ≤ (8 : ℝ) * R at hgeom
  have hcomp := abs_fourierPotential_sub_le_of_radiusSq_gap
    (d := d) (e := e) (d' := m) (e' := 0) (ρ := R) (L := 8)
    (by simpa [R] using hR)
    (le_trans (le_max_left d e) (Nat.le_mul_of_pos_left _ (by omega)))
    (le_trans (le_max_right d e) (Nat.le_mul_of_pos_left _ (by omega)))
    hgeom.2.1 (by omega) (by simp [R]) (by simpa using hgeom.1) (by
      simpa [Q, m, radiusSq] using hgeom.2.2)
  have haxis := abs_fourierPotential_axis_sub_log_sub_cDiag_le
    (d := m) (hRpos.trans_le hgeom.1)
  have hQlo : R ^ 2 ≤ Q := by
    dsimp [R, Q, radiusSq]
    rcases max_cases d e with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
      exact Nat.le_add_right _ _
    · rw [h]
      exact Nat.le_add_left _ _
  have hlog := abs_log_natSqrt_sub_log_sqrt_le hRpos hQlo
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcoef : (2 : ℝ) / Real.pi ≤ 1 := by
    rw [div_le_one hpi]
    exact Real.two_le_pi
  have hmR : (R : ℝ) ≤ m := by exact_mod_cast hgeom.1
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hRpos
  have hmreal : (0 : ℝ) < m := by exact_mod_cast (hRpos.trans_le hgeom.1)
  have haxis' :
      |fourierPotential m 0 - (2 / Real.pi) * Real.log (m : ℝ) - cDiag| ≤
        4 / (R : ℝ) := by
    calc
      _ ≤ 4 / (Real.pi * (m : ℝ)) := haxis
      _ ≤ 4 / (R : ℝ) := by
        rw [div_le_div_iff₀ (mul_pos hpi hmreal) hRreal]
        nlinarith [Real.two_le_pi]
  have hlog' :
      |(2 / Real.pi) *
          (Real.log (m : ℝ) - Real.log (diagonalRadius d e))| ≤
        1 / (R : ℝ) := by
    have hradius : diagonalRadius d e = Real.sqrt (Q : ℝ) := by rfl
    rw [abs_mul, abs_of_nonneg (div_nonneg (by norm_num) hpi.le), hradius]
    calc
      (2 / Real.pi) *
          |Real.log (m : ℝ) - Real.log (Real.sqrt (Q : ℝ))| ≤
        1 * (1 / (R : ℝ)) := mul_le_mul hcoef hlog (abs_nonneg _) (by positivity)
      _ = _ := one_mul _
  have hfinal :
      |fourierPotential d e - (2 / Real.pi) * Real.log (diagonalRadius d e) -
        cDiag| ≤ 1611010000 / (R : ℝ) := by
    calc
      |fourierPotential d e - (2 / Real.pi) * Real.log (diagonalRadius d e) -
          cDiag| =
        |(fourierPotential d e - fourierPotential m 0) +
          (fourierPotential m 0 - (2 / Real.pi) * Real.log (m : ℝ) - cDiag) +
          (2 / Real.pi) *
            (Real.log (m : ℝ) - Real.log (diagonalRadius d e))| := by ring_nf
      _ ≤ |fourierPotential d e - fourierPotential m 0| +
          |fourierPotential m 0 - (2 / Real.pi) * Real.log (m : ℝ) - cDiag| +
          |(2 / Real.pi) *
            (Real.log (m : ℝ) - Real.log (diagonalRadius d e))| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (1611000000 + 1000 * (8 : ℝ)) / (R : ℝ) +
          4 / (R : ℝ) + 1 / (R : ℝ) :=
        add_le_add (add_le_add hcomp haxis') hlog'
      _ ≤ 1611010000 / (R : ℝ) := by
        field_simp
        norm_num
  simpa [R] using hfinal

/-- At an even-parity point, its Euclidean radius is at most twice the
maximum half-diagonal coordinate. -/
theorem euclideanRadius_le_two_mul_diagonalMax_of_even {x : Point}
    (hx : Even (x.1 + x.2)) :
    euclideanRadius x ≤ 2 *
      (max (firstDiagonalOffset x) (secondDiagonalOffset x) : ℕ) := by
  let d := firstDiagonalOffset x
  let e := secondDiagonalOffset x
  let R := max d e
  have hsq := radiusSq_diagonalOffsets_eq_cartesian_half_of_even hx
  have hRbound := radiusSq_le_two_mul_max_sq d e
  have heq : euclideanRadius x ^ 2 = 2 * (radiusSq d e : ℝ) := by
    rw [euclideanRadius_sq, hsq]
    ring
  have hsquare : euclideanRadius x ^ 2 ≤ (2 * (R : ℝ)) ^ 2 := by
    rw [heq]
    have hcast : (radiusSq d e : ℝ) ≤ 2 * (R : ℝ) ^ 2 := by
      exact_mod_cast hRbound
    nlinarith
  have := (sq_le_sq₀ (euclideanRadius_nonneg x)
    (by positivity : (0 : ℝ) ≤ 2 * (R : ℝ))).1 hsquare
  simpa [d, e, R] using this

/-- Radial asymptotic at an even-parity lattice point, now in ordinary
Euclidean coordinates and with the classical constant. -/
theorem abs_planarPotentialKernel_sub_log_euclideanRadius_sub_cPotential_le_of_even
    {x : Point} (hx : Even (x.1 + x.2))
    (hR : 2 ≤ max (firstDiagonalOffset x) (secondDiagonalOffset x)) :
    |planarPotentialKernel x - (2 / Real.pi) * Real.log (euclideanRadius x) -
        cPotential| ≤ 3222020000 / euclideanRadius x := by
  let d := firstDiagonalOffset x
  let e := secondDiagonalOffset x
  let R := max d e
  have hdiagPos : 0 < diagonalRadius d e := by
    unfold diagonalRadius
    rw [Real.sqrt_pos]
    have : 0 < radiusSq d e := by
      unfold radiusSq
      rcases eq_zero_or_pos d with hd0 | hd
      · rcases eq_zero_or_pos e with he0 | he
        · simp [R, d, e, hd0, he0] at hR
        · rw [hd0]
          positivity
      · positivity
    exact_mod_cast this
  have hlog := log_euclideanRadius_eq_of_even hx hdiagPos
  have hp := abs_fourierPotential_sub_log_diagonalRadius_sub_cDiag_le
    (d := d) (e := e) (by simpa [R, d, e] using hR)
  have hidentity :
      planarPotentialKernel x - (2 / Real.pi) * Real.log (euclideanRadius x) -
          cPotential =
        fourierPotential d e - (2 / Real.pi) * Real.log (diagonalRadius d e) -
          cDiag := by
    rw [planarPotentialKernel_eq_diagonalPotential_of_even hx,
      diagonalPotential_eq_fourierPotential, hlog]
    unfold cPotential
    ring
  rw [hidentity]
  have hRadiusUpper : euclideanRadius x ≤ 2 * (R : ℝ) := by
    simpa [R, d, e] using euclideanRadius_le_two_mul_diagonalMax_of_even hx
  have hRpos : (0 : ℝ) < R := by
    exact_mod_cast (show 0 < R by dsimp [R, d, e]; omega)
  have hxne : x ≠ 0 := by
    intro hzero
    subst x
    simp [d, e, R, firstDiagonalOffset, secondDiagonalOffset] at hR
  have hrpos : 0 < euclideanRadius x := (euclideanRadius_pos_iff x).2 hxne
  calc
    |fourierPotential d e - (2 / Real.pi) * Real.log (diagonalRadius d e) -
        cDiag| ≤ 1611010000 / (R : ℝ) := by simpa [R] using hp
    _ ≤ 3222020000 / euclideanRadius x := by
      rw [div_le_div_iff₀ hRpos hrpos]
      nlinarith

/-- A lattice point embedded in the complex plane. -/
noncomputable def pointComplex (x : Point) : ℂ :=
  ⟨(x.1 : ℝ), (x.2 : ℝ)⟩

theorem euclideanRadius_eq_norm_pointComplex (x : Point) :
    euclideanRadius x = ‖pointComplex x‖ := by
  unfold euclideanRadius euclideanRadiusSq
  rw [Complex.norm_def]
  congr 1
  simp [pointComplex, Complex.normSq_apply]
  ring

private lemma pointComplex_sub (x y : Point) :
    pointComplex (x - y) = pointComplex x - pointComplex y := by
  apply Complex.ext <;> simp [pointComplex]

private lemma norm_pointComplex_directionVector (d : Direction) :
    ‖pointComplex (directionVector d)‖ = 1 := by
  fin_cases d <;> simp [pointComplex, directionVector, Complex.norm_def,
    Complex.normSq_apply]

/-- A nearest-neighbor step changes Euclidean radius by at most one. -/
theorem abs_euclideanRadius_sub_neighbor_le (x : Point) (d : Direction) :
    |euclideanRadius x - euclideanRadius (x - directionVector d)| ≤ 1 := by
  rw [euclideanRadius_eq_norm_pointComplex,
    euclideanRadius_eq_norm_pointComplex]
  calc
    |‖pointComplex x‖ - ‖pointComplex (x - directionVector d)‖| ≤
        ‖pointComplex x - pointComplex (x - directionVector d)‖ :=
      abs_norm_sub_norm_le _ _
    _ = ‖pointComplex (directionVector d)‖ := by
      rw [pointComplex_sub]
      abel
    _ = 1 := norm_pointComplex_directionVector d

private lemma abs_log_sub_log_le_two_div {r s : ℝ}
    (hr : 2 ≤ r) (hs : 0 < s) (hrs : |r - s| ≤ 1) :
    |Real.log s - Real.log r| ≤ 2 / r := by
  have hrpos : 0 < r := by linarith
  have hdiff₁ : s - r ≤ 1 := by linarith [(abs_le.mp hrs).1]
  have hdiff₂ : r - s ≤ 1 := (abs_le.mp hrs).2
  rcases le_total r s with hrs' | hsr
  · have hlog : Real.log r ≤ Real.log s := Real.log_le_log hrpos hrs'
    rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
    have hratio : 0 < s / r := div_pos hs hrpos
    calc
      Real.log s - Real.log r = Real.log (s / r) := by
        rw [Real.log_div hs.ne' hrpos.ne']
      _ ≤ s / r - 1 := Real.log_le_sub_one_of_pos hratio
      _ ≤ 1 / r := by
        apply (sub_le_iff_le_add).2
        rw [div_le_iff₀ hrpos]
        calc
          s ≤ r + 1 := by linarith
          _ = (1 / r + 1) * r := by field_simp <;> ring
      _ ≤ 2 / r := by gcongr <;> norm_num
  · have hslow : r / 2 ≤ s := by linarith
    have hlog : Real.log s ≤ Real.log r := Real.log_le_log hs hsr
    rw [abs_of_nonpos (sub_nonpos.mpr hlog), neg_sub]
    have hratio : 0 < r / s := div_pos hrpos hs
    calc
      Real.log r - Real.log s = Real.log (r / s) := by
        rw [Real.log_div hrpos.ne' hs.ne']
      _ ≤ r / s - 1 := Real.log_le_sub_one_of_pos hratio
      _ ≤ 1 / s := by
        apply (sub_le_iff_le_add).2
        rw [div_le_iff₀ hs]
        calc
          r ≤ s + 1 := by linarith
          _ = (1 / s + 1) * s := by field_simp <;> ring
      _ ≤ 2 / r := by
        rw [div_le_div_iff₀ hs hrpos]
        nlinarith

end PotentialRadialAsymptotic
end Erdos1165
