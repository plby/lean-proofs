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

/-!
# Sharp radial asymptotic for the planar potential kernel

The Fourier potential at diagonal coordinates `(d,e)` is compared with the
axis point `(⌊√(d²+e²)⌋,0)`.  The local central limit theorem makes the
comparison error uniform in the angle, while the exact axis formula supplies
the additive constant.  We then transport the result to ordinary Euclidean
coordinates and both parity classes of the planar lattice.
-/

open Real

namespace Erdos1165
namespace PotentialRadial

open PotentialAxis PotentialFourierIntegral PotentialRadialMass
  PotentialEuclideanGeometry

private lemma one_div_pi_le_one : (1 : ℝ) / Real.pi ≤ 1 := by
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpi

/-- The integer axis radius associated with diagonal coordinates. -/
def axisRadius (d e : ℕ) : ℕ := Nat.sqrt (radiusSq d e)

lemma max_sq_le_radiusSq (d e : ℕ) : (max d e) ^ 2 ≤ radiusSq d e := by
  unfold radiusSq
  rcases max_cases d e with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
    exact Nat.le_add_right _ _
  · rw [h]
    exact Nat.le_add_left _ _

lemma radiusSq_le_two_mul_max_sq (d e : ℕ) :
    radiusSq d e ≤ 2 * (max d e) ^ 2 := by
  unfold radiusSq
  have hd : d ≤ max d e := le_max_left _ _
  have he : e ≤ max d e := le_max_right _ _
  nlinarith [Nat.pow_le_pow_left hd 2, Nat.pow_le_pow_left he 2]

lemma max_le_axisRadius (d e : ℕ) : max d e ≤ axisRadius d e := by
  rw [axisRadius, Nat.le_sqrt]
  simpa [pow_two] using max_sq_le_radiusSq d e

lemma axisRadius_le_two_mul_max (d e : ℕ) :
    axisRadius d e ≤ 2 * max d e := by
  have hQ := radiusSq_le_two_mul_max_sq d e
  calc
    axisRadius d e ≤ Nat.sqrt ((2 * max d e) ^ 2) := by
      unfold axisRadius
      apply Nat.sqrt_le_sqrt
      nlinarith
    _ = 2 * max d e := Nat.sqrt_eq' _

lemma radiusSq_sub_axisRadius_sq_le (d e : ℕ) :
    radiusSq d e - (axisRadius d e) ^ 2 ≤ 5 * max d e := by
  have hlo : (axisRadius d e) ^ 2 ≤ radiusSq d e := by
    exact Nat.sqrt_le' _
  have hhi : radiusSq d e < (axisRadius d e + 1) ^ 2 := by
    simpa [axisRadius] using Nat.lt_succ_sqrt' (radiusSq d e)
  have hs := axisRadius_le_two_mul_max d e
  have hsquare : (axisRadius d e + 1) ^ 2 =
      (axisRadius d e) ^ 2 + 2 * axisRadius d e + 1 := by ring
  rw [hsquare] at hhi
  omega

private lemma abs_natCast_radius_gap_le (d e : ℕ) :
    |(radiusSq d e : ℝ) - ((axisRadius d e) ^ 2 : ℕ)| ≤
      (5 : ℝ) * max d e := by
  have hlo : (axisRadius d e) ^ 2 ≤ radiusSq d e := Nat.sqrt_le' _
  have hloR : (((axisRadius d e) ^ 2 : ℕ) : ℝ) ≤ radiusSq d e := by
    exact_mod_cast hlo
  rw [abs_of_nonneg (sub_nonneg.mpr hloR)]
  rw [← Nat.cast_sub hlo]
  exact_mod_cast radiusSq_sub_axisRadius_sq_le d e

/-- The logarithm of the integer axis radius differs from the logarithm of
the true diagonal squared radius by `O(1/rho)`. -/
private lemma abs_two_log_axisRadius_sub_log_radiusSq_le
    {d e ρ : ℕ} (hρ : 1 ≤ ρ) (hρmax : ρ ≤ max d e)
    (hmaxρ : max d e ≤ ρ) :
    |2 * Real.log (axisRadius d e) - Real.log (radiusSq d e)| ≤
      5 / (ρ : ℝ) := by
  let s := axisRadius d e
  let Q := radiusSq d e
  have hsNat : ρ ≤ s := hρmax.trans (max_le_axisRadius d e)
  have hsPos : 0 < s := lt_of_lt_of_le (by omega : 0 < ρ) hsNat
  have hsqNat : s ^ 2 ≤ Q := by
    simpa only [pow_two, s, Q, axisRadius] using
      Nat.sqrt_le (radiusSq d e)
  have hQPos : 0 < Q := lt_of_lt_of_le (Nat.pow_pos hsPos) hsqNat
  have hgapNat : Q - s ^ 2 ≤ 5 * max d e := by
    simpa [s, Q] using radiusSq_sub_axisRadius_sq_le d e
  have hgap : (Q : ℝ) - (s : ℝ) ^ 2 ≤ 5 * ρ := by
    have hmaxρR : (max d e : ℝ) ≤ ρ := by exact_mod_cast hmaxρ
    calc
      (Q : ℝ) - (s : ℝ) ^ 2 = ((Q - s ^ 2 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hsqNat, Nat.cast_pow]
      _ ≤ (5 * max d e : ℕ) := by exact_mod_cast hgapNat
      _ = 5 * (max d e : ℝ) := by norm_num
      _ ≤ 5 * ρ := by gcongr
  have hsR : (0 : ℝ) < s := by exact_mod_cast hsPos
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQPos
  have hρR : (0 : ℝ) < ρ := by positivity
  have hsρR : (ρ : ℝ) ≤ s := by exact_mod_cast hsNat
  have hsqR : (s : ℝ) ^ 2 ≤ Q := by exact_mod_cast hsqNat
  have hlogle : Real.log ((s : ℝ) ^ 2) ≤ Real.log Q :=
    Real.strictMonoOn_log.monotoneOn
      (by simp only [Set.mem_Ioi]; positivity)
      (by simp only [Set.mem_Ioi]; positivity) hsqR
  have hfrac : (Q : ℝ) / (s : ℝ) ^ 2 - 1 ≤ 5 / (ρ : ℝ) := by
    apply (le_div_iff₀ hρR).2
    rw [div_eq_mul_inv]
    field_simp [ne_of_gt hsR]
    nlinarith [sq_nonneg ((s : ℝ) - ρ)]
  have hloggap : Real.log Q - Real.log ((s : ℝ) ^ 2) ≤ 5 / (ρ : ℝ) := by
    calc
      Real.log Q - Real.log ((s : ℝ) ^ 2) =
          Real.log ((Q : ℝ) / (s : ℝ) ^ 2) := by
            rw [Real.log_div (ne_of_gt hQR) (by positivity)]
      _ ≤ (Q : ℝ) / (s : ℝ) ^ 2 - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hQR (sq_pos_of_pos hsR))
      _ ≤ 5 / (ρ : ℝ) := hfrac
  rw [show 2 * Real.log (axisRadius d e) =
      Real.log ((s : ℝ) ^ 2) by
        dsimp [s]
        rw [Real.log_pow]
        norm_num]
  rw [abs_of_nonpos (sub_nonpos.mpr hlogle)]
  linarith

/-- Uniform radial expansion in the independent diagonal coordinates. -/
theorem abs_fourierPotential_sub_log_radiusSq_sub_cDiag_le
    {d e : ℕ} (hmax : 2 ≤ max d e) :
    |fourierPotential d e - (1 / Real.pi) * Real.log (radiusSq d e) - cDiag| ≤
      1611010000 / (max d e : ℝ) := by
  let ρ := max d e
  let s := axisRadius d e
  have hρ : 2 ≤ ρ := hmax
  have hd : d ≤ 2 * ρ := (le_max_left _ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  have he : e ≤ 2 * ρ := (le_max_right _ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  have hsρ : ρ ≤ s := by simpa [ρ, s] using max_le_axisRadius d e
  have hsUpper : s ≤ 2 * ρ := by simpa [ρ, s] using axisRadius_le_two_mul_max d e
  have hsPos : 0 < s := lt_of_lt_of_le (by omega : 0 < ρ) hsρ
  have hshell := abs_fourierPotential_sub_le_of_radiusSq_gap
    (d := d) (e := e) (d' := s) (e' := 0) (ρ := ρ) (L := 5)
    hρ hd he hsUpper (by omega) (by simp [ρ]) (by simpa using hsρ)
    (by simpa [ρ, s, radiusSq, pow_two] using abs_natCast_radius_gap_le d e)
  have haxis := abs_fourierPotential_axis_sub_log_sub_cDiag_le hsPos
  have hlog := abs_two_log_axisRadius_sub_log_radiusSq_le
    (d := d) (e := e) (ρ := ρ) (by omega) (by simp [ρ]) (by simp [ρ])
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlogScaled :
      |(2 / Real.pi) * Real.log s -
          (1 / Real.pi) * Real.log (radiusSq d e)| ≤ 5 / (ρ : ℝ) := by
    calc
      |(2 / Real.pi) * Real.log s -
          (1 / Real.pi) * Real.log (radiusSq d e)| =
          |(1 / Real.pi) *
            (2 * Real.log s - Real.log (radiusSq d e))| := by
              congr 1
              ring
      _ = (1 / Real.pi) *
            |2 * Real.log s - Real.log (radiusSq d e)| := by
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.pi)]
      _ ≤ 1 * (5 / (ρ : ℝ)) := by
        gcongr
        exact one_div_pi_le_one
      _ = 5 / (ρ : ℝ) := by ring
  have hfinal :
      |fourierPotential d e - (1 / Real.pi) * Real.log (radiusSq d e) - cDiag| ≤
        1611010000 / (ρ : ℝ) := by
    calc
      |fourierPotential d e - (1 / Real.pi) * Real.log (radiusSq d e) - cDiag| ≤
          |fourierPotential d e - fourierPotential s 0| +
            |fourierPotential s 0 - (2 / Real.pi) * Real.log s - cDiag| +
            |(2 / Real.pi) * Real.log s -
              (1 / Real.pi) * Real.log (radiusSq d e)| := by
        calc
          _ = |(fourierPotential d e - fourierPotential s 0) +
              ((fourierPotential s 0 - (2 / Real.pi) * Real.log s - cDiag) +
                ((2 / Real.pi) * Real.log s -
                  (1 / Real.pi) * Real.log (radiusSq d e)))| := by
                    apply congrArg abs
                    ring
          _ ≤ |fourierPotential d e - fourierPotential s 0| +
              |(fourierPotential s 0 - (2 / Real.pi) * Real.log s - cDiag) +
                ((2 / Real.pi) * Real.log s -
                  (1 / Real.pi) * Real.log (radiusSq d e))| := abs_add_le _ _
          _ ≤ |fourierPotential d e - fourierPotential s 0| +
              (|fourierPotential s 0 - (2 / Real.pi) * Real.log s - cDiag| +
                |(2 / Real.pi) * Real.log s -
                  (1 / Real.pi) * Real.log (radiusSq d e)|) :=
            add_le_add le_rfl (abs_add_le _ _)
          _ = _ := by ring
      _ ≤ (1611000000 + 1000 * (5 : ℝ)) / (ρ : ℝ) +
            4 / (Real.pi * s) + 5 / (ρ : ℝ) :=
        add_le_add (add_le_add hshell haxis) hlogScaled
      _ ≤ 1611010000 / (ρ : ℝ) := by
        have hρR : (0 : ℝ) < ρ := by positivity
        have hsR : (ρ : ℝ) ≤ s := by exact_mod_cast hsρ
        have hsRpos : (0 : ℝ) < s := by exact_mod_cast hsPos
        have haxisDen : 4 / (Real.pi * (s : ℝ)) ≤ 2 / (ρ : ℝ) := by
          have hden : (2 : ℝ) * ρ ≤ Real.pi * s := by
            nlinarith [Real.two_le_pi]
          exact (div_le_div_iff₀ (mul_pos hpi hsRpos) hρR).2 (by nlinarith)
        calc
          (1611000000 + 1000 * (5 : ℝ)) / (ρ : ℝ) +
                4 / (Real.pi * s) + 5 / (ρ : ℝ) ≤
              (1611005000 : ℝ) / ρ + 2 / ρ + 5 / ρ := by
                norm_num
                exact haxisDen
          _ ≤ 1611010000 / (ρ : ℝ) := by
            field_simp
            norm_num
  simpa only [ρ, Nat.cast_max] using hfinal

end PotentialRadial
end Erdos1165
