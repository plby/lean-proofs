/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.ExternalGreenRenewal

/-!
# A finite Tauberian estimate for the external walk

We apply the positive-coefficient Abel estimate from
`ExternalGreenRenewal` at

`D_N = (N + 2) log (N + 2)`,  `z_N = 1 - 1 / D_N`.

Bernoulli's inequality loses only `O(1 / log N)` in the multiplier of the
truncated Green sum.  Meanwhile the logarithmic singularity is
`log N + log log N + O(1)`.  The lemmas below absorb both errors into
`32 * (log (N + 2))^(3/5)`.  In particular, the leading coefficient remains
exactly `15 / (16 * pi)`.
-/

open Filter
open scoped Topology

namespace Erdos1165.ExternalGreenTauberian

open ExternalWalk ExternalGreenRenewal LazyDecomposition

/-- The logarithmic scale used in the finite Tauberian parameter. -/
noncomputable def abelLog (N : ℕ) : ℝ := Real.log ((N : ℝ) + 2)

/-- The denominator in `z_N = 1 - 1 / D_N`. -/
noncomputable def abelDenominator (N : ℕ) : ℝ :=
  ((N : ℝ) + 2) * abelLog N

/-- `log (N + 2)` tends to infinity. -/
lemma tendsto_abelLog : Tendsto abelLog atTop atTop := by
  have harg : Tendsto (fun N : ℕ ↦ (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono' atTop
      (Filter.Eventually.of_forall fun N ↦ by norm_num)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  exact Real.tendsto_log_atTop.comp harg

/-- The elementary quantitative estimate used to absorb `log log N` into
the chosen `3/5`-power error. -/
lemma log_le_five_thirds_mul_rpow_three_fifths {L : ℝ} (hL : 0 ≤ L) :
    Real.log L ≤ (5 / 3 : ℝ) * L ^ (3 / 5 : ℝ) := by
  have h := Real.log_le_rpow_div hL (by norm_num : (0 : ℝ) < 3 / 5)
  calc
    Real.log L ≤ L ^ (3 / 5 : ℝ) / (3 / 5 : ℝ) := h
    _ = (5 / 3 : ℝ) * L ^ (3 / 5 : ℝ) := by ring

/-- The logarithmic factor in the explicit Green bound has leading term
`L / pi`; the `log L` term is absorbed by `L^(3/5)`. -/
lemma logarithmic_factor_le {N : ℕ} {L D : ℝ}
    (hL : 2 ≤ L) (hlogN : Real.log ((N : ℝ) + 2) = L)
    (hD : D = ((N : ℝ) + 2) * L) :
    1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9 ≤
      L / Real.pi + 5 * L ^ (3 / 5 : ℝ) := by
  let P : ℝ := L ^ (3 / 5 : ℝ)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLone : 1 ≤ L := by linarith
  have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by norm_num
  have hDfour : 4 ≤ D := by rw [hD]; nlinarith
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hDfour
  have hdenpos : 0 < 16 * D - 1 := by nlinarith
  have hPnonneg : 0 ≤ P := Real.rpow_nonneg hLpos.le _
  have hPone : 1 ≤ P := by
    dsimp [P]
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hLone
        (by norm_num : (0 : ℝ) ≤ 3 / 5)
  have hargpos : 0 < (16 * D - 1) / 15 := div_pos hdenpos (by norm_num)
  have hargle : (16 * D - 1) / 15 ≤ 2 * D := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 15)]
    nlinarith
  have hlogTwo : Real.log (2 : ℝ) ≤ 1 := by
    calc
      Real.log (2 : ℝ) ≤ 2 - 1 :=
        Real.log_le_sub_one_of_pos (by norm_num)
      _ = 1 := by norm_num
  have hlogD : Real.log D = L + Real.log L := by
    rw [hD, Real.log_mul (by positivity) hLpos.ne', hlogN]
  have hlogarg : Real.log ((16 * D - 1) / 15) ≤
      L + Real.log L + 1 := by
    calc
      Real.log ((16 * D - 1) / 15) ≤ Real.log (2 * D) :=
        Real.log_le_log hargpos hargle
      _ = Real.log 2 + Real.log D := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hDpos.ne']
      _ = Real.log 2 + (L + Real.log L) := by rw [hlogD]
      _ ≤ L + Real.log L + 1 := by linarith
  have hlogLnonneg : 0 ≤ Real.log L := Real.log_nonneg hLone
  have hlogLpow : Real.log L ≤ (5 / 3 : ℝ) * P := by
    simpa only [P] using log_le_five_thirds_mul_rpow_three_fifths hLpos.le
  have hpiOne : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hpiPos : 0 < Real.pi := Real.pi_pos
  have hdiv := div_le_div_of_nonneg_right hlogarg hpiPos.le
  have hrestdiv : (Real.log L + 1) / Real.pi ≤ Real.log L + 1 :=
    div_le_self (by linarith) hpiOne
  have hpifrac : Real.pi / 9 ≤ 1 := by linarith [Real.pi_le_four]
  change 1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9 ≤
    L / Real.pi + 5 * P
  calc
    1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9 ≤
        1 + (L + Real.log L + 1) / Real.pi + Real.pi / 9 := by
          linarith
    _ = L / Real.pi +
        (1 + (Real.log L + 1) / Real.pi + Real.pi / 9) := by ring
    _ ≤ L / Real.pi + (Real.log L + 3) := by linarith
    _ ≤ L / Real.pi + 5 * P := by nlinarith

/-- The rational prefactor differs from `15/16` by at most `1/D`. -/
lemma green_prefactor_le {D : ℝ} (hD : 1 ≤ D) :
    15 * D / (16 * D - 1) ≤ 15 / 16 + 1 / D := by
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hdenpos : 0 < 16 * D - 1 := by nlinarith
  have haux : 16 * D / (16 * D - 1) = 1 + 1 / (16 * D - 1) := by
    rw [div_eq_iff hdenpos.ne']
    calc
      16 * D = (16 * D - 1) + 1 := by ring
      _ = (1 + 1 / (16 * D - 1)) * (16 * D - 1) := by
        field_simp [hdenpos.ne']
  have heq : 15 * D / (16 * D - 1) =
      15 / 16 + (15 / 16) * (1 / (16 * D - 1)) := by
    calc
      15 * D / (16 * D - 1) =
          (15 / 16) * (16 * D / (16 * D - 1)) := by ring
      _ = (15 / 16) * (1 + 1 / (16 * D - 1)) := by rw [haux]
      _ = 15 / 16 + (15 / 16) * (1 / (16 * D - 1)) := by ring
  have hinvnonneg : 0 ≤ 1 / (16 * D - 1) := by positivity
  have hfirst : (15 / 16) * (1 / (16 * D - 1)) ≤
      1 / (16 * D - 1) := by nlinarith
  have hsecond : 1 / (16 * D - 1) ≤ 1 / D := by
    rw [div_le_div_iff₀ hdenpos hDpos]
    nlinarith
  rw [heq]
  linarith

/-- The complete right-hand side of the finite Abel bound, before removing
the multiplier on the truncated Green sum. -/
lemma finite_abel_rhs_le {N : ℕ} {L D : ℝ}
    (hL : 2 ≤ L) (hlogN : Real.log ((N : ℝ) + 2) = L)
    (hD : D = ((N : ℝ) + 2) * L) :
    (15 * D / (16 * D - 1)) *
        (1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9) ≤
      (15 / (16 * Real.pi)) * L + 9 * L ^ (3 / 5 : ℝ) := by
  let P : ℝ := L ^ (3 / 5 : ℝ)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by norm_num
  have hDfour : 4 ≤ D := by rw [hD]; nlinarith
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hDfour
  have hDone : 1 ≤ D := by linarith
  have hPnonneg : 0 ≤ P := Real.rpow_nonneg hLpos.le _
  have hPone : 1 ≤ P := by
    dsimp [P]
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ L)
        (by norm_num : (0 : ℝ) ≤ 3 / 5)
  have hB := logarithmic_factor_le hL hlogN hD
  have hBnonneg : 0 ≤
      1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9 := by
    have harg : 1 ≤ (16 * D - 1) / 15 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 15)]
      nlinarith
    have hlog : 0 ≤ Real.log ((16 * D - 1) / 15) := Real.log_nonneg harg
    exact add_nonneg
      (add_nonneg zero_le_one (div_nonneg hlog Real.pi_pos.le))
      (div_nonneg Real.pi_pos.le (by norm_num))
  have hQ := green_prefactor_le hDone
  have hQupperNonneg : 0 ≤ (15 / 16 : ℝ) + 1 / D := by positivity
  have hLDpi : L / (D * Real.pi) ≤ P := by
    rw [div_le_iff₀ (mul_pos hDpos Real.pi_pos)]
    have hLP : L ≤ P * D := by
      nlinarith [mul_le_mul_of_nonneg_left hPone hDpos.le]
    have hDpi : D ≤ D * Real.pi := by
      have hpiOne : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hpiOne hDpos.le
    exact hLP.trans (mul_le_mul_of_nonneg_left hDpi hPnonneg)
  have hPD : 5 * P / D ≤ 2 * P := by
    rw [div_le_iff₀ hDpos]
    have hfourP : 4 * P ≤ D * P :=
      mul_le_mul_of_nonneg_right hDfour hPnonneg
    nlinarith
  change (15 * D / (16 * D - 1)) *
        (1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9) ≤
      (15 / (16 * Real.pi)) * L + 9 * P
  calc
    (15 * D / (16 * D - 1)) *
        (1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9) ≤
        (15 / 16 + 1 / D) *
          (1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9) :=
      mul_le_mul_of_nonneg_right hQ hBnonneg
    _ ≤ (15 / 16 + 1 / D) * (L / Real.pi + 5 * P) :=
      mul_le_mul_of_nonneg_left hB hQupperNonneg
    _ = (15 / (16 * Real.pi)) * L + (75 / 16) * P +
        L / (D * Real.pi) + 5 * P / D := by ring
    _ ≤ (15 / (16 * Real.pi)) * L + 9 * P := by nlinarith

/-- Removing the Bernoulli multiplier costs only another constant multiple of
`L^(3/5)`. -/
lemma remove_abel_multiplier {N : ℕ} {L D G R : ℝ}
    (hL : 2 ≤ L) (hD : D = ((N : ℝ) + 2) * L) (hG : 0 ≤ G)
    (hfinite : (1 - (N : ℝ) / D) * G ≤ R) (hRnonneg : 0 ≤ R)
    (hR : R ≤ (15 / (16 * Real.pi)) * L + 9 * L ^ (3 / 5 : ℝ)) :
    G ≤ (15 / (16 * Real.pi)) * L + 32 * L ^ (3 / 5 : ℝ) := by
  let P : ℝ := L ^ (3 / 5 : ℝ)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hLone : 1 ≤ L := by linarith
  have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by norm_num
  have hDfour : 4 ≤ D := by rw [hD]; nlinarith
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hDfour
  have hPnonneg : 0 ≤ P := Real.rpow_nonneg hLpos.le _
  have hPone : 1 ≤ P := by
    dsimp [P]
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hLone
        (by norm_num : (0 : ℝ) ≤ 3 / 5)
  have hratio : (N : ℝ) / D ≤ 1 / L := by
    rw [div_le_div_iff₀ hDpos hLpos, hD]
    simp only [one_mul]
    calc
      (N : ℝ) * L ≤ (N : ℝ) * L + 2 * L :=
        le_add_of_nonneg_right (mul_nonneg (by norm_num) hLpos.le)
      _ = ((N : ℝ) + 2) * L := by ring
  have hbasepos : 0 < 1 - 1 / L := by
    rw [sub_pos, div_lt_one hLpos]
    linarith
  have hleft : (1 - 1 / L) * G ≤ R := by
    calc
      (1 - 1 / L) * G ≤ (1 - (N : ℝ) / D) * G :=
        mul_le_mul_of_nonneg_right (by linarith) hG
      _ ≤ R := hfinite
  have hGdiv : G ≤ R / (1 - 1 / L) := by
    rw [le_div_iff₀ hbasepos]
    simpa [mul_comm] using hleft
  have hinv : 1 / (1 - 1 / L) ≤ 1 + 2 / L := by
    rw [div_le_iff₀ hbasepos]
    have htwoDiv : 2 / L ≤ 1 := (div_le_one hLpos).2 hL
    have hproduct : 0 ≤ (1 / L) * (1 - 2 / L) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr htwoDiv)
    calc
      1 ≤ 1 + (1 / L) * (1 - 2 / L) := le_add_of_nonneg_right hproduct
      _ = (1 + 2 / L) * (1 - 1 / L) := by ring
  have hfactorNonneg : 0 ≤ 1 + 2 / L := by positivity
  have hGfactor : G ≤ (1 + 2 / L) * R := by
    calc
      G ≤ R / (1 - 1 / L) := hGdiv
      _ = (1 / (1 - 1 / L)) * R := by ring
      _ ≤ (1 + 2 / L) * R := mul_le_mul_of_nonneg_right hinv hRnonneg
  have hpiOne : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hcOne : (15 / (16 * Real.pi) : ℝ) ≤ 1 := by
    rw [div_le_one (mul_pos (by norm_num) Real.pi_pos)]
    calc
      (15 : ℝ) ≤ 16 := by norm_num
      _ ≤ 16 * Real.pi :=
        by simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hpiOne (by norm_num : (0 : ℝ) ≤ 16)
  have hPL : P / L ≤ P := div_le_self hPnonneg hLone
  have hcancelL : (2 / L) * ((15 / (16 * Real.pi)) * L) =
      2 * (15 / (16 * Real.pi)) := by
    calc
      (2 / L) * ((15 / (16 * Real.pi)) * L) =
          2 * (15 / (16 * Real.pi)) * (L / L) := by ring
      _ = 2 * (15 / (16 * Real.pi)) := by rw [div_self hLpos.ne', mul_one]
  change G ≤ (15 / (16 * Real.pi)) * L + 32 * P
  have hR' : R ≤ (15 / (16 * Real.pi)) * L + 9 * P := hR
  calc
    G ≤ (1 + 2 / L) * R := hGfactor
    _ ≤ (1 + 2 / L) * ((15 / (16 * Real.pi)) * L + 9 * P) :=
      mul_le_mul_of_nonneg_left hR' hfactorNonneg
    _ = (15 / (16 * Real.pi)) * L + 9 * P +
        2 * (15 / (16 * Real.pi)) + 18 * (P / L) := by
      rw [mul_add, add_mul, one_mul, hcancelL]
      ring
    _ ≤ (15 / (16 * Real.pi)) * L + 32 * P := by nlinarith

/-- A pointwise finite Tauberian bound at the parameter
`D = (N+2) log (N+2)`. -/
lemma externalTruncatedGreenCount_le_of_two_le_log (o : Orientation) (N : ℕ)
    (hlog : 2 ≤ Real.log ((N : ℝ) + 2)) :
    externalTruncatedGreenCount o N ≤
      (15 / (16 * Real.pi)) * Real.log ((N : ℝ) + 2) +
        32 * Real.log ((N : ℝ) + 2) ^ (3 / 5 : ℝ) := by
  let L : ℝ := Real.log ((N : ℝ) + 2)
  let D : ℝ := ((N : ℝ) + 2) * L
  let R : ℝ := (15 * D / (16 * D - 1)) *
    (1 + Real.log ((16 * D - 1) / 15) / Real.pi + Real.pi / 9)
  have hL : 2 ≤ L := hlog
  have hD : D = ((N : ℝ) + 2) * L := rfl
  have hDfour : 4 ≤ D := by
    have hN2 : (2 : ℝ) ≤ (N : ℝ) + 2 := by norm_num
    rw [hD]
    nlinarith
  have hDone : 1 ≤ D := by linarith
  have hfinite :=
    one_sub_nat_div_mul_externalTruncatedGreenCount_le_log_D o N D hDone
  change (1 - (N : ℝ) / D) * externalTruncatedGreenCount o N ≤ R at hfinite
  have hR := finite_abel_rhs_le hL (show Real.log ((N : ℝ) + 2) = L from rfl) hD
  change R ≤ (15 / (16 * Real.pi)) * L + 9 * L ^ (3 / 5 : ℝ) at hR
  have hRnonneg : 0 ≤ R := by
    have hdenpos : 0 < 16 * D - 1 := by nlinarith
    have harg : 1 ≤ (16 * D - 1) / 15 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 15)]
      nlinarith
    have hlognonneg : 0 ≤ Real.log ((16 * D - 1) / 15) :=
      Real.log_nonneg harg
    dsimp [R]
    exact mul_nonneg
      (div_nonneg (mul_nonneg (by norm_num) (by linarith)) hdenpos.le)
      (add_nonneg
        (add_nonneg zero_le_one (div_nonneg hlognonneg Real.pi_pos.le))
        (div_nonneg Real.pi_pos.le (by norm_num)))
  exact remove_abel_multiplier hL hD
    (externalTruncatedGreenCount_nonneg o N) hfinite hRnonneg hR

/-- Sharp-leading truncated Green upper bound for the actual external walk.
The error is explicit and sublinear. -/
theorem eventually_externalTruncatedGreenCount_le (o : Orientation) :
    ∀ᶠ N : ℕ in atTop,
      externalTruncatedGreenCount o N ≤
        (15 / (16 * Real.pi)) * Real.log ((N : ℝ) + 2) +
          32 * Real.log ((N : ℝ) + 2) ^ (3 / 5 : ℝ) := by
  have hlarge : ∀ᶠ N : ℕ in atTop, 2 ≤ abelLog N :=
    tendsto_abelLog.eventually (eventually_ge_atTop 2)
  filter_upwards [hlarge] with N hN
  exact externalTruncatedGreenCount_le_of_two_le_log o N hN

/-- The same sharp-leading estimate for the renewal module's real truncated
Green function. -/
theorem eventually_externalTruncatedGreenReal_le (o : Orientation) :
    ∀ᶠ N : ℕ in atTop,
      ExternalRenewal.externalTruncatedGreenReal o N ≤
        (15 / (16 * Real.pi)) * Real.log ((N : ℝ) + 2) +
          32 * Real.log ((N : ℝ) + 2) ^ (3 / 5 : ℝ) := by
  filter_upwards [eventually_externalTruncatedGreenCount_le o] with N hN
  rw [← externalTruncatedGreenCount_eq_renewal]
  exact hN

end Erdos1165.ExternalGreenTauberian
