/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos360.LowerAssembly
import ErdosProblems.Erdos360.TotientStep

/-!
# Numerical diagonal estimates for the public lower-bound assembly

This file discharges the three real inequalities grouped in
`CFPDiagonalNumericBounds`.  The proof is deliberately separated from the
finite CFP theorem: it uses only the definition of `resolutionScale`, the
floor bounds for `lowerColorCount`, and the uniform maximal-order bound for
`n / φ(n)`.
-/

namespace Erdos360

open Filter
open scoped Topology

lemma resolutionScale_mul_totient_eq
    {n : ℕ} (hn : 0 < n) :
    resolutionScale n * (Nat.totient n : ℝ) =
      Real.rpow (n : ℝ) (4 / 3 : ℝ) /
        (Real.rpow (Real.log (n : ℝ)) (1 / 3 : ℝ) *
          Real.rpow (Real.log (Real.log (n : ℝ))) (2 / 3 : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hphi : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast (Nat.totient_pos.mpr hn)
  have hpow :
      Real.rpow (n : ℝ) (4 / 3 : ℝ) =
        Real.rpow (n : ℝ) (1 / 3 : ℝ) * (n : ℝ) := by
    calc
      Real.rpow (n : ℝ) (4 / 3 : ℝ) =
          Real.rpow (n : ℝ) ((1 / 3 : ℝ) + 1) := by norm_num
      _ = Real.rpow (n : ℝ) (1 / 3 : ℝ) *
          Real.rpow (n : ℝ) 1 := Real.rpow_add hnR _ _
      _ = Real.rpow (n : ℝ) (1 / 3 : ℝ) * (n : ℝ) := by
        congr 1
        exact Real.rpow_one (n : ℝ)
  rw [resolutionScale, hpow]
  field_simp [hphi.ne']

private lemma resolutionScale_cube_cross
    {n : ℕ} (hn : 0 < n)
    (hL : 0 < Real.log (n : ℝ))
    (hLL : 0 < Real.log (Real.log (n : ℝ))) :
    Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) ^ 2 *
        resolutionScale n ^ 3 =
      (Nat.totient n : ℝ) *
        ((n : ℝ) / Nat.totient n) ^ 4 := by
  have hphi : (0 : ℝ) < Nat.totient n := by
    exact_mod_cast (Nat.totient_pos.mpr hn)
  have hscale : 0 < resolutionScale n := by
    rw [resolutionScale]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hn) _)
        (div_pos (by exact_mod_cast hn) hphi))
      (mul_pos (Real.rpow_pos_of_pos hL _)
        (Real.rpow_pos_of_pos hLL _))
  have hid := resolutionScale_mainTerm_identity hn hL hLL
  have hden : 0 < Real.log (n : ℝ) *
      Real.log (Real.log (n : ℝ)) ^ 2 * resolutionScale n ^ 2 := by
    positivity
  have hcross :
      (n : ℝ) * ((n : ℝ) / Nat.totient n) ^ 3 =
        resolutionScale n *
          (Real.log (n : ℝ) *
            Real.log (Real.log (n : ℝ)) ^ 2 *
              resolutionScale n ^ 2) :=
    (div_eq_iff hden.ne').mp hid
  have hnratio : (n : ℝ) =
      (Nat.totient n : ℝ) * ((n : ℝ) / Nat.totient n) := by
    field_simp [hphi.ne']
  have hnratioPow :
      (n : ℝ) * ((n : ℝ) / Nat.totient n) ^ 3 =
        (Nat.totient n : ℝ) *
          ((n : ℝ) / Nat.totient n) ^ 4 := by
    field_simp [hphi.ne']
  calc
    Real.log (n : ℝ) * Real.log (Real.log (n : ℝ)) ^ 2 *
        resolutionScale n ^ 3 =
        resolutionScale n *
          (Real.log (n : ℝ) *
            Real.log (Real.log (n : ℝ)) ^ 2 *
              resolutionScale n ^ 2) := by ring
    _ = (n : ℝ) * ((n : ℝ) / Nat.totient n) ^ 3 := hcross.symm
    _ = (Nat.totient n : ℝ) *
        ((n : ℝ) / Nat.totient n) ^ 4 := hnratioPow

private lemma loglog_sq_le_sixteen_mul_sqrt_log
    {n : ℕ} (hL : 1 ≤ Real.log (n : ℝ)) :
    Real.log (Real.log (n : ℝ)) ^ 2 ≤
      16 * Real.rpow (Real.log (n : ℝ)) (1 / 2 : ℝ) := by
  have hLpos : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hL
  have hlogBound := Real.log_le_rpow_div hLpos.le
    (show (0 : ℝ) < 1 / 4 by norm_num)
  have hsqrtNonneg : 0 ≤
      Real.rpow (Real.log (n : ℝ)) (1 / 2 : ℝ) :=
    Real.rpow_nonneg hLpos.le _
  have hquarterNonneg : 0 ≤
      Real.rpow (Real.log (n : ℝ)) (1 / 4 : ℝ) :=
    Real.rpow_nonneg hLpos.le _
  have hpow :
      (Real.rpow (Real.log (n : ℝ)) (1 / 4 : ℝ)) ^ 2 =
        Real.rpow (Real.log (n : ℝ)) (1 / 2 : ℝ) := by
    calc
      (Real.rpow (Real.log (n : ℝ)) (1 / 4 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow (Real.log (n : ℝ)) (1 / 4 : ℝ))
            (2 : ℝ) := (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (Real.log (n : ℝ)) ((1 / 4 : ℝ) * 2) :=
        (Real.rpow_mul hLpos.le _ _).symm
      _ = Real.rpow (Real.log (n : ℝ)) (1 / 2 : ℝ) := by norm_num
  have hlogNonneg : 0 ≤ Real.log (Real.log (n : ℝ)) := by
    exact Real.log_nonneg (by
      exact hL)
  have hsquare := pow_le_pow_left₀ hlogNonneg hlogBound 2
  calc
    Real.log (Real.log (n : ℝ)) ^ 2 ≤
        (Real.rpow (Real.log (n : ℝ)) (1 / 4 : ℝ) /
          (1 / 4 : ℝ)) ^ 2 := hsquare
    _ = 16 * Real.rpow (Real.log (n : ℝ)) (1 / 2 : ℝ) := by
      rw [div_pow, hpow]
      ring

lemma resolutionScale_mul_totient_bounds
    {n : ℕ} (hn : 0 < n)
    (hL : 1 ≤ Real.log (n : ℝ))
    (hLL : 1 ≤ Real.log (Real.log (n : ℝ))) :
    Real.rpow (n : ℝ) (4 / 3 : ℝ) / Real.log (n : ℝ) ≤
        resolutionScale n * (Nat.totient n : ℝ) ∧
      resolutionScale n * (Nat.totient n : ℝ) ≤
        Real.rpow (n : ℝ) (4 / 3 : ℝ) := by
  let L : ℝ := Real.log (n : ℝ)
  let LL : ℝ := Real.log L
  let D : ℝ := Real.rpow L (1 / 3 : ℝ) *
    Real.rpow LL (2 / 3 : ℝ)
  have hLpos : 0 < L := by simpa [L] using zero_lt_one.trans_le hL
  have hLLpos : 0 < LL := by simpa [LL, L] using zero_lt_one.trans_le hLL
  have hLLleL : LL ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    dsimp [LL]
    linarith
  have hDpos : 0 < D := by
    dsimp [D]
    exact mul_pos (Real.rpow_pos_of_pos hLpos _)
      (Real.rpow_pos_of_pos hLLpos _)
  have hDone : 1 ≤ D := by
    dsimp [D]
    have hLpow := Real.one_le_rpow (show 1 ≤ L by simpa [L] using hL)
      (show (0 : ℝ) ≤ 1 / 3 by norm_num)
    have hLLpow := Real.one_le_rpow
      (show 1 ≤ LL by simpa [LL, L] using hLL)
      (show (0 : ℝ) ≤ 2 / 3 by norm_num)
    nlinarith
  have hDle : D ≤ L := by
    have h23 : Real.rpow LL (2 / 3 : ℝ) ≤
        Real.rpow L (2 / 3 : ℝ) :=
      Real.rpow_le_rpow hLLpos.le hLLleL (by norm_num)
    calc
      D ≤ Real.rpow L (1 / 3 : ℝ) *
          Real.rpow L (2 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_left h23 (Real.rpow_nonneg hLpos.le _)
      _ = Real.rpow L ((1 / 3 : ℝ) + (2 / 3 : ℝ)) :=
        (Real.rpow_add hLpos _ _).symm
      _ = L := by norm_num
  have heq := resolutionScale_mul_totient_eq hn
  change resolutionScale n * (Nat.totient n : ℝ) =
      Real.rpow (n : ℝ) (4 / 3 : ℝ) / D at heq
  rw [heq]
  have hNpow : 0 ≤ Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  constructor
  · change Real.rpow (n : ℝ) (4 / 3 : ℝ) / L ≤
      Real.rpow (n : ℝ) (4 / 3 : ℝ) / D
    exact div_le_div_of_nonneg_left hNpow hDpos hDle
  · exact (div_le_iff₀ hDpos).2 (by
      nlinarith [mul_le_mul_of_nonneg_left hDone hNpow])

/-- The quartic member of the diagonal numerical hypotheses. -/
private theorem eventually_CFPDiagonalNumericBounds_first
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (((lowerColorCount c n : ℝ) ^ 2) ^ 2) ≤
        (15 / 2 : ℝ) * lowerColorCount c n * Nat.totient n *
          Real.log (lowerColorCount c n : ℝ) := by
  obtain ⟨C, hC, hratio⟩ := exists_eventually_totientRatio_le_loglog
  have hsqrtLogTop : Tendsto (fun n : ℕ ↦
      Real.rpow (Real.log (n : ℝ)) (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_coe_at_top
  have hpowFifteenthTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 15 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hpowThirdTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have hscaleLarge := resolutionScale_tendsto_atTop.eventually
    (eventually_ge_atTop (2 / c))
  filter_upwards [eventually_gt_atTop 0,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_three_le_lowerColorCount hc, hratio,
    hsqrtLogTop.eventually
      (eventually_ge_atTop (16 * c ^ 3 * C ^ 4)),
    hpowFifteenthTop.eventually (eventually_ge_atTop (4 / c)),
    hpowThirdTop.eventually (eventually_ge_atTop (1200 * c)),
    hpowThirdTop.eventually (eventually_ge_atTop (3 * c * C)),
    hscaleLarge] with n hn hL hLL hcolors hratioN
      hsqrtLarge hpowFifteenthLarge hpowThirdLarge hpowThirdCLarge
      hscaleLargeN
  let h : ℝ := lowerColorCount c n
  let H : ℝ := resolutionScale n
  let N : ℝ := n
  let L : ℝ := Real.log N
  let LL : ℝ := Real.log L
  let R : ℝ := N / Nat.totient n
  let P : ℝ := Nat.totient n
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hLone : 1 ≤ L := by simpa [L, N] using hL
  have hLLone : 1 ≤ LL := by simpa [LL, L, N] using hLL
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hLLpos : 0 < LL := zero_lt_one.trans_le hLLone
  have hPpos : 0 < P := by
    dsimp [P]
    exact_mod_cast (Nat.totient_pos.mpr hn)
  have hHpos : 0 < H := by
    dsimp [H]
    rw [resolutionScale]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hNpos _)
        (div_pos hNpos hPpos))
      (mul_pos (Real.rpow_pos_of_pos hLpos _)
        (Real.rpow_pos_of_pos hLLpos _))
  have hhNonneg : 0 ≤ h := by positivity
  have hhPos : 0 < h := by
    dsimp [h]
    exact_mod_cast (show 0 < lowerColorCount c n by omega)
  have hhUpper : h ≤ c * H := by
    simpa [h, H] using
      (lowerColorCount_bounds hc.le hHpos.le).1
  have hhLower : c * H / 2 ≤ h := by
    have hfloor := (lowerColorCount_bounds hc.le hHpos.le).2
    have hcH : 2 ≤ c * H := by
      have : 2 / c ≤ H := by simpa [H] using hscaleLargeN
      simpa [mul_comm] using (div_le_iff₀ hc).mp this
    dsimp [h, H] at hfloor ⊢
    nlinarith
  have hloghOne : 1 ≤ Real.log h := by
    have hthree : (3 : ℝ) ≤ h := by
      dsimp [h]
      exact_mod_cast hcolors
    have hlogThree : 1 < Real.log (3 : ℝ) :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
        Real.exp_one_lt_three
    exact hlogThree.le.trans (Real.log_le_log (by norm_num) hthree)
  have hratioBound : R ≤ C * LL := by
    simpa [R, N, LL, L] using hratioN n hn le_rfl
  have hratioNonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hscaleProduct := resolutionScale_mul_totient_bounds hn hL hLL
  have hscaleProductLower :
      Real.rpow N (4 / 3 : ℝ) / L ≤ H * P := by
    simpa [N, L, H, P] using hscaleProduct.1
  have hscaleProductUpper :
      H * P ≤ Real.rpow N (4 / 3 : ℝ) := by
    simpa [N, H, P] using hscaleProduct.2
  have hcubeCross : L * LL ^ 2 * H ^ 3 = P * R ^ 4 := by
    simpa [N, L, LL, H, P, R] using
      resolutionScale_cube_cross hn hLpos hLLpos
  have hLLsq : LL ^ 2 ≤
      16 * Real.rpow L (1 / 2 : ℝ) := by
    simpa [N, L, LL] using loglog_sq_le_sixteen_mul_sqrt_log hL
  have hsqrtNonneg : 0 ≤ Real.rpow L (1 / 2 : ℝ) :=
    Real.rpow_nonneg hLpos.le _
  have hsqrtSq : (Real.rpow L (1 / 2 : ℝ)) ^ 2 = L := by
    calc
      (Real.rpow L (1 / 2 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow L (1 / 2 : ℝ)) (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow L ((1 / 2 : ℝ) * 2) :=
        (Real.rpow_mul hLpos.le _ _).symm
      _ = L := by norm_num
  have hcoeff : c ^ 3 * C ^ 4 * LL ^ 2 ≤ L := by
    calc
      c ^ 3 * C ^ 4 * LL ^ 2 ≤
          c ^ 3 * C ^ 4 *
            (16 * Real.rpow L (1 / 2 : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hLLsq (by positivity)
      _ = (16 * c ^ 3 * C ^ 4) *
          Real.rpow L (1 / 2 : ℝ) := by ring
      _ ≤ Real.rpow L (1 / 2 : ℝ) *
          Real.rpow L (1 / 2 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (by simpa [N, L] using hsqrtLarge) hsqrtNonneg
      _ = L := by rw [← pow_two, hsqrtSq]
  have hratioPow : R ^ 4 ≤ C ^ 4 * LL ^ 4 := by
    calc
      R ^ 4 ≤ (C * LL) ^ 4 :=
        pow_le_pow_left₀ hratioNonneg hratioBound 4
      _ = C ^ 4 * LL ^ 4 := by ring
  have hcRatio : c ^ 3 * R ^ 4 ≤ L * LL ^ 2 := by
    calc
      c ^ 3 * R ^ 4 ≤ c ^ 3 * (C ^ 4 * LL ^ 4) :=
        mul_le_mul_of_nonneg_left hratioPow (by positivity)
      _ = (c ^ 3 * C ^ 4 * LL ^ 2) * LL ^ 2 := by ring
      _ ≤ L * LL ^ 2 :=
        mul_le_mul_of_nonneg_right hcoeff (sq_nonneg LL)
  have hcHcube : c ^ 3 * H ^ 3 ≤ P := by
    have hdenPos : 0 < L * LL ^ 2 := mul_pos hLpos (sq_pos_of_pos hLLpos)
    have hmul : (c ^ 3 * H ^ 3) * (L * LL ^ 2) ≤
        P * (L * LL ^ 2) := calc
      (c ^ 3 * H ^ 3) * (L * LL ^ 2) =
          c ^ 3 * (L * LL ^ 2 * H ^ 3) := by ring
      _ = c ^ 3 * (P * R ^ 4) := by rw [hcubeCross]
      _ = P * (c ^ 3 * R ^ 4) := by ring
      _ ≤ P * (L * LL ^ 2) :=
        mul_le_mul_of_nonneg_left hcRatio hPpos.le
    nlinarith
  have hhCube : h ^ 3 ≤ P := by
    calc
      h ^ 3 ≤ (c * H) ^ 3 := pow_le_pow_left₀ hhNonneg hhUpper 3
      _ = c ^ 3 * H ^ 3 := by ring
      _ ≤ P := hcHcube
  have hfirst : (h ^ 2) ^ 2 ≤
      (15 / 2 : ℝ) * h * P * Real.log h := by
    have hone : 1 ≤ (15 / 2 : ℝ) * Real.log h := by nlinarith
    calc
      (h ^ 2) ^ 2 = h * h ^ 3 := by ring
      _ ≤ h * P := mul_le_mul_of_nonneg_left hhCube hhNonneg
      _ ≤ (15 / 2 : ℝ) * h * P * Real.log h := by
        nlinarith [mul_le_mul_of_nonneg_left hone
          (mul_nonneg hhNonneg hPpos.le)]

  simpa only [h, P] using hfirst

/- The following derivation was the initial monolithic version of the
second and third estimates.  It is retained as a local development note;
the compiled split lemmas below avoid exceeding Lean's ordinary heartbeat
budget without changing it.

  have hpowTwoFifteenths :
      Real.rpow N (2 / 15 : ℝ) =
        Real.rpow N (1 / 15 : ℝ) *
          Real.rpow N (1 / 15 : ℝ) := by
    have := Real.rpow_add hNpos (1 / 15 : ℝ) (1 / 15 : ℝ)
    convert this using 1 <;> norm_num
  have hlogTarget : L ≤
      (15 * c / 4) * Real.rpow N (2 / 15 : ℝ) := by
    have hlogRaw := Real.log_le_rpow_div hNpos.le
      (show (0 : ℝ) < 1 / 15 by norm_num)
    have hpNonneg : 0 ≤ Real.rpow N (1 / 15 : ℝ) :=
      Real.rpow_nonneg hNpos.le _
    have hpLarge : 4 / c ≤ Real.rpow N (1 / 15 : ℝ) := by
      simpa [N] using hpowFifteenthLarge
    have hfour : 4 ≤ c * Real.rpow N (1 / 15 : ℝ) :=
      by simpa [mul_comm] using (div_le_iff₀ hc).mp hpLarge
    calc
      L ≤ 15 * Real.rpow N (1 / 15 : ℝ) := by
        simpa [L, N, div_eq_mul_inv, mul_comm] using hlogRaw
      _ ≤ (15 * c / 4) *
          (Real.rpow N (1 / 15 : ℝ) *
            Real.rpow N (1 / 15 : ℝ)) := by
        nlinarith
      _ = (15 * c / 4) * Real.rpow N (2 / 15 : ℝ) := by
        rw [hpowTwoFifteenths]
  have hpowSplitSecond :
      Real.rpow N (4 / 3 : ℝ) =
        Real.rpow N (6 / 5 : ℝ) *
          Real.rpow N (2 / 15 : ℝ) := by
    have := Real.rpow_add hNpos (6 / 5 : ℝ) (2 / 15 : ℝ)
    convert this using 1 <;> norm_num
  have hsecondBase : Real.rpow N (6 / 5 : ℝ) ≤
      (15 * c / 4) * (Real.rpow N (4 / 3 : ℝ) / L) := by
    have heq : (15 * c / 4) * (Real.rpow N (4 / 3 : ℝ) / L) =
        ((15 * c / 4) * Real.rpow N (4 / 3 : ℝ)) / L := by ring
    rw [heq]
    apply (le_div_iff₀ hLpos).2
    calc
      Real.rpow N (6 / 5 : ℝ) * L ≤
          Real.rpow N (6 / 5 : ℝ) *
            ((15 * c / 4) * Real.rpow N (2 / 15 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogTarget
          (Real.rpow_nonneg hNpos.le _)
      _ = (15 * c / 4) * Real.rpow N (4 / 3 : ℝ) := by
        rw [hpowSplitSecond]
        ring
  have hcolorProductLower :
      (c / 2) * (Real.rpow N (4 / 3 : ℝ) / L) ≤ h * P := by
    calc
      (c / 2) * (Real.rpow N (4 / 3 : ℝ) / L) ≤
          (c / 2) * (H * P) :=
        mul_le_mul_of_nonneg_left hscaleProductLower (by positivity)
      _ = (c * H / 2) * P := by ring
      _ ≤ h * P := mul_le_mul_of_nonneg_right hhLower hPpos.le
  have hsecond : Real.rpow N (6 / 5 : ℝ) ≤
      (15 / 2 : ℝ) * h * P * Real.log h := by
    calc
      Real.rpow N (6 / 5 : ℝ) ≤
          (15 * c / 4) * (Real.rpow N (4 / 3 : ℝ) / L) :=
        hsecondBase
      _ = (15 / 2 : ℝ) *
          ((c / 2) * (Real.rpow N (4 / 3 : ℝ) / L)) := by ring
      _ ≤ (15 / 2 : ℝ) * (h * P) :=
        mul_le_mul_of_nonneg_left hcolorProductLower (by norm_num)
      _ ≤ (15 / 2 : ℝ) * h * P * Real.log h := by
        have hm : h * P ≤ (h * P) * Real.log h :=
          by simpa using mul_le_mul_of_nonneg_left hloghOne
            (mul_nonneg hhNonneg hPpos.le)
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 15 / 2)

  have hLLleL : LL ≤ L := by
    have := Real.log_le_sub_one_of_pos hLpos
    dsimp [LL]
    linarith
  have hscaleUpperRaw : H ≤ Real.rpow N (1 / 3 : ℝ) * R := by
    let D : ℝ := Real.rpow L (1 / 3 : ℝ) *
      Real.rpow LL (2 / 3 : ℝ)
    have hDone : 1 ≤ D := by
      dsimp [D]
      have h1 := Real.one_le_rpow hLone (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have h2 := Real.one_le_rpow hLLone (by norm_num : (0 : ℝ) ≤ 2 / 3)
      nlinarith
    have hDpos : 0 < D := zero_lt_one.trans_le hDone
    rw [show H = Real.rpow N (1 / 3 : ℝ) * R / D by rfl]
    exact (div_le_iff₀ hDpos).2 (by
      have hnumNonneg : 0 ≤ Real.rpow N (1 / 3 : ℝ) * R :=
        mul_nonneg (Real.rpow_nonneg hNpos.le _) hratioNonneg
      nlinarith [mul_le_mul_of_nonneg_left hDone hnumNonneg])
  have hlogRawThird := Real.log_le_rpow_div hNpos.le
    (show (0 : ℝ) < 1 / 3 by norm_num)
  have hlogThird : L ≤ 3 * Real.rpow N (1 / 3 : ℝ) := by
    simpa [L, N, div_eq_mul_inv] using hlogRawThird
  have hHcrude : H ≤
      C * L * Real.rpow N (1 / 3 : ℝ) := by
    calc
      H ≤ Real.rpow N (1 / 3 : ℝ) * R := hscaleUpperRaw
      _ ≤ Real.rpow N (1 / 3 : ℝ) * (C * LL) :=
        mul_le_mul_of_nonneg_left hratioBound
          (Real.rpow_nonneg hNpos.le _)
      _ ≤ Real.rpow N (1 / 3 : ℝ) * (C * L) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hLLleL hC.le)
          (Real.rpow_nonneg hNpos.le _)
      _ = C * L * Real.rpow N (1 / 3 : ℝ) := by ring
  have hpowTwoThirds :
      Real.rpow N (2 / 3 : ℝ) =
        Real.rpow N (1 / 3 : ℝ) *
          Real.rpow N (1 / 3 : ℝ) := by
    have := Real.rpow_add hNpos (1 / 3 : ℝ) (1 / 3 : ℝ)
    convert this using 1 <;> norm_num
  have hpowOneThird_mul_twoThirds :
      Real.rpow N (1 / 3 : ℝ) *
          Real.rpow N (2 / 3 : ℝ) = N := by
    have := Real.rpow_add hNpos (1 / 3 : ℝ) (2 / 3 : ℝ)
    convert this using 1 <;> norm_num
  have hhLeN : h ≤ N := by
    calc
      h ≤ c * H := hhUpper
      _ ≤ c * (C * L * Real.rpow N (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hHcrude hc.le
      _ ≤ c * (C * (3 * Real.rpow N (1 / 3 : ℝ)) *
          Real.rpow N (1 / 3 : ℝ)) := by
        gcongr
      _ = (3 * c * C) * Real.rpow N (2 / 3 : ℝ) := by
        rw [hpowTwoThirds]
        ring
      _ ≤ Real.rpow N (1 / 3 : ℝ) *
          Real.rpow N (2 / 3 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (by simpa [N] using hpowThirdCLarge)
          (Real.rpow_nonneg hNpos.le _)
      _ = N := hpowOneThird_mul_twoThirds
  have hloghLe : Real.log h ≤ L := by
    dsimp [L]
    exact Real.log_le_log hhPos hhLeN
  have hpowFiveThirds :
      Real.rpow N (5 / 3 : ℝ) =
        Real.rpow N (4 / 3 : ℝ) *
          Real.rpow N (1 / 3 : ℝ) := by
    have := Real.rpow_add hNpos (4 / 3 : ℝ) (1 / 3 : ℝ)
    convert this using 1 <;> norm_num
  have hpowTwo :
      N ^ 2 = Real.rpow N (5 / 3 : ℝ) *
          Real.rpow N (1 / 3 : ℝ) := by
    calc
      N ^ 2 = Real.rpow N (2 : ℝ) := Real.rpow_two N
      _ = Real.rpow N ((5 / 3 : ℝ) + (1 / 3 : ℝ)) := by norm_num
      _ = Real.rpow N (5 / 3 : ℝ) *
          Real.rpow N (1 / 3 : ℝ) := Real.rpow_add hNpos _ _
  have hthird : 100 * h * P * Real.log h ≤ (N / 2) ^ 2 := by
    have hhP : h * P ≤ c * Real.rpow N (4 / 3 : ℝ) := by
      calc
        h * P ≤ (c * H) * P :=
          mul_le_mul_of_nonneg_right hhUpper hPpos.le
        _ = c * (H * P) := by ring
        _ ≤ c * Real.rpow N (4 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hscaleProductUpper hc.le
    calc
      100 * h * P * Real.log h ≤
          100 * (c * Real.rpow N (4 / 3 : ℝ)) * L := by
        have hlogNonneg : 0 ≤ Real.log h := zero_le_one.trans hloghOne
        have := mul_le_mul hhP hloghLe hlogNonneg
          (mul_nonneg hhNonneg hPpos.le)
        nlinarith
      _ ≤ 300 * c *
          (Real.rpow N (4 / 3 : ℝ) *
            Real.rpow N (1 / 3 : ℝ)) := by
        have := mul_le_mul_of_nonneg_left hlogThird
          (mul_nonneg (by positivity : 0 ≤ 100 * c)
            (Real.rpow_nonneg hNpos.le _))
        nlinarith
      _ = 300 * c * Real.rpow N (5 / 3 : ℝ) := by
        rw [hpowFiveThirds]
      _ ≤ (1 / 4 : ℝ) *
          (Real.rpow N (5 / 3 : ℝ) *
            Real.rpow N (1 / 3 : ℝ)) := by
        have hlarge : 1200 * c ≤ Real.rpow N (1 / 3 : ℝ) := by
          simpa [N] using hpowThirdLarge
        have hpowNonneg : 0 ≤ Real.rpow N (5 / 3 : ℝ) :=
          Real.rpow_nonneg hNpos.le _
        nlinarith [mul_le_mul_of_nonneg_right hlarge hpowNonneg]
      _ = (N / 2) ^ 2 := by rw [← hpowTwo]; ring
  exact ⟨hfirst, hsecond, hthird⟩
-/

/-- The lower, `n^(6/5)`, member of the diagonal numerical hypotheses. -/
private theorem eventually_CFPDiagonalNumericBounds_second
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Real.rpow (n : ℝ) (6 / 5 : ℝ) ≤
        (15 / 2 : ℝ) * lowerColorCount c n * Nat.totient n *
          Real.log (lowerColorCount c n : ℝ) := by
  have hpTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 15 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_three_le_lowerColorCount hc,
    resolutionScale_tendsto_atTop.eventually (eventually_ge_atTop (2 / c)),
    hpTop.eventually (eventually_ge_atTop (4 / c))] with
      n hn hL hLL hcolors hscaleLarge hpLarge
  let h : ℝ := lowerColorCount c n
  let H : ℝ := resolutionScale n
  let N : ℝ := n
  let L : ℝ := Real.log N
  let P : ℝ := Nat.totient n
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hLpos : 0 < L := by simpa [L, N] using zero_lt_one.trans_le hL
  have hPpos : 0 < P := by
    dsimp [P]
    exact_mod_cast (Nat.totient_pos.mpr hn)
  have hHpos : 0 < H := by
    dsimp [H]
    rw [resolutionScale]
    have hLLpos : 0 < Real.log (Real.log (n : ℝ)) :=
      zero_lt_one.trans_le hLL
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hNpos _)
        (div_pos hNpos hPpos))
      (mul_pos (Real.rpow_pos_of_pos hLpos _)
        (Real.rpow_pos_of_pos hLLpos _))
  have hhNonneg : 0 ≤ h := by positivity
  have hhLower : c * H / 2 ≤ h := by
    have hfloor := (lowerColorCount_bounds hc.le hHpos.le).2
    have hcH : 2 ≤ c * H := by
      have hx : 2 / c ≤ H := by simpa [H] using hscaleLarge
      simpa [mul_comm] using (div_le_iff₀ hc).mp hx
    dsimp [h, H] at hfloor ⊢
    nlinarith
  have hloghOne : 1 ≤ Real.log h := by
    have hthree : (3 : ℝ) ≤ h := by
      dsimp [h]
      exact_mod_cast hcolors
    have hlogThree : 1 < Real.log (3 : ℝ) :=
      (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)).2
        Real.exp_one_lt_three
    exact hlogThree.le.trans (Real.log_le_log (by norm_num) hthree)
  have hscaleLower : Real.rpow N (4 / 3 : ℝ) / L ≤ H * P := by
    simpa [N, L, H, P] using
      (resolutionScale_mul_totient_bounds hn hL hLL).1
  have hpNonneg : 0 ≤ Real.rpow N (1 / 15 : ℝ) :=
    Real.rpow_nonneg hNpos.le _
  have hfour : 4 ≤ c * Real.rpow N (1 / 15 : ℝ) := by
    have : 4 / c ≤ Real.rpow N (1 / 15 : ℝ) := by
      simpa [N] using hpLarge
    simpa [mul_comm] using (div_le_iff₀ hc).mp this
  have hpowTwoFifteenths :
      Real.rpow N (2 / 15 : ℝ) =
        Real.rpow N (1 / 15 : ℝ) *
          Real.rpow N (1 / 15 : ℝ) := by
    have := Real.rpow_add hNpos (1 / 15 : ℝ) (1 / 15 : ℝ)
    convert this using 1 <;> norm_num
  have hlogTarget : L ≤
      (15 * c / 4) * Real.rpow N (2 / 15 : ℝ) := by
    have hraw := Real.log_le_rpow_div hNpos.le
      (show (0 : ℝ) < 1 / 15 by norm_num)
    have hlogRaw : L ≤ 15 * Real.rpow N (1 / 15 : ℝ) := by
      simpa [L, N, div_eq_mul_inv, mul_comm] using hraw
    have hmul : 15 * Real.rpow N (1 / 15 : ℝ) ≤
        (15 * c / 4) *
          (Real.rpow N (1 / 15 : ℝ) *
            Real.rpow N (1 / 15 : ℝ)) := by
      have hx := mul_le_mul_of_nonneg_left hfour
        (show 0 ≤ 15 * Real.rpow N (1 / 15 : ℝ) / 4 by positivity)
      nlinarith
    calc
      L ≤ 15 * Real.rpow N (1 / 15 : ℝ) := hlogRaw
      _ ≤ (15 * c / 4) *
          (Real.rpow N (1 / 15 : ℝ) *
            Real.rpow N (1 / 15 : ℝ)) := hmul
      _ = (15 * c / 4) * Real.rpow N (2 / 15 : ℝ) := by
        rw [hpowTwoFifteenths]
  have hsplit : Real.rpow N (4 / 3 : ℝ) =
      Real.rpow N (6 / 5 : ℝ) *
        Real.rpow N (2 / 15 : ℝ) := by
    have := Real.rpow_add hNpos (6 / 5 : ℝ) (2 / 15 : ℝ)
    convert this using 1 <;> norm_num
  have hbase : Real.rpow N (6 / 5 : ℝ) ≤
      (15 * c / 4) * (Real.rpow N (4 / 3 : ℝ) / L) := by
    have heq : (15 * c / 4) * (Real.rpow N (4 / 3 : ℝ) / L) =
        ((15 * c / 4) * Real.rpow N (4 / 3 : ℝ)) / L := by ring
    rw [heq]
    apply (le_div_iff₀ hLpos).2
    calc
      Real.rpow N (6 / 5 : ℝ) * L ≤
          Real.rpow N (6 / 5 : ℝ) *
            ((15 * c / 4) * Real.rpow N (2 / 15 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlogTarget
          (Real.rpow_nonneg hNpos.le _)
      _ = (15 * c / 4) * Real.rpow N (4 / 3 : ℝ) := by
        rw [hsplit]
        ring
  have hcolorLower :
      (c / 2) * (Real.rpow N (4 / 3 : ℝ) / L) ≤ h * P := by
    calc
      (c / 2) * (Real.rpow N (4 / 3 : ℝ) / L) ≤
          (c / 2) * (H * P) :=
        mul_le_mul_of_nonneg_left hscaleLower (by positivity)
      _ = (c * H / 2) * P := by ring
      _ ≤ h * P := mul_le_mul_of_nonneg_right hhLower hPpos.le
  have hmain : Real.rpow N (6 / 5 : ℝ) ≤
      (15 / 2 : ℝ) * h * P * Real.log h := by
    calc
      Real.rpow N (6 / 5 : ℝ) ≤
          (15 * c / 4) * (Real.rpow N (4 / 3 : ℝ) / L) := hbase
      _ = (15 / 2 : ℝ) *
          ((c / 2) * (Real.rpow N (4 / 3 : ℝ) / L)) := by ring
      _ ≤ (15 / 2 : ℝ) * (h * P) :=
        mul_le_mul_of_nonneg_left hcolorLower (by norm_num)
      _ ≤ (15 / 2 : ℝ) * h * P * Real.log h := by
        have hm : h * P ≤ (h * P) * Real.log h := by
          simpa using mul_le_mul_of_nonneg_left hloghOne
            (mul_nonneg hhNonneg hPpos.le)
        simpa [mul_assoc] using
          mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 15 / 2)
  simpa only [N, h, P] using hmain

/-- The upper quadratic member of the diagonal numerical hypotheses. -/
private theorem eventually_CFPDiagonalNumericBounds_third
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      100 * lowerColorCount c n * Nat.totient n *
          Real.log (lowerColorCount c n : ℝ) ≤
        (((n : ℝ) / 2) ^ 2) := by
  obtain ⟨C, hC, hratio⟩ := exists_eventually_totientRatio_le_loglog
  have hpowThirdTop : Tendsto (fun n : ℕ ↦
      Real.rpow (n : ℝ) (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_gt_atTop 0,
    tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    tendsto_log_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_three_le_lowerColorCount hc, hratio,
    hpowThirdTop.eventually (eventually_ge_atTop (1200 * c)),
    hpowThirdTop.eventually (eventually_ge_atTop (3 * c * C))] with
      n hn hL hLL hcolors hratioN hpowThirdLarge hpowThirdCLarge
  let h : ℝ := lowerColorCount c n
  let H : ℝ := resolutionScale n
  let N : ℝ := n
  let L : ℝ := Real.log N
  let LL : ℝ := Real.log L
  let R : ℝ := N / Nat.totient n
  let P : ℝ := Nat.totient n
  have hNpos : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hLone : 1 ≤ L := by simpa [L, N] using hL
  have hLLone : 1 ≤ LL := by simpa [LL, L, N] using hLL
  have hLpos : 0 < L := zero_lt_one.trans_le hLone
  have hLLpos : 0 < LL := zero_lt_one.trans_le hLLone
  have hPpos : 0 < P := by
    dsimp [P]
    exact_mod_cast (Nat.totient_pos.mpr hn)
  have hHpos : 0 < H := by
    dsimp [H]
    rw [resolutionScale]
    exact div_pos
      (mul_pos (Real.rpow_pos_of_pos hNpos _)
        (div_pos hNpos hPpos))
      (mul_pos (Real.rpow_pos_of_pos hLpos _)
        (Real.rpow_pos_of_pos hLLpos _))
  have hhNonneg : 0 ≤ h := by positivity
  have hhPos : 0 < h := by
    dsimp [h]
    exact_mod_cast (show 0 < lowerColorCount c n by omega)
  have hhUpper : h ≤ c * H := by
    simpa [h, H] using (lowerColorCount_bounds hc.le hHpos.le).1
  have hratioBound : R ≤ C * LL := by
    simpa [R, N, LL, L] using hratioN n hn le_rfl
  have hratioNonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hscaleProductUpper : H * P ≤ Real.rpow N (4 / 3 : ℝ) := by
    simpa [N, H, P] using
      (resolutionScale_mul_totient_bounds hn hL hLL).2
  have hLLleL : LL ≤ L := by
    have hx := Real.log_le_sub_one_of_pos hLpos
    dsimp [LL]
    linarith
  have hscaleUpperRaw : H ≤ Real.rpow N (1 / 3 : ℝ) * R := by
    let D : ℝ := Real.rpow L (1 / 3 : ℝ) *
      Real.rpow LL (2 / 3 : ℝ)
    have hDone : 1 ≤ D := by
      dsimp [D]
      have h1 := Real.one_le_rpow hLone
        (by norm_num : (0 : ℝ) ≤ 1 / 3)
      have h2 := Real.one_le_rpow hLLone
        (by norm_num : (0 : ℝ) ≤ 2 / 3)
      nlinarith
    have hDpos : 0 < D := zero_lt_one.trans_le hDone
    rw [show H = Real.rpow N (1 / 3 : ℝ) * R / D by rfl]
    apply (div_le_iff₀ hDpos).2
    have hnumNonneg : 0 ≤ Real.rpow N (1 / 3 : ℝ) * R :=
      mul_nonneg (Real.rpow_nonneg hNpos.le _) hratioNonneg
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hDone hnumNonneg
  have hlogThird : L ≤ 3 * Real.rpow N (1 / 3 : ℝ) := by
    have hraw := Real.log_le_rpow_div hNpos.le
      (show (0 : ℝ) < 1 / 3 by norm_num)
    simpa [L, N, div_eq_mul_inv, mul_comm] using hraw
  have hHcrude : H ≤ C * L * Real.rpow N (1 / 3 : ℝ) := by
    calc
      H ≤ Real.rpow N (1 / 3 : ℝ) * R := hscaleUpperRaw
      _ ≤ Real.rpow N (1 / 3 : ℝ) * (C * LL) :=
        mul_le_mul_of_nonneg_left hratioBound
          (Real.rpow_nonneg hNpos.le _)
      _ ≤ Real.rpow N (1 / 3 : ℝ) * (C * L) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hLLleL hC.le)
          (Real.rpow_nonneg hNpos.le _)
      _ = C * L * Real.rpow N (1 / 3 : ℝ) := by ring
  have hpowTwoThirds : Real.rpow N (2 / 3 : ℝ) =
      Real.rpow N (1 / 3 : ℝ) * Real.rpow N (1 / 3 : ℝ) := by
    have := Real.rpow_add hNpos (1 / 3 : ℝ) (1 / 3 : ℝ)
    convert this using 1 <;> norm_num
  have hpowThirdTwoThirds : Real.rpow N (1 / 3 : ℝ) *
      Real.rpow N (2 / 3 : ℝ) = N := by
    calc
      Real.rpow N (1 / 3 : ℝ) * Real.rpow N (2 / 3 : ℝ) =
          Real.rpow N ((1 / 3 : ℝ) + (2 / 3 : ℝ)) :=
        (Real.rpow_add hNpos _ _).symm
      _ = Real.rpow N 1 := by norm_num
      _ = N := Real.rpow_one N
  have hhLeN : h ≤ N := by
    calc
      h ≤ c * H := hhUpper
      _ ≤ c * (C * L * Real.rpow N (1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_left hHcrude hc.le
      _ ≤ c * (C * (3 * Real.rpow N (1 / 3 : ℝ)) *
          Real.rpow N (1 / 3 : ℝ)) := by
        have hx : C * L ≤ C * (3 * Real.rpow N (1 / 3 : ℝ)) :=
          mul_le_mul_of_nonneg_left hlogThird hC.le
        have hy := mul_le_mul_of_nonneg_right hx
          (Real.rpow_nonneg hNpos.le (1 / 3 : ℝ))
        exact mul_le_mul_of_nonneg_left hy hc.le
      _ = (3 * c * C) * Real.rpow N (2 / 3 : ℝ) := by
        rw [hpowTwoThirds]
        ring
      _ ≤ Real.rpow N (1 / 3 : ℝ) *
          Real.rpow N (2 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_right
          (by simpa [N] using hpowThirdCLarge)
          (Real.rpow_nonneg hNpos.le _)
      _ = N := hpowThirdTwoThirds
  have hloghLe : Real.log h ≤ L := by
    dsimp [L]
    exact Real.log_le_log hhPos hhLeN
  have hloghNonneg : 0 ≤ Real.log h := by
    apply Real.log_nonneg
    have : (3 : ℝ) ≤ h := by
      dsimp [h]
      exact_mod_cast hcolors
    linarith
  have hhP : h * P ≤ c * Real.rpow N (4 / 3 : ℝ) := by
    calc
      h * P ≤ (c * H) * P :=
        mul_le_mul_of_nonneg_right hhUpper hPpos.le
      _ = c * (H * P) := by ring
      _ ≤ c * Real.rpow N (4 / 3 : ℝ) :=
        mul_le_mul_of_nonneg_left hscaleProductUpper hc.le
  have hpowFiveThirds : Real.rpow N (5 / 3 : ℝ) =
      Real.rpow N (4 / 3 : ℝ) * Real.rpow N (1 / 3 : ℝ) := by
    have := Real.rpow_add hNpos (4 / 3 : ℝ) (1 / 3 : ℝ)
    convert this using 1 <;> norm_num
  have hpowTwo : N ^ 2 = Real.rpow N (5 / 3 : ℝ) *
      Real.rpow N (1 / 3 : ℝ) := by
    calc
      N ^ 2 = Real.rpow N (2 : ℝ) := (Real.rpow_two N).symm
      _ = Real.rpow N ((5 / 3 : ℝ) + (1 / 3 : ℝ)) := by norm_num
      _ = Real.rpow N (5 / 3 : ℝ) * Real.rpow N (1 / 3 : ℝ) :=
        Real.rpow_add hNpos _ _
  have hmain : 100 * h * P * Real.log h ≤ (N / 2) ^ 2 := by
    calc
      100 * h * P * Real.log h ≤
          100 * (c * Real.rpow N (4 / 3 : ℝ)) * L := by
        have hx := mul_le_mul hhP hloghLe hloghNonneg
          (mul_nonneg hc.le (Real.rpow_nonneg hNpos.le _))
        have hx100 := mul_le_mul_of_nonneg_left hx (by norm_num : (0 : ℝ) ≤ 100)
        simpa [mul_assoc] using hx100
      _ ≤ 300 * c * (Real.rpow N (4 / 3 : ℝ) *
          Real.rpow N (1 / 3 : ℝ)) := by
        have hx := mul_le_mul_of_nonneg_left hlogThird
          (show 0 ≤ 100 * (c * Real.rpow N (4 / 3 : ℝ)) by
            exact mul_nonneg (by norm_num)
              (mul_nonneg hc.le (Real.rpow_nonneg hNpos.le _)))
        nlinarith
      _ = 300 * c * Real.rpow N (5 / 3 : ℝ) := by
        rw [hpowFiveThirds]
      _ ≤ (1 / 4 : ℝ) * (Real.rpow N (5 / 3 : ℝ) *
          Real.rpow N (1 / 3 : ℝ)) := by
        have hlarge : 1200 * c ≤ Real.rpow N (1 / 3 : ℝ) := by
          simpa [N] using hpowThirdLarge
        have hx := mul_le_mul_of_nonneg_left hlarge
          (show 0 ≤ Real.rpow N (5 / 3 : ℝ) / 4 by
            exact div_nonneg (Real.rpow_nonneg hNpos.le _) (by norm_num))
        nlinarith
      _ = (N / 2) ^ 2 := by rw [← hpowTwo]; ring
  simpa only [N, h, P] using hmain

/-- All three diagonal numerical hypotheses hold for every fixed positive
constant multiplying the resolution scale. -/
theorem eventually_CFPDiagonalNumericBounds_lowerColorCount
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      CFPDiagonalNumericBounds n (lowerColorCount c n) := by
  filter_upwards [eventually_CFPDiagonalNumericBounds_first hc,
    eventually_CFPDiagonalNumericBounds_second hc,
    eventually_CFPDiagonalNumericBounds_third hc] with n h1 h2 h3
  exact ⟨h1, h2, h3⟩

#print axioms Erdos360.eventually_CFPDiagonalNumericBounds_lowerColorCount

end Erdos360
