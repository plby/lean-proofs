import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Filter MeasureTheory Set

/-!
This file is mostly a compatibility layer for the old Lean 3 `for_mathlib/integral_rpow` file.
All of the main half-line `rpow` lemmas are now available in Mathlib 4 under standard names.
-/

theorem integrable_on_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x ^ r) (Ioi a) :=
  integrableOn_Ioi_rpow_of_lt hr ha

theorem integral_rpow_Ioi {a r : ℝ} (hr : r < -1) (ha : 0 < a) :
    ∫ x in Ioi a, x ^ r = -a ^ (r + 1) / (r + 1) :=
  integral_Ioi_rpow_of_lt hr ha

theorem integral_Ioi_rpow_tendsto_aux {a r : ℝ} (hr : r < -1) (ha : 0 < a)
    {ι : Type*} {b : ι → ℝ} {l : Filter ι} (hb : Tendsto b l atTop) :
    Tendsto (fun i ↦ ∫ x in a..b i, x ^ r) l (nhds (-a ^ (r + 1) / (r + 1))) := by
  have hEq :
      (fun i ↦ ∫ x in a..b i, x ^ r) =ᶠ[l]
        fun i ↦ b i ^ (r + 1) / (r + 1) - a ^ (r + 1) / (r + 1) := by
    filter_upwards [hb.eventually (eventually_ge_atTop a)] with i hi
    rw [integral_rpow]
    · rw [sub_div]
    · exact Or.inr ⟨hr.ne, Set.notMem_uIcc_of_lt ha (ha.trans_le hi)⟩
  refine Tendsto.congr' hEq.symm ?_
  have hpow : Tendsto (fun i ↦ b i ^ (r + 1)) l (nhds 0) := by
    simpa only [neg_neg] using
      (tendsto_rpow_neg_atTop (by linarith : 0 < -(r + 1))).comp hb
  simpa [neg_div] using hpow.div_const (r + 1) |>.sub_const (a ^ (r + 1) / (r + 1))

theorem integrable_on_rpow_inv_Ioi {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ r)⁻¹) (Ioi a) := by
  refine (integrable_on_rpow_Ioi (neg_lt_neg hr) ha).congr_fun (fun x hx ↦ ?_) measurableSet_Ioi
  change x ^ (-r) = (x ^ r)⁻¹
  rw [Real.rpow_neg (ha.trans hx).le]

theorem integral_rpow_inv {a r : ℝ} (hr : 1 < r) (ha : 0 < a) :
    ∫ x in Ioi a, (x ^ r)⁻¹ = a ^ (1 - r) / (r - 1) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ by
    rw [← Real.rpow_neg (ha.trans hx).le])]
  rw [integral_rpow_Ioi (neg_lt_neg hr) ha]
  rw [show -r + 1 = 1 - r by ring]
  rw [show 1 - r = -(r - 1) by ring, div_neg, neg_div, neg_neg]

theorem integrable_on_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ x ^ n) (Ioi a) := by
  simpa using (integrable_on_rpow_Ioi (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integral_zpow_Ioi {a : ℝ} {n : ℤ} (hn : n < -1) (ha : 0 < a) :
    ∫ x in Ioi a, x ^ n = -a ^ (n + 1) / (n + 1) := by
  exact_mod_cast (integral_rpow_Ioi (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integrable_on_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ n)⁻¹) (Ioi a) := by
  simpa using (integrable_on_rpow_inv_Ioi (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integral_zpow_inv_Ioi {a : ℝ} {n : ℤ} (hn : 1 < n) (ha : 0 < a) :
    ∫ x in Ioi a, (x ^ n)⁻¹ = a ^ (1 - n) / (n - 1) := by
  exact_mod_cast (integral_rpow_inv (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha)

theorem integrable_on_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ ↦ (x ^ n)⁻¹) (Ioi a) := by
  simpa only [← zpow_natCast] using
    (integrable_on_zpow_inv_Ioi (n := (n : ℤ)) (show 1 < (n : ℤ) by exact_mod_cast hn) ha)

theorem integral_pow_inv_Ioi {a : ℝ} {n : ℕ} (hn : 1 < n) (ha : 0 < a) :
    ∫ x in Ioi a, (x ^ n)⁻¹ = (a ^ (n - 1))⁻¹ / (n - 1) := by
  have h :=
    integral_rpow_inv (a := a) (r := (n : ℝ)) (by exact_mod_cast hn) ha
  have hexp : 1 - (n : ℝ) = -((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn.le]
    ring
  have hden : (n : ℝ) - 1 = ((n - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hn.le]
    ring
  rw [hexp, hden, Real.rpow_neg ha.le, Real.rpow_natCast] at h
  simpa [Nat.cast_sub hn.le] using h
