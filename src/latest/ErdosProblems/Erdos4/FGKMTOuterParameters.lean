import ErdosProblems.Erdos4.FGKMTGrowingIndexBounds
import ErdosProblems.Erdos4.FGKMTGrowingSieveAccuracy
import ErdosProblems.Erdos4.EulerDensityBounds

/-! Concrete random-sieve and gap-length parameters at the FGKMT18 scale. -/

namespace Erdos4.FGKMT

open Filter Asymptotics

noncomputable def growingOuterScale (x : ℕ) : ℝ :=
  Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))) / Real.log (Real.log (x : ℝ))

noncomputable def growingRandomEnd (x : ℕ) : ℕ :=
  ⌊Real.exp (growingOuterScale x / 100)⌋₊

noncomputable def growingGapLength (c : ℝ) (x : ℕ) : ℕ :=
  ⌊c * (x : ℝ) * growingOuterScale x⌋₊

noncomputable def growingRandomPrimes (x : ℕ) : Finset ℕ :=
  ArithmeticFibers.primeWindow (growingRandomStart x) (growingRandomEnd x)

noncomputable def growingRandomValue (x : ℕ) (p : growingRandomPrimes x) : ℕ := p.val

instance growingRandomValue_prime (x : ℕ) (p : growingRandomPrimes x) :
    Fact (growingRandomValue x p).Prime :=
  ⟨(ArithmeticFibers.mem_primeWindow.mp p.property).1⟩

theorem growingRandomValue_injective (x : ℕ) : Function.Injective (growingRandomValue x) :=
  Subtype.val_injective

theorem growingRandomValue_above_start (x : ℕ) (p : growingRandomPrimes x) :
    growingRandomStart x < growingRandomValue x p :=
  (ArithmeticFibers.mem_primeWindow.mp p.property).2.1

theorem eventually_growing_outer_log_budget :
    ∀ᶠ x : ℕ in atTop,
      1 ≤ Real.log (x : ℝ) ∧ 1 ≤ Real.log (Real.log (x : ℝ)) ∧
      1000 * Real.log (Real.log (x : ℝ)) ≤ Real.sqrt (Real.log (x : ℝ)) ∧
      Real.sqrt (Real.log (x : ℝ)) ≤ growingOuterScale x / 100 ∧
      growingOuterScale x ≤ Real.log (x : ℝ) := by
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hsmall := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
    hlog).bound (by norm_num : (0 : ℝ) < 1 / 1000)
  filter_upwards [hsmall, hlog.eventually (eventually_ge_atTop 1),
    hloglog.eventually (eventually_ge_atTop (max 1 (Real.exp 1)))] with x hsmall hL hlarge
  let L := Real.log (x : ℝ)
  let l := Real.log L
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  have hl : 1 ≤ l := (le_max_left _ _).trans hlarge
  have hlpos : 0 < l := lt_of_lt_of_le (by norm_num) hl
  have hlogl : 1 ≤ Real.log l := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hlarge)
    simpa only [Real.log_exp, Function.comp_apply, l, L] using hh
  have hsmall' : l ≤ (1 / 1000 : ℝ) * Real.sqrt L := by
    simp only [Function.comp_apply, Real.norm_eq_abs] at hsmall
    change |l| ≤ (1 / 1000 : ℝ) * |L ^ (1 / 2 : ℝ)| at hsmall
    rw [abs_of_nonneg hlpos.le, abs_of_nonneg (Real.rpow_nonneg hLpos.le (1 / 2 : ℝ)),
      ← Real.sqrt_eq_rpow] at hsmall
    exact hsmall
  have hdom : 1000 * l ≤ Real.sqrt L := by linarith
  have hsqrt : 0 ≤ Real.sqrt L := Real.sqrt_nonneg L
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLpos.le
  have hscale : Real.sqrt L ≤ growingOuterScale x / 100 := by
    change Real.sqrt L ≤ (L * Real.log l / l) / 100
    rw [div_div]
    apply (le_div_iff₀ (by positivity : 0 < l * 100)).mpr
    have hmul := mul_le_mul_of_nonneg_left hdom hsqrt
    have hmain := mul_le_mul_of_nonneg_left hlogl hLpos.le
    nlinarith
  have hupper : growingOuterScale x ≤ L := by
    change L * Real.log l / l ≤ L
    apply (div_le_iff₀ hlpos).mpr
    have hh := Real.log_le_sub_one_of_pos hlpos
    exact mul_le_mul_of_nonneg_left (by linarith : Real.log l ≤ l) hLpos.le
  exact ⟨hL, hl, hdom, hscale, hupper⟩

theorem floor_exp_log_bounds {t : ℝ} (ht : 2 ≤ t) :
    2 ≤ ⌊Real.exp t⌋₊ ∧ t / 2 ≤ Real.log (⌊Real.exp t⌋₊ : ℝ) ∧
      Real.log (⌊Real.exp t⌋₊ : ℝ) ≤ t := by
  have hexp : 2 ≤ Real.exp t := by
    have hh := Real.add_one_le_exp t
    linarith
  have hn : 2 ≤ ⌊Real.exp t⌋₊ := Nat.le_floor hexp
  have hnR : (2 : ℝ) ≤ ⌊Real.exp t⌋₊ := by exact_mod_cast hn
  have hhalf : Real.exp t / 2 ≤ (⌊Real.exp t⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp t)
    linarith
  have hlo := Real.log_le_log (by positivity : 0 < Real.exp t / 2) hhalf
  rw [Real.log_div (Real.exp_pos t).ne' (by norm_num : (2 : ℝ) ≠ 0), Real.log_exp] at hlo
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hup := Real.log_le_log (by linarith : (0 : ℝ) < ⌊Real.exp t⌋₊)
    (Nat.floor_le (Real.exp_pos t).le)
  rw [Real.log_exp] at hup
  exact ⟨hn, by linarith, hup⟩

end Erdos4.FGKMT
