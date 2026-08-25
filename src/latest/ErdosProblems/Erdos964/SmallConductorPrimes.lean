import ErdosProblems.Erdos964.PrimeCharacterBounds
import ErdosProblems.Erdos964.LinearCharacterSieve
import BoundedGaps.BombieriVinogradov.Analytic.PrimeCountingLogSaving

/-!
# Logarithmic savings for prime character sums

The unconditional prime-counting theorem implies this character estimate.
The factor `q` is harmless for logarithmic conductors once the saving exponent
is chosen larger. The wider displayed modulus range is retained explicitly.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem exists_primeCharacterSum_le_logSaving :
    ∀ A : ℝ, 0 ≤ A →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
        ∀ x : ℕ, X₀ ≤ x → ∀ q : ℕ, 0 < q →
          (q : ℝ) ≤ Real.sqrt (x : ℝ) / Real.rpow (Real.log (x : ℝ)) (A + 5) →
          ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
            ‖finiteCharacterSum x.primesLE q χ‖ ≤
              C * (q : ℝ) * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A := by
  intro A hA
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ :=
    exists_sum_maxProgressionDiscrepancy_le_logSaving_allCutoffs A hA
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro x hx q hq hcut χ hχ
  have hsingle : maxProgressionDiscrepancy x q ≤
      ∑ d ∈ Finset.Icc 1 q, maxProgressionDiscrepancy x d :=
    Finset.single_le_sum (fun d _ => maxProgressionDiscrepancy_nonneg x d)
      (Finset.mem_Icc.mpr ⟨hq, le_rfl⟩)
  calc
    _ ≤ (q : ℝ) * maxProgressionDiscrepancy x q :=
      norm_primeCharacterSum_le_progressionDiscrepancy x hq χ hχ
    _ ≤ (q : ℝ) * (C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A) :=
      mul_le_mul_of_nonneg_left (hsingle.trans (hbound x hx q hcut)) (Nat.cast_nonneg q)
    _ = _ := by ring

/-- Every prescribed logarithmic saving is available uniformly over all
nonprincipal characters whose conductors are bounded by a fixed power of
the logarithm. All constants and thresholds are supplied unconditionally. -/
theorem exists_smallConductor_primeCharacterSum_le_logSaving :
    ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
        ∀ x : ℕ, X₀ ≤ x → ∀ q : ℕ, 0 < q →
          (q : ℝ) ≤ Real.rpow (Real.log (x : ℝ)) B →
          ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
            ‖finiteCharacterSum x.primesLE q χ‖ ≤
              C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A := by
  intro A B hA hB
  obtain ⟨C, hC, Xsave, hXsave, hsave⟩ :=
    exists_primeCharacterSum_le_logSaving (A + B) (add_nonneg hA hB)
  have hdom :=
    ((isLittleO_log_rpow_rpow_atTop (A + 2 * B + 5) (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      tendsto_natCast_atTop_atTop).eventuallyLE
  rw [Filter.eventually_atTop] at hdom
  obtain ⟨Xgrow, hgrow⟩ := hdom
  refine ⟨C, hC, max Xsave Xgrow, hXsave.trans (le_max_left _ _), ?_⟩
  intro x hx q hq hqlog χ hχ
  have hxsave := (le_max_left Xsave Xgrow).trans hx
  have hxgrow := (le_max_right Xsave Xgrow).trans hx
  have hx4 : 4 ≤ x := hXsave.trans hxsave
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hgrowth := hgrow x hxgrow
  simp only [Function.comp_apply, Real.norm_eq_abs] at hgrowth
  rw [abs_of_nonneg (Real.rpow_nonneg hlogpos.le _),
    abs_of_nonneg (Real.rpow_nonneg hxpos.le _), ← Real.sqrt_eq_rpow] at hgrowth
  have hcut : (q : ℝ) ≤
      Real.sqrt (x : ℝ) / Real.rpow (Real.log (x : ℝ)) (A + B + 5) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlogpos _)).mpr
    calc
      _ ≤ Real.rpow (Real.log (x : ℝ)) B *
          Real.rpow (Real.log (x : ℝ)) (A + B + 5) :=
        mul_le_mul_of_nonneg_right hqlog (Real.rpow_nonneg hlogpos.le _)
      _ = Real.rpow (Real.log (x : ℝ)) (B + (A + B + 5)) :=
        (Real.rpow_add hlogpos B (A + B + 5)).symm
      _ = Real.rpow (Real.log (x : ℝ)) (A + 2 * B + 5) := by congr 1; ring
      _ ≤ _ := hgrowth
  calc
    _ ≤ C * (q : ℝ) * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) (A + B) :=
      hsave x hxsave q hq hcut χ hχ
    _ ≤ C * Real.rpow (Real.log (x : ℝ)) B * (x : ℝ) /
        Real.rpow (Real.log (x : ℝ)) (A + B) := by
      gcongr
      exact Real.rpow_nonneg hlogpos.le _
    _ = _ := by
      have hdenom : Real.rpow (Real.log (x : ℝ)) (A + B) =
          Real.rpow (Real.log (x : ℝ)) A * Real.rpow (Real.log (x : ℝ)) B :=
        Real.rpow_add hlogpos A B
      rw [hdenom]
      have hpowB : Real.rpow (Real.log (x : ℝ)) B ≠ 0 := (Real.rpow_pos_of_pos hlogpos B).ne'
      field_simp

theorem primeInterval_cutoffMaximum_le_of_prefix_bound (L U q : ℕ) (hLU : L ≤ U)
    (χ : DirichletCharacter ℂ q) (B : ℝ) (hB : 0 ≤ B)
    (hprefix : ∀ x : ℕ, L ≤ x → x ≤ U → ‖finiteCharacterSum x.primesLE q χ‖ ≤ B) :
    finiteCharacterCutoffMaximum ((Finset.Ioc L U).filter Nat.Prime) U q χ ≤ 2 * B := by
  unfold finiteCharacterCutoffMaximum
  split_ifs with hU
  · apply Finset.sup'_le
    intro X hX
    have hXU := (Finset.mem_Icc.mp hX).2
    by_cases hLX : L ≤ X
    · have hfilter : ((Finset.Ioc L U).filter Nat.Prime).filter (fun n => n ≤ X) =
          (Finset.Ioc L X).filter Nat.Prime := by
        apply Finset.ext
        intro n
        constructor
        · intro hn
          obtain ⟨hnprime, hnX⟩ := Finset.mem_filter.mp hn
          obtain ⟨hnLU, hp⟩ := Finset.mem_filter.mp hnprime
          exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr
            ⟨(Finset.mem_Ioc.mp hnLU).1, hnX⟩, hp⟩
        · intro hn
          obtain ⟨hnLX, hp⟩ := Finset.mem_filter.mp hn
          obtain ⟨hnL, hnX⟩ := Finset.mem_Ioc.mp hnLX
          exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
            ⟨Finset.mem_Ioc.mpr ⟨hnL, hnX.trans hXU⟩, hp⟩, hnX⟩
      rw [hfilter]
      change ‖finiteCharacterSum ((Finset.Ioc L X).filter Nat.Prime) q χ‖ ≤ 2 * B
      rw [finiteCharacterSum_primeInterval L X hLX q χ]
      calc
        _ ≤ ‖finiteCharacterSum X.primesLE q χ‖ + ‖finiteCharacterSum L.primesLE q χ‖ :=
          norm_sub_le _ _
        _ ≤ B + B := add_le_add (hprefix X hLX hXU) (hprefix L le_rfl hLU)
        _ = _ := by ring
    · have hempty : ((Finset.Ioc L U).filter Nat.Prime).filter (fun n => n ≤ X) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro n hn
        have hn' := Finset.mem_filter.mp hn
        have hnL := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn'.1).1).1
        omega
      rw [hempty, Finset.sum_empty, norm_zero]
      positivity
  · positivity

/-- Uniformity over every endpoint of a prime interval. The conductor
cutoff is measured at the lower endpoint, so it works for all product
slices that occur in a semiprime block. -/
theorem exists_smallConductor_primeIntervalMaximum_le_logSaving :
    ∀ A B : ℝ, 0 ≤ A → 0 ≤ B →
      ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, 4 ≤ X₀ ∧
        ∀ L U : ℕ, X₀ ≤ L → L ≤ U → ∀ q : ℕ, 0 < q →
          (q : ℝ) ≤ Real.rpow (Real.log (L : ℝ)) B →
          ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
            finiteCharacterCutoffMaximum ((Finset.Ioc L U).filter Nat.Prime) U q χ ≤
              C * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A := by
  intro A B hA hB
  obtain ⟨C, hC, X₀, hX₀, hsave⟩ :=
    exists_smallConductor_primeCharacterSum_le_logSaving A B hA hB
  refine ⟨2 * C, by positivity, X₀, hX₀, ?_⟩
  intro L U hL hLU q hq hqlog χ hχ
  have hL4 : 4 ≤ L := hX₀.trans hL
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hlogLpos : 0 < Real.log (L : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < L by omega))
  have hprefix (x : ℕ) (hLx : L ≤ x) (hxU : x ≤ U) :
      ‖finiteCharacterSum x.primesLE q χ‖ ≤
        C * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A := by
    have hlogLx : Real.log (L : ℝ) ≤ Real.log (x : ℝ) :=
      Real.log_le_log hLpos (by exact_mod_cast hLx)
    have hqx : (q : ℝ) ≤ Real.rpow (Real.log (x : ℝ)) B :=
      hqlog.trans (Real.rpow_le_rpow hlogLpos.le hlogLx hB)
    calc
      _ ≤ C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) A :=
        hsave x (hL.trans hLx) q hq hqx χ hχ
      _ ≤ C * (U : ℝ) / Real.rpow (Real.log (x : ℝ)) A :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hxU) hC)
          (Real.rpow_nonneg (hlogLpos.le.trans hlogLx) _)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity)
        (Real.rpow_pos_of_pos hlogLpos A) (Real.rpow_le_rpow hlogLpos.le hlogLx hA)
  calc
    _ ≤ 2 * (C * (U : ℝ) / Real.rpow (Real.log (L : ℝ)) A) :=
      primeInterval_cutoffMaximum_le_of_prefix_bound L U q hLU χ _
        (div_nonneg (mul_nonneg hC (Nat.cast_nonneg U)) (Real.rpow_nonneg hlogLpos.le A)) hprefix
    _ = _ := by ring

end Erdos964
