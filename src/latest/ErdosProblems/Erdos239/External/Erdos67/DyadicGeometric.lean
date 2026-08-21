import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

/-!
# Summing dyadic power-saving blocks

This elementary lemma packages the geometric summation used by the
fixed-depth Weyl argument.  A norm bound `C X⁻ᵟ` for every interval
`(X,B]`, `B ≤ 2X`, gives the same order of bound for an arbitrary tail,
with the exact geometric factor `(1 - 2⁻ᵟ)⁻¹`.
-/

open scoped BigOperators

namespace Erdos67.DyadicGeometric

noncomputable section

theorem norm_sum_Ioc_le_of_dyadic_powerSaving
    (f : ℕ → ℂ) {M H : ℕ} (hM : 0 < M)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ)
    (hblock : ∀ (X B : ℕ), 0 < X → X < B → B ≤ 2 * X →
      ‖∑ n ∈ Finset.Ioc X B, f n‖ ≤ C * (X : ℝ) ^ (-δ)) :
    ‖∑ n ∈ Finset.Ioc M H, f n‖ ≤
      C * (M : ℝ) ^ (-δ) / (1 - (2 : ℝ) ^ (-δ)) := by
  have hq0 : 0 < (2 : ℝ) ^ (-δ) := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : (2 : ℝ) ^ (-δ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hδ)
  have hden : 0 < 1 - (2 : ℝ) ^ (-δ) := sub_pos.mpr hq1
  have hgeom (X : ℕ) (hX : 0 < X) :
      C * (X : ℝ) ^ (-δ) +
          C * ((2 * X : ℕ) : ℝ) ^ (-δ) /
            (1 - (2 : ℝ) ^ (-δ)) =
        C * (X : ℝ) ^ (-δ) / (1 - (2 : ℝ) ^ (-δ)) := by
    have hcast : (((2 * X : ℕ) : ℝ)) = 2 * (X : ℝ) := by norm_num
    rw [hcast, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
      (by positivity : (0 : ℝ) ≤ X)]
    field_simp
    ring
  generalize hd : H - M = d
  induction d using Nat.strong_induction_on generalizing M H with
  | h d ih =>
      by_cases hHM : H ≤ M
      · rw [Finset.Ioc_eq_empty_of_le hHM, Finset.sum_empty, norm_zero]
        exact div_nonneg
          (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg M) _)) hden.le
      · have hMH : M < H := lt_of_not_ge hHM
        by_cases hHtwo : H ≤ 2 * M
        · have hb := hblock M H hM hMH hHtwo
          calc
            ‖∑ n ∈ Finset.Ioc M H, f n‖ ≤
                C * (M : ℝ) ^ (-δ) := hb
            _ ≤ C * (M : ℝ) ^ (-δ) /
                (1 - (2 : ℝ) ^ (-δ)) := by
              apply (le_div_iff₀ hden).2
              have hnum : 0 ≤ C * (M : ℝ) ^ (-δ) :=
                mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg M) _)
              nlinarith
        · have htwoH : 2 * M < H := lt_of_not_ge hHtwo
          have htwoPos : 0 < 2 * M := by positivity
          have hdiff : H - 2 * M < d := by omega
          have hrec := ih (H - 2 * M) hdiff
            (M := 2 * M) (H := H) htwoPos rfl
          have hunion : Finset.Ioc M (2 * M) ∪ Finset.Ioc (2 * M) H =
              Finset.Ioc M H :=
            Finset.Ioc_union_Ioc_eq_Ioc (by omega) htwoH.le
          have hdis : Disjoint (Finset.Ioc M (2 * M))
              (Finset.Ioc (2 * M) H) :=
            Finset.Ioc_disjoint_Ioc_of_le le_rfl
          have hsplit :
              (∑ n ∈ Finset.Ioc M H, f n) =
                (∑ n ∈ Finset.Ioc M (2 * M), f n) +
                  ∑ n ∈ Finset.Ioc (2 * M) H, f n := by
            rw [← hunion, Finset.sum_union hdis]
          rw [hsplit]
          calc
            ‖(∑ n ∈ Finset.Ioc M (2 * M), f n) +
                ∑ n ∈ Finset.Ioc (2 * M) H, f n‖ ≤
                ‖∑ n ∈ Finset.Ioc M (2 * M), f n‖ +
                  ‖∑ n ∈ Finset.Ioc (2 * M) H, f n‖ := norm_add_le _ _
            _ ≤ C * (M : ℝ) ^ (-δ) +
                C * ((2 * M : ℕ) : ℝ) ^ (-δ) /
                  (1 - (2 : ℝ) ^ (-δ)) :=
              add_le_add (hblock M (2 * M) hM (by omega) le_rfl) hrec
            _ = C * (M : ℝ) ^ (-δ) /
                (1 - (2 : ℝ) ^ (-δ)) := hgeom M hM

/-- A uniform bound for dyadic blocks accumulates at most once per binary
scale.  The exact natural logarithmic count is convenient when the block
bound is chosen after an epsilon. -/
theorem norm_sum_Ioc_le_log_mul_of_dyadic_bound
    (f : ℕ → ℂ) {M H : ℕ} (hM : 0 < M)
    {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ (X Y : ℕ), 0 < X → X < Y → Y ≤ 2 * X →
      ‖∑ n ∈ Finset.Ioc X Y, f n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc M H, f n‖ ≤
      ((Nat.log 2 H - Nat.log 2 M + 1 : ℕ) : ℝ) * B := by
  generalize hd : H - M = d
  induction d using Nat.strong_induction_on generalizing M H with
  | h d ih =>
      by_cases hHM : H ≤ M
      · rw [Finset.Ioc_eq_empty_of_le hHM, Finset.sum_empty, norm_zero]
        positivity
      · have hMH : M < H := lt_of_not_ge hHM
        have hlogMH : Nat.log 2 M ≤ Nat.log 2 H :=
          Nat.log_mono_right hMH.le
        by_cases hHtwo : H ≤ 2 * M
        · have hb := hblock M H hM hMH hHtwo
          calc
            ‖∑ n ∈ Finset.Ioc M H, f n‖ ≤ B := hb
            _ ≤ ((Nat.log 2 H - Nat.log 2 M + 1 : ℕ) : ℝ) * B := by
              have hone : 1 ≤ Nat.log 2 H - Nat.log 2 M + 1 := by omega
              have honeR : (1 : ℝ) ≤
                  (Nat.log 2 H - Nat.log 2 M + 1 : ℕ) := by
                exact_mod_cast hone
              nlinarith
        · have htwoH : 2 * M < H := lt_of_not_ge hHtwo
          have htwoPos : 0 < 2 * M := by positivity
          have hdiff : H - 2 * M < d := by omega
          have hrec := ih (H - 2 * M) hdiff
            (M := 2 * M) (H := H) htwoPos rfl
          have hunion : Finset.Ioc M (2 * M) ∪ Finset.Ioc (2 * M) H =
              Finset.Ioc M H :=
            Finset.Ioc_union_Ioc_eq_Ioc (by omega) htwoH.le
          have hdis : Disjoint (Finset.Ioc M (2 * M))
              (Finset.Ioc (2 * M) H) :=
            Finset.Ioc_disjoint_Ioc_of_le le_rfl
          have hsplit :
              (∑ n ∈ Finset.Ioc M H, f n) =
                (∑ n ∈ Finset.Ioc M (2 * M), f n) +
                  ∑ n ∈ Finset.Ioc (2 * M) H, f n := by
            rw [← hunion, Finset.sum_union hdis]
          have hlogTwo : Nat.log 2 (2 * M) = Nat.log 2 M + 1 := by
            rw [show 2 * M = M * 2 by omega, Nat.log_mul_base]
            · norm_num
            · omega
          have hlogTwoH : Nat.log 2 (2 * M) ≤ Nat.log 2 H :=
            Nat.log_mono_right htwoH.le
          rw [hsplit]
          calc
            ‖(∑ n ∈ Finset.Ioc M (2 * M), f n) +
                ∑ n ∈ Finset.Ioc (2 * M) H, f n‖ ≤
                ‖∑ n ∈ Finset.Ioc M (2 * M), f n‖ +
                  ‖∑ n ∈ Finset.Ioc (2 * M) H, f n‖ := norm_add_le _ _
            _ ≤ B +
                ((Nat.log 2 H - Nat.log 2 (2 * M) + 1 : ℕ) : ℝ) * B :=
              add_le_add (hblock M (2 * M) hM (by omega) le_rfl) hrec
            _ = ((Nat.log 2 H - Nat.log 2 M + 1 : ℕ) : ℝ) * B := by
              rw [hlogTwo]
              have : Nat.log 2 M + 1 ≤ Nat.log 2 H := by
                simpa only [hlogTwo] using hlogTwoH
              have hn :
                  1 + (Nat.log 2 H - (Nat.log 2 M + 1) + 1) =
                    Nat.log 2 H - Nat.log 2 M + 1 := by omega
              calc
                B +
                    ((Nat.log 2 H - (Nat.log 2 M + 1) + 1 : ℕ) : ℝ) * B =
                    ((1 + (Nat.log 2 H - (Nat.log 2 M + 1) + 1) : ℕ) : ℝ) *
                      B := by push_cast; ring
                _ = ((Nat.log 2 H - Nat.log 2 M + 1 : ℕ) : ℝ) * B := by
                  rw [hn]

/-- The binary natural logarithm is bounded by the real logarithm with the
usual change of base. -/
theorem natLog_two_le_realLog_div {H : ℕ} (hH : 0 < H) :
    (Nat.log 2 H : ℝ) ≤ Real.log H / Real.log 2 := by
  have hpow : 2 ^ Nat.log 2 H ≤ H := Nat.pow_log_le_self 2 hH.ne'
  have hpowPos : (0 : ℝ) < (2 ^ Nat.log 2 H : ℕ) := by positivity
  have hpowR : ((2 ^ Nat.log 2 H : ℕ) : ℝ) ≤ H := by
    exact_mod_cast hpow
  have hlog := Real.log_le_log hpowPos hpowR
  have hlogPow : Real.log ((2 ^ Nat.log 2 H : ℕ) : ℝ) =
      (Nat.log 2 H : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [hlogPow] at hlog
  exact (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2 hlog

/-- Bounded-range version of the logarithmic dyadic summation lemma.  Only
blocks which actually lie between the target endpoints are assumed. -/
theorem norm_sum_Ioc_le_log_mul_of_dyadic_bound_on
    (f : ℕ → ℂ) {M H : ℕ} (hM : 0 < M)
    {B : ℝ} (hB : 0 ≤ B)
    (hblock : ∀ (X Y : ℕ), M ≤ X → Y ≤ H →
      0 < X → X < Y → Y ≤ 2 * X →
      ‖∑ n ∈ Finset.Ioc X Y, f n‖ ≤ B) :
    ‖∑ n ∈ Finset.Ioc M H, f n‖ ≤
      ((Nat.log 2 H - Nat.log 2 M + 1 : ℕ) : ℝ) * B := by
  generalize hd : H - M = d
  induction d using Nat.strong_induction_on generalizing M H with
  | h d ih =>
      by_cases hHM : H ≤ M
      · rw [Finset.Ioc_eq_empty_of_le hHM, Finset.sum_empty, norm_zero]
        positivity
      · have hMH : M < H := lt_of_not_ge hHM
        have hlogMH : Nat.log 2 M ≤ Nat.log 2 H :=
          Nat.log_mono_right hMH.le
        by_cases hHtwo : H ≤ 2 * M
        · have hb := hblock M H le_rfl le_rfl hM hMH hHtwo
          calc
            ‖∑ n ∈ Finset.Ioc M H, f n‖ ≤ B := hb
            _ ≤ ((Nat.log 2 H - Nat.log 2 M + 1 : ℕ) : ℝ) * B := by
              have hone : 1 ≤ Nat.log 2 H - Nat.log 2 M + 1 := by omega
              have honeR : (1 : ℝ) ≤
                  (Nat.log 2 H - Nat.log 2 M + 1 : ℕ) := by
                exact_mod_cast hone
              nlinarith
        · have htwoH : 2 * M < H := lt_of_not_ge hHtwo
          have htwoPos : 0 < 2 * M := by positivity
          have hdiff : H - 2 * M < d := by omega
          have hrec := ih (H - 2 * M) hdiff
            (M := 2 * M) (H := H) htwoPos
            (fun X Y hMX hYH hX hXY hYtwo ↦
              hblock X Y (by omega) hYH hX hXY hYtwo) rfl
          have hunion : Finset.Ioc M (2 * M) ∪ Finset.Ioc (2 * M) H =
              Finset.Ioc M H :=
            Finset.Ioc_union_Ioc_eq_Ioc (by omega) htwoH.le
          have hdis : Disjoint (Finset.Ioc M (2 * M))
              (Finset.Ioc (2 * M) H) :=
            Finset.Ioc_disjoint_Ioc_of_le le_rfl
          have hsplit :
              (∑ n ∈ Finset.Ioc M H, f n) =
                (∑ n ∈ Finset.Ioc M (2 * M), f n) +
                  ∑ n ∈ Finset.Ioc (2 * M) H, f n := by
            rw [← hunion, Finset.sum_union hdis]
          have hlogTwo : Nat.log 2 (2 * M) = Nat.log 2 M + 1 := by
            rw [show 2 * M = M * 2 by omega, Nat.log_mul_base]
            · norm_num
            · omega
          rw [hsplit]
          calc
            ‖(∑ n ∈ Finset.Ioc M (2 * M), f n) +
                ∑ n ∈ Finset.Ioc (2 * M) H, f n‖ ≤
                ‖∑ n ∈ Finset.Ioc M (2 * M), f n‖ +
                  ‖∑ n ∈ Finset.Ioc (2 * M) H, f n‖ := norm_add_le _ _
            _ ≤ B +
                ((Nat.log 2 H - Nat.log 2 (2 * M) + 1 : ℕ) : ℝ) * B :=
              add_le_add
                (hblock M (2 * M) le_rfl htwoH.le hM (by omega) le_rfl)
                hrec
            _ = ((Nat.log 2 H - Nat.log 2 M + 1 : ℕ) : ℝ) * B := by
              rw [hlogTwo]
              have hh : Nat.log 2 M + 1 ≤ Nat.log 2 H := by
                have hmono : Nat.log 2 (2 * M) ≤ Nat.log 2 H :=
                  Nat.log_mono_right htwoH.le
                simpa only [hlogTwo] using hmono
              have hn :
                  1 + (Nat.log 2 H - (Nat.log 2 M + 1) + 1) =
                    Nat.log 2 H - Nat.log 2 M + 1 := by omega
              calc
                B +
                    ((Nat.log 2 H - (Nat.log 2 M + 1) + 1 : ℕ) : ℝ) * B =
                    ((1 + (Nat.log 2 H - (Nat.log 2 M + 1) + 1) : ℕ) : ℝ) *
                      B := by push_cast; ring
                _ = ((Nat.log 2 H - Nat.log 2 M + 1 : ℕ) : ℝ) * B := by
                  rw [hn]

end

end Erdos67.DyadicGeometric
