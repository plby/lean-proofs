import Arxiv.Arxiv2411_18291.FiniteFlatteningRound
import Arxiv.Arxiv2411_18291.SmallCarrierExchange
import Arxiv.Arxiv2411_18291.FiniteFlatteningIterations
import Arxiv.Arxiv2411_18291.CliqueMultiplicityBound

/-!
# Sparse flattening with an explicit valid size bound

The paper threshold handles each individual round. A separate, explicit
iteration-cost threshold accounts for their accumulated density loss.
The output preserves every generated integral vector and has multiplicity 16.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_flattening_of_iteration_bound {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hcost : ∃ k : ℕ, (flatteningStep^[k]) n ≤ 16 ∧
      (flatteningRoundConstant q r : ℝ) ^ k ≤ (n : ℝ) ^ (paperAlpha q (r + 1) / 10))
    (D : Finset (Block (Fin n) q))
    (hD : IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)))) :
    ∃ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))) ∧
      (∀ J : Block (Fin n) (r + 1) → ℤ, GeneratedBy D J → GeneratedBy F J) ∧
      ∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤ 16 := by
  obtain ⟨S, A, hS, hA, _, _, hwS⟩ :=
    exists_small_carrier_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨E, N, e₀, hpair, hE, hwE⟩ := exists_small_carrier_elimination_pattern q r hqr
  let C : ℝ := flatteningRoundConstant q r
  let α := paperAlpha q (r + 1)
  let ρ := 3 * α / 5
  let η := α / 2
  have hC : 1 ≤ C := by dsimp only [C]; exact_mod_cast flatteningRoundConstant_pos q r
  have hα : 0 < α := paperAlpha_pos hqr
  have hn16 : 16 ≤ n := by
    have hq : 2 ≤ q := by omega
    calc
      16 ≤ (4 * q) ^ 2 := by nlinarith only [hq]
      _ ≤ (4 * q) ^ (90 * q) := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ n := (boost_threshold_le_paper_threshold hqr).trans hn
  obtain ⟨k, hstop, hcost⟩ := hcost
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hθ : 0 ≤ (n : ℝ) ^ (-ρ) := Real.rpow_nonneg hnpos.le _
  have htotal : C ^ k * (n : ℝ) ^ (-ρ) ≤ (n : ℝ) ^ (-η) := by
    calc
      _ ≤ (n : ℝ) ^ (α / 10) * (n : ℝ) ^ (-ρ) :=
        mul_le_mul_of_nonneg_right hcost hθ
      _ = _ := by rw [← Real.rpow_add hnpos]; congr 1; dsimp only [ρ, η]; ring
  have hmult (e : Block (Fin n) (r + 1)) : (D.filter fun Q => e.val ⊆ Q.val).card ≤ n := by
    have hθ1 : (n : ℝ) ^ (-ρ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast (show 1 ≤ n by omega)) (by dsimp only [ρ]; linarith only [hα])
    have hbound := (hD.multiplicity_lt e).le.trans
      (mul_le_mul_of_nonneg_right hθ1 (Nat.cast_nonneg (Fintype.card (Fin n))))
    simpa only [Fintype.card_fin, one_mul, Nat.cast_le] using hbound
  have hiter (j : ℕ) : j ≤ k → ∃ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F (C ^ j * (n : ℝ) ^ (-ρ)) ∧
        (∀ J : Block (Fin n) (r + 1) → ℤ, GeneratedBy D J → GeneratedBy F J) ∧
        ∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤
          (flatteningStep^[j]) n := by
    induction j with
    | zero =>
      intro _
      exact ⟨D, by simpa only [pow_zero, one_mul] using hD,
        fun _ h => h, by simpa only [Function.iterate_zero_apply] using hmult⟩
    | succ j ih =>
      intro hj
      obtain ⟨F, hF, hgen, hm⟩ := ih (by omega)
      have hlo : (n : ℝ) ^ (-ρ) ≤ C ^ j * (n : ℝ) ^ (-ρ) := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (one_le_pow₀ hC) hθ
      have hhi : C ^ j * (n : ℝ) ^ (-ρ) ≤ (n : ℝ) ^ (-η) :=
        (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC (show j ≤ k by omega)) hθ).trans htotal
      obtain ⟨F', hF', hgen', hm'⟩ := exists_uniform_flattening_round_paper_threshold
        S.system hA E.system N e₀ hpair hqr hn hwS hwE hS hE hlo hhi
        ((flatteningStep^[j]) n) (iterate_flatteningStep_le_initial hn16 j) F hF hm
      refine ⟨F', ?_, fun J hJ => hgen' J (hgen J hJ), ?_⟩
      · convert hF' using 1
        rw [pow_succ]
        ring
      · simpa only [Function.iterate_succ_apply'] using hm'
  obtain ⟨F, hF, hgen, hm⟩ := hiter k le_rfl
  exact ⟨F, hF.mono htotal, hgen, fun e => (hm e).trans hstop⟩

/-- This explicit threshold includes the accumulated iteration cost; it is
not asserted to be bounded by the paper's smaller printed threshold. -/
def finiteFlatteningThreshold (q r : ℕ) : ℕ :=
  max (paperSizeThreshold q (r + 1))
    (flatteningCostThreshold (flatteningRoundConstant q r) (paperAlpha q (r + 1) / 10))

theorem exists_sparse_flattening_explicit {q r n : ℕ} (hqr : r + 1 < q)
    (hn : finiteFlatteningThreshold q r ≤ n) (D : Finset (Block (Fin n) q))
    (hD : IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)))) :
    ∃ F : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r F ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))) ∧
      (∀ J : Block (Fin n) (r + 1) → ℤ, GeneratedBy D J → GeneratedBy F J) ∧
      ∀ e : Block (Fin n) (r + 1), (F.filter fun Q => e.val ⊆ Q.val).card ≤ 16 := by
  have hpaper : paperSizeThreshold q (r + 1) ≤ n := (le_max_left _ _).trans hn
  have hcost : flatteningCostThreshold (flatteningRoundConstant q r)
      (paperAlpha q (r + 1) / 10) ≤ n := (le_max_right _ _).trans hn
  have hC : (1 : ℝ) ≤ flatteningRoundConstant q r := by
    exact_mod_cast flatteningRoundConstant_pos q r
  have hα : 0 < paperAlpha q (r + 1) / 10 := div_pos (paperAlpha_pos hqr) (by norm_num)
  exact exists_sparse_flattening_of_iteration_bound hqr hpaper
    (exists_flattening_iterations_explicit hC hα hcost) D hD

end Arxiv2411_18291
