import Arxiv.Arxiv2411_18291.PaperThresholdDensity
import Arxiv.Arxiv2411_18291.FiniteComplementDensity
import Arxiv.Arxiv2411_18291.AbsorberFromGenerators

/-! # Finite input bounds for the boost and nibble after removing the reserve and absorber -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem paperSizeThreshold_ge_square {q r : ℕ} (hqr : r < q) :
    (4 * q) ^ 2 ≤ paperSizeThreshold q r := by
  have hq : 0 < q := by omega
  have hprod : 1 ≤ q * paperInverseAlpha q r :=
    Nat.succ_le_of_lt (Nat.mul_pos hq (paperInverseAlpha_pos hqr))
  have hexp : 2 ≤ 90 * q * paperInverseAlpha q r := by
    rw [mul_assoc]
    omega
  exact Nat.pow_le_pow_right (by omega : 0 < 4 * q) hexp

theorem paperSizeThreshold_ge_double_rank {q r : ℕ} (hqr : r < q) :
    2 * r ≤ paperSizeThreshold q r := by
  calc
    _ ≤ 4 * q := by omega
    _ = (4 * q) * 1 := by ring
    _ ≤ (4 * q) * (4 * q) := Nat.mul_le_mul_left _ (by omega : 1 ≤ 4 * q)
    _ = (4 * q) ^ 2 := (pow_two _).symm
    _ ≤ _ := paperSizeThreshold_ge_square hqr

theorem boostComplementBound_lt_quarter {q : ℕ} (hq : 1 ≤ q) :
    boostComplementBound q < 1 / 4 := by
  have hp : (4 : ℝ) < (2 : ℝ) ^ (3 * q) := by
    have hnat : 8 ≤ 2 ^ (3 * q) :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ 3 * q)
    have hh : (8 : ℝ) ≤ (2 : ℝ) ^ (3 * q) := by exact_mod_cast hnat
    linarith only [hh]
  simpa only [boostComplementBound, one_div] using
    one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 4) hp

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem bounded_union_paper_threshold (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ Fintype.card V)
    (A R : Hypergraph V (r + 1))
    (hA : IsGraphBounded A ((Fintype.card V : ℝ) ^ (-(paperAlpha q (r + 1) / 4))))
    (hR : IsGraphBounded R ((Fintype.card V : ℝ) ^ (-paperRho q (r + 1)))) :
    IsGraphBounded (A ∪ R) (boostComplementBound q) := by
  apply (hA.union hR).mono
  simpa only [add_comm] using paper_threshold_reserve_absorber_density hqr hn

theorem paper_threshold_regular_host (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ Fintype.card V)
    (A R : Hypergraph V (r + 1))
    (hA : IsGraphBounded A ((Fintype.card V : ℝ) ^ (-(paperAlpha q (r + 1) / 4))))
    (hR : IsGraphBounded R ((Fintype.card V : ℝ) ^ (-paperRho q (r + 1)))) :
    let G := complete V (r + 1) \ (A ∪ R)
    IsGraphBounded (complete V (r + 1) \ G) (boostComplementBound q) ∧
      (1 / 2 : ℝ) * (Fintype.card V).choose (r + 1) < G.card := by
  let G := complete V (r + 1) \ (A ∪ R)
  have hcomp : complete V (r + 1) \ G = A ∪ R := by
    ext e
    simp [G, complete]
  have hb : IsGraphBounded (complete V (r + 1) \ G) (boostComplementBound q) := by
    rw [hcomp]
    exact bounded_union_paper_threshold hqr hn A R hA hR
  refine ⟨hb, dense_of_bounded_complement_finite hb ?_ ?_ ?_⟩
  · unfold boostComplementBound
    positivity
  · exact boostComplementBound_lt_quarter (by omega)
  · exact (paperSizeThreshold_ge_double_rank hqr).trans hn

end Arxiv2411_18291
