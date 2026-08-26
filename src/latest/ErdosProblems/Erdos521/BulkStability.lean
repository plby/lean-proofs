/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Almost-sure stability of the bulk root count across a degree block.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.AlmostSureRepulsion
import ErdosProblems.Erdos521.BulkComparison
import ErdosProblems.Erdos521.BulkParameters
import ErdosProblems.Erdos521.PolynomialTails
import ErdosProblems.Erdos521.EndpointLimit

namespace Erdos521

open MeasureTheory Filter

theorem endpointCenter_antitone_constant {C D : ℝ} (hCD : C ≤ D) {n : ℕ} (hn : 1 ≤ n) :
    endpointCenter D n ≤ endpointCenter C n := by
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h := mul_le_mul_of_nonneg_right hCD (div_nonneg hlog (Nat.cast_nonneg n))
  dsimp [endpointCenter]
  simp only [mul_div_assoc] at *
  linarith

theorem ae_bulk_stability :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ε ∂sequenceLaw, ∀ᶠ n : ℕ in atTop,
      ∀ m : ℕ, n ≤ m → m ≤ 2 * n →
        |(intervalRootCount ε m (9 / 10) (endpointCenter C n) : ℝ) -
          (intervalRootCount ε n (9 / 10) (endpointCenter C n) : ℝ)| ≤ 2 := by
  obtain ⟨C₀, hC₀, B, hB, hrep⟩ := ae_root_repulsion
  let C := 2 * C₀ + 4 * B + 8
  have hC : 0 < C := by dsimp [C]; positivity
  have hCC : 2 * C₀ ≤ C := by dsimp [C]; linarith
  have hCM : 1 - C ≤ -(4 * B + 6) := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [hrep, ae_sequence_signs] with ε hεrep hεsign
  have hε : ∀ k, |ε k| ≤ 1 := by
    intro k
    rcases hεsign k with h | h <;> simp [h]
  have hε₀ : ε 0 ≠ 0 := by rcases hεsign 0 with h | h <;> simp [h]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hεrep
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 2,
    eventually_bulk_parameters hB, eventually_polynomial_tail_le hC,
    eventually_endpointCenter_bounds hC] with n hnN hn₂ hnparams hntail hncenter
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  let δ := (n : ℝ) ^ (-2 * B)
  let ρ := (n : ℝ) ^ (-(2 * B + 4))
  let η := (n : ℝ) ^ (-(4 * B + 6))
  have hδ : 0 < δ := Real.rpow_pos_of_pos hn₀ _
  have hρ : 0 < ρ := Real.rpow_pos_of_pos hn₀ _
  have hI : Set.Icc (9 / 10 : ℝ) (endpointCenter C n) ⊆ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨by linarith [hx.1], hx.2.trans hncenter.2.le⟩
  have hrepblock (k : ℕ) (hnk : n ≤ k) (hkn : k ≤ 2 * n)
      (x : ℝ) (hx : x ∈ Set.Icc (9 / 10 : ℝ) (endpointCenter C n)) :
      δ < max |(polynomial ε k).eval x| |(polynomial ε k).derivative.eval x| := by
    have hcenter := (endpointCenter_antitone_constant hCC (by omega : 1 ≤ n)).trans
      (endpointCenter_block_le hC₀.le (by omega) hnk hkn)
    exact (block_repulsion_lower hB.le hn₂ hnk hkn).trans_lt
      (hN k (hnN.trans hnk) x ⟨hx.1, hx.2.trans hcenter⟩)
  intro m hnm hmn
  have hclose (x : ℝ) (hx : x ∈ Set.Icc (9 / 10 : ℝ) (endpointCenter C n)) :
      |(polynomial ε m).eval x - (polynomial ε n).eval x| ≤ η := by
    exact (hntail ε hε m hnm x ⟨by linarith [hx.1], hx.2⟩).trans
      (Real.rpow_le_rpow_of_exponent_le hn₁ hCM)
  have hnn : n ≤ 2 * n := by omega
  have hparamsn := hnparams n hnn
  have hparamsm := hnparams m hmn
  have hforward := intervalRootCount_le_of_repulsion ε hε hε₀ n m hI hδ hρ
    hparamsn.1 hparamsn.2.1 hparamsn.2.2 (hrepblock n le_rfl hnn) hclose
  have hback := intervalRootCount_le_of_repulsion ε hε hε₀ m n hI hδ hρ
    hparamsm.1 hparamsm.2.1 hparamsm.2.2 (hrepblock m hnm hmn)
    (fun x hx ↦ by simpa only [abs_sub_comm] using hclose x hx)
  have hforward' : (intervalRootCount ε n (9 / 10) (endpointCenter C n) : ℝ) ≤
      (intervalRootCount ε m (9 / 10) (endpointCenter C n) : ℝ) + 2 := by exact_mod_cast hforward
  have hback' : (intervalRootCount ε m (9 / 10) (endpointCenter C n) : ℝ) ≤
      (intervalRootCount ε n (9 / 10) (endpointCenter C n) : ℝ) + 2 := by exact_mod_cast hback
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos521
