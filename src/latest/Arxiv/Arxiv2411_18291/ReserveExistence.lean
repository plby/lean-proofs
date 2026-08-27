import Arxiv.Arxiv2411_18291.ReserveCriterion
import Arxiv.Arxiv2411_18291.AsymptoticTypicality

/-!
# Eventual existence of the sparse reserve

Sample at one quarter of the target density. Typicality then gives strict
boundedness at the target density while the extra factor in the clique-count
exponent absorbs the fixed losses in the counting argument.
-/

open Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem reserve_size_scale {x : ℝ} (hx : 0 < x) (ρ : ℝ) (K : ℕ) :
    x * (x ^ (-ρ) / 8) ^ K / 4 = x ^ (1 - ρ * K) / (4 * 8 ^ K) := by
  rw [show 1 - ρ * K = 1 + (-ρ) * K by ring, Real.rpow_add hx,
    Real.rpow_one, Real.rpow_mul_natCast hx.le, div_pow]
  ring

/-- A reserve with strict `n^(-ρ)`-boundedness and the paper's clique-count
exponent exists for all sufficiently large `n`. No reserve is assumed. -/
theorem eventually_exists_reserve (q r : ℕ) (hqr : r + 1 ≤ q) {ρ : ℝ}
    (hρ : 0 < ρ) (hρK : ρ * q.choose (r + 1) < 1 / 4) :
    ∀ᶠ n : ℕ in atTop, ∃ R : Hypergraph (Fin n) (r + 1),
      IsGraphBounded R ((n : ℝ) ^ (-ρ)) ∧
      ∀ e : Block (Fin n) (r + 1),
        (n : ℝ) ^ (-((q.choose (r + 1) : ℝ) * ρ)) * (n : ℝ) ^ (q - (r + 1)) ≤
          (puncturedCliques R e q).card := by
  let K := q.choose (r + 1)
  let t := q - (r + 1)
  have hK : 1 ≤ K := Nat.choose_pos hqr
  have hexp : (2 * ρ) * K + 2 * (1 / 8 : ℝ) < 1 := by
    change ρ * K < 1 / 4 at hρK
    nlinarith
  have hgen := eventually_exists_typicalGraph r K hK (by positivity : 0 ≤ 2 * ρ)
    (by norm_num : (0 : ℝ) < 1 / 8) hexp
  have hzlim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-ρ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hρ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hclim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hTlim : Tendsto (fun n : ℕ => (4 + 2 * K * 2 ^ K : ℝ) *
      (n : ℝ) ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hclim.const_mul (4 + 2 * K * 2 ^ K : ℝ)
  have hslim : Tendsto (fun n : ℕ => (n : ℝ) ^ (-ρ) * 2 ^ t * 8 ^ (K - 1) *
      t.factorial) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      ((hzlim.mul_const ((2 : ℝ) ^ t)).mul_const ((8 : ℝ) ^ (K - 1))).mul_const (t.factorial : ℝ)
  have hgrowth : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 - ρ * K) / (4 * 8 ^ K)) atTop atTop :=
    Tendsto.atTop_div_const (by positivity)
      ((tendsto_rpow_atTop (by linarith : 0 < 1 - ρ * K)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [hgen, hzlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    hclim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
    hTlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4)),
    hslim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    hgrowth.eventually (eventually_ge_atTop (q : ℝ)), eventually_ge_atTop (1 : ℕ)] with
    n hgn hzn hcn hTn hsn hqn hn
  let z := (n : ℝ) ^ (-ρ)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : 0 < z := Real.rpow_pos_of_pos hnpos _
  have hzsmall : z < 1 / 4 := hzn
  let p : unitInterval := ⟨z / 4, by constructor <;> linarith⟩
  have hp : (n : ℝ) ^ (-(2 * ρ)) ≤ (p : ℝ) := by
    change (n : ℝ) ^ (-(2 * ρ)) ≤ z / 4
    calc
      _ = z ^ 2 := by
        rw [show -(2 * ρ) = (-ρ) * 2 by ring]
        simpa only [Nat.cast_ofNat, z] using Real.rpow_mul_natCast hnpos.le (-ρ) 2
      _ ≤ _ := by nlinarith
  obtain ⟨R, hd, hT⟩ := hgn p hp
  have hderr : |density R - z / 4| ≤ z / 8 := by
    change |density R - z / 4| ≤ (n : ℝ) ^ (-(1 / 8 : ℝ)) * (z / 4) at hd
    have hc := mul_le_mul_of_nonneg_right hcn.le (by positivity : 0 ≤ z / 4)
    nlinarith
  have hdlo : z / 8 ≤ density R := by have hl := (abs_le.mp hderr).1; linarith
  have hdhi : density R ≤ z / 2 := by have hu := (abs_le.mp hderr).2; linarith
  have hsize : (q : ℝ) ≤ Fintype.card (Fin n) * (z / 8) ^ K / 4 := by
    rw [Fintype.card_fin]
    change (q : ℝ) ≤ (n : ℝ) * ((n : ℝ) ^ (-ρ) / 8) ^ K / 4
    rw [reserve_size_scale hnpos]
    exact hqn
  have hs : z * 2 ^ t * 8 ^ (K - 1) * t.factorial ≤ 1 := hsn.le
  have hres := reserve_of_typical hT (q := q) le_rfl hTn.le hqr
    (by simpa only [Fintype.card_fin] using (show 0 < n by omega)) hz hdlo hdhi hsize hs
  have heq : z ^ K = (n : ℝ) ^ (-((K : ℝ) * ρ)) := by
    dsimp only [z]
    rw [← Real.rpow_mul_natCast hnpos.le]
    congr 1
    ring
  refine ⟨R, hres.1, fun e => ?_⟩
  simpa only [Fintype.card_fin, heq, K] using hres.2 e

/-- The reserve at the paper's choice `ρ = (6*choose q (r+1))^(-2)`.
The size threshold is eventual; the degree bound is strengthened to `n^(-ρ)`. -/
theorem eventually_exists_reserve_paper_parameters (q r : ℕ) (hqr : r + 1 < q) :
    let K := q.choose (r + 1)
    let ρ : ℝ := 1 / (6 * K : ℝ) ^ 2
    ∀ᶠ n : ℕ in atTop, ∃ R : Hypergraph (Fin n) (r + 1),
      IsGraphBounded R ((n : ℝ) ^ (-ρ)) ∧
      ∀ e : Block (Fin n) (r + 1),
        (n : ℝ) ^ (-((K : ℝ) * ρ)) * (n : ℝ) ^ (q - (r + 1)) ≤
          (puncturedCliques R e q).card := by
  dsimp only
  have hK : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast Nat.choose_pos hqr.le
  have hKpos : (0 : ℝ) < q.choose (r + 1) := by linarith
  apply eventually_exists_reserve q r hqr.le (by positivity)
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_lt_iff₀ (by positivity)).mpr
  have hsq := mul_le_mul_of_nonneg_left hK hKpos.le
  nlinarith

end Arxiv2411_18291
