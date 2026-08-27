import Arxiv.Arxiv2411_18291.CliqueCountEstimates
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Precise clique counts at polynomial density scales

Discharge the collision and accumulated-error conditions uniformly for
every graph of density at least `b*n^(-α)`. If `α*choose(q,r)+δ<1`,
typicality error `n^(-δ)` gives relative counting error `n^(-κ)` for every
fixed `κ<δ` and all sufficiently large ambient sizes.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

theorem clique_count_scale {x : ℝ} (hx : 0 < x) (b α δ : ℝ) (k : ℕ) :
    x ^ (-δ) * (x * (b * x ^ (-α)) ^ k) = b ^ k * x ^ (1 - δ - α * k) := by
  calc
    _ = b ^ k * (x ^ (-δ) * (x * (x ^ (-α)) ^ k)) := by rw [mul_pow]; ring
    _ = _ := by
      rw [show 1 - δ - α * k = -δ + (1 + (-α) * k) by ring,
        Real.rpow_add hx, Real.rpow_add hx, Real.rpow_one, Real.rpow_mul_natCast hx.le]

theorem eventually_precise_clique_numerics (q r : ℕ) {b α δ κ : ℝ}
    (hb : 0 < b) (hδ : 0 < δ) (hκδ : κ < δ) (hgap : α * q.choose (r + 1) + δ < 1) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ 2 * (n : ℝ) ^ (-δ) ≤ 1 ∧
      (2 * (n : ℝ) ^ (-δ)) * q * 2 ^ q ≤ (n : ℝ) ^ (-κ) ∧
      ∀ d : ℝ, b * (n : ℝ) ^ (-α) ≤ d →
        (q : ℝ) ≤ (n : ℝ) ^ (-δ) * (n * d ^ q.choose (r + 1)) := by
  have hηlim : Tendsto (fun n : ℕ => 2 * (n : ℝ) ^ (-δ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_rpow_neg_atTop hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul 2
  have hsmall := hηlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have herror := ((tendsto_rpow_atTop (by linarith : 0 < δ - κ)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop (2 * q * 2 ^ q : ℝ))
  have hlarge := ((tendsto_rpow_atTop (by linarith : 0 < 1 - δ - α * q.choose (r + 1))).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
      (eventually_ge_atTop ((q : ℝ) / b ^ q.choose (r + 1)))
  filter_upwards [eventually_ge_atTop (1 : ℕ), hsmall, herror, hlarge] with n hn hsn hen hln
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hc0 : 0 ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg hnpos.le _
  refine ⟨by omega, hsn.le, ?_, ?_⟩
  · calc
      _ = (2 * q * 2 ^ q : ℝ) * (n : ℝ) ^ (-δ) := by ring
      _ ≤ (n : ℝ) ^ (δ - κ) * (n : ℝ) ^ (-δ) :=
        mul_le_mul_of_nonneg_right hen hc0
      _ = _ := by rw [← Real.rpow_add hnpos]; congr 1; ring
  · intro d hd
    have hbase : (q : ℝ) ≤ b ^ q.choose (r + 1) *
        (n : ℝ) ^ (1 - δ - α * q.choose (r + 1)) := by
      have h := (div_le_iff₀ (pow_pos hb (q.choose (r + 1)))).mp hln
      simpa only [Function.comp_def, mul_comm] using h
    calc
      _ ≤ _ := hbase
      _ = (n : ℝ) ^ (-δ) * (n * (b * (n : ℝ) ^ (-α)) ^ q.choose (r + 1)) :=
        (clique_count_scale hnpos b α δ (q.choose (r + 1))).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg hb.le (Real.rpow_nonneg hnpos.le _)) hd _) hnpos.le) hc0

theorem eventually_rootedClique_relative_error (q r h : ℕ) (hqh : q.choose (r + 1) ≤ h)
    {b α δ κ : ℝ} (hb : 0 < b) (hδ : 0 < δ) (hκδ : κ < δ)
    (hgap : α * q.choose (r + 1) + δ < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-δ)) h → b * (n : ℝ) ^ (-α) ≤ density K →
      ∀ a, ∀ I : Block (Fin n) a, a ≤ q →
        |((rootedCliques K I q).card : ℝ) - cliqueMainTerm n (density K) q (r + 1) a| ≤
          (n : ℝ) ^ (-κ) * cliqueMainTerm n (density K) q (r + 1) a := by
  filter_upwards [eventually_precise_clique_numerics q r hb hδ hκδ hgap] with n hn
  intro K hT hd a I haq
  have hc0 : 0 ≤ (n : ℝ) ^ (-δ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hsize : (q : ℝ) ≤ (2 * (n : ℝ) ^ (-δ) - (n : ℝ) ^ (-δ)) *
      (Fintype.card (Fin n) * density K ^ q.choose (r + 1)) := by
    rw [Fintype.card_fin, show 2 * (n : ℝ) ^ (-δ) - (n : ℝ) ^ (-δ) =
      (n : ℝ) ^ (-δ) by ring]
    exact hn.2.2.2 (density K) hd
  have hc := hT.rootedCliques_relative hqh (by linarith) (by positivity) hn.2.1 hsize I haq
  simp only [Fintype.card_fin] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right hn.2.2.1
    (cliqueMainTerm_nonneg (Nat.cast_nonneg _) (density_nonneg K) q (r + 1) a))

end Arxiv2411_18291
