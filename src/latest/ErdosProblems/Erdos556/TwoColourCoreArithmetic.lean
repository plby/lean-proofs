import ErdosProblems.Erdos556.Basic

/-!
# The two-colour core edge-count calculation

At order close to four times the half-cycle length, stopped pruning in
both colours forces both cores to have order close to twice that length
and to miss only a small number of edges.
-/

namespace Erdos556

theorem core_quadratic_deficit (L b s : ℝ) (hL : 0 ≤ L)
    (hslo : L + b + 1 ≤ s) (hshi : s ≤ 2 * L + b) :
    L * (2 * L + b - s) ≤
      ((2 * L + b) ^ 2 - (2 * (L + b) + 1) * (2 * L + b)) -
        (s ^ 2 - (2 * (L + b) + 1) * s) := by
  have h := mul_nonneg (sub_nonneg.mpr hshi) (sub_nonneg.mpr hslo)
  nlinarith

theorem two_colour_core_capacity (L b N : ℝ) (hL : 0 ≤ L) (hb : 1 ≤ b)
    (hNlo : 4 * L - b ≤ N) (hNhi : N ≤ 4 * L) :
    4 * (L + b) * N +
      2 * ((2 * L + b) ^ 2 - (2 * (L + b) + 1) * (2 * L + b)) - N ^ 2 + N ≤ 24 * b * L := by
  have hδ0 : 0 ≤ 4 * (L + b) - N := by linarith
  have hδ : 4 * (L + b) - N ≤ 5 * b := by linarith
  have hmul := mul_le_mul hNhi hδ hδ0 (by positivity : (0 : ℝ) ≤ 4 * L)
  have hterm : 0 ≤ (2 * L + b) * (b + 1) := by positivity
  have hbL := mul_le_mul_of_nonneg_right hb hL
  nlinarith

theorem two_colour_core_size_and_missing_edges (L b N s t e f eS eT : ℝ)
    (hL : 0 < L) (hb : 1 ≤ b)
    (hNlo : 4 * L - b ≤ N) (hNhi : N ≤ 4 * L)
    (hslo : L + b + 1 ≤ s) (hshi : s ≤ 2 * L + b)
    (htlo : L + b + 1 ≤ t) (hthi : t ≤ 2 * L + b)
    (hcount : 2 * (e + f) = N * (N - 1))
    (he : e - (L + b) * N ≤ eS - (L + b) * s)
    (hf : f - (L + b) * N ≤ eT - (L + b) * t)
    (heS : 2 * eS ≤ s * (s - 1)) (heT : 2 * eT ≤ t * (t - 1)) :
    2 * L - 24 * b ≤ s ∧ 2 * L - 24 * b ≤ t ∧
      s * (s - 1) - 2 * eS ≤ 24 * b * L ∧ t * (t - 1) - 2 * eT ≤ 24 * b * L := by
  have hs := core_quadratic_deficit L b s hL.le hslo hshi
  have ht := core_quadratic_deficit L b t hL.le htlo hthi
  have hcap := two_colour_core_capacity L b N hL.le hb hNlo hNhi
  have htotal : L * (2 * L + b - s) + L * (2 * L + b - t) +
      (s * (s - 1) - 2 * eS) + (t * (t - 1) - 2 * eT) ≤ 24 * b * L := by
    nlinarith only [hs, ht, hcap, hcount, he, hf]
  have hsnon : 0 ≤ L * (2 * L + b - s) := mul_nonneg hL.le (sub_nonneg.mpr hshi)
  have htnon : 0 ≤ L * (2 * L + b - t) := mul_nonneg hL.le (sub_nonneg.mpr hthi)
  have hsbound : L * (2 * L + b - s) ≤ L * (24 * b) := by nlinarith only [htotal, htnon, heS, heT]
  have htbound : L * (2 * L + b - t) ≤ L * (24 * b) := by nlinarith only [htotal, hsnon, heS, heT]
  have hs' := (mul_le_mul_iff_right₀ hL).mp hsbound
  have ht' := (mul_le_mul_iff_right₀ hL).mp htbound
  refine ⟨by linarith, by linarith, ?_, ?_⟩ <;> nlinarith only [htotal, hsnon, htnon, heS, heT]

#print axioms two_colour_core_size_and_missing_edges

end Erdos556
