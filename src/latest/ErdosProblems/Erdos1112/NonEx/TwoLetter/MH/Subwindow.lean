/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- Copyright 2026 Johan Land.
Licensed under the Apache License, Version 2.0; see LICENSE and NOTICE.
Modified for this repository and Lean/Mathlib 4.33.0. -/
/-
Erdős Problem 1112.
Informal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
Formal proof: Johan Land, using Claude Fable 5 and Claude Opus 4.8.
GPT-5.5 and Gemini 3.1 supplied advice and adversarial review.
Source: https://www.erdosproblems.com/1112#post-7375
https://github.com/beetree/math_erdos_1112/tree/63ed94d3e802782aeb521095c17d6109a2dc57b5
Original Lean version: 4.27.0.
Original Mathlib commit: a3a10db0e9d66acbebf76c5e6a135066525ac900.
-/
/-
Morse–Hedlund, stage 5: paper the corresponding paper lemma Steps 0+2
(the sub-window claim), with Step 1 (uniform syndeticity) taken as a
hypothesis to avoid an import cycle with `Sturmian.lean` (dependency
inversion; `Sturmian.lean` instantiates `hsyn` with `uniform_syndeticity`).

Follows (2.10.1)–(2.10.6) literally: for `s ≥ S₀ := 2k²L + 1` and any integer
`w` at depth `θ := sα + kβ − w ∈ [η, k−η]`, pick `κ := η/4`, the interval
`I := (max 0 (θ−1) + κ, min (k−1) θ − κ)` (nonempty of length ≥ η/2 in each
of the three θ-regimes), its midpoint `T*`, the arc
`J := ((T*−κ)/(k−1), (T*+κ)/(k−1)) ⊆ (0,1)` of length `η/(2(k−1))`; one free
index per block `(jL, (j+1)L]` via `hsyn`, forced last index
`i_k := s − ∑`; the fractional sum `Θ` lies in `(θ−1, θ+1) ∩ (θ+ℤ) = {θ}`
(the mod-1 pinning), which converts to `∑ q(i_t) = w` by the exact
mechanical form.
-/
import ErdosProblems.Erdos1112.NonEx.TwoLetter.Core

namespace Erdos1112
namespace Proof
namespace MH

/-- **Sub-window claim** (paper 2.10 Step 2).  Route:
choice over blocks via `choose`; sum splitting via `Fin.snoc`,
`Fin.sum_univ_castSucc`; pinning via "integer in `(−1,1)` is `0`". -/
theorem subwindow (h : ℕ → Bool) {α β : ℝ}
    (hmech : ∀ n : ℕ, (qCount h n : ℤ) = ⌊(n : ℝ) * α + β⌋)
    {k : ℕ} (hk : 3 ≤ k) {η : ℝ} (hη0 : 0 < η) (hη8 : η ≤ 1 / 8)
    (L : ℕ)
    (hsyn : ∀ (u : ℝ) (N : ℕ), u + η / (2 * ((k : ℝ) - 1)) ≤ 1 → 0 ≤ u →
      ∃ n, N < n ∧ n ≤ N + L ∧
        Int.fract ((n : ℝ) * α + β) ∈ Set.Ioo u (u + η / (2 * ((k : ℝ) - 1)))) :
    ∃ S₀ : ℕ, ∀ s : ℕ, S₀ ≤ s → ∀ w : ℤ,
      η ≤ (s : ℝ) * α + k * β - w → (s : ℝ) * α + k * β - w ≤ k - η →
      ∃ f : Fin k → ℕ, (∀ j, 1 ≤ f j) ∧ (∑ j, f j) = s ∧
        (∑ j, (qCount h (f j) : ℤ)) = w := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hm2 : 2 ≤ m := by omega
  have hmR2 : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hmRpos : (0 : ℝ) < m := by linarith
  have hmp1 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
  set κ : ℝ := η / 4 with hκ
  have hκ0 : 0 < κ := by rw [hκ]; linarith
  set W : ℝ := η / (2 * (((m + 1 : ℕ) : ℝ) - 1)) with hW
  have hWeq : W = η / (2 * (m : ℝ)) := by rw [hW, hmp1]; ring_nf
  have hW0 : 0 < W := by rw [hWeq]; positivity
  have hmW : (m : ℝ) * W = 2 * κ := by rw [hWeq, hκ]; field_simp; ring
  refine ⟨(m + 1) * (m + 1) * L + 1, fun s hs w hθlo hθhi => ?_⟩
  set θ : ℝ := (s : ℝ) * α + ((m + 1 : ℕ) : ℝ) * β - w with hθ
  have hθlo' : η ≤ θ := hθlo
  have hθhi' : θ ≤ (m : ℝ) + 1 - η := by rw [hmp1] at hθhi; exact hθhi
  -- the interval `(max 0 (θ-1)+κ, min m θ − κ)` is nonempty
  have hnonempty : max 0 (θ - 1) + κ < min (m : ℝ) θ - κ := by
    have hlt_θ : max 0 (θ - 1) < θ - 2 * κ :=
      max_lt (by rw [hκ]; linarith) (by rw [hκ]; linarith)
    have hlt_mR : max 0 (θ - 1) < (m : ℝ) - 2 * κ :=
      max_lt (by rw [hκ]; linarith) (by rw [hκ]; linarith)
    have : max 0 (θ - 1) + 2 * κ < min (m : ℝ) θ := lt_min (by linarith) (by linarith)
    linarith
  obtain ⟨Tstar, hTlo, hThi⟩ := exists_between hnonempty
  have hTκ0 : 0 ≤ Tstar - κ := by have := le_max_left 0 (θ - 1); linarith
  have hTκmR : Tstar + κ ≤ (m : ℝ) := by have := min_le_left (m : ℝ) θ; linarith
  set u : ℝ := (Tstar - κ) / m with hu
  have hu0 : 0 ≤ u := by rw [hu]; positivity
  have huW : u + W ≤ 1 := by
    rw [hu, hWeq, div_add_div _ _ (ne_of_gt hmRpos) (by positivity),
      div_le_one (by positivity)]
    nlinarith [hTκmR, hmRpos]
  -- choose one index per disjoint length-`L` block, fract in the arc `(u, u+W)`
  have hchoose : ∀ j : Fin m, ∃ n, j.val * L < n ∧ n ≤ j.val * L + L ∧
      Int.fract ((n : ℝ) * α + β) ∈ Set.Ioo u (u + W) :=
    fun j => hsyn u (j.val * L) huW hu0
  choose idx hidxlo hidxhi hidxfr using hchoose
  have hidxbd : ∀ j : Fin m, idx j ≤ m * L := by
    intro j
    have h1 := hidxhi j
    have h2 : j.val * L + L ≤ m * L := by
      have h3 : (j.val + 1) * L ≤ m * L := by gcongr; omega
      have h4 : (j.val + 1) * L = j.val * L + L := by ring
      omega
    omega
  have hsum_le : (∑ j, idx j) ≤ m * (m * L) := by
    calc (∑ j : Fin m, idx j) ≤ ∑ _j : Fin m, m * L := Finset.sum_le_sum (fun j _ => hidxbd j)
      _ = m * (m * L) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
  have hbd : m * (m * L) ≤ (m + 1) * (m + 1) * L := by
    rw [show m * (m * L) = m * m * L from by ring]; gcongr <;> omega
  set ik : ℕ := s - ∑ j, idx j with hik
  have hik1 : 1 ≤ ik := by rw [hik]; omega
  set f : Fin (m + 1) → ℕ := Fin.snoc idx ik with hf
  refine ⟨f, ?_, ?_, ?_⟩
  · -- each index ≥ 1
    intro t
    refine Fin.lastCases ?_ ?_ t
    · rw [hf, Fin.snoc_last]; exact hik1
    · intro j; rw [hf, Fin.snoc_castSucc]; have := hidxlo j; omega
  · -- sum = s
    rw [hf, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    rw [hik]; omega
  · -- `∑ q = w`, by fract-sum pinning
    set x : Fin (m + 1) → ℝ := fun t => (f t : ℝ) * α + β with hx
    have hfsum : (∑ t, f t) = s := by
      rw [hf, Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]; rw [hik]; omega
    have hfr_j : ∀ j : Fin m, x (Fin.castSucc j) = (idx j : ℝ) * α + β := by
      intro j; simp only [hx, hf, Fin.snoc_castSucc]
    have hne : (Finset.univ : Finset (Fin m)).Nonempty := ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    have hmu : (m : ℝ) * u = Tstar - κ := by rw [hu]; field_simp
    have hmuW : (m : ℝ) * (u + W) = Tstar + κ := by rw [mul_add, hmu, hmW]; ring
    have hΘsplit : (∑ t, Int.fract (x t))
        = (∑ j, Int.fract (x (Fin.castSucc j))) + Int.fract (x (Fin.last m)) :=
      Fin.sum_univ_castSucc _
    have hfr_lo : (m : ℝ) * u < ∑ j, Int.fract (x (Fin.castSucc j)) := by
      calc (m : ℝ) * u = ∑ _j : Fin m, u := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ < ∑ j, Int.fract (x (Fin.castSucc j)) :=
              Finset.sum_lt_sum_of_nonempty hne (fun j _ => by rw [hfr_j]; exact (hidxfr j).1)
    have hfr_hi : (∑ j, Int.fract (x (Fin.castSucc j))) < (m : ℝ) * (u + W) := by
      calc (∑ j, Int.fract (x (Fin.castSucc j)))
            < ∑ _j : Fin m, (u + W) :=
              Finset.sum_lt_sum_of_nonempty hne (fun j _ => by rw [hfr_j]; exact (hidxfr j).2)
        _ = (m : ℝ) * (u + W) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hik_fr0 : 0 ≤ Int.fract (x (Fin.last m)) := Int.fract_nonneg _
    have hik_fr1 : Int.fract (x (Fin.last m)) < 1 := Int.fract_lt_one _
    have hΘlo : θ - 1 < ∑ t, Int.fract (x t) := by
      rw [hΘsplit]; linarith [hfr_lo, hmu, hik_fr0, hTlo, le_max_right (0 : ℝ) (θ - 1)]
    have hΘhi : (∑ t, Int.fract (x t)) < θ + 1 := by
      rw [hΘsplit]; linarith [hfr_hi, hmuW, hik_fr1, hThi, min_le_right (m : ℝ) θ]
    have hxsum : (∑ t, x t) = θ + w := by
      simp only [hx]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      rw [show (∑ t, (f t : ℝ)) = ((s : ℕ) : ℝ) from by rw [← Nat.cast_sum, hfsum]]
      rw [hθ]; push_cast; ring
    have hfloorsum : ((∑ t, ⌊x t⌋ : ℤ) : ℝ) = θ + w - ∑ t, Int.fract (x t) := by
      rw [Int.cast_sum,
        Finset.sum_congr rfl (fun t _ => by
          change ((⌊x t⌋ : ℤ) : ℝ) = x t - Int.fract (x t)
          linarith [Int.floor_add_fract (x t)]),
        Finset.sum_sub_distrib, hxsum]
    have hq_eq : (∑ t, (qCount h (f t) : ℤ)) = ∑ t, ⌊x t⌋ :=
      Finset.sum_congr rfl (fun t _ => by rw [hmech])
    rw [hq_eq]
    have hint : (((∑ t, ⌊x t⌋) - w : ℤ) : ℝ) = θ - ∑ t, Int.fract (x t) := by
      rw [Int.cast_sub, hfloorsum]; ring
    have hlt1 : |(((∑ t, ⌊x t⌋) - w : ℤ) : ℝ)| < 1 := by
      rw [hint, abs_lt]; exact ⟨by linarith [hΘhi], by linarith [hΘlo]⟩
    have hz : (∑ t, ⌊x t⌋) - w = 0 := by
      by_contra hne'
      have h1 : (1 : ℝ) ≤ |(((∑ t, ⌊x t⌋) - w : ℤ) : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne'
      linarith
    omega

end MH
end Proof
end Erdos1112
