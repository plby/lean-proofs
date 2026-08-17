/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos636.External.Erdos88.Richness

/-!
# The richness input for Erdős Problem 636

This file translates the three-parameter richness predicate proved in
`Erdos88.ksssLemma44` into the corrected two-parameter predicate used by
Kwan--Sudakov.  The latter uses strict exceptional-degree inequalities;
consequently it follows from the former at the same exceptional threshold.
-/

open SimpleGraph

namespace Erdos636

universe u

noncomputable section

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The union of the two strict exceptional classes in the corrected
Kwan--Sudakov definition of richness. -/
def strictExceptionalVertices (G : SimpleGraph V) (W : Finset V) (ε : ℝ) :
    Finset V :=
  Finset.univ.filter fun v ↦
    ((Erdos88.neighborsIn G v W).card : ℝ) < ε * W.card ∨
      ((W \ Erdos88.neighborsIn G v W).card : ℝ) < ε * W.card

@[simp] lemma mem_strictExceptionalVertices {G : SimpleGraph V} {W : Finset V}
    {ε : ℝ} {v : V} :
    v ∈ strictExceptionalVertices G W ε ↔
      ((Erdos88.neighborsIn G v W).card : ℝ) < ε * W.card ∨
        ((W \ Erdos88.neighborsIn G v W).card : ℝ) < ε * W.card := by
  simp [strictExceptionalVertices]

/-- Corrected Kwan--Sudakov richness: every set of at least a `δ` fraction
of the vertices has at most `|V|^(1/5)` vertices which are exceptionally
sparse or exceptionally dense into it. -/
def KwanSudakovRich (G : SimpleGraph V) (δ ε : ℝ) : Prop :=
  ∀ W : Finset V,
    δ * Fintype.card V ≤ W.card →
      ((strictExceptionalVertices G W ε).card : ℝ) ≤
        (Fintype.card V : ℝ) ^ (1 / 5 : ℝ)

/-- The checked KSSS richness predicate implies the corrected
Kwan--Sudakov predicate.  The point is that every strict exceptional vertex
is also exceptional for the non-strict inequalities in `Erdos88.Rich`. -/
lemma kwanSudakovRich_of_rich {G : SimpleGraph V} {δ ε : ℝ}
    (h : Erdos88.Rich G δ ε (1 / 5 : ℝ)) : KwanSudakovRich G δ ε := by
  intro W hW
  refine le_trans ?_ (h W hW)
  norm_cast
  apply Finset.card_le_card
  intro v hv
  simp only [mem_strictExceptionalVertices] at hv
  simp only [Erdos88.mem_exceptionalVertices]
  exact hv.imp le_of_lt le_of_lt

/-- Raising the minimum test-set size preserves corrected richness. -/
lemma KwanSudakovRich.mono_delta {G : SimpleGraph V} {δ₁ δ₂ ε : ℝ}
    (h : KwanSudakovRich G δ₁ ε) (hδ : δ₁ ≤ δ₂) :
    KwanSudakovRich G δ₂ ε := by
  intro W hW
  apply h W
  exact (mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)).trans hW

/-- Eventual linear rich-subgraph extraction in precisely the corrected
Kwan--Sudakov form used for Erdős Problem 636. -/
theorem exists_linear_ksRich_induce (C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
        ∃ U : Finset (Fin n),
          c * n ≤ U.card ∧
            KwanSudakovRich (G.induce (U : Set (Fin n))) δ ε := by
  obtain ⟨ρ, hρ, hρone, N₀, hrich⟩ :=
    Erdos88.ksssLemma44 C (1 / 5 : ℝ) hC (by norm_num)
  let d : ℝ := min δ 1
  let c : ℝ := min (ρ / 2) (d ^ (1 / ρ))
  have hd : 0 < d := by
    dsimp [d]
    exact lt_min hδ zero_lt_one
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by positivity) (Real.rpow_pos_of_pos hd _)
  have hcρ : c ≤ ρ := by
    exact (min_le_left (ρ / 2) (d ^ (1 / ρ))).trans (by linarith)
  have hcpow : c ^ ρ ≤ δ := by
    have hcroot : c ≤ d ^ (1 / ρ) := min_le_right _ _
    have hpow := Real.rpow_le_rpow hc.le hcroot hρ.le
    calc
      c ^ ρ ≤ (d ^ (1 / ρ)) ^ ρ := hpow
      _ = d := by
        rw [← Real.rpow_mul hd.le]
        field_simp
        exact Real.rpow_one d
      _ ≤ δ := min_le_left _ _
  obtain ⟨N₁, hN₁eventual⟩ :=
    Erdos88.exists_nat_rpow_ge (1 / 2 : ℝ) (1 / c) (by norm_num)
  let N := max 1 (max N₀ N₁)
  refine ⟨ρ, c, hρ, hc, N, ?_⟩
  intro n hn G hG
  have hn1 : 1 ≤ n := (le_max_left 1 (max N₀ N₁)).trans hn
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hN₀ : N₀ ≤ n :=
    (le_max_left N₀ N₁).trans ((le_max_right 1 (max N₀ N₁)).trans hn)
  have hN₁n : N₁ ≤ n :=
    (le_max_right N₀ N₁).trans ((le_max_right 1 (max N₀ N₁)).trans hn)
  have hinv : 1 / c ≤ Real.sqrt n := by
    have := hN₁eventual n hN₁n
    simpa [Real.sqrt_eq_rpow] using this
  have hsqrt : Real.sqrt n ≤ c * n := by
    have hcsqrt : 1 ≤ c * Real.sqrt n := by
      have := mul_le_mul_of_nonneg_left hinv hc.le
      field_simp at this
      simpa [mul_comm] using this
    have hsqrt_nonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnreal.le
    nlinarith
  have hmρ : c * n ≤ ρ * n :=
    mul_le_mul_of_nonneg_right hcρ (Nat.cast_nonneg _)
  obtain ⟨U, hU, hURich⟩ := hrich n hN₀ (c * n) hsqrt hmρ G hG
  refine ⟨U, hU, ?_⟩
  have hratio : c * (n : ℝ) / n = c := by field_simp
  have hRichδ :
      Erdos88.Rich (G.induce (U : Set (Fin n))) δ ρ (1 / 5 : ℝ) := by
    apply hURich.mono_delta
    simpa [hratio] using hcpow
  exact kwanSudakovRich_of_rich hRichδ

/-- Noncircular specialization for bounded-set arguments.  The exceptional
threshold `ε` is chosen first by `ksssLemma44`; the minimum test-set density
is then `ε ^ K`, and only after that do we choose the positive linear scale
of the induced subgraph.  In particular, when `1 ≤ K`, this density is at
most `ε ^ (K - 1)`, as required by the common-neighbourhood induction. -/
theorem exists_linear_ksRich_induce_pow (C : ℝ) (K : ℕ)
    (hC : 0 < C) (_hK : 1 ≤ K) :
    ∃ ε c : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < c ∧
      ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), Erdos88.RamseyFree C G →
        ∃ U : Finset (Fin n),
          c * n ≤ U.card ∧
            KwanSudakovRich (G.induce (U : Set (Fin n))) (ε ^ K) ε := by
  obtain ⟨ρ, hρ, hρone, N₀, hrich⟩ :=
    Erdos88.ksssLemma44 C (1 / 5 : ℝ) hC (by norm_num)
  let d : ℝ := ρ ^ K
  let c : ℝ := min (ρ / 2) (d ^ (1 / ρ))
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (by positivity) (Real.rpow_pos_of_pos hd _)
  have hcρ : c ≤ ρ := by
    exact (min_le_left (ρ / 2) (d ^ (1 / ρ))).trans (by linarith)
  have hcpow : c ^ ρ ≤ ρ ^ K := by
    have hcroot : c ≤ d ^ (1 / ρ) := min_le_right _ _
    have hpow := Real.rpow_le_rpow hc.le hcroot hρ.le
    calc
      c ^ ρ ≤ (d ^ (1 / ρ)) ^ ρ := hpow
      _ = d := by
        rw [← Real.rpow_mul hd.le]
        field_simp
        exact Real.rpow_one d
      _ = ρ ^ K := rfl
  obtain ⟨N₁, hN₁eventual⟩ :=
    Erdos88.exists_nat_rpow_ge (1 / 2 : ℝ) (1 / c) (by norm_num)
  let N := max 1 (max N₀ N₁)
  refine ⟨ρ, c, hρ, hρone, hc, N, ?_⟩
  intro n hn G hG
  have hnpos : 0 < n := by
    have hn1 : 1 ≤ n := (le_max_left 1 (max N₀ N₁)).trans hn
    omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hN₀ : N₀ ≤ n :=
    (le_max_left N₀ N₁).trans ((le_max_right 1 (max N₀ N₁)).trans hn)
  have hN₁n : N₁ ≤ n :=
    (le_max_right N₀ N₁).trans ((le_max_right 1 (max N₀ N₁)).trans hn)
  have hinv : 1 / c ≤ Real.sqrt n := by
    have := hN₁eventual n hN₁n
    simpa [Real.sqrt_eq_rpow] using this
  have hsqrt : Real.sqrt n ≤ c * n := by
    have hcsqrt : 1 ≤ c * Real.sqrt n := by
      have := mul_le_mul_of_nonneg_left hinv hc.le
      field_simp at this
      simpa [mul_comm] using this
    have hsqrt_nonneg : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hsqrt_sq : (Real.sqrt n) ^ 2 = (n : ℝ) := Real.sq_sqrt hnreal.le
    nlinarith
  have hmρ : c * n ≤ ρ * n :=
    mul_le_mul_of_nonneg_right hcρ (Nat.cast_nonneg _)
  obtain ⟨U, hU, hURich⟩ := hrich n hN₀ (c * n) hsqrt hmρ G hG
  refine ⟨U, hU, ?_⟩
  have hratio : c * (n : ℝ) / n = c := by field_simp
  have hRichδ :
      Erdos88.Rich (G.induce (U : Set (Fin n))) (ρ ^ K) ρ (1 / 5 : ℝ) := by
    apply hURich.mono_delta
    simpa [hratio] using hcpow
  exact kwanSudakovRich_of_rich hRichδ

/-- The power density chosen above is no larger than the preceding power;
this is the scalar side condition used by the common-neighbourhood lemma. -/
lemma ksRich_pow_le_previous {ε : ℝ} {K : ℕ} (hε : 0 ≤ ε) (hεone : ε ≤ 1)
    (hK : 1 ≤ K) : ε ^ K ≤ ε ^ (K - 1) := by
  obtain ⟨L, rfl⟩ := Nat.exists_eq_add_of_le hK
  simp only [Nat.add_sub_cancel_left]
  rw [Nat.add_comm]
  rw [pow_succ]
  simpa using mul_le_mul_of_nonneg_left hεone (pow_nonneg hε L)

end

end Erdos636
