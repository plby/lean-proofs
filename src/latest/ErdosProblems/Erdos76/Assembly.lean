/-
Copyright 2026 The Lean-Proofs Authors.

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
import ErdosProblems.Erdos76.Fractional
import Mathlib.Tactic

/-! Assembly of the exact fractional theorem and uniform rounding theorem. -/

open Filter

namespace Erdos76

noncomputable section

lemma cast_nat_div_four_lower (k : ℕ) :
    (((k / 4 : ℕ) : ℝ)) ≥ (k : ℝ) / 4 - 1 := by
  have hnat : k < k / 4 * 4 + 4 := Nat.lt_div_mul_add (by omega)
  have hreal : (k : ℝ) < ((k / 4 * 4 + 4 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  push_cast at hreal
  linarith

lemma fractional_threshold_lower {ε : ℝ} {n : ℕ}
    (hn : 1 ≤ n) (hlarge : (n : ℝ) / 6 + 1 / 4 ≤ ε / 2 * (n : ℝ) ^ 2) :
    (1 / 12 - ε / 2) * (n : ℝ) ^ 2 ≤
      (((n - 1) ^ 2 / 4 : ℕ) : ℝ) / 3 := by
  have hfloor := cast_nat_div_four_lower ((n - 1) ^ 2)
  norm_num [Nat.cast_pow, Nat.cast_sub hn] at hfloor ⊢
  nlinarith

lemma eventually_fractional_threshold (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      26 ≤ n ∧
        (1 / 12 - ε / 2) * (n : ℝ) ^ 2 ≤
          (((n - 1) ^ 2 / 4 : ℕ) : ℝ) / 3 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (1 / ε))
  filter_upwards [eventually_ge_atTop (max 26 N)] with n hn
  have hn26 : 26 ≤ n := (le_max_left 26 N).trans hn
  have hNn : N ≤ n := (le_max_right 26 N).trans hn
  have hnreal : max 1 (1 / ε) < (n : ℝ) :=
    hN.trans_le (by exact_mod_cast hNn)
  have hnreal_one : (1 : ℝ) < n := (le_max_left 1 (1 / ε)).trans_lt hnreal
  have hn1 : 1 ≤ n := by exact_mod_cast hnreal_one.le
  have hone_div : 1 / ε < (n : ℝ) :=
    (le_max_right 1 (1 / ε)).trans_lt hnreal
  have hone_lt : (1 : ℝ) < ε * (n : ℝ) := by
    rw [div_lt_iff₀ hε] at hone_div
    simpa [mul_comm] using hone_div
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans hnreal_one
  have hprod : (n : ℝ) ≤ (ε * (n : ℝ)) * (n : ℝ) :=
    by simpa using mul_le_mul_of_nonneg_right hone_lt.le hnpos.le
  have hlinear : (n : ℝ) ≤ ε * (n : ℝ) ^ 2 := by
    simpa [pow_two, mul_assoc] using hprod
  have hlarge : (n : ℝ) / 6 + 1 / 4 ≤ ε / 2 * (n : ℝ) ^ 2 := by
    nlinarith
  exact ⟨hn26, fractional_threshold_lower hn1 hlarge⟩

lemma combine_fractional_roundings {n : ℕ} {G : SimpleGraph (Fin n)}
    {wR wB : Finset (Fin n) → ℝ} {η q : ℝ}
    (hfrac : q ≤ fractionalCoveredSize G wR + fractionalCoveredSize Gᶜ wB)
    (hroundR : ∃ P : Finset (Finset (Fin n)),
      (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧
        fractionalSize G wR ≤ (P.card : ℝ) + η * (n : ℝ) ^ 2)
    (hroundB : ∃ Q : Finset (Finset (Fin n)),
      (∀ t ∈ Q, Gᶜ.IsNClique 3 t) ∧ EdgeDisjoint Q ∧
        fractionalSize Gᶜ wB ≤ (Q.card : ℝ) + η * (n : ℝ) ^ 2) :
    q / 3 - 2 * η * (n : ℝ) ^ 2 ≤ (monoPackingNumber G : ℝ) := by
  obtain ⟨P, hPsub, hPed, hRP⟩ := hroundR
  obtain ⟨Q, hQsub, hQed, hRQ⟩ := hroundB
  have hPQnat : P.card + Q.card ≤ monoPackingNumber G :=
    add_card_le_monoPackingNumber_of_isNClique hPsub hQsub hPed hQed
  have hPQ : (P.card : ℝ) + (Q.card : ℝ) ≤ monoPackingNumber G := by
    exact_mod_cast hPQnat
  simp only [fractionalCoveredSize] at hfrac
  nlinarith

lemma final_epsilon_arithmetic {ε x q M : ℝ}
    (hthreshold : (1 / 12 - ε / 2) * x ^ 2 ≤ q / 3)
    (hcombined : q / 3 - 2 * (ε / 4) * x ^ 2 ≤ M) :
    (1 / 12 - ε) * x ^ 2 ≤ M := by
  nlinarith

lemma resolution_at_n (hGL : GruslysLetzterFractional)
    {ε : ℝ} {n : ℕ}
    (hround : ∀ (G : SimpleGraph (Fin n)) (w : Finset (Fin n) → ℝ),
      IsFractionalPacking G w →
        ∃ P : Finset (Finset (Fin n)),
          (∀ t ∈ P, G.IsNClique 3 t) ∧ EdgeDisjoint P ∧
            fractionalSize G w ≤ (P.card : ℝ) + (ε / 4) * (n : ℝ) ^ 2)
    (hthreshold : 26 ≤ n ∧
      (1 / 12 - ε / 2) * (n : ℝ) ^ 2 ≤
        (((n - 1) ^ 2 / 4 : ℕ) : ℝ) / 3)
    (G : SimpleGraph (Fin n)) :
    (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ (monoPackingNumber G : ℝ) := by
  obtain ⟨wR, wB, hwR, hwB, hfrac⟩ := hGL.apply n hthreshold.1 G
  apply final_epsilon_arithmetic hthreshold.2
  exact combine_fractional_roundings (η := ε / 4)
    (q := (((n - 1) ^ 2 / 4 : ℕ) : ℝ)) hfrac
    (hround G wR hwR) (hround Gᶜ wB hwB)

lemma resolution_at_epsilon
    (hGL : GruslysLetzterFractional) (hHR : HaxellRodlRounding)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ G : SimpleGraph (Fin n),
      (1 / 12 - ε) * (n : ℝ) ^ 2 ≤ (monoPackingNumber G : ℝ) := by
  have hη : 0 < ε / 4 := by positivity
  have hround := hHR.eventually_apply (ε / 4) hη
  have hthreshold := eventually_fractional_threshold ε hε
  exact (hround.and hthreshold).mono fun n hn ↦
    resolution_at_n hGL hn.1 hn.2

/-- The final argument after the two substantive published ingredients have
been formalized. -/
theorem resolution_of_fractional_and_rounding
    (hGL : GruslysLetzterFractional) (hHR : HaxellRodlRounding) : Resolution :=
  fun ε hε ↦ resolution_at_epsilon hGL hHR ε hε

/-- The final assembly only needs the asymptotic form of the fractional
theorem.  This formulation is also the bridge used by the local-averaging and
weighted-Kahn route. -/
theorem resolution_of_asymptotic_fractional
    (hAF : AsymptoticFractional) (hHR : HaxellRodlRounding) : Resolution := by
  intro ε hε
  have hδ : 0 < (3 * ε / 2 : ℝ) := by positivity
  have hη : 0 < (ε / 4 : ℝ) := by positivity
  filter_upwards [hAF (3 * ε / 2) hδ,
    hHR.eventually_apply (ε / 4) hη] with n hfrac hround
  intro G
  obtain ⟨wR, wB, hwR, hwB, hsize⟩ := hfrac G
  have hcombined := combine_fractional_roundings
    (n := n) (G := G) (wR := wR) (wB := wB)
    (η := ε / 4) (q := (1 / 4 - 3 * ε / 2) * (n : ℝ) ^ 2)
    hsize (hround G wR hwR) (hround Gᶜ wB hwB)
  nlinarith

end

end Erdos76
