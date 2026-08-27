/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.UniformSourceStageScale

/-! # Simultaneously feasible physical exponent gaps, including the first retained stage -/

namespace Erdos207

theorem exists_source_stage_exponent_schedule (q h b den : ℕ) :
    ∃ S P K : ℕ, 1 ≤ S ∧ 1 ≤ P ∧ 1 ≤ K ∧
      ∀ v D : ℕ, 1 ≤ v → K * v ≤ D →
        v + 2 * b + 4 ≤ S * v ∧
        v + b * (h + 2) + 4 ≤ S * v ∧
        2 * (S * v) + 2 * b + v + 2 ≤ P * v ∧
        b + 1 ≤ P * v ∧ den * (P * v + 1) ≤ D ∧
        2 * (S * v) + 3 * b + v + 2 ≤ D - v ∧
        v + (q + 1) * (1 + v + S * v + 2 * b) + 2 ≤ D - v ∧
        b * (h + 1) + v + 2 ≤ D - v ∧
        S * v + 4 * b + 2 ≤ D := by
  let S := b * (h + 4) + 12
  let P := 2 * S + 2 * b + 8
  let K := den * (P + 2) + (2 * S + 3 * b + 4) +
    ((q + 1) * (S + 2 * b + 2) + 4) + (b * (h + 1) + 4) + (S + 4 * b + 4) + 10
  have hS1 : 1 ≤ S := by dsimp only [S]; omega
  have hP1 : 1 ≤ P := by dsimp only [P]; omega
  have hK1 : 1 ≤ K := by dsimp only [K]; omega
  have hSsmall : 2 * b + 5 ≤ S := by dsimp only [S]; nlinarith
  have hSdegree : b * (h + 2) + 5 ≤ S := by dsimp only [S]; nlinarith
  have hKden : den * (P + 2) ≤ K := by dsimp only [K]; omega
  have hKleft : 2 * S + 3 * b + 4 ≤ K := by dsimp only [K]; omega
  have hKmarked : (q + 1) * (S + 2 * b + 2) + 4 ≤ K := by dsimp only [K]; omega
  have hKquasi : b * (h + 1) + 4 ≤ K := by dsimp only [K]; omega
  have hKreserve : S + 4 * b + 4 ≤ K := by dsimp only [K]; omega
  refine ⟨S, P, K, hS1, hP1, hK1, ?_⟩
  intro v D hv hD
  have hvD : v ≤ D := by
    have hle : v ≤ K * v := by simpa only [one_mul] using Nat.mul_le_mul_right v hK1
    exact hle.trans hD
  have hsub := Nat.sub_add_cancel hvD
  have hsmallV := Nat.mul_le_mul_left (2 * b + 4) hv
  have hdegreeV := Nat.mul_le_mul_left (b * (h + 2) + 4) hv
  have hleftV := Nat.mul_le_mul_left (3 * b + 2) hv
  have hmarkedV := Nat.mul_le_mul_left (1 + 2 * b) hv
  have hquasiV := Nat.mul_le_mul_left (b * (h + 1) + 2) hv
  have hreserveV := Nat.mul_le_mul_left (4 * b + 2) hv
  have hsmallScale := Nat.mul_le_mul_right v hSsmall
  have hdegreeScale := Nat.mul_le_mul_right v hSdegree
  refine ⟨by nlinarith only [hsmallScale, hsmallV], by nlinarith only [hdegreeScale, hdegreeV],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [P]
    nlinarith only [hsmallV, hv]
  · have hbP : b + 1 ≤ P := by dsimp only [P]; omega
    exact hbP.trans (by simpa only [mul_one] using Nat.mul_le_mul_left P hv)
  · calc
      den * (P * v + 1) ≤ den * ((P + 2) * v) := Nat.mul_le_mul_left den (by nlinarith only [hv])
      _ = (den * (P + 2)) * v := by ring
      _ ≤ K * v := Nat.mul_le_mul_right v hKden
      _ ≤ D := hD
  · have hreq := (Nat.mul_le_mul_right v hKleft).trans hD
    nlinarith only [hreq, hleftV, hsub]
  · have hin : 1 + v + S * v + 2 * b ≤ (S + 2 * b + 2) * v := by
      nlinarith only [hmarkedV]
    have hm := Nat.mul_le_mul_left (q + 1) hin
    have hreq := (Nat.mul_le_mul_right v hKmarked).trans hD
    nlinarith only [hm, hreq, hsub, hv]
  · have hreq := (Nat.mul_le_mul_right v hKquasi).trans hD
    nlinarith only [hreq, hquasiV, hsub]
  · have hreq := (Nat.mul_le_mul_right v hKreserve).trans hD
    nlinarith only [hreq, hreserveV]

theorem source_stage_inner_power_lower
    (t n u D v : ℕ) (ht : 0 < t) (hvD : v ≤ D)
    (hn : t ^ D ≤ n) (hratio : n ≤ t ^ v * u) : t ^ (D - v) ≤ u := by
  have hmul : t ^ v * t ^ (D - v) ≤ t ^ v * u := by
    rw [← pow_add, Nat.add_sub_of_le hvD]
    exact hn.trans hratio
  exact Nat.le_of_mul_le_mul_left hmul (pow_pos ht v)

end Erdos207
