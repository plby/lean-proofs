/-
Copyright (c) 2026 The Leanprovers contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos95.GuthInduction

/-!
# Rich points of the Elekes--Sharir family

The strong incidence certificate has no exceptional surface when it is
applied to the full `P × P` family at a sufficiently large scale: the
Elekes--Sharir non-clustering theorem gives only `O_D(|P|)` lines on a
degree-`D` irreducible surface, whereas a certificate surface contains at
least `|P|^(1+2η)` lines.
-/

namespace Erdos95.SpecialRichPoints

open Erdos95.ES Erdos95.LineFamilies Erdos95.GuthStructure
open Erdos95.GuthParameters Erdos95.GuthInduction
open Erdos95.ScaleBounds Erdos95.SpecialFamily
open Erdos95.SurfaceFactors Erdos95.RichPointCombinatorics

abbrev LineIndex := PlanePoint × PlanePoint

theorem full_family_rich_point_bound :
    ∀ δ : ℝ, 0 < δ → ∃ A : ℝ, 0 < A ∧
      ∀ (P : Finset PlanePoint) (k : ℕ), 2 ≤ k →
        ((richPoints (P.product P) k).card : ℝ) ≤
          A * (P.card : ℝ) ^ (3 + δ) / (k : ℝ) ^ 2 := by
  intro δ hδ
  let η : ℝ := min (δ / 4) ((1 : ℝ) / 8)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by positivity) (by norm_num)
  have hηle : η ≤ (1 : ℝ) / 4 := by
    dsimp [η]
    exact (min_le_right _ _).trans (by norm_num)
  have htwoη : 2 * η ≤ δ := by
    have hle : η ≤ δ / 4 := min_le_left _ _
    linarith
  let par : Parameters η := Classical.choice (exists_parameters hη hηle)
  obtain ⟨K, hK, hcert⟩ := exists_certificate_constant hη hηle par
  let D : ℕ := wallDegree par.k
  let Cline : ℕ := surfaceLineConstant D
  obtain ⟨N, hNpos, hNscale⟩ :=
    exists_pos_nat_forall_le_rpow (show 0 < 2 * η by positivity)
      (2 * (Cline : ℝ) + 1)
  let C₀ : ℝ := K + (N : ℝ) ^ 4 + 1
  let A : ℝ := 2 * C₀
  have hC₀ : 0 < C₀ := by
    dsimp [C₀]
    positivity
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro P k hk
  by_cases hkn : k ≤ P.card
  · have hP : 0 < P.card := by omega
    let L : Finset LineIndex := P.product P
    have hLcard : L.card = P.card ^ 2 := by
      simp [L, pow_two]
    have hrange : k ^ 2 ≤ 4 * L.card := by
      rw [hLcard]
      nlinarith
    have hPone : 1 ≤ (P.card : ℝ) := by exact_mod_cast hP
    have hPpos : 0 < (P.card : ℝ) := by exact_mod_cast hP
    have hexp : 0 ≤ 3 + δ := by linarith
    have hpowone : 1 ≤ (P.card : ℝ) ^ (3 + δ) :=
      Real.one_le_rpow hPone hexp
    have hpair :
        ((k * (k - 1) * (richPoints L k).card : ℕ) : ℝ) ≤
          C₀ * (P.card : ℝ) ^ (3 + δ) := by
      by_cases hlarge : N ≤ P.card
      · have hscaleWeak := hNscale P.card hlarge
        have hscale :
            2 * (Cline : ℝ) < (P.card : ℝ) ^ (2 * η) := by
          linarith
        let cert : Certificate η D K L k :=
          Classical.choice (hcert L k hk hrange)
        have hsurfaces : cert.surfaces = ∅ := by
          apply Finset.not_nonempty_iff_eq_empty.mp
          rintro ⟨Q, hQ⟩
          have hlower := cert.many_lines Q hQ
          have hupperNat : (surfaceLines L Q).card ≤
              Cline * (P.card + 1) := by
            exact card_surfaceLines_le_degree
              (show L ⊆ P.product P by simp [L])
              (cert.irreducible Q hQ) (cert.degree_le Q hQ)
          have hupper : ((surfaceLines L Q).card : ℝ) ≤
              Cline * (P.card + 1) := by exact_mod_cast hupperNat
          have hLpow :
              (L.card : ℝ) ^ ((1 : ℝ) / 2 + η) =
                (P.card : ℝ) ^ (1 + 2 * η) := by
            rw [hLcard]
            push_cast
            rw [show (P.card : ℝ) ^ (2 : ℕ) =
              (P.card : ℝ) ^ (2 : ℝ) by
                exact (Real.rpow_natCast _ 2).symm]
            rw [← Real.rpow_mul hPpos.le]
            congr 1
            ring
          have hgrow :
              (Cline : ℝ) * (P.card + 1) <
                (P.card : ℝ) ^ (1 + 2 * η) := by
            have hmul := mul_lt_mul_of_pos_left hscale hPpos
            have hsum : (P.card : ℝ) + 1 ≤ 2 * P.card := by
              exact_mod_cast (show P.card + 1 ≤ 2 * P.card by omega)
            have hleft :
                (Cline : ℝ) * ((P.card : ℝ) + 1) ≤
                  (P.card : ℝ) * (2 * Cline) := by
              nlinarith [show 0 ≤ (Cline : ℝ) by positivity]
            have hpow :
                (P.card : ℝ) ^ (1 + 2 * η) =
                  (P.card : ℝ) * (P.card : ℝ) ^ (2 * η) := by
              rw [Real.rpow_add hPpos]
              simp
            rw [hpow]
            exact hleft.trans_lt (by simpa [mul_comm, mul_left_comm,
              mul_assoc] using hmul)
          rw [hLpow] at hlower
          linarith
        have hres : residualRichPoints L cert.surfaces k =
            richPoints L k := by
          rw [hsurfaces]
          simp [residualRichPoints, surfaceRichPoints]
        have hcertBound := cert.residual_bound
        rw [hres] at hcertBound
        have hbasepow :
            (L.card : ℝ) ^ ((3 : ℝ) / 2 + η) =
              (P.card : ℝ) ^ (3 + 2 * η) := by
          rw [hLcard]
          push_cast
          rw [show (P.card : ℝ) ^ (2 : ℕ) =
            (P.card : ℝ) ^ (2 : ℝ) by
              exact (Real.rpow_natCast _ 2).symm]
          rw [← Real.rpow_mul hPpos.le]
          congr 1
          ring
        rw [hbasepow] at hcertBound
        have hpowmono :
            (P.card : ℝ) ^ (3 + 2 * η) ≤
              (P.card : ℝ) ^ (3 + δ) :=
          Real.rpow_le_rpow_of_exponent_le hPone (by linarith)
        calc
          ((k * (k - 1) * (richPoints L k).card : ℕ) : ℝ) ≤
              K * (P.card : ℝ) ^ (3 + 2 * η) := hcertBound
          _ ≤ K * (P.card : ℝ) ^ (3 + δ) := by gcongr
          _ ≤ C₀ * (P.card : ℝ) ^ (3 + δ) := by
            gcongr
            dsimp [C₀]
            nlinarith [show 0 ≤ (N : ℝ) ^ 4 by positivity]
      · have hsmall : P.card < N := Nat.lt_of_not_ge hlarge
        have hnat := richness_mul_pred_mul_card_le_sq L k
        have hcast :
            ((k * (k - 1) * (richPoints L k).card : ℕ) : ℝ) ≤
              (L.card : ℝ) ^ 2 := by exact_mod_cast hnat
        have hLn : (L.card : ℝ) ^ 2 = (P.card : ℝ) ^ 4 := by
          rw [hLcard]
          push_cast
          ring
        have hnN : (P.card : ℝ) ^ 4 ≤ (N : ℝ) ^ 4 := by
          gcongr
        calc
          ((k * (k - 1) * (richPoints L k).card : ℕ) : ℝ) ≤
              (L.card : ℝ) ^ 2 := hcast
          _ = (P.card : ℝ) ^ 4 := hLn
          _ ≤ (N : ℝ) ^ 4 := hnN
          _ ≤ (N : ℝ) ^ 4 * (P.card : ℝ) ^ (3 + δ) := by
            nlinarith [show 0 ≤ (N : ℝ) ^ 4 by positivity]
          _ ≤ C₀ * (P.card : ℝ) ^ (3 + δ) := by
            gcongr
            dsimp [C₀]
            nlinarith [show 0 ≤ (N : ℝ) ^ 4 by positivity]
    have hkpairNat : k ^ 2 ≤ 2 * (k * (k - 1)) := by
      calc
        k ^ 2 = k * k := by ring
        _ ≤ k * (2 * (k - 1)) := by gcongr <;> omega
        _ = 2 * (k * (k - 1)) := by ring
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hscaled :
        (k : ℝ) ^ 2 * ((richPoints L k).card : ℝ) ≤
          2 * C₀ * (P.card : ℝ) ^ (3 + δ) := by
      have hkpair : (k : ℝ) ^ 2 ≤
          2 * ((k * (k - 1) : ℕ) : ℝ) := by exact_mod_cast hkpairNat
      have hcardnonneg : 0 ≤ ((richPoints L k).card : ℝ) := by positivity
      calc
        (k : ℝ) ^ 2 * ((richPoints L k).card : ℝ) ≤
            (2 * ((k * (k - 1) : ℕ) : ℝ)) *
              ((richPoints L k).card : ℝ) := by gcongr
        _ = 2 *
            ((k * (k - 1) * (richPoints L k).card : ℕ) : ℝ) := by
          push_cast
          ring
        _ ≤ 2 * (C₀ * (P.card : ℝ) ^ (3 + δ)) := by gcongr
        _ = 2 * C₀ * (P.card : ℝ) ^ (3 + δ) := by ring
    change ((richPoints L k).card : ℝ) ≤ _
    dsimp [A]
    apply (le_div_iff₀ (sq_pos_of_pos hkpos)).mpr
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
  · have hempty : richPoints (P.product P) k = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨x, hx⟩
      have hkline := (mem_richPoints_iff.mp hx).2
      have hcap := card_linesThrough_le_points
        (P := P) (L := P.product P) (by rfl) x
      omega
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end Erdos95.SpecialRichPoints
