/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FineInitialPowerVortexPackage
import ErdosProblems.Erdos207.InitialPowerOuterOnlyBounds

/-!
# Fine-error initial outer-only endpoints

The fine initial typicality gives a live pair-star floor within
`2 * (n / t^fineInitialExponent) + 4` of the exact outer-only cutoff.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem FineInitialPowerVortexPackage.initialOuterOnlyPairFloor_of_gap
    {q h n ell t rootPower step m : ℕ}
    (P : FineInitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (hh : 2 ≤ h)
    (hgap : ((((P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 2 + m : ℕ) :
        ℝ≥0) <
      (1 - fineInitialError t) *
        ((1 : ℝ≥0) ^ 2 * 1 *
          (P.W.U ((⟨0, hell⟩ : Fin ell).castSucc)).card))) :
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let A := (absorberGreedyInitialState F
      (outsideAvailableTriangles P.H P.B)).available
    let i : Fin ell := ⟨0, hell⟩
    HasAvailablePairFloor (m + 1)
      (absorberGreedyInitialState F
        (outerOnlyAvailable (P.W.U i.succ) A)) := by
  dsimp only
  let F := absorberErdosForbiddenConfigurationsOn q P.B
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let A := (absorberGreedyInitialState F
    (outsideAvailableTriangles P.H P.B)).available
  let i : Fin ell := ⟨0, hell⟩
  have hpoint : IsMasterStagePointwiseGood P.W 0 F G A
      ∅ ∅ 1 1 (fineInitialError t) h := by
    simpa only [F, G, A] using
      initialMasterStagePointwiseGood_of_typical P.typicalFine
  have hInv : GreedyInvariant F (relativePreliminaryInitialState ∅ A) :=
    greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
      hpoint
  have hsupport : GraphSupportedOn G (P.W.U i.castSucc : Set (Fin n)) := by
    have hi : i.castSucc = (0 : Fin (ell + 1)) := by
      ext
      rfl
    rw [hi, P.W.root]
    intro u v _huv
    simp
  exact P.typicalFine.hasAvailablePairFloor_outerOnly hpoint.2.2.2.2.2.1
    i (by simp [i]) hsupport hh m (by simpa only [i] using hgap) hInv

/-- The fine typicality gap with an explicit integer quotient. -/
theorem FineInitialPowerVortexPackage.initialOuterOnlyFineNearFullGap
    {q h n ell t rootPower step : ℕ}
    (P : FineInitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (ht : 2 ≤ t)
    (hlevelSmall : 2 * (P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 8 ≤ n) :
    let i : Fin ell := ⟨0, hell⟩
    let U := P.W.U i.succ
    let outer := (univ \ U).card
    let r := n / t ^ fineInitialExponent
    let m := outer - 2 * r - 4
    (((((U.card + 2 + m : ℕ) : ℝ≥0)) <
      (1 - fineInitialError t) *
        ((1 : ℝ≥0) ^ 2 * 1 * (P.W.U i.castSucc).card))) := by
  dsimp only
  let i : Fin ell := ⟨0, hell⟩
  let U := P.W.U i.succ
  let outer := (univ \ U).card
  let T := t ^ fineInitialExponent
  let r := n / T
  have hiCast : i.castSucc = (0 : Fin (ell + 1)) := by
    ext
    rfl
  have hUle : U.card ≤ n := by
    have hcard : U.card ≤ Fintype.card (Fin n) := Finset.card_le_univ U
    simpa only [Fintype.card_fin] using hcard
  have houterCard : outer = n - U.card := by
    simp [outer, card_sdiff]
  have hTge : 8 ≤ T := by
    dsimp only [T]
    have hbase : 2 ^ 3 ≤ t ^ 3 := Nat.pow_le_pow_left ht 3
    have hexp : t ^ 3 ≤ t ^ fineInitialExponent := by
      apply Nat.pow_le_pow_right (Nat.zero_lt_one.trans_le
        ((by norm_num : 1 ≤ 2).trans ht))
      norm_num [fineInitialExponent]
    norm_num at hbase ⊢
    exact hbase.trans hexp
  have hTpos : 0 < T := (by norm_num : 0 < 8).trans_le hTge
  have hrMul : r * T ≤ n := by
    simpa only [r, Nat.mul_comm] using Nat.div_mul_le_self n T
  have heightR : 8 * r ≤ n := by
    calc
      8 * r ≤ T * r := Nat.mul_le_mul_right r hTge
      _ = r * T := Nat.mul_comm _ _
      _ ≤ n := hrMul
  have houterLarge : 2 * r + 4 ≤ outer := by
    rw [houterCard]
    change 2 * r + 4 ≤ n - U.card
    have hsmall : 2 * U.card + 8 ≤ n := by
      simpa only [U, i] using hlevelSmall
    omega
  have hsum : U.card + outer = n := by
    rw [houterCard]
    omega
  have hleftNat : U.card + 2 + (outer - 2 * r - 4) =
      n - 2 * r - 2 := by
    omega
  have hquotient : (n : ℝ≥0) / (T : ℝ≥0) < (r + 1 : ℕ) := by
    apply (div_lt_iff₀ (by exact_mod_cast hTpos)).2
    have hmod : n % T < T := Nat.mod_lt n hTpos
    have hdecomp : n % T + T * (n / T) = n := Nat.mod_add_div n T
    have hnlt : n < T + T * (n / T) := by omega
    have hnlt' : n < (r + 1) * T := by
      calc
        n < T + T * (n / T) := hnlt
        _ = (r + 1) * T := by simp [r]; ring
    exact_mod_cast hnlt'
  have hleftPlus :
      ((n - 2 * r - 2 : ℕ) : ℝ≥0) +
          (n : ℝ≥0) / (T : ℝ≥0) < (n : ℝ≥0) := by
    calc
      ((n - 2 * r - 2 : ℕ) : ℝ≥0) +
          (n : ℝ≥0) / (T : ℝ≥0) <
          ((n - 2 * r - 2 : ℕ) : ℝ≥0) + (r + 1 : ℕ) :=
        by simpa only [add_comm] using
          add_lt_add_left hquotient (((n - 2 * r - 2 : ℕ) : ℝ≥0))
      _ ≤ (n : ℝ≥0) := by
        exact_mod_cast (show n - 2 * r - 2 + (r + 1) ≤ n by omega)
  have hinvPow : fineInitialError t = (T : ℝ≥0)⁻¹ := by
    unfold fineInitialError
    dsimp only [T]
    push_cast
    rw [inv_pow]
  have hright : ((n - 2 * r - 2 : ℕ) : ℝ≥0) <
      (1 - fineInitialError t) * (n : ℝ≥0) := by
    rw [hinvPow, tsub_mul, one_mul, inv_mul_eq_div]
    rw [lt_tsub_iff_right]
    simpa only [add_comm] using hleftPlus
  rw [hiCast, P.W.root]
  simp only [card_univ, Fintype.card_fin, one_pow, one_mul]
  rw [show (P.W.U i.succ).card = U.card by rfl,
    show (univ \ P.W.U i.succ).card = outer by rfl,
    show n / t ^ fineInitialExponent = r by rfl, hleftNat]
  exact hright

theorem FineInitialPowerVortexPackage.initialOuterOnlyFineNearFullPairFloor
    {q h n ell t rootPower step : ℕ}
    (P : FineInitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (hh : 2 ≤ h) (ht : 2 ≤ t)
    (hlevelSmall : 2 * (P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 8 ≤ n) :
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let A := (absorberGreedyInitialState F
      (outsideAvailableTriangles P.H P.B)).available
    let i : Fin ell := ⟨0, hell⟩
    let outer := (univ \ P.W.U i.succ).card
    HasAvailablePairFloor
      (outer - 2 * (n / t ^ fineInitialExponent) - 4 + 1)
      (absorberGreedyInitialState F
        (outerOnlyAvailable (P.W.U i.succ) A)) := by
  dsimp only
  apply P.initialOuterOnlyPairFloor_of_gap hell hh
  simpa only using P.initialOuterOnlyFineNearFullGap hell ht hlevelSmall

end

end Erdos207
