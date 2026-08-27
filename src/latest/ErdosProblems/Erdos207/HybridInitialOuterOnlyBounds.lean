/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.HybridVortexTransitionData
import ErdosProblems.Erdos207.OuterOnlyPairStarBounds

/-!
# Quantitative initial bounds for the hybrid vortex

The first positive hybrid level has size at most five eighths of the
ambient order.  The level-zero iteration window therefore leaves at least
`n / 32 + 1` completely outside extensions through every live pair.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

/-- The level-zero extension window has room for a linear pair-star floor. -/
theorem InitialHybridVortexPackage.initialOuterOnlyFloorGap
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (hn : 31 < n) :
    (((((P.W.U ((⟨0, by omega⟩ : Fin 2).succ)).card + 2 + n / 32 : ℕ) :
        ℝ≥0)) <
      (1 - (t : ℝ≥0)⁻¹) *
        ((1 : ℝ≥0) ^ 2 * 1 *
          (P.W.U ((⟨0, by omega⟩ : Fin 2).castSucc)).card)) := by
  have hroot8 : 8 * t ^ rootPower ≤ n :=
    (Nat.mul_le_mul_left 8 P.rootPower_le_absorberBound).trans P.absorberEight
  have hnatLeft :
      4 * (t ^ rootPower + n / 2 + 2 + n / 32) < 3 * n := by
    have hhalf : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    have hthirtytwo : 32 * (n / 32) ≤ n := Nat.mul_div_le n 32
    omega
  have hleft :
      (((t ^ rootPower + n / 2 + 2 + n / 32 : ℕ) : ℝ≥0)) <
        (3 * (n : ℝ≥0)) / 4 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 4)).2
    exact_mod_cast (by simpa only [mul_comm] using hnatLeft)
  have htNat : 0 < t := (by norm_num : 0 < 8).trans_le P.base_ge_eight
  have htpos : (0 : ℝ≥0) < t := by exact_mod_cast htNat
  have hinv : (t : ℝ≥0)⁻¹ ≤ (8 : ℝ≥0)⁻¹ := by
    apply (inv_le_inv₀ htpos (by norm_num : (0 : ℝ≥0) < 8)).2
    exact_mod_cast P.base_ge_eight
  have heightInvOne : (8 : ℝ≥0)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by norm_num : (0 : ℝ≥0) < 8)]
    norm_num
  have hinvOne : (t : ℝ≥0)⁻¹ ≤ 1 := hinv.trans heightInvOne
  have hthreeQuarter : (3 : ℝ≥0) / 4 ≤ 1 - (t : ℝ≥0)⁻¹ := by
    rw [le_tsub_iff_right hinvOne]
    calc
      (3 : ℝ≥0) / 4 + (t : ℝ≥0)⁻¹ ≤
          (3 : ℝ≥0) / 4 + (8 : ℝ≥0)⁻¹ := add_le_add_right hinv _
      _ = (7 : ℝ≥0) / 8 := by norm_num
      _ ≤ 1 := (div_le_one (by norm_num : (0 : ℝ≥0) < 8)).2 (by norm_num)
  have hright : (3 * (n : ℝ≥0)) / 4 ≤
      (1 - (t : ℝ≥0)⁻¹) * (n : ℝ≥0) := by
    rw [div_eq_mul_inv]
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right hthreeQuarter (n : ℝ≥0)
  have hsucc : ((⟨0, by omega⟩ : Fin 2).succ) = (1 : Fin 3) := by
    ext
    rfl
  have hcast : ((⟨0, by omega⟩ : Fin 2).castSucc) = (0 : Fin 3) := by
    ext
    rfl
  rw [hsucc, hcast, P.firstLevel_card, P.rootLevel_card]
  simpa only [one_pow, one_mul] using hleft.trans_le hright

/-- The canonical first-phase state has a pair-star floor linear in `n`. -/
theorem InitialHybridVortexPackage.initialOuterOnlyPairFloor
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (hh : 2 ≤ h) (hn : 31 < n) :
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let A := (absorberGreedyInitialState F
      (outsideAvailableTriangles P.H P.B)).available
    let i : Fin 2 := ⟨0, by omega⟩
    HasAvailablePairFloor (n / 32 + 1)
      (absorberGreedyInitialState F
        (outerOnlyAvailable (P.W.U i.succ) A)) := by
  dsimp only
  let F := absorberErdosForbiddenConfigurationsOn q P.B
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let A := (absorberGreedyInitialState F
    (outsideAvailableTriangles P.H P.B)).available
  let i : Fin 2 := ⟨0, by omega⟩
  have hpoint : IsMasterStagePointwiseGood P.W 0 F G A
      ∅ ∅ 1 1 (t : ℝ≥0)⁻¹ h := by
    simpa only [F, G, A] using
      initialMasterStagePointwiseGood_of_typical P.typical
  have hInv : GreedyInvariant F (relativePreliminaryInitialState ∅ A) :=
    greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
      hpoint
  have hsupport : GraphSupportedOn G (P.W.U i.castSucc : Set (Fin n)) := by
    have hi : i.castSucc = (0 : Fin 3) := by ext; rfl
    rw [hi, P.W.root]
    intro u v _huv
    simp
  have hgap := P.initialOuterOnlyFloorGap hn
  exact P.typical.hasAvailablePairFloor_outerOnly hpoint.2.2.2.2.2.1
    i (by simp [i]) hsupport hh (n / 32)
      (by simpa only [i] using hgap) hInv

/-- The loss from the full outer-vertex pair star is only the level-zero
typicality error.  The deliberately doubled quotient avoids any ceiling
notation while still making this loss `o(n)` along the dyadic hierarchy. -/
theorem InitialHybridVortexPackage.initialOuterOnlyNearFullGap
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (hn : 31 < n) :
    let i : Fin 2 := ⟨0, by omega⟩
    let outer := (univ \ P.W.U i.succ).card
    let m := outer - 2 * (n / t) - 4
    (((((P.W.U i.succ).card + 2 + m : ℕ) : ℝ≥0)) <
      (1 - (t : ℝ≥0)⁻¹) *
        ((1 : ℝ≥0) ^ 2 * 1 * (P.W.U i.castSucc).card)) := by
  dsimp only
  let i : Fin 2 := ⟨0, by omega⟩
  let U := P.W.U i.succ
  let outer := (univ \ U).card
  let r := n / t
  have hiSucc : i.succ = (1 : Fin 3) := by ext; rfl
  have hiCast : i.castSucc = (0 : Fin 3) := by ext; rfl
  have hUcard : U.card = t ^ rootPower + n / 2 := by
    simpa only [U, hiSucc] using P.firstLevel_card
  have hroot8 : 8 * t ^ rootPower ≤ n :=
    (Nat.mul_le_mul_left 8 P.rootPower_le_absorberBound).trans P.absorberEight
  have hhalf : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have hUle : U.card ≤ n := by
    rw [hUcard]
    omega
  have houterCard : outer = n - U.card := by
    simp [outer, card_sdiff]
  have htPos : 0 < t := (by norm_num : 0 < 8).trans_le P.base_ge_eight
  have hrMul : r * t ≤ n := by
    simpa only [r, Nat.mul_comm] using Nat.div_mul_le_self n t
  have houterLarge : 2 * r + 4 ≤ outer := by
    have htEight : 8 * r ≤ n := by
      calc
        8 * r ≤ t * r := Nat.mul_le_mul_right r P.base_ge_eight
        _ = r * t := Nat.mul_comm _ _
        _ ≤ n := hrMul
    rw [houterCard, hUcard]
    omega
  have hsum : U.card + outer = n := by
    rw [houterCard]
    omega
  have hleftNat : U.card + 2 + (outer - 2 * r - 4) =
      n - 2 * r - 2 := by
    omega
  have hquotient : (n : ℝ≥0) / (t : ℝ≥0) < (r + 1 : ℕ) := by
    apply (div_lt_iff₀ (by exact_mod_cast htPos)).2
    have hmod : n % t < t := Nat.mod_lt n htPos
    have hdecomp : n % t + t * (n / t) = n := Nat.mod_add_div n t
    have hnlt : n < t + t * (n / t) := by omega
    have hnlt' : n < (r + 1) * t := by
      calc
        n < t + t * (n / t) := hnlt
        _ = (r + 1) * t := by simp [r]; ring
    exact_mod_cast hnlt'
  have hinvLeOne : (t : ℝ≥0)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ (by exact_mod_cast
      ((by norm_num : 1 ≤ 8).trans P.base_ge_eight))
  have hleftPlus :
      ((n - 2 * r - 2 : ℕ) : ℝ≥0) +
          (n : ℝ≥0) / (t : ℝ≥0) < (n : ℝ≥0) := by
    calc
      ((n - 2 * r - 2 : ℕ) : ℝ≥0) +
          (n : ℝ≥0) / (t : ℝ≥0) <
          ((n - 2 * r - 2 : ℕ) : ℝ≥0) + (r + 1 : ℕ) :=
        by simpa only [add_comm] using
          add_lt_add_left hquotient
            (((n - 2 * r - 2 : ℕ) : ℝ≥0))
      _ ≤ (n : ℝ≥0) := by
        exact_mod_cast (show n - 2 * r - 2 + (r + 1) ≤ n by omega)
  have hright : ((n - 2 * r - 2 : ℕ) : ℝ≥0) <
      (1 - (t : ℝ≥0)⁻¹) * (n : ℝ≥0) := by
    rw [tsub_mul, one_mul, inv_mul_eq_div]
    rw [lt_tsub_iff_right]
    simpa only [add_comm] using hleftPlus
  rw [hiCast, P.rootLevel_card]
  simp only [one_pow, one_mul]
  rw [show (P.W.U i.succ).card = U.card by rfl,
    show (univ \ P.W.U i.succ).card = outer by rfl,
    show n / t = r by rfl, hleftNat]
  exact hright

/-- Near-full initial live-pair floor at the first hybrid level. -/
theorem InitialHybridVortexPackage.initialOuterOnlyNearFullPairFloor
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (hh : 2 ≤ h) (hn : 31 < n) :
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let A := (absorberGreedyInitialState F
      (outsideAvailableTriangles P.H P.B)).available
    let i : Fin 2 := ⟨0, by omega⟩
    let outer := (univ \ P.W.U i.succ).card
    HasAvailablePairFloor (outer - 2 * (n / t) - 4 + 1)
      (absorberGreedyInitialState F
        (outerOnlyAvailable (P.W.U i.succ) A)) := by
  dsimp only
  let F := absorberErdosForbiddenConfigurationsOn q P.B
  let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let A := (absorberGreedyInitialState F
    (outsideAvailableTriangles P.H P.B)).available
  let i : Fin 2 := ⟨0, by omega⟩
  have hpoint : IsMasterStagePointwiseGood P.W 0 F G A
      ∅ ∅ 1 1 (t : ℝ≥0)⁻¹ h := by
    simpa only [F, G, A] using
      initialMasterStagePointwiseGood_of_typical P.typical
  have hInv : GreedyInvariant F (relativePreliminaryInitialState ∅ A) :=
    greedyInvariant_relativePreliminaryInitialState_of_masterPointwiseGood
      hpoint
  have hsupport : GraphSupportedOn G (P.W.U i.castSucc : Set (Fin n)) := by
    have hi : i.castSucc = (0 : Fin 3) := by ext; rfl
    rw [hi, P.W.root]
    intro u v _huv
    simp
  exact P.typical.hasAvailablePairFloor_outerOnly hpoint.2.2.2.2.2.1
    i (by simp [i]) hsupport hh
      ((univ \ P.W.U i.succ).card - 2 * (n / t) - 4)
      (by simpa only [i] using P.initialOuterOnlyNearFullGap hn) hInv

end

end Erdos207
