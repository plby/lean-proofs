/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialPowerTransitionData
import ErdosProblems.Erdos207.OuterOnlyResidualDegree
import ErdosProblems.Erdos207.PowerVortexLevelBounds

/-!
# Initial outer-only pair bounds for the power vortex

The level-zero typicality package gives a live-pair floor through the first
positive vortex level.  Together with the exact outer-only injection this
supplies both initial endpoints of the recursive sharp schedule.
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

/-- The first power-vortex boundary has an arbitrary certified pair floor
whenever the corresponding level-zero typicality gap is available. -/
theorem InitialPowerVortexPackage.initialOuterOnlyPairFloor_of_gap
    {q h n ell t rootPower step m : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (hh : 2 ≤ h)
    (hgap : ((((P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 2 + m : ℕ) :
        ℝ≥0) <
      (1 - (t : ℝ≥0)⁻¹) *
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
      ∅ ∅ 1 1 (t : ℝ≥0)⁻¹ h := by
    simpa only [F, G, A] using
      initialMasterStagePointwiseGood_of_typical P.typical
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
  exact P.typical.hasAvailablePairFloor_outerOnly hpoint.2.2.2.2.2.1
    i (by simp [i]) hsupport hh m (by simpa only [i] using hgap) hInv

/-- At the same boundary every available pair star is bounded by the exact
number of vertices outside the protected first level. -/
theorem InitialPowerVortexPackage.initialOuterOnlyPairCutoff
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (hh : 2 ≤ h)
    (hgap : ((((P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 2 : ℕ) :
        ℝ≥0) <
      (1 - (t : ℝ≥0)⁻¹) *
        ((1 : ℝ≥0) ^ 2 * 1 *
          (P.W.U ((⟨0, hell⟩ : Fin ell).castSucc)).card))) :
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let A := (absorberGreedyInitialState F
      (outsideAvailableTriangles P.H P.B)).available
    let i : Fin ell := ⟨0, hell⟩
    HasAvailablePairCutoff (univ \ P.W.U i.succ).card
      (absorberGreedyInitialState F
        (outerOnlyAvailable (P.W.U i.succ) A)) := by
  dsimp only
  let F := absorberErdosForbiddenConfigurationsOn q P.B
  let A := (absorberGreedyInitialState F
    (outsideAvailableTriangles P.H P.B)).available
  let i : Fin ell := ⟨0, hell⟩
  have hready := P.initialOuterOnlyReady hell hh hgap
  exact hasAvailablePairCutoff_outerOnly_card hready.1

/-- A near-full pair floor follows from two transparent cardinal facts: the
common base is at least eight and the first positive vortex level occupies
at most half of the ambient vertices, with a fixed margin. -/
theorem InitialPowerVortexPackage.initialOuterOnlyNearFullGap
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (ht : 8 ≤ t)
    (hlevelSmall : 2 * (P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 8 ≤ n) :
    let i : Fin ell := ⟨0, hell⟩
    let U := P.W.U i.succ
    let outer := (univ \ U).card
    let m := outer - 2 * (n / t) - 4
    (((((U.card + 2 + m : ℕ) : ℝ≥0)) <
      (1 - (t : ℝ≥0)⁻¹) *
        ((1 : ℝ≥0) ^ 2 * 1 * (P.W.U i.castSucc).card))) := by
  dsimp only
  let i : Fin ell := ⟨0, hell⟩
  let U := P.W.U i.succ
  let outer := (univ \ U).card
  let r := n / t
  have hiCast : i.castSucc = (0 : Fin (ell + 1)) := by
    ext
    rfl
  have hUle : U.card ≤ n := by
    have hcard : U.card ≤ Fintype.card (Fin n) := Finset.card_le_univ U
    simpa only [Fintype.card_fin] using hcard
  have houterCard : outer = n - U.card := by
    simp [outer, card_sdiff]
  have htPos : 0 < t := (by norm_num : 0 < 8).trans_le ht
  have hrMul : r * t ≤ n := by
    simpa only [r, Nat.mul_comm] using Nat.div_mul_le_self n t
  have heightR : 8 * r ≤ n := by
    calc
      8 * r ≤ t * r := Nat.mul_le_mul_right r ht
      _ = r * t := Nat.mul_comm _ _
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
      ((by norm_num : 1 ≤ 8).trans ht))
  have hleftPlus :
      ((n - 2 * r - 2 : ℕ) : ℝ≥0) +
          (n : ℝ≥0) / (t : ℝ≥0) < (n : ℝ≥0) := by
    calc
      ((n - 2 * r - 2 : ℕ) : ℝ≥0) +
          (n : ℝ≥0) / (t : ℝ≥0) <
          ((n - 2 * r - 2 : ℕ) : ℝ≥0) + (r + 1 : ℕ) :=
        by simpa only [add_comm] using
          add_lt_add_left hquotient (((n - 2 * r - 2 : ℕ) : ℝ≥0))
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

/-- The preceding gap gives the concrete near-full live-pair floor used to
initialize the sharp recursive trajectory. -/
theorem InitialPowerVortexPackage.initialOuterOnlyNearFullPairFloor
    {q h n ell t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (hh : 2 ≤ h) (ht : 8 ≤ t)
    (hlevelSmall : 2 * (P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 8 ≤ n) :
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let A := (absorberGreedyInitialState F
      (outsideAvailableTriangles P.H P.B)).available
    let i : Fin ell := ⟨0, hell⟩
    let outer := (univ \ P.W.U i.succ).card
    HasAvailablePairFloor (outer - 2 * (n / t) - 4 + 1)
      (absorberGreedyInitialState F
        (outerOnlyAvailable (P.W.U i.succ) A)) := by
  dsimp only
  apply P.initialOuterOnlyPairFloor_of_gap hell hh
  simpa only using P.initialOuterOnlyNearFullGap hell ht hlevelSmall

/-- The dyadic power hierarchy automatically makes the first positive level
small enough for the near-full initial pair floor. -/
theorem InitialPowerVortexPackage.firstLevel_twice_add_eight_le
    {q h n ell t rootPower step E : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (hell : 0 < ell) (ht : 12 ≤ t)
    (hexponent : max rootPower (step * (ell - 1)) + 1 ≤ E)
    (hpower : t ^ E ≤ n) :
    2 * (P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 8 ≤ n := by
  let i : Fin ell := ⟨0, hell⟩
  have hiSucc : i.succ.val = 1 := rfl
  have hiNonzero : i.succ ≠ (0 : Fin (ell + 1)) := by
    intro heq
    have := congrArg Fin.val heq
    simp [i] at this
  have hlevel := P.positiveLevel_card_le_two_mul_power i.succ hiNonzero
  rw [hiSucc] at hlevel
  let A := max rootPower (step * (ell - 1))
  have htOne : 1 ≤ t := (by norm_num : 1 ≤ 12).trans ht
  have hpowOne : 1 ≤ t ^ A := Nat.one_le_pow A t htOne
  have hfour : 2 * (P.W.U i.succ).card ≤ 4 * t ^ A := by
    calc
      2 * (P.W.U i.succ).card ≤ 2 * (2 * t ^ A) := by
        simpa only [A] using Nat.mul_le_mul_left 2 hlevel
      _ = 4 * t ^ A := by ring
  have htwelve : 4 * t ^ A + 8 ≤ 12 * t ^ A := by omega
  calc
    2 * (P.W.U ((⟨0, hell⟩ : Fin ell).succ)).card + 8 =
        2 * (P.W.U i.succ).card + 8 := rfl
    _ ≤ 4 * t ^ A + 8 := Nat.add_le_add_right hfour 8
    _ ≤ 12 * t ^ A := htwelve
    _ ≤ t * t ^ A := Nat.mul_le_mul_right (t ^ A) ht
    _ = t ^ (A + 1) := by rw [pow_succ, Nat.mul_comm]
    _ ≤ t ^ E := Nat.pow_le_pow_right
      (Nat.zero_lt_one.trans_le htOne) hexponent
    _ ≤ n := hpower

end

end Erdos207
