/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.VortexReindexInitialBands
import ErdosProblems.Erdos207.PowerSourceWellSpread

/-! # Direct absorber source bounds on prefixes of a retained power vortex -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem InitialPowerVortexPackage.reindexed_inner_separated
    {q h n ell length t rootPower step : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (stage : Fin (length + 1) → Fin (ell + 1)) (hstage : StrictMono stage) (hzero : stage 0 = 0)
    (i : Fin (length + 1)) (hi : i ≠ 0) :
    AbsorberSeparatedLevel P.H P.X P.B ((P.W.reindex stage hstage.monotone hzero).U i) := by
  apply P.inner_separated
  intro h0
  exact hi (hstage.injective (h0.trans hzero.symm))

theorem InitialPowerVortexPackage.reindexed_positive_prefix_sourceWellSpread
    {q h n ell length t rootPower step R : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (stage : Fin (length + 1) → Fin (ell + 1)) (hstage : StrictMono stage) (hzero : stage 0 = 0)
    (ht : 2 ≤ t) (hell : 0 < ell) (hcoeff : powerBankSubsetCoefficient q ≤ t)
    (hgap : powerBankSubsetExponent q rootPower + max rootPower (step * (ell - 1)) + 1 ≤ R)
    (hscale : t ^ R ≤ n) (i : Fin length) (j : ℕ) (hj : 4 ≤ j) (hjq : j ≤ q) :
    SourceVortexWellSpread ((P.W.reindex stage hstage.monotone hzero).prefix i.succ) j
      (absorberInducedConfigurationsOn q j P.B)
      (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1))
      (2 * (((2 : ℝ≥0) ^ (12 * (q + 2) ^ 2) + 1) * exactBankVortexOrderCoefficient q (i.val + 1)) +
        exactBankVortexCoefficient j (i.val + 1)) := by
  let W := P.W.reindex stage hstage.monotone hzero
  have hprefixRoot : (W.prefix i.succ).U 0 = P.W.U 0 := by
    rw [(W.prefix i.succ).root, P.W.root]
  have hterminal : 0 < (W.prefix i.succ).terminalSize := by
    rw [W.prefix_terminalSize]
    exact card_pos.mpr (P.nonempty (stage i.succ))
  have hroot : 0 < ((W.prefix i.succ).U 0).card := by
    rw [hprefixRoot]
    exact card_pos.mpr (P.nonempty 0)
  have hsep : ∀ x ∈ graphSupportFinset P.H, x ∉ P.X → x ∉ (W.prefix i.succ).U 1 := by
    intro x hxH hxX hxU
    let k := vortexPrefixEmbedding i.succ (1 : Fin (i.succ.val + 1))
    have hk : k ≠ 0 := by
      intro hk0
      have hv := congrArg Fin.val hk0
      have hone : (1 : Fin (i.succ.val + 1)).val = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by simp only [Fin.val_succ]; omega)
      change (1 : Fin (i.succ.val + 1)).val = 0 at hv
      omega
    exact ((P.reindexed_inner_separated stage hstage hzero k hk).2 x hxU hxX).1 hxH
  have hbankRoot : (subsetsUpToCard P.B q).card ≤ ((W.prefix i.succ).U 0).card := by
    rw [hprefixRoot]
    apply P.bankSubsets_le_root hcoeff (E := R) ?_ hscale
    change powerBankSubsetExponent q rootPower ≤ R
    omega
  have hbank : ((subsetsUpToCard P.B q).card : ℝ≥0) * (W.prefix i.succ).terminalSize ≤
      ((W.prefix i.succ).U 0).card * (1 : ℝ≥0) := by
    rw [W.prefix_terminalSize, hprefixRoot, mul_one]
    have hstagePos : stage i.succ ≠ 0 := by
      intro hz
      exact Fin.succ_ne_zero i (hstage.injective (hz.trans hzero.symm))
    exact_mod_cast P.bankSubsets_mul_level_le_root ht hell hcoeff hgap hscale (stage i.succ) hstagePos
  exact absorberInduced_sourceVortexWellSpread_localized (W.prefix i.succ) P.H P.X P.B 1
    P.localization hsep hj hjq hterminal hroot hbankRoot hbank

theorem InitialPowerVortexPackage.reindexed_zero_prefix_sourceWellSpread
    {q h n ell length t rootPower step R : ℕ}
    (P : InitialPowerVortexPackage q h n ell t rootPower step)
    (stage : Fin (length + 1) → Fin (ell + 1)) (hstage : Monotone stage) (hzero : stage 0 = 0)
    (hcoeff : powerBankSubsetCoefficient q ≤ t)
    (hgap : powerBankSubsetExponent q rootPower ≤ R) (hscale : t ^ R ≤ n)
    (j : ℕ) (hj : 4 ≤ j) :
    SourceVortexWellSpread ((P.W.reindex stage hstage hzero).prefix 0) j
      (absorberInducedConfigurationsOn q j P.B)
      (2 * exactBankVortexOrderCoefficient q 0)
      (2 * ((subsetsUpToCard P.B q).card * (exactBankVortexOrderCoefficient q 0 : ℝ≥0)) +
        exactBankVortexCoefficient j 0) := by
  let W := P.W.reindex stage hstage hzero
  have hterminalEq : (W.prefix 0).terminalSize = (P.W.U 0).card := by
    rw [W.prefix_terminalSize]
    change (P.W.U (stage 0)).card = (P.W.U 0).card
    rw [hzero]
  have hterminal : 0 < (W.prefix 0).terminalSize := by
    rw [hterminalEq]
    exact card_pos.mpr (P.nonempty 0)
  have hbank : (subsetsUpToCard P.B q).card ≤ (W.prefix 0).terminalSize := by
    rw [hterminalEq]
    exact P.bankSubsets_le_root hcoeff hgap hscale
  exact absorberInduced_sourceVortexWellSpread_global (W.prefix 0) P.B hj hterminal hbank

end

end Erdos207
