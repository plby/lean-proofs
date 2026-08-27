/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialHybridVortexPackage
import ErdosProblems.Erdos207.PowerBankSubsetAbsorption
import ErdosProblems.Erdos207.PowerSeparatedLocalizedMasterFirstMoment
import ErdosProblems.Erdos207.VortexA2LocalizedRootedThreatWeight
import ErdosProblems.Erdos207.MasterOutsidePairSurvival
import ErdosProblems.Erdos207.OuterOnlyPreliminaryGeometry

/-!
# Deterministic transition data for the hybrid vortex
-/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

@[simp]
theorem InitialHybridVortexPackage.rootLevel_card
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower) :
    (P.W.U 0).card = n := by
  rw [P.W.root, card_univ, Fintype.card_fin]

@[simp]
theorem InitialHybridVortexPackage.terminalSize_eq
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower) :
    P.W.terminalSize = t ^ rootPower := by
  rw [Vortex.terminalSize, P.terminal, P.rootCard]

@[simp]
theorem InitialHybridVortexPackage.firstLevel_card
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower) :
    (P.W.U (1 : Fin 3)).card = t ^ rootPower + n / 2 := by
  rw [P.levelCard 1 (by decide), hybridFreeSize_one]

lemma InitialHybridVortexPackage.rootPower_le_absorberBound
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower) :
    t ^ rootPower ≤ highGirthAbsorberCardCoefficient (q + 2) *
      (2 * t ^ rootPower) ^ 156 := by
  have htOne : 1 ≤ t := (by norm_num : 1 ≤ 8).trans P.base_ge_eight
  have hcoef : 1 ≤ highGirthAbsorberCardCoefficient (q + 2) := by
    have hp : 0 < highGirthAbsorberCardCoefficient (q + 2) := by
      unfold highGirthAbsorberCardCoefficient cycleCoverCardConstant
      positivity
    omega
  have hbase : t ^ rootPower ≤ 2 * t ^ rootPower := by omega
  have hpow : 2 * t ^ rootPower ≤ (2 * t ^ rootPower) ^ 156 := by
    simpa only [pow_one] using pow_le_pow_right'
      (by have := one_le_pow_of_one_le' htOne rootPower; omega :
        1 ≤ 2 * t ^ rootPower)
      (by omega : 1 ≤ 156)
  calc
    t ^ rootPower ≤ (2 * t ^ rootPower) ^ 156 := hbase.trans hpow
    _ = 1 * (2 * t ^ rootPower) ^ 156 := by simp
    _ ≤ highGirthAbsorberCardCoefficient (q + 2) *
        (2 * t ^ rootPower) ^ 156 := Nat.mul_le_mul_right _ hcoef

/-- The half-density first level satisfies the strict gap needed to
reinitialize the outer-only process. -/
theorem InitialHybridVortexPackage.initialOuterOnlyGap
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (hn : 17 < n) :
    ((((P.W.U ((⟨0, by omega⟩ : Fin 2).succ)).card + 2 : ℕ) : ℝ≥0) <
      (1 - (t : ℝ≥0)⁻¹) *
        ((1 : ℝ≥0) ^ 2 * 1 *
          (P.W.U ((⟨0, by omega⟩ : Fin 2).castSucc)).card)) := by
  have hroot8 : 8 * t ^ rootPower ≤ n :=
    (Nat.mul_le_mul_left 8 P.rootPower_le_absorberBound).trans P.absorberEight
  have hhalf : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
  have hnatLeft : 4 * (t ^ rootPower + n / 2 + 2) < 3 * n := by
    omega
  have hleft : (((t ^ rootPower + n / 2 + 2 : ℕ) : ℝ≥0)) <
      (3 * (n : ℝ≥0)) / 4 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 4)).2
    exact_mod_cast (by simpa only [mul_comm] using hnatLeft)
  have htNat : 0 < t := (by norm_num : 0 < 8).trans_le P.base_ge_eight
  have heightNat : 8 ≤ t := P.base_ge_eight
  have htpos : (0 : ℝ≥0) < t := by exact_mod_cast htNat
  have hinv : (t : ℝ≥0)⁻¹ ≤ (8 : ℝ≥0)⁻¹ := by
    apply (inv_le_inv₀ htpos (by norm_num : (0 : ℝ≥0) < 8)).2
    exact_mod_cast heightNat
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

/-- The packaged initial typical state gives the level-zero compressed law. -/
theorem InitialHybridVortexPackage.exists_initialCompressedMasterLaw
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (hadmissible : Admissible n) :
    ∃ law : FiniteLaw (MasterStateOn (Fin n)),
      IsCompressedMasterLaw law P.W 0
        (absorberErdosForbiddenConfigurationsOn q P.B)
        (graphDifference (SimpleGraph.completeGraph (Fin n)) P.H)
        (outsideAvailableTriangles P.H P.B)
        1 1 (t : ℝ≥0)⁻¹ 1 0 h := by
  let Gzero := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
  let A := (absorberGreedyInitialState
    (absorberErdosForbiddenConfigurationsOn q P.B)
    (outsideAvailableTriangles P.H P.B)).available
  let ambient := outsideAvailableTriangles P.H P.B
  have hpoint : IsMasterStagePointwiseGood P.W 0
      (absorberErdosForbiddenConfigurationsOn q P.B) Gzero A
      ∅ ∅ 1 1 (t : ℝ≥0)⁻¹ h := by
    simpa only [Gzero, A] using
      initialMasterStagePointwiseGood_of_typical P.typical
  have heven : ∀ v : Fin n, Even ((neighborsIn Gzero univ v).card) := by
    simpa only [Gzero] using
      initialRemainder_even_of_admissible_absorber hadmissible P.absorption
  have hsupport : GraphSupportedOn Gzero (P.W.U 0 : Set (Fin n)) := by
    rw [P.W.root]
    intro u v _huv
    simp
  have hA : A ⊆ ambient := by
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let A₀ := outsideAvailableTriangles P.H P.B
    have hInv : AbsorberGreedyInvariant F A₀
        (absorberGreedyInitialState F A₀) :=
      absorberGreedyInitialState_invariant F A₀
        (fun _S hS ↦ absorberErdosForbidden_nonempty hS)
    simpa only [A, ambient, F, A₀] using hInv.2.1.2
  refine ⟨FiniteLaw.pure (initialMasterState Gzero A), ?_⟩
  exact initialCompressedMasterLaw_of_pointwise_subset heven hsupport hA hpoint

/-- Reinitialize the hybrid base state on triangles disjoint from the first
positive level. -/
theorem InitialHybridVortexPackage.initialOuterOnlyReady
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (hh : 2 ≤ h)
    (hgap : ((((P.W.U ((⟨0, by omega⟩ : Fin 2).succ)).card + 2 : ℕ) : ℝ≥0) <
      (1 - (t : ℝ≥0)⁻¹) *
        ((1 : ℝ≥0) ^ 2 * 1 *
          (P.W.U ((⟨0, by omega⟩ : Fin 2).castSucc)).card))) :
    let F := absorberErdosForbiddenConfigurationsOn q P.B
    let G := graphDifference (SimpleGraph.completeGraph (Fin n)) P.H
    let A := (absorberGreedyInitialState F
      (outsideAvailableTriangles P.H P.B)).available
    let i : Fin 2 := ⟨0, by omega⟩
    let S₀ := absorberGreedyInitialState F
      (outerOnlyAvailable (P.W.U i.succ) A)
    AbsorberGreedyInvariant F (outerOnlyAvailable (P.W.U i.succ) A) S₀ ∧
      OutsideLeavePairsAlive
        (internalOuterGraph G (P.W.U i.succ))ᶜ (P.W.U i.succ) S₀ ∧
      S₀.chosen = ∅ := by
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
  exact P.typical.absorberGreedyInitialState_outerOnly_ready
    i (by simp [i]) hsupport hh hgap hInv
      (fun _S hS ↦ absorberErdosForbidden_nonempty hS)

/-- Bounded bank subfamilies fit into the ambient level under the same
common-base exponent gap as in the all-power package. -/
theorem InitialHybridVortexPackage.bankSubsets_le_root
    {q h n t rootPower E : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (hcoeff : powerBankSubsetCoefficient q ≤ t)
    (hExp : 3 * (156 * rootPower) * q + 1 ≤ E)
    (hn : t ^ E ≤ n) :
    (subsetsUpToCard P.B q).card ≤ (P.W.U 0).card := by
  let c := powerAbsorberCoefficient q
  let b := 156 * rootPower
  have ht : 1 ≤ t := (by norm_num : 1 ≤ 8).trans P.base_ge_eight
  have htpow : 1 ≤ t ^ (3 * b) := Nat.one_le_pow _ _ ht
  have hbank : P.B.card ≤ (c * t ^ b) ^ 3 := by
    simpa only [c, b, highGirthAbsorber_power_normalize] using P.bankCard
  have hbase : P.B.card + 1 ≤ (c ^ 3 + 1) * t ^ (3 * b) := by
    calc
      P.B.card + 1 ≤ (c * t ^ b) ^ 3 + 1 := Nat.add_le_add_right hbank 1
      _ = c ^ 3 * t ^ (3 * b) + 1 := by
        rw [mul_pow, ← pow_mul]
        simp only [Nat.mul_comm b 3]
      _ ≤ c ^ 3 * t ^ (3 * b) + t ^ (3 * b) :=
        Nat.add_le_add_left htpow _
      _ = (c ^ 3 + 1) * t ^ (3 * b) := by ring
  calc
    (subsetsUpToCard P.B q).card ≤
        (q + 1) * (P.B.card + 1) ^ q := card_subsetsUpToCard_le P.B q
    _ ≤ (q + 1) * ((c ^ 3 + 1) * t ^ (3 * b)) ^ q := by gcongr
    _ = powerBankSubsetCoefficient q * t ^ (3 * b * q) := by
      simp only [powerBankSubsetCoefficient, c, mul_pow, ← pow_mul]
      ring
    _ ≤ t ^ E := coeff_mul_pow_le_pow ht hcoeff (by
      simpa only [b] using hExp)
    _ ≤ n := hn
    _ = (P.W.U 0).card := P.rootLevel_card.symm

/-- Every positive hybrid level is absorber-separated. -/
theorem InitialHybridVortexPackage.separatedLevel
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (k : Fin 3) (hk : k ≠ 0) :
    AbsorberSeparatedLevel P.H P.X P.B (P.W.U k) := by
  rw [P.vortex_eq]
  exact separatedCardinalVortex_separated P.H P.X P.B
    (hybridFreeSize n) (hybridFreeSize_antitone n) hk

/-- The first positive hybrid level is disjoint from the non-root support of
the absorber graph. -/
theorem InitialHybridVortexPackage.firstLevel_graphSeparated
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower) :
    ∀ x ∈ P.W.U 1, x ∉ P.X → x ∉ graphSupportFinset P.H := by
  have hsep : AbsorberSeparatedLevel P.H P.X P.B (P.W.U 1) :=
    P.separatedLevel 1 (by decide)
  intro x hx hxX
  exact (hsep.2 x hx hxX).1

/-- The A2-sharp all-root localized extension estimate also holds at either
positive endpoint of the two-step hybrid vortex. -/
theorem InitialHybridVortexPackage.localizedMasterExtensionBound
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (i : Fin 2) (p : ℝ≥0) (hp : p ≤ 1)
    (hbank : (subsetsUpToCard P.B q).card ≤ (P.W.U 0).card)
    (e : DistinctPair (Fin n)) :
    HasExtensionBound
      (fun z : LocalizedRootedThreatWitness (Fin n)
          (absorberErdosForbiddenConfigurationsOn q P.B)
          e.1.1 e.1.2 (P.W.U i.succ) ↦
        localizedRootedThreatRemainder z)
      (masterUnionTriangleWeight P.W i.succ p)
      (((P.W.U i.succ).card : ℝ≥0) *
        localizedRootedThreatVortexA2LargeCoefficient
          (P.W.prefix i.succ) q (12 * (q + 2) ^ 2) 2 0) := by
  apply localizedRootedThreatRemainder_hasExtensionBound_masterUnion_A2
    P.W P.H P.X P.B i p hp P.localization P.firstLevel_graphSeparated
      P.nonempty hbank e.2

/-- The same localized extension estimate with one additional ambient
inverse point weight, as required to select an old packing with uniform
relative extension bounds. -/
theorem InitialHybridVortexPackage.localizedMasterExtensionBound_add_ambient
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (i : Fin 2) (p : ℝ≥0) (hp : p ≤ 1)
    (hbank : (subsetsUpToCard P.B q).card ≤ (P.W.U 0).card)
    (e : DistinctPair (Fin n)) :
    HasExtensionBound
      (fun z : LocalizedRootedThreatWitness (Fin n)
          (absorberErdosForbiddenConfigurationsOn q P.B)
          e.1.1 e.1.2 (P.W.U i.succ) ↦
        localizedRootedThreatRemainder z)
      (fun T ↦ masterUnionTriangleWeight P.W i.succ p T +
        (n : ℝ≥0)⁻¹)
      (((P.W.U i.succ).card : ℝ≥0) *
        localizedRootedThreatVortexA2LargeCoefficient
          (P.W.prefix i.succ) q (12 * (q + 2) ^ 2) 3 0) := by
  simpa only [Fintype.card_fin] using
    localizedRootedThreatRemainder_hasExtensionBound_masterUnion_add_ambient_A2
      P.W P.H P.X P.B i p hp P.localization P.firstLevel_graphSeparated
        P.nonempty hbank e.2 (P.W.U i.succ)

/-- Linear empty-root master extension bound at either hybrid transition. -/
theorem InitialHybridVortexPackage.localizedMasterFirstMomentBound
    {q h n t rootPower : ℕ}
    (P : InitialHybridVortexPackage q h n t rootPower)
    (i : Fin 2) (p : ℝ≥0) (hp : p ≤ 1)
    (hbank : (subsetsUpToCard P.B q).card ≤ (P.W.U 0).card)
    (e : DistinctPair (Fin n)) :
    extensionWeight
        (fun z : LocalizedRootedThreatWitness (Fin n)
            (absorberErdosForbiddenConfigurationsOn q P.B)
            e.1.1 e.1.2 (P.W.U i.succ) ↦
          localizedRootedThreatRemainder z)
        (masterUnionTriangleWeight P.W i.succ p) ∅ ≤
      ((P.W.U i.succ).card : ℝ≥0) *
        powerLocalizedRootedFirstCoefficient q i.val
          (12 * (q + 2) ^ 2) := by
  have hsepFull : AbsorberSeparatedLevel P.H P.X P.B (P.W.U 1) :=
    P.separatedLevel 1 (by decide)
  have hembOne : vortexPrefixEmbedding i.succ
      (1 : Fin (i.succ.val + 1)) = (1 : Fin 3) := by
    have hsrc : ((1 : Fin (i.succ.val + 1)).val) = 1 := by
      rw [Fin.val_one']
      exact Nat.mod_eq_of_lt (by
        have hisucc : 0 < i.succ.val := by simp
        omega)
    apply Fin.ext
    simp only [vortexPrefixEmbedding_val, hsrc, Fin.val_one']
  have hsepPrefix : AbsorberSeparatedLevel P.H P.X P.B
      ((P.W.prefix i.succ).U 1) := by
    simpa only [Vortex.prefix_U, hembOne] using hsepFull
  have houter : ∀ j : Fin (i.val + 1),
      0 < ((P.W.prefix i.succ).U j.castSucc).card := by
    intro j
    exact card_pos.mpr (P.nonempty _)
  have hterminal : 0 < (P.W.prefix i.succ).terminalSize := by
    rw [P.W.prefix_terminalSize i.succ]
    exact card_pos.mpr (P.nonempty i.succ)
  have hembZero : vortexPrefixEmbedding i.succ
      (0 : Fin (i.succ.val + 1)) = (0 : Fin 3) := by
    apply Fin.ext
    rfl
  have hbankPrefix : (subsetsUpToCard P.B q).card ≤
      ((P.W.prefix i.succ).U 0).card := by
    simpa only [Vortex.prefix_U, hembZero] using hbank
  have hvortex :=
    extensionWeight_localizedRootedThreat_vortex_empty_le_level_sharp
      (P.W.prefix i.succ) P.H P.X P.B 2 P.localization hsepPrefix
      houter hterminal hbankPrefix (P.W.U i.succ) e.2
  exact (extensionWeight_mono_pointwise _
      (masterUnionTriangleWeight_le_prefix_vortex_two
        P.W i.succ p hp P.nonempty) ∅).trans (by
    simpa only [powerLocalizedRootedFirstCoefficient] using hvortex)

end

end Erdos207
