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
import ErdosProblems.Erdos722.SpecialCliqueCandidatesAsymptotic
import Mathlib

set_option relaxedAutoImplicit true

/-!
# Fresh rotations after fixing the special exchange cliques

This is the probabilistic core of property (iv) in Keevash's Lemma 6.3.
The root clique is already rainbow.  For each root edge we first choose its
distinguished negative exchange clique in the correspondingly coloured
rotated unsaturated family.  Independent fresh rotations then put every
remaining exchange block into the base unsaturated family.
-/

namespace Erdos722.SpecialCliqueRotationAsymptotic

open Finset Filter
open scoped Topology Real
open Erdos722.Typicality
open Erdos722.Reserve
open Erdos722.IntegralGenerators
open Erdos722.Rotations
open Erdos722.GeneratorAsymptotic
open Erdos722.RotationAsymptotic
open Erdos722.CliqueRotationAsymptotic
open Erdos722.CandidateCliqueRotation
open Erdos722.SpecialCliqueCandidates
open Erdos722.SpecialCliqueCandidatesAsymptotic
open Erdos722.RootedEmbedding
open Erdos722.Exchange
open Erdos722.ExchangePattern

noncomputable section

/-- The base two-cap unsaturated clique family. -/
def baseUnsaturatedCliques
    {N n q r faceCap edgeCap threshold Mface Medge : ℕ}
    (D : TwoCapPrunedData N n q r faceCap edgeCap threshold Mface Medge) :
    Finset (Finset (Fin n)) :=
  twoCapUnsaturatedCliques n q r faceCap edgeCap D.K D.selected

/-- The distinguished clique associated with a root edge is selected from
the rotation indexed by that edge's already assigned rainbow colour. -/
def specialCliqueFamily
    {N n q r faceCap edgeCap threshold Mface Medge u : ℕ}
    (D : TwoCapPrunedData N n q r faceCap edgeCap threshold Mface Medge)
    (σ : Fin u → Equiv.Perm (Fin n)) (color : RootEdge q r → Fin u)
    (e : RootEdge q r) : Finset (Finset (Fin n)) :=
  rotateFamily (σ (color e)) (baseUnsaturatedCliques D)

theorem baseUnsaturatedCliques_uniform
    {N n q r faceCap edgeCap threshold Mface Medge : ℕ}
    (D : TwoCapPrunedData N n q r faceCap edgeCap threshold Mface Medge)
    {Q : Finset (Fin n)} (hQ : Q ∈ baseUnsaturatedCliques D) :
    Q.card = q := by
  exact (mem_cliquesIn.mp
    (mem_twoCapUnsaturatedCliques.mp hQ).1).1

theorem specialCliqueFamily_uniform
    {N n q r faceCap edgeCap threshold Mface Medge u : ℕ}
    (D : TwoCapPrunedData N n q r faceCap edgeCap threshold Mface Medge)
    (σ : Fin u → Equiv.Perm (Fin n)) (color : RootEdge q r → Fin u)
    (e : RootEdge q r) {Q : Finset (Fin n)}
    (hQ : Q ∈ specialCliqueFamily D σ color e) : Q.card = q := by
  have hpre : rotateEdge (σ (color e)).symm Q ∈
      baseUnsaturatedCliques D := mem_rotateFamily.mp hQ
  simpa using baseUnsaturatedCliques_uniform D hpre

/-- A surviving edge in a rotated colour has the full pruned local lower
bound in the correspondingly rotated unsaturated-clique family. -/
theorem specialCliqueFamily_local_lower
    {N n q r d u : ℕ} (hn : 0 < n) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    (ω : {e // e ∈ uniformEdges n r} → Bool)
    (D : TwoCapPrunedData N n q r
      (generatorFaceCap d n) (generatorEdgeCap d n)
      (generatorPruneThreshold q r d n)
      (generatorFaceCliqueCap q r d n)
      (generatorEdgeCliqueCap q r d n))
    (htyp : ∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
      commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
        Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω ∧
      Erdos722.Probability.finiteRandomSum
          (fun x ↦ commonNeighborIndicator n r roots (by omega)
            (root_card_of_mem_rootFamilies hroots) x) ω <
        2 * commonMean n roots (reserveProbabilityIcc n d hn))
    (hDK : D.K = sampledEdges n r ω)
    (hnlarge : 2 * (Nat.choose q r * (r - 1)) ≤ n)
    (σ : Fin u → Equiv.Perm (Fin n)) (color : RootEdge q r → Fin u)
    (e : RootEdge q r) {g : Finset (Fin n)}
    (hg : g ∈ D.rotatedKstar σ (color e)) :
    generatorCliqueLower q r d n - generatorPruneThreshold q r d n ≤
      ((specialCliqueFamily D σ color e).filter fun Q ↦ g ⊆ Q).card := by
  let τ := σ (color e)
  let g₀ := rotateEdge τ.symm g
  have hg₀ : g₀ ∈ D.Kstar := by
    exact mem_rotateFamily.mp (by
      simpa [TwoCapPrunedData.rotatedKstar, τ, g₀] using hg)
  have hgSample : g₀ ∈ sampledEdges n r ω := by
    simpa [← hDK] using D.Kstar_subset hg₀
  have htotal : generatorCliqueLower q r d n ≤
      ((cliquesIn n q r D.K).filter fun Q ↦ g₀ ⊆ Q).card := by
    simpa [hDK] using generatorCliqueLower_le_cliques_through_edge
      hn hr hrq hqd hnlarge ω htyp hgSample
  have hbase : generatorCliqueLower q r d n -
      generatorPruneThreshold q r d n ≤
        ((baseUnsaturatedCliques D).filter fun Q ↦ g₀ ⊆ Q).card :=
    (Nat.sub_le_sub_right htotal
      (generatorPruneThreshold q r d n)).trans (by
        simpa [baseUnsaturatedCliques] using D.good_lower g₀ hg₀)
  have hrot := counterLoad_rotateFamily τ (baseUnsaturatedCliques D) g₀
  change generatorCliqueLower q r d n -
      generatorPruneThreshold q r d n ≤
        Generators.counterLoad (fun a Q : Finset (Fin n) ↦ a ⊆ Q)
          (specialCliqueFamily D σ color e) g
  rw [show g = rotateEdge τ g₀ by simp [g₀]]
  simpa [specialCliqueFamily, τ] using hbase.trans_eq hrot.symm

/-- Exact denominator-clearing for an arbitrary restricted candidate
family. -/
theorem candidateRotation_exceptional_of_expected_lower
    {v n m q : ℕ} {embeddings : Finset (Fin v ↪ Fin n)}
    {U : Finset (Finset (Fin n))}
    (hU : ∀ Q ∈ U, Q.card = q)
    {blocks : Fin m → Finset (Fin v)}
    (hblocks : ∀ i, (blocks i).card = q)
    (φ : Fin v ↪ Fin n) {L : ℕ}
    (hexpected : L * Nat.choose n q ^ m ≤
      embeddings.card * U.card ^ m) :
    Fintype.card (Fin m → Equiv.Perm (Fin n)) * L ≤
      embeddings.card * (rootedRotationSuccess U blocks φ).card := by
  let A := (rootedRotationSuccess U blocks φ).card
  let S := Fintype.card (Fin m → Equiv.Perm (Fin n))
  let W := Nat.choose n q
  have htargets : ∀ i, (mapEdge φ (blocks i)).card = q := by
    intro i
    exact (card_mapEdge φ (blocks i)).trans (hblocks i)
  have hsuccess : A * W ^ m = U.card ^ m * S := by
    simpa [A, W, S, rootedRotationSuccess, mappedTargets,
      Fintype.card_fun] using
      (card_rainbowHitSamples_mul_choose_pow hU htargets)
  have hWpow : 0 < W ^ m := by
    by_cases hm : m = 0
    · simp [hm]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let i : Fin m := ⟨0, hmpos⟩
      have hqn : q ≤ n := by
        calc
          q = (blocks i).card := (hblocks i).symm
          _ = (mapEdge φ (blocks i)).card :=
            (card_mapEdge φ _).symm
          _ ≤ (Finset.univ : Finset (Fin n)).card :=
            Finset.card_le_card (Finset.subset_univ _)
          _ = n := by simp
      exact pow_pos (Nat.choose_pos hqn) m
  refine Nat.le_of_mul_le_mul_right ?_ hWpow
  calc
    (S * L) * W ^ m = S * (L * W ^ m) := by ring
    _ ≤ S * (embeddings.card * U.card ^ m) := by gcongr
    _ = embeddings.card * (U.card ^ m * S) := by ring
    _ = embeddings.card * (A * W ^ m) := by rw [← hsuccess]
    _ = (embeddings.card * A) * W ^ m := by ring

/-- The number of vertices occupied by the root and special cliques fits in
the exchange vertex set. -/
theorem specialSupportSize_le_v (E : RelabeledFullExchange q r) :
    specialSupportSize q r ≤ E.v := by
  calc
    specialSupportSize q r = (specialSupport E).card := by
      rw [specialSupport_card E]
      rfl
    _ ≤ (Finset.univ : Finset (Fin E.v)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = E.v := by simp

/-- Complete eventual second-moment estimate for the source-faithful
rainbow-span construction. -/
theorem eventually_prunedGenerator_specialCandidateRotation_failure
    (N q r d : ℕ) (hr : 1 < r) (hrq : r < q)
    (hqd : Nat.choose q r < d)
    (E : RelabeledFullExchange q r)
    (hbudget : Nat.choose q r *
      (Nat.choose q r - 1 + (remainingBlocks E).card) < d) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (hn : 0 < n)
        (ω : {e // e ∈ uniformEdges n r} → Bool)
        (D : TwoCapPrunedData N n q r
          (generatorFaceCap d n) (generatorEdgeCap d n)
          (generatorPruneThreshold q r d n)
          (generatorFaceCliqueCap q r d n)
          (generatorEdgeCliqueCap q r d n)),
      (∀ roots, ∀ hroots : roots ∈ rootFamilies n r (Nat.choose q r),
        commonMean n roots (reserveProbabilityIcc n d hn) / 2 <
          Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω ∧
        Erdos722.Probability.finiteRandomSum
            (fun x ↦ commonNeighborIndicator n r roots (by omega)
              (root_card_of_mem_rootFamilies hroots) x) ω <
          2 * commonMean n roots (reserveProbabilityIcc n d hn)) →
      D.K = sampledEdges n r ω →
      (uniformEdges n (r - 1)).card * generatorDegreeLower d n ≤
        2 * D.Kstar.card * Nat.choose r (r - 1) →
      ∀ (u : ℕ) (σ : Fin u → Equiv.Perm (Fin n))
        (request : RootRequest E.v n E.pattern.root)
        (color : RootEdge q r → Fin u),
      (∀ e, requestedRootEdge E request e ∈
        D.rotatedKstar σ (color e)) →
      let U₀ := baseUnsaturatedCliques D
      let families := specialCliqueFamily D σ color
      let m := (remainingBlocks E).card
      let blocks : Fin m → Finset (Fin E.v) := fun i ↦
        ((remainingBlocks E).equivFin.symm i).1
      let embeddings := specialGoodEmbeddings E request families
      let R := cliqueRotationPairConstant q r ^ m + 2
      R * ((rotationSamples n m).filter fun fresh ↦
        Erdos722.Probability.finiteSuccessCount embeddings
          (rootedRotationSuccess U₀ blocks) fresh = 0).card ≤
        (R - 1) * Fintype.card (Fin m → Equiv.Perm (Fin n)) := by
  have hpair := eventually_prunedGenerator_unsaturated_pair_ratio
    N q r d hr hrq hqd
  have hscale := eventually_specialCandidate_expected_lower
    hr hrq hqd (specialSupportSize_le_v E) hbudget
  have hprune := eventually_two_mul_generatorPruneThreshold_le_cliqueLower
    q r d (by omega) hrq hqd
  have herror := eventually_four_mul_specialChoiceError_le_cliqueLower
    q r d (by omega) hrq hqd
  have hKpos : 0 < Nat.choose q r := Nat.choose_pos hrq.le
  have hdegree := eventually_rpow_div_sixteen_le_generatorDegreeLower
    (by omega : 1 < d)
  have hclique := eventually_generatorCliqueLower_lower q r d
    (by omega) hrq hqd
  filter_upwards [hpair, hscale, hprune, herror, hdegree, hclique,
      eventually_ge_atTop
        (max (max (2 * E.v) q)
          (2 * (Nat.choose q r * (r - 1))))] with
      n hpair hscale hprune herror hdegree hclique hnlarge
  intro hn ω D htyp hDK hmass u σ request color hrootColors
  let U₀ := baseUnsaturatedCliques D
  let families := specialCliqueFamily D σ color
  let m := (remainingBlocks E).card
  let blocks : Fin m → Finset (Fin E.v) := fun i ↦
    ((remainingBlocks E).equivFin.symm i).1
  let embeddings := specialGoodEmbeddings E request families
  let R := cliqueRotationPairConstant q r ^ m + 2
  have hnGen : 2 * (Nat.choose q r * (r - 1)) ≤ n :=
    (le_max_right _ _).trans hnlarge
  have hnTwoV : 2 * E.v ≤ n :=
    ((le_max_left (2 * E.v) q).trans
      (le_max_left (max (2 * E.v) q) _)).trans hnlarge
  have hnq : q ≤ n :=
    ((le_max_right (2 * E.v) q).trans
      (le_max_left (max (2 * E.v) q) _)).trans hnlarge
  have hUuniform : ∀ Q ∈ U₀, Q.card = q := by
    intro Q hQ
    exact baseUnsaturatedCliques_uniform D hQ
  have hfamiliesUniform : ∀ e, ∀ Q ∈ families e, Q.card = q := by
    intro e Q hQ
    exact specialCliqueFamily_uniform D σ color e hQ
  have hlocal : ∀ e,
      generatorCliqueLower q r d n - generatorPruneThreshold q r d n ≤
        ((families e).filter fun Q ↦
          requestedRootEdge E request e ⊆ Q).card := by
    intro e
    exact specialCliqueFamily_local_lower hn hr hrq hqd ω D htyp hDK
      hnGen σ color e (hrootColors e)
  have hroom : specialChoiceError q r n ≤
      generatorCliqueLower q r d n - generatorPruneThreshold q r d n :=
    specialChoiceError_le_prunedLower hprune herror
  have hcandidatesLower :
      specialChoiceLower q r d n ^ Nat.choose q r *
          (n - specialSupportSize q r).descFactorial
            (E.v - specialSupportSize q r) ≤ embeddings.card := by
    have hmany := many_specialGoodEmbeddings E hrq request families
      hfamiliesUniform hlocal hroom
    simpa [embeddings, specialChoiceLower, specialChoiceError,
      specialSupportSize] using hmany
  have hmassU : Nat.choose n (r - 1) * generatorDegreeLower d n *
      generatorCliqueLower q r d n ≤
        (4 * r * Nat.choose q r) * U₀.card := by
    simpa [U₀, baseUnsaturatedCliques] using
      prunedGenerator_unsaturated_mass hn hr hrq hqd ω D htyp hDK hmass
        hnGen hprune
  have hscaleU :
      ((E.v - q) ^ 2 * n ^ (E.v - (q + 1))) *
          Nat.choose n q ^ m ≤
        specialChoiceLower q r d n ^ Nat.choose q r *
          (n - specialSupportSize q r).descFactorial
            (E.v - specialSupportSize q r) * U₀.card ^ m := by
    simpa [m] using hscale U₀ hmassU
  have hexpected :
      ((E.v - E.pattern.root.card) ^ 2 *
          n ^ (E.v - (E.pattern.root.card + 1))) *
          Nat.choose n q ^ m ≤ embeddings.card * U₀.card ^ m := by
    rw [E.root_card]
    exact hscaleU.trans (Nat.mul_le_mul_right _ hcandidatesLower)
  have hdegreePos : 0 < generatorDegreeLower d n := by
    have hstrict : (0 : ℝ) <
        (n : ℝ) ^ (((d - 1 : ℕ) : ℝ) / d) / 16 := by positivity
    have : (0 : ℝ) < generatorDegreeLower d n := hstrict.trans_le hdegree
    exact_mod_cast this
  have hcliquePos : 0 < generatorCliqueLower q r d n := by
    have hstrict : (0 : ℝ) <
        (n : ℝ) ^
          (((d * (q - r) - (Nat.choose q r - 1) : ℕ) : ℝ) / d) /
            (2 * (16 : ℝ) ^ (q - r) * (2 ^ q : ℝ) ^ (q - r)) := by
      positivity
    have : (0 : ℝ) < generatorCliqueLower q r d n :=
      hstrict.trans_le hclique
    exact_mod_cast this
  have hchoosePos : 0 < Nat.choose n (r - 1) :=
    Nat.choose_pos (by omega)
  have hUpos : 0 < U₀.card := by
    have hleft : 0 < Nat.choose n (r - 1) * generatorDegreeLower d n *
        generatorCliqueLower q r d n := by positivity
    have hright : 0 < (4 * r * Nat.choose q r) * U₀.card :=
      hleft.trans_le hmassU
    exact Nat.pos_of_mul_pos_left hright
  have hblocks : ∀ i, (blocks i).card = q := by
    intro i
    exact remainingBlocks_uniform E
      ((remainingBlocks E).equivFin.symm i).2
  have hproper : ∀ i, (blocks i ∩ E.pattern.root).card < r := by
    intro i
    exact remainingBlocks_inter_root_card_lt E
      ((remainingBlocks E).equivFin.symm i).2
  have hleftPos : 0 <
      ((E.v - E.pattern.root.card) ^ 2 *
        n ^ (E.v - (E.pattern.root.card + 1))) * Nat.choose n q ^ m := by
    have hrootlt := E.root_card_lt_v hrq
    have hnpos : 0 < n := hn
    have hchoose : 0 < Nat.choose n q := Nat.choose_pos hnq
    exact Nat.mul_pos
      (Nat.mul_pos (pow_pos (Nat.sub_pos_of_lt hrootlt) 2)
        (pow_pos hnpos _))
      (pow_pos hchoose _)
  have hcandidates : 0 < embeddings.card := by
    have hrightPos : 0 < embeddings.card * U₀.card ^ m :=
      hleftPos.trans_le hexpected
    exact Nat.pos_of_mul_pos_right hrightPos
  have hrooted : ∀ φ ∈ embeddings,
      ExtendsRequest E.pattern.root request φ := by
    intro φ hφ
    exact specialGoodEmbeddings_extends E request families hφ
  have hexceptional : ∀ φ ∈ embeddings,
      (outsideMeetingCandidates E.pattern.root embeddings φ).card ≤
        (E.v - E.pattern.root.card) ^ 2 *
          n ^ (E.v - (E.pattern.root.card + 1)) := by
    intro φ hφ
    exact card_outsideMeetingCandidates_le hrooted φ
  have hpairU : ∀ j < r,
      (orderedIntersectionPairs U₀ j).card * Nat.choose n q ^ 2 ≤
        cliqueRotationPairConstant q r * U₀.card ^ 2 *
          (orderedIntersectionPairs (uniformEdges n q) j).card := by
    simpa [U₀, baseUnsaturatedCliques] using
      hpair hn ω D htyp hDK hmass
  have hexception : ∀ φ ∈ embeddings,
      Fintype.card (Fin m → Equiv.Perm (Fin n)) *
          ((E.v - E.pattern.root.card) ^ 2 *
            n ^ (E.v - (E.pattern.root.card + 1))) ≤
        embeddings.card * (rootedRotationSuccess U₀ blocks φ).card := by
    intro φ hφ
    exact candidateRotation_exceptional_of_expected_lower
      hUuniform hblocks φ hexpected
  simpa [R, U₀, families, m, blocks, embeddings] using
    (candidateRotationFailures_paley hUuniform hpairU hblocks hproper
      hUpos hcandidates hrooted hexceptional hexception)

end

end Erdos722.SpecialCliqueRotationAsymptotic
