/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
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

import ErdosProblems.Erdos1165.AnnularBridgeFactorization
import ErdosProblems.Erdos1165.AnnularProfileLevelSkeleton
import ErdosProblems.Erdos1165.AlternatingConcatPrefixFree
import ErdosProblems.Erdos1165.TerminalSkeletonInvariance

/-!
# Exact stopped-word factorization at one intermediate annular level

For a fixed compressed complementary skeleton, canonical marked annular
bridge words are inserted between its retained pieces.  Prefix-free parsing
proves injectivity of the insertion map.  Once the complete assembled words
have their literal common stopping boundary, they form a genuine
`ComplementarySkeletonAtom`; its fair-walk mass is therefore exactly the
retained weight times the product of joint offspring-count/endpoint kernels.
-/

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1165.AnnularLevelFactorization

noncomputable section

open MarkedBridgeFactorization AnnularBoundaryExcursionKernel
open AnnularBridgeFactorization TerminalSkeletonWords
open TerminalSkeletonInvariance
open AlternatingConcatPrefixFree TerminalSequentialVisitLaw

private theorem assembleAfterPrefix_injective_of_prefixFree
    {start m : ℕ} (code : TerminalSkeletonCode m)
    (Bridge : Fin m → Type*)
    (word : (j : Fin m) → Bridge j → List Direction)
    (hfree : ∀ j, PrefixFree (fun b ↦ listStoppedWord (word j b))) :
    Function.Injective
      (fun c : (Fin start → Direction) × ((j : Fin m) → Bridge j) ↦
        assembleAfterPrefix c.1 code (fun j ↦ word j (c.2 j))) := by
  rintro ⟨pre, bridges⟩ ⟨pre', bridges'⟩ hassemble
  have hlists :
      List.ofFn pre ++ reconstructTerminalPacket
          (code, fun j ↦ word j (bridges j)) =
        List.ofFn pre' ++ reconstructTerminalPacket
          (code, fun j ↦ word j (bridges' j)) := by
    have hwords := congrArg (fun w : StoppedWord ↦ List.ofFn w.2) hassemble
    simpa only [assembleAfterPrefix, stoppedWordOfList_toList] using hwords
  have hpreList : List.ofFn pre = List.ofFn pre' :=
    List.append_inj_left hlists (by simp)
  have hpre : pre = pre' := List.ofFn_injective hpreList
  have htail :
      reconstructTerminalPacket (code, fun j ↦ word j (bridges j)) =
        reconstructTerminalPacket (code, fun j ↦ word j (bridges' j)) :=
    List.append_inj_right hlists (by simp)
  have hbridges : bridges = bridges' := by
    apply alternatingConcat_injective_of_prefixFree
      m code.1.retainedPiece Bridge word hfree
    simpa only [reconstructTerminalPacket] using htail
  simp only [hpre, hbridges]

private theorem prefixFree_of_injective_of_absoluteBoundaryFirstAt
    {Code : Type*} (word : Code → StoppedWord)
    (hinjective : Function.Injective word)
    (boundary : Set Point) (start : Point)
    (hfirst : ∀ c, AbsoluteBoundaryFirstAt boundary start
      (extendStoppedWord (word c)) (word c).1) :
    PrefixFree word := by
  intro c d hcd
  rw [Set.disjoint_left]
  intro omega hc hd
  have hcfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hc (hfirst c)
  have hdfirst := absoluteBoundaryFirstAt_of_mem_stoppedWordCylinder hd (hfirst d)
  have hlen : (word c).1 = (word d).1 :=
    absoluteBoundaryFirstAt_unique hcfirst hdfirst
  apply hcd
  apply hinjective
  apply Sigma.ext hlen
  apply (Fin.heq_fun_iff hlen).2
  intro i
  change stepPrefix (word c).1 omega = (word c).2 at hc
  change stepPrefix (word d).1 omega = (word d).2 at hd
  have hci := congrFun hc i
  have hdi := congrFun hd ⟨(i : ℕ), hlen ▸ i.2⟩
  simpa only [stepPrefix] using hci.symm.trans hdi

/-- Canonical marked bridge code at each coordinate of a one-level
complementary skeleton. -/
abbrev AnnularLevelBridgeCode {m : ℕ}
    (outer middle inner : Fin m → Set Point)
    (code : TerminalSkeletonCode m) (offspring : Fin m → ℕ)
    (j : Fin m) :=
  BoundaryExcursionExitWordCode
    (outer j) (middle j) (inner j)
    (code.2.1 j) (offspring j) (code.2.2 j)

/-- Erase the proof fields of the canonical bridge codes to the direction
lists inserted into the compressed skeleton. -/
def annularLevelBridgeWords {m : ℕ}
    {outer middle inner : Fin m → Set Point}
    {code : TerminalSkeletonCode m} {offspring : Fin m → ℕ}
    (bridges : (j : Fin m) →
      AnnularLevelBridgeCode outer middle inner code offspring j) :
    TerminalSegmentWords m := fun j ↦ List.ofFn (bridges j).1.2

/-- The stopped word obtained after an arbitrary deterministic pre-prefix
and the canonical marked intermediate-annulus insertions. -/
def assembleAnnularLevelBridges {start m : ℕ}
    {outer middle inner : Fin m → Set Point}
    (code : TerminalSkeletonCode m) (offspring : Fin m → ℕ)
    (c : (Fin start → Direction) × ((j : Fin m) →
      AnnularLevelBridgeCode outer middle inner code offspring j)) :
    StoppedWord :=
  assembleAfterPrefix c.1 code (annularLevelBridgeWords c.2)

theorem prefixFree_annularLevelBridgeWords
    {m : ℕ} {outer middle inner : Fin m → Set Point}
    (code : TerminalSkeletonCode m) (offspring : Fin m → ℕ)
    (j : Fin m) :
    PrefixFree (fun b : AnnularLevelBridgeCode
      outer middle inner code offspring j ↦
        listStoppedWord (List.ofFn b.1.2)) := by
  have hword (b : AnnularLevelBridgeCode
      outer middle inner code offspring j) :
      listStoppedWord (List.ofFn b.1.2) = b.1 := by
    have hlen : (listStoppedWord (List.ofFn b.1.2)).1 = b.1.1 := by
      simp [listStoppedWord]
    apply Sigma.ext hlen
    apply (Fin.heq_fun_iff hlen).2
    intro i
    simp [listStoppedWord]
  simpa only [hword] using
    (prefixFree_boundaryExcursionExitWordCode
      (outer j) (middle j) (inner j)
      (code.2.1 j) (offspring j) (code.2.2 j))

/-- Alternating reconstruction is injective in the pre-prefix and in every
canonical annular bridge word. -/
theorem assembleAnnularLevelBridges_injective
    {start m : ℕ} {outer middle inner : Fin m → Set Point}
    (code : TerminalSkeletonCode m) (offspring : Fin m → ℕ) :
    Function.Injective
      (assembleAnnularLevelBridges (start := start)
        (outer := outer) (middle := middle) (inner := inner)
        code offspring) := by
  apply assembleAfterPrefix_injective_of_prefixFree code
    (fun j ↦ AnnularLevelBridgeCode outer middle inner code offspring j)
    (fun _ b ↦ List.ofFn b.1.2)
  exact prefixFree_annularLevelBridgeWords code offspring

/-- The concrete one-level alternating insertion family.  Its only pathwise
input is the common literal stopping-boundary property of every assembled
word; probability factorization is then derived, not assumed. -/
def annularLevelComplementarySkeletonAtom
    {start m : ℕ} {outer middle inner : Fin m → Set Point}
    (code : TerminalSkeletonCode m) (offspring : Fin m → ℕ)
    (globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ c, AbsoluteBoundaryFirstAt globalBoundary globalStart
      (extendStoppedWord
        (assembleAnnularLevelBridges (start := start)
          (outer := outer) (middle := middle) (inner := inner)
          code offspring c))
      (assembleAnnularLevelBridges (start := start)
        (outer := outer) (middle := middle) (inner := inner)
        code offspring c).1) :
    ComplementarySkeletonAtom m (Fin start → Direction)
      (fun j ↦ AnnularLevelBridgeCode outer middle inner code offspring j) where
  complementWord := fun pre ↦ retainedTerminalWord pre code
  bridgeWord := fun _ bridge ↦ bridge.1
  assemble := assembleAnnularLevelBridges (start := start)
    (outer := outer) (middle := middle) (inner := inner) code offspring
  prefixFree_assemble :=
    prefixFree_of_injective_of_absoluteBoundaryFirstAt _
      (assembleAnnularLevelBridges_injective code offspring)
      globalBoundary globalStart hfirst
  prefixFree_bridge := fun j ↦
    prefixFree_boundaryExcursionExitWordCode
      (outer j) (middle j) (inner j)
      (code.2.1 j) (offspring j) (code.2.2 j)
  length_assemble := by
    rintro ⟨pre, bridges⟩
    rw [assembleAnnularLevelBridges, assembleAfterPrefix_length_eq]
    rw [retainedTerminalWord, assembleAfterPrefix_length_eq]
    simp only [emptyTerminalWords, List.length_nil, Finset.sum_const_zero,
      add_zero, annularLevelBridgeWords, List.length_ofFn]

/-- Exact probability factorization of a concrete one-level annular
insertion family. -/
theorem fairSteps_annularLevelAtom_eq_weight_mul_kernels
    {start m : ℕ} {outer middle inner : Fin m → Set Point}
    (code : TerminalSkeletonCode m) (offspring : Fin m → ℕ)
    (globalBoundary : Set Point) (globalStart : Point)
    (hfirst : ∀ c, AbsoluteBoundaryFirstAt globalBoundary globalStart
      (extendStoppedWord
        (assembleAnnularLevelBridges (start := start)
          (outer := outer) (middle := middle) (inner := inner)
          code offspring c))
      (assembleAnnularLevelBridges (start := start)
        (outer := outer) (middle := middle) (inner := inner)
        code offspring c).1) :
    let atom := annularLevelComplementarySkeletonAtom
      code offspring globalBoundary globalStart hfirst
    fairSteps atom.event = atom.weight *
      ∏ j, boundaryExcursionExitKernel
        (outer j) (middle j) (inner j)
        (code.2.1 j) (offspring j) (code.2.2 j) := by
  dsimp only
  apply fairSteps_event_eq_weight_mul_canonical_excursionKernel
  intro j b
  rfl

end

end Erdos1165.AnnularLevelFactorization
