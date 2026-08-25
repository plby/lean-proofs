/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.AtomLeaves
import ErdosProblems.Erdos232.Independence

namespace Erdos232

private def atomSuffixBlock25Leaf_5636096
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5636096 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5636352 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5636608 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5636864 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5637120 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5637376 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5637632 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5637888 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5638144 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5638400 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5638656 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5638912 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5639168 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5639424 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5639680 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5639936 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5636096 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5636096 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5636096 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5636096
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5636352
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5636608
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5636864
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5637120
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5637376
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5637632
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5637888
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5638144
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5638400
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5638656
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5638912
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5639168
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5639424
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5639680
  · simpa only [atomSuffixBlock25Leaf_5636096] using
      certificateAtomInt_suffix_leaf_5639936

private def atomSuffixBlock25Leaf_5640192
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5640192 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5640448 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5640704 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5640960 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5641216 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5641472 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5641728 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5641984 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5642240 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5642496 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5642752 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5643008 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5643264 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5643520 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5643776 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5644032 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5640192 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5640192 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5640192 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5640192
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5640448
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5640704
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5640960
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5641216
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5641472
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5641728
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5641984
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5642240
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5642496
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5642752
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5643008
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5643264
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5643520
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5643776
  · simpa only [atomSuffixBlock25Leaf_5640192] using
      certificateAtomInt_suffix_leaf_5644032

private def atomSuffixBlock25Leaf_5652480
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5652480 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5652736 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5652992 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5653248 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5653504 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5653760 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5654016 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5654272 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5654528 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5654784 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5655040 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5655296 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5655552 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5655808 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5656064 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5656320 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5652480 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5652480 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5652480 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5652480
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5652736
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5652992
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5653248
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5653504
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5653760
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5654016
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5654272
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5654528
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5654784
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5655040
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5655296
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5655552
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5655808
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5656064
  · simpa only [atomSuffixBlock25Leaf_5652480] using
      certificateAtomInt_suffix_leaf_5656320

private def atomSuffixBlock25Leaf_5656576
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5656576 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5656832 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5657088 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5657344 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5657600 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5657856 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5658112 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5658368 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5658624 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5658880 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5659136 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5659392 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5659648 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5659904 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5660160 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5660416 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5656576 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5656576 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5656576 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5656576
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5656832
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5657088
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5657344
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5657600
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5657856
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5658112
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5658368
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5658624
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5658880
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5659136
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5659392
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5659648
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5659904
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5660160
  · simpa only [atomSuffixBlock25Leaf_5656576] using
      certificateAtomInt_suffix_leaf_5660416

private def atomSuffixBlock25Leaf_5668864
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5668864 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5669120 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5669376 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5669632 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5669888 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5670144 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5670400 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5670656 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5670912 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5671168 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5671424 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5671680 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5671936 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5672192 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5672448 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5672704 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5668864 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5668864 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5668864 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5668864
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5669120
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5669376
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5669632
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5669888
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5670144
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5670400
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5670656
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5670912
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5671168
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5671424
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5671680
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5671936
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5672192
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5672448
  · simpa only [atomSuffixBlock25Leaf_5668864] using
      certificateAtomInt_suffix_leaf_5672704

private def atomSuffixBlock25Leaf_5672960
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5672960 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5673216 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5673472 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5673728 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5673984 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5674240 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5674496 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5674752 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5675008 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5675264 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5675520 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5675776 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5676032 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5676288 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5676544 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5676800 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5672960 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5672960 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5672960 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5672960
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5673216
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5673472
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5673728
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5673984
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5674240
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5674496
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5674752
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5675008
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5675264
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5675520
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5675776
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5676032
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5676288
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5676544
  · simpa only [atomSuffixBlock25Leaf_5672960] using
      certificateAtomInt_suffix_leaf_5676800

private def atomSuffixBlock25Leaf_5685248
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5685248 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5685504 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5685760 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5686016 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5686272 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5686528 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5686784 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5687040 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5687296 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5687552 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5687808 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5688064 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5688320 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5688576 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5688832 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5689088 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5685248 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5685248 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5685248 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5685248
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5685504
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5685760
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5686016
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5686272
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5686528
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5686784
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5687040
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5687296
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5687552
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5687808
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5688064
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5688320
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5688576
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5688832
  · simpa only [atomSuffixBlock25Leaf_5685248] using
      certificateAtomInt_suffix_leaf_5689088

private def atomSuffixBlock25Leaf_5689344
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5689344 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5689600 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5689856 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5690112 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5690368 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5690624 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5690880 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5691136 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5691392 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5691648 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5691904 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5692160 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5692416 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5692672 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5692928 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5693184 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5689344 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5689344 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5689344 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5689344
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5689600
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5689856
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5690112
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5690368
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5690624
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5690880
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5691136
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5691392
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5691648
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5691904
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5692160
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5692416
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5692672
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5692928
  · simpa only [atomSuffixBlock25Leaf_5689344] using
      certificateAtomInt_suffix_leaf_5693184

private def atomSuffixBlock25Leaf_5767168
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5767168 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5767424 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5767680 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5767936 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5768192 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5768448 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5768704 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5768960 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5769216 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5769472 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5769728 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5769984 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5770240 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5770496 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5770752 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5771008 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5767168 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5767168 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5767168 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5767168
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5767424
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5767680
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5767936
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5768192
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5768448
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5768704
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5768960
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5769216
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5769472
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5769728
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5769984
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5770240
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5770496
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5770752
  · simpa only [atomSuffixBlock25Leaf_5767168] using
      certificateAtomInt_suffix_leaf_5771008

private def atomSuffixBlock25Leaf_5771264
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5771264 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5771520 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5771776 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5772032 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5772288 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5772544 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5772800 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5773056 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5773312 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5773568 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5773824 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5774080 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5774336 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5774592 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5774848 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5775104 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5771264 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5771264 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5771264 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5771264
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5771520
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5771776
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5772032
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5772288
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5772544
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5772800
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5773056
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5773312
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5773568
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5773824
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5774080
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5774336
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5774592
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5774848
  · simpa only [atomSuffixBlock25Leaf_5771264] using
      certificateAtomInt_suffix_leaf_5775104

private def atomSuffixBlock25Leaf_5775360
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5775360 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5775616 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5775872 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5776128 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5776384 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5776640 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5776896 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5777152 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5777408 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5777664 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5777920 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5778176 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5778432 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5778688 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5778944 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5779200 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5775360 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5775360 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5775360 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5775360
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5775616
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5775872
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5776128
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5776384
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5776640
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5776896
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5777152
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5777408
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5777664
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5777920
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5778176
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5778432
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5778688
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5778944
  · simpa only [atomSuffixBlock25Leaf_5775360] using
      certificateAtomInt_suffix_leaf_5779200

private def atomSuffixBlock25Leaf_5779456
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5779456 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5779712 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5779968 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5780224 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5780480 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5780736 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5780992 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5781248 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5781504 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5781760 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5782016 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5782272 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5782528 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5782784 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5783040 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5783296 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5779456 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5779456 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5779456 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5779456
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5779712
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5779968
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5780224
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5780480
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5780736
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5780992
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5781248
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5781504
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5781760
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5782016
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5782272
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5782528
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5782784
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5783040
  · simpa only [atomSuffixBlock25Leaf_5779456] using
      certificateAtomInt_suffix_leaf_5783296

private def atomSuffixBlock25Leaf_5783552
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5783552 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5783808 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5784064 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5784320 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5784576 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5784832 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5785088 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5785344 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5785600 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5785856 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5786112 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5786368 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5786624 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5786880 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5787136 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5787392 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5783552 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5783552 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5783552 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5783552
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5783808
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5784064
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5784320
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5784576
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5784832
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5785088
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5785344
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5785600
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5785856
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5786112
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5786368
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5786624
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5786880
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5787136
  · simpa only [atomSuffixBlock25Leaf_5783552] using
      certificateAtomInt_suffix_leaf_5787392

private def atomSuffixBlock25Leaf_5787648
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5787648 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5787904 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5788160 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5788416 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5788672 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5788928 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5789184 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5789440 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5789696 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5789952 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5790208 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5790464 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5790720 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5790976 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5791232 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5791488 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5787648 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5787648 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5787648 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5787648
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5787904
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5788160
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5788416
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5788672
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5788928
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5789184
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5789440
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5789696
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5789952
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5790208
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5790464
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5790720
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5790976
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5791232
  · simpa only [atomSuffixBlock25Leaf_5787648] using
      certificateAtomInt_suffix_leaf_5791488

private def atomSuffixBlock25Leaf_5791744
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5791744 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5792000 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5792256 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5792512 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5792768 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5793024 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5793280 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5793536 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5793792 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5794048 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5794304 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5794560 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5794816 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5795072 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5795328 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5795584 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5791744 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5791744 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5791744 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5791744
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5792000
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5792256
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5792512
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5792768
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5793024
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5793280
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5793536
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5793792
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5794048
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5794304
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5794560
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5794816
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5795072
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5795328
  · simpa only [atomSuffixBlock25Leaf_5791744] using
      certificateAtomInt_suffix_leaf_5795584

private def atomSuffixBlock25Leaf_5795840
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons true
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5795840 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5796096 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5796352 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5796608 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5796864 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5797120 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5797376 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5797632 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5797888 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5798144 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5798400 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5798656 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5798912 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5799168 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5799424 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5799680 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock25Leaf_5795840 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock25Leaf_5795840 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5795840 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b10 <;>
    cases b10 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b9 <;>
    cases b9 <;>
    rw [BitVec.forall_cons_iff] <;>
    intro b8 <;>
    cases b8
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5795840
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5796096
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5796352
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5796608
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5796864
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5797120
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5797376
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5797632
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5797888
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5798144
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5798400
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5798656
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5798912
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5799168
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5799424
  · simpa only [atomSuffixBlock25Leaf_5795840] using
      certificateAtomInt_suffix_leaf_5799680

end Erdos232
