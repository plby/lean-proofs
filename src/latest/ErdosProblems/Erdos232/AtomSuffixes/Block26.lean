/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.AtomLeaves
import ErdosProblems.Erdos232.Independence

namespace Erdos232

private def atomSuffixBlock26Leaf_5799936
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
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5799936 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5800192 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5800448 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5800704 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5800960 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5801216 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5801472 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5801728 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5801984 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5802240 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5802496 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5802752 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5803008 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5803264 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5803520 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5803776 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5799936 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5799936 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5799936 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5799936
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5800192
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5800448
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5800704
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5800960
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5801216
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5801472
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5801728
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5801984
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5802240
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5802496
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5802752
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5803008
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5803264
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5803520
  · simpa only [atomSuffixBlock26Leaf_5799936] using
      certificateAtomInt_suffix_leaf_5803776

private def atomSuffixBlock26Leaf_5804032
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
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5804032 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5804288 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5804544 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5804800 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5805056 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5805312 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5805568 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5805824 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5806080 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5806336 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5806592 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5806848 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5807104 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5807360 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5807616 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5807872 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5804032 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5804032 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5804032 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5804032
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5804288
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5804544
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5804800
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5805056
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5805312
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5805568
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5805824
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5806080
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5806336
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5806592
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5806848
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5807104
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5807360
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5807616
  · simpa only [atomSuffixBlock26Leaf_5804032] using
      certificateAtomInt_suffix_leaf_5807872

private def atomSuffixBlock26Leaf_5808128
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5808128 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5808384 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5808640 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5808896 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5809152 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5809408 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5809664 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5809920 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5810176 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5810432 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5810688 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5810944 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5811200 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5811456 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5811712 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5811968 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5808128 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5808128 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5808128 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5808128
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5808384
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5808640
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5808896
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5809152
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5809408
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5809664
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5809920
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5810176
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5810432
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5810688
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5810944
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5811200
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5811456
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5811712
  · simpa only [atomSuffixBlock26Leaf_5808128] using
      certificateAtomInt_suffix_leaf_5811968

private def atomSuffixBlock26Leaf_5812224
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5812224 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5812480 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5812736 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5812992 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5813248 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5813504 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5813760 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5814016 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5814272 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5814528 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5814784 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5815040 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5815296 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5815552 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5815808 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5816064 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5812224 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5812224 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5812224 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5812224
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5812480
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5812736
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5812992
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5813248
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5813504
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5813760
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5814016
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5814272
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5814528
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5814784
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5815040
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5815296
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5815552
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5815808
  · simpa only [atomSuffixBlock26Leaf_5812224] using
      certificateAtomInt_suffix_leaf_5816064

private def atomSuffixBlock26Leaf_5816320
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
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5816320 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5816576 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5816832 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5817088 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5817344 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5817600 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5817856 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5818112 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5818368 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5818624 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5818880 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5819136 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5819392 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5819648 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5819904 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5820160 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5816320 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5816320 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5816320 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5816320
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5816576
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5816832
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5817088
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5817344
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5817600
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5817856
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5818112
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5818368
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5818624
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5818880
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5819136
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5819392
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5819648
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5819904
  · simpa only [atomSuffixBlock26Leaf_5816320] using
      certificateAtomInt_suffix_leaf_5820160

private def atomSuffixBlock26Leaf_5820416
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
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5820416 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5820672 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5820928 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5821184 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5821440 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5821696 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5821952 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5822208 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5822464 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5822720 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5822976 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5823232 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5823488 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5823744 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5824000 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5824256 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5820416 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5820416 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5820416 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5820416
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5820672
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5820928
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5821184
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5821440
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5821696
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5821952
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5822208
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5822464
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5822720
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5822976
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5823232
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5823488
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5823744
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5824000
  · simpa only [atomSuffixBlock26Leaf_5820416] using
      certificateAtomInt_suffix_leaf_5824256

private def atomSuffixBlock26Leaf_5824512
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5824512 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5824768 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5825024 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5825280 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5825536 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5825792 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5826048 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5826304 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5826560 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5826816 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5827072 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5827328 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5827584 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5827840 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5828096 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5828352 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5824512 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5824512 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5824512 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5824512
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5824768
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5825024
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5825280
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5825536
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5825792
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5826048
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5826304
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5826560
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5826816
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5827072
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5827328
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5827584
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5827840
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5828096
  · simpa only [atomSuffixBlock26Leaf_5824512] using
      certificateAtomInt_suffix_leaf_5828352

private def atomSuffixBlock26Leaf_5828608
    (b8 b9 b10 b11 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons b9
  let s := s.cons b10
  let s := s.cons b11
  let s := s.cons true
  let s := s.cons true
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5828608 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5828864 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5829120 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5829376 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5829632 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5829888 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5830144 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5830400 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5830656 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5830912 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5831168 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5831424 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5831680 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5831936 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5832192 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5832448 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5828608 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5828608 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5828608 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons true).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons true).cons true).cons false).cons false).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5828608
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5828864
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5829120
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5829376
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5829632
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5829888
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5830144
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5830400
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5830656
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5830912
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5831168
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5831424
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5831680
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5831936
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5832192
  · simpa only [atomSuffixBlock26Leaf_5828608] using
      certificateAtomInt_suffix_leaf_5832448

private def atomSuffixBlock26Leaf_5898240
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
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5898240 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5898496 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5898752 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5899008 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5899264 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5899520 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5899776 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5900032 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5900288 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5900544 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5900800 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5901056 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5901312 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5901568 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5901824 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5902080 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5898240 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5898240 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5898240 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5898240
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5898496
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5898752
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5899008
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5899264
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5899520
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5899776
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5900032
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5900288
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5900544
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5900800
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5901056
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5901312
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5901568
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5901824
  · simpa only [atomSuffixBlock26Leaf_5898240] using
      certificateAtomInt_suffix_leaf_5902080

private def atomSuffixBlock26Leaf_5902336
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
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5902336 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5902592 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5902848 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5903104 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5903360 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5903616 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5903872 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5904128 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5904384 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5904640 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5904896 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5905152 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5905408 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5905664 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5905920 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5906176 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5902336 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5902336 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5902336 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5902336
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5902592
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5902848
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5903104
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5903360
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5903616
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5903872
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5904128
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5904384
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5904640
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5904896
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5905152
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5905408
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5905664
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5905920
  · simpa only [atomSuffixBlock26Leaf_5902336] using
      certificateAtomInt_suffix_leaf_5906176

private def atomSuffixBlock26Leaf_5914624
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
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5914624 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5914880 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5915136 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5915392 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5915648 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5915904 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5916160 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5916416 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5916672 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5916928 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5917184 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5917440 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5917696 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5917952 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5918208 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5918464 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5914624 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5914624 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5914624 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5914624
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5914880
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5915136
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5915392
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5915648
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5915904
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5916160
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5916416
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5916672
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5916928
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5917184
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5917440
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5917696
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5917952
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5918208
  · simpa only [atomSuffixBlock26Leaf_5914624] using
      certificateAtomInt_suffix_leaf_5918464

private def atomSuffixBlock26Leaf_5918720
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
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5918720 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5918976 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5919232 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5919488 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5919744 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5920000 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5920256 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5920512 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5920768 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5921024 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5921280 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5921536 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5921792 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5922048 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5922304 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5922560 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5918720 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5918720 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5918720 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5918720
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5918976
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5919232
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5919488
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5919744
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5920000
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5920256
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5920512
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5920768
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5921024
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5921280
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5921536
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5921792
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5922048
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5922304
  · simpa only [atomSuffixBlock26Leaf_5918720] using
      certificateAtomInt_suffix_leaf_5922560

private def atomSuffixBlock26Leaf_5931008
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
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5931008 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5931264 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5931520 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5931776 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5932032 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5932288 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5932544 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5932800 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5933056 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5933312 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5933568 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5933824 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5934080 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5934336 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5934592 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5934848 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5931008 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5931008 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5931008 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5931008
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5931264
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5931520
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5931776
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5932032
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5932288
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5932544
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5932800
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5933056
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5933312
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5933568
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5933824
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5934080
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5934336
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5934592
  · simpa only [atomSuffixBlock26Leaf_5931008] using
      certificateAtomInt_suffix_leaf_5934848

private def atomSuffixBlock26Leaf_5935104
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
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5935104 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5935360 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5935616 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5935872 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5936128 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5936384 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5936640 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5936896 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5937152 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5937408 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5937664 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5937920 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5938176 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5938432 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5938688 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5938944 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5935104 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5935104 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5935104 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5935104
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5935360
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5935616
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5935872
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5936128
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5936384
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5936640
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5936896
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5937152
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5937408
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5937664
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5937920
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5938176
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5938432
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5938688
  · simpa only [atomSuffixBlock26Leaf_5935104] using
      certificateAtomInt_suffix_leaf_5938944

private def atomSuffixBlock26Leaf_5947392
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
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5947392 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5947648 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5947904 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5948160 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5948416 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5948672 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5948928 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5949184 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5949440 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5949696 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5949952 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5950208 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5950464 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5950720 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5950976 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5951232 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5947392 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5947392 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5947392 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5947392
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5947648
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5947904
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5948160
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5948416
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5948672
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5948928
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5949184
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5949440
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5949696
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5949952
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5950208
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5950464
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5950720
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5950976
  · simpa only [atomSuffixBlock26Leaf_5947392] using
      certificateAtomInt_suffix_leaf_5951232

private def atomSuffixBlock26Leaf_5951488
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
  let s := s.cons false
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons true
  s

private theorem certificateAtomInt_suffix_leaf_5951488 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 false false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 false false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5951744 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 true false false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 true false false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5952000 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 false true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 false true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5952256 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 true true false false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 true true false false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5952512 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 false false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 false false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5952768 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 true false true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 true false true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5953024 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 false true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 false true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5953280 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 true true true false s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 true true true false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5953536 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 false false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 false false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5953792 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 true false false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 true false false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5954048 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 false true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 false true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5954304 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 true true false true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 true true false true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5954560 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 false false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 false false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5954816 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 true false true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 true false true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5955072 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 false true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 false true true true s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_leaf_5955328 :
    ∀ s : BitVec 8,
      independentMaskBV (atomSuffixBlock26Leaf_5951488 true true true true s) = true →
        0 ≤ certificateAtomInt
          (atomSuffixBlock26Leaf_5951488 true true true true s).toNat := by
  decide +revert

theorem certificateAtomInt_suffix_5951488 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons true).cons true).cons false).cons true) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons true).cons true).cons false).cons true).toNat := by
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
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5951488
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5951744
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5952000
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5952256
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5952512
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5952768
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5953024
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5953280
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5953536
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5953792
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5954048
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5954304
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5954560
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5954816
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5955072
  · simpa only [atomSuffixBlock26Leaf_5951488] using
      certificateAtomInt_suffix_leaf_5955328

end Erdos232
