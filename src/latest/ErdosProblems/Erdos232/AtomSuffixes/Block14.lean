/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.AtomLeaves
import ErdosProblems.Erdos232.Independence

namespace Erdos232

/-
private def atomSuffix2359808 (s : BitVec 9) : BitVec 23 :=
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  s

private theorem certificateAtomInt_suffix_helper_2359808 :
    ∀ s : BitVec 9, independentMaskBV (atomSuffix2359808 s) = true →
      0 ≤ certificateAtomInt (atomSuffix2359808 s).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b8
  cases b8 <;> decide +revert
-/

private def atomSuffix2362880Leaf (b8 : Bool) (s : BitVec 8) : BitVec 23 :=
  let s := s.cons b8
  let s := s.cons true
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  s

private theorem certificateAtomInt_suffix_helper_2362880 :
    ∀ s : BitVec 8, independentMaskBV (atomSuffix2362880Leaf false s) = true →
      0 ≤ certificateAtomInt (atomSuffix2362880Leaf false s).toNat := by
  decide +revert

private theorem certificateAtomInt_suffix_helper_2363136 :
    ∀ s : BitVec 8, independentMaskBV (atomSuffix2362880Leaf true s) = true →
      0 ≤ certificateAtomInt (atomSuffix2362880Leaf true s).toNat := by
  decide +revert

private def atomSuffix2362880 (s : BitVec 9) : BitVec 23 :=
  let s := s.cons true
  let s := s.cons true
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  let s := s.cons false
  let s := s.cons true
  let s := s.cons false
  s

private theorem certificateAtomInt_suffix_helper_2362880_9 :
    ∀ s : BitVec 9, independentMaskBV (atomSuffix2362880 s) = true →
      0 ≤ certificateAtomInt (atomSuffix2362880 s).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b8
  cases b8
  · simpa only [atomSuffix2362880, atomSuffix2362880Leaf] using
      certificateAtomInt_suffix_helper_2362880
  · simpa only [atomSuffix2362880, atomSuffix2362880Leaf] using
      certificateAtomInt_suffix_helper_2363136

theorem certificateAtomInt_suffix_2228224 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228224
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228225
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228226
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228228
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228232
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228233
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228256
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228258
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228260
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228264
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228288
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228289
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228290
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228292
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228352
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228353
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228354
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228356
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228384
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228386
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228388
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228416
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228417
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228418
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228420
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228480
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228482
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228484
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228488
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228512
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228514
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228516
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228520
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228544
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228546
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228548
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228736
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228737
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228738
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228740
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228744
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228745
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228768
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228770
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228772
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228776
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228800
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228801
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228802
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228804
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228992
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228994
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2228996
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229000
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229024
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229026
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229028
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229032
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229056
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229058
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229060
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229248
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229249
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229250
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229252
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229312
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229313
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229314
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229316
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229760
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229761
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229762
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229764
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229824
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229825
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229826
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2229828
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2244608 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244608
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244609
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244610
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244612
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244616
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244617
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244640
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244642
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244644
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244648
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244672
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244673
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244674
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244676
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244736
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244737
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244738
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244740
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244768
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244770
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244772
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244800
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244801
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244802
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244804
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244864
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244866
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244868
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244872
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244896
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244898
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244900
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244904
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244928
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244930
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2244932
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2245632
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2245633
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2245634
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2245636
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2245696
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2245697
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2245698
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2245700
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2260992 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2260992
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2260993
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2260994
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2260996
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261000
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261001
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261056
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261057
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261058
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261060
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261120
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261121
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261122
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261124
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261184
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261185
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261186
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261188
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261248
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261250
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261252
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261256
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261312
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261314
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2261316
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2277376 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277376
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277377
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277378
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277380
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277384
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277385
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277440
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277441
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277442
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277444
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277504
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277505
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277506
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277508
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277568
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277569
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277570
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277572
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277632
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277634
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277636
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277640
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277696
                        ·
                          decide +revert
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277698
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2277700
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2359296 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359296
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359297
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359300
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359304
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359305
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359312
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359316
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359320
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359328
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359332
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359336
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359424
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359425
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359428
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359456
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359460
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
            ·
              decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359552
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359556
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359560
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359568
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359572
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359576
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359584
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359588
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359592
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359808
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359809
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359812
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359816
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359817
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359840
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359844
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2359848
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360064
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360068
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360072
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360096
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360100
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360104
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360320
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360321
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360324
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360336
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360340
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360832
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360833
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2360836
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361344
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361345
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361348
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361352
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361353
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361360
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361364
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361368
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361376
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361380
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361384
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361472
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361473
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361476
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361504
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361508
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
            ·
              decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361600
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361604
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361608
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361616
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361620
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361624
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361632
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361636
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2361640
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2362368
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2362369
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2362372
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2362384
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2362388
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        simpa only [atomSuffix2362880] using
          certificateAtomInt_suffix_helper_2362880_9

theorem certificateAtomInt_suffix_2367488 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367488
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367489
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367492
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367496
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367497
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367504
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367508
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367512
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367520
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367524
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367528
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367744
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367748
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367752
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367760
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367764
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367768
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367776
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367780
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2367784
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368000
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368001
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368004
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368008
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368009
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368032
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368036
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368040
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368256
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368260
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368264
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368288
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368292
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368296
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368512
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368513
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368516
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368528
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2368532
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2369024
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2369025
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2369028
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2375680 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375680
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375681
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375684
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375688
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375689
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375696
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375700
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375704
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375712
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375716
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375720
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375808
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375809
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375812
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375840
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375844
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
            ·
              decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375936
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375940
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375944
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375952
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375956
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375960
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375968
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375972
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2375976
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2376704
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2376705
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2376708
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2376720
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2376724
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2383872 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383872
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383873
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383876
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383880
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383881
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383888
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383892
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383896
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383904
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383908
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2383912
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384128
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384132
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384136
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384144
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384148
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384152
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384160
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384164
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384168
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384896
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384897
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384900
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384912
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2384916
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2392064 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392064
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392065
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392068
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392072
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392073
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392080
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392084
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392088
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392192
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392193
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392196
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392320
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392324
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392328
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392336
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392340
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2392344
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394112
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394113
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394116
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394120
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394121
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394128
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394132
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394136
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394240
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394241
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394244
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394368
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394372
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394376
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394384
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394388
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2394392
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert

theorem certificateAtomInt_suffix_2400256 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400256
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400257
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400260
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400264
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400265
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400272
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400276
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400280
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400512
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400516
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400520
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400528
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400532
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2400536
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2408448 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408448
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408449
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408452
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408456
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408457
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408464
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408468
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408472
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408576
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408577
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408580
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408704
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408708
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408712
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408720
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408724
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2408728
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2416640 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416640
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416641
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416644
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416648
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416649
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416656
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416660
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416664
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416896
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416900
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416904
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416912
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416916
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2416920
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2490368 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490368
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490369
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490372
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490376
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490377
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490400
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490404
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490408
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490496
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490497
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490500
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490528
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490532
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
            ·
              decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490624
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490628
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490632
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490656
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490660
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490664
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490880
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490881
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490884
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490888
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490889
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490912
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490916
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2490920
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491136
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491140
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491144
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491168
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491172
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491176
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491392
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491393
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491396
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491904
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491905
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2491908
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2506752 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506752
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506753
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506756
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506760
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506761
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506784
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506788
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506792
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506880
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506881
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506884
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506912
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2506916
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
            ·
              decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2507008
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2507012
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2507016
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2507040
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2507044
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2507048
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2507776
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2507777
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2507780
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2523136 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523136
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523137
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523140
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523144
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523145
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523264
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523265
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523268
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523392
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523396
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2523400
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_2539520 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons true).cons false).cons false).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons true).cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b11
  cases b11
  ·
    rw [BitVec.forall_cons_iff]
    intro b10
    cases b10
    ·
      rw [BitVec.forall_cons_iff]
      intro b9
      cases b9
      ·
        rw [BitVec.forall_cons_iff]
        intro b8
        cases b8
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539520
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539521
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539524
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539528
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539529
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539648
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539649
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539652
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
        ·
          rw [BitVec.forall_cons_iff]
          intro b7
          cases b7
          ·
            rw [BitVec.forall_cons_iff]
            intro b6
            cases b6
            ·
              rw [BitVec.forall_cons_iff]
              intro b5
              cases b5
              ·
                rw [BitVec.forall_cons_iff]
                intro b4
                cases b4
                ·
                  rw [BitVec.forall_cons_iff]
                  intro b3
                  cases b3
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539776
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539780
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_2539784
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

end Erdos232
