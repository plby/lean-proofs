/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.AtomLeaves
import ErdosProblems.Erdos232.Independence

namespace Erdos232

theorem certificateAtomInt_suffix_1343488 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343488
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343489
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343492
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343496
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343497
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343504
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343508
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343512
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343616
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343617
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343620
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343744
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343748
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343752
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343760
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343764
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1343768
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345536
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345537
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345540
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345544
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345545
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345552
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345556
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345560
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345664
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345665
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345668
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345792
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345796
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345800
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345808
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345812
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1345816
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

theorem certificateAtomInt_suffix_1347584 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347584
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347585
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347588
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347592
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347593
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347712
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347713
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347716
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347840
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347844
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1347848
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349632
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349633
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349636
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349640
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349641
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349760
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349761
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349764
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349888
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349892
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1349896
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

theorem certificateAtomInt_suffix_1351680 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351680
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351681
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351684
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351688
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351689
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351696
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351700
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351704
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351936
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351940
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351944
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351952
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351956
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1351960
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

theorem certificateAtomInt_suffix_1355776 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1355776
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1355777
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1355780
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1355784
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1355785
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1356032
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1356036
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1356040
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

theorem certificateAtomInt_suffix_1359872 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1359872
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1359873
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1359876
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1359880
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1359881
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1359888
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1359892
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1359896
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1360000
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1360001
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1360004
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1360128
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1360132
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1360136
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1360144
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1360148
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1360152
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

theorem certificateAtomInt_suffix_1363968 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1363968
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1363969
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1363972
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1363976
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1363977
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1364096
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1364097
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1364100
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1364224
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1364228
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1364232
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

theorem certificateAtomInt_suffix_1368064 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368064
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368065
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368068
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368072
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368073
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368080
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368084
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368088
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368320
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368324
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368328
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368336
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368340
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1368344
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

theorem certificateAtomInt_suffix_1372160 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1372160
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1372161
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1372164
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1372168
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1372169
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1372416
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1372420
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1372424
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

theorem certificateAtomInt_suffix_1441792 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441792
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441793
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441796
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441800
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441801
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441824
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441828
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441832
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441920
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441921
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441924
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441952
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1441956
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442048
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442052
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442056
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442080
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442084
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442088
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442304
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442305
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442308
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442312
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442313
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442336
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442340
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442344
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442560
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442564
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442568
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442592
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442596
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1442600
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

theorem certificateAtomInt_suffix_1445888 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1445888
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1445889
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1445892
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1445896
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1445897
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1445920
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1445924
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1445928
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446016
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446017
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446020
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446048
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446052
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446144
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446148
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446152
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446176
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446180
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1446184
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

theorem certificateAtomInt_suffix_1458176 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458176
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458177
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458180
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458184
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458185
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458208
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458212
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458216
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458304
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458305
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458308
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458336
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458340
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458432
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458436
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458440
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458464
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458468
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1458472
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

theorem certificateAtomInt_suffix_1462272 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462272
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462273
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462276
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462280
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462281
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462304
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462308
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462312
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462400
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462401
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462404
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462432
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462436
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462528
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462532
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462536
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462560
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462564
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1462568
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

theorem certificateAtomInt_suffix_1474560 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474560
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474561
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474564
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474568
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474569
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474688
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474689
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474692
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474816
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474820
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1474824
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

theorem certificateAtomInt_suffix_1478656 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478656
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478657
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478660
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478664
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478665
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478784
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478785
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478788
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478912
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478916
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1478920
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

theorem certificateAtomInt_suffix_1490944 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1490944
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1490945
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1490948
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1490952
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1490953
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1491072
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1491073
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1491076
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1491200
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1491204
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1491208
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

theorem certificateAtomInt_suffix_1495040 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495040
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495041
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495044
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495048
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495049
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495168
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495169
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495172
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495296
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495300
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_1495304
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
