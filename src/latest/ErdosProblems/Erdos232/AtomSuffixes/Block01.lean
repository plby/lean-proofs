/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.AtomLeaves
import ErdosProblems.Erdos232.Independence

namespace Erdos232

theorem certificateAtomInt_suffix_0065536 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065536
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065537
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065538
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065540
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065544
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065545
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065552
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065554
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065556
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065560
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065568
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065570
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065572
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065576
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065600
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065601
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065602
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065604
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065664
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065665
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065666
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065668
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065696
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065698
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065700
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065728
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065729
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065730
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065732
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065792
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065794
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065796
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065800
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065808
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065810
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065812
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065816
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065824
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065826
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065828
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065832
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065856
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065858
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0065860
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066560
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066561
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066562
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066564
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066576
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066578
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066580
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066624
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066625
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066626
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0066628
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0069632 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069632
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069633
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069634
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069636
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069640
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069641
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069664
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069666
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069668
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069672
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069696
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069697
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069698
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069700
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069760
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069761
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069762
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069764
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069792
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069794
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069796
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069824
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069825
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069826
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069828
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069888
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069890
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069892
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069896
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069920
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069922
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069924
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069928
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069952
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069954
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0069956
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0070656
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0070657
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0070658
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0070660
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0070720
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0070721
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0070722
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0070724
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0073728 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073728
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073729
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073730
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073732
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073736
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073737
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073744
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073746
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073748
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073752
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073760
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073762
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073764
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073768
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073792
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073793
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073794
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073796
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073984
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073986
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073988
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0073992
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074000
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074002
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074004
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074008
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074016
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074018
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074020
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074024
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074048
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074050
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074052
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074752
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074753
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074754
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074756
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074768
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074770
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074772
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074816
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074817
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074818
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0074820
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0077824 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077824
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077825
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077826
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077828
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077832
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077833
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077856
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077858
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077860
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077864
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077888
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077889
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077890
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0077892
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078080
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078082
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078084
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078088
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078112
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078114
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078116
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078120
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078144
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078146
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078148
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078848
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078849
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078850
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078852
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078912
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078913
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078914
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0078916
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0081920 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081920
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081921
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081922
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081924
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081928
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081929
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081936
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081938
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081940
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081944
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081952
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081954
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081956
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081960
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081984
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081985
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081986
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0081988
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082048
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082049
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082050
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082052
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082080
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082082
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082084
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082112
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082113
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082114
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082116
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082176
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082178
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082180
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082184
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082192
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082194
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082196
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082200
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082208
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082210
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082212
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082216
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082240
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082242
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082244
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082944
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082945
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082946
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082948
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082960
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082962
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0082964
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0083008
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0083009
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0083010
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0083012
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0086016 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086016
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086017
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086018
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086020
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086024
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086025
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086048
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086050
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086052
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086056
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086080
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086081
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086082
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086084
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086144
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086145
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086146
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086148
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086176
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086178
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086180
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086208
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086209
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086210
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086212
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086272
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086274
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086276
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086280
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086304
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086306
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086308
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086312
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086336
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086338
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0086340
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0087040
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0087041
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0087042
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0087044
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0087104
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0087105
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0087106
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0087108
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0090112 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090112
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090113
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090114
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090116
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090120
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090121
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090128
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090130
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090132
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090136
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090144
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090146
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090148
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090152
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090176
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090177
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090178
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090180
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090368
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090370
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090372
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090376
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090384
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090386
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090388
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090392
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090400
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090402
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090404
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090408
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090432
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090434
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0090436
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091136
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091137
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091138
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091140
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091152
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091154
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091156
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091200
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091201
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091202
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0091204
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0094208 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094208
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094209
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094210
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094212
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094216
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094217
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094240
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094242
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094244
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094248
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094272
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094273
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094274
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094276
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094464
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094466
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094468
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094472
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094496
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094498
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094500
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094504
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094528
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094530
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0094532
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0095232
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0095233
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0095234
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0095236
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0095296
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0095297
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0095298
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0095300
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0098304 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098304
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098305
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098306
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098308
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098312
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098313
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098320
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098322
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098324
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098328
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098368
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098369
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098370
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098372
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098432
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098433
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098434
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098436
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098496
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098497
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098498
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098500
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098560
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098562
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098564
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098568
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098576
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098578
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098580
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098584
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098624
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098626
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0098628
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0102400 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102400
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102401
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102402
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102404
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102408
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102409
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102464
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102465
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102466
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102468
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102528
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102529
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102530
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102532
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102592
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102593
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102594
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102596
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102656
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102658
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102660
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102664
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102720
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102722
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0102724
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0106496 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106496
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106497
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106498
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106500
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106504
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106505
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106512
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106514
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106516
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106520
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106560
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106561
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106562
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106564
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106752
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106754
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106756
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106760
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106768
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106770
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106772
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106776
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106816
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106818
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0106820
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0110592 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110592
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110593
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110594
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110596
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110600
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110601
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110656
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110657
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110658
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110660
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110848
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110850
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110852
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110856
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110912
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110914
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0110916
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0114688 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114688
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114689
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114690
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114692
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114696
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114697
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114704
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114706
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114708
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114712
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114752
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114753
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114754
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114756
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114816
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114817
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114818
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114820
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114880
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114881
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114882
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114884
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114944
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114946
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114948
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114952
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114960
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114962
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114964
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0114968
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0115008
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0115010
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0115012
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0118784 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118784
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118785
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118786
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118788
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118792
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118793
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118848
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118849
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118850
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118852
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118912
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118913
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118914
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118916
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118976
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118977
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118978
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0118980
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0119040
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0119042
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0119044
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0119048
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0119104
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0119106
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0119108
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0122880 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122880
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122881
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122882
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122884
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122888
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122889
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122896
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122898
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122900
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122904
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122944
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122945
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122946
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0122948
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123136
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123138
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123140
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123144
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123152
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123154
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123156
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123160
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123200
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123202
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0123204
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0126976 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0126976
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0126977
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0126978
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0126980
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0126984
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0126985
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127040
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127041
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127042
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127044
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127232
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127234
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127236
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127240
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127296
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127298
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0127300
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
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
