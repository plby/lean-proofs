/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.AtomLeaves
import ErdosProblems.Erdos232.Independence

namespace Erdos232

theorem certificateAtomInt_suffix_0327680 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327680
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327681
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327684
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327688
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327689
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327696
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327700
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327704
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327712
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327716
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327720
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327808
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327809
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327812
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327840
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327844
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327936
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327940
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327944
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327952
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327956
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327960
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327968
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327972
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0327976
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0328704
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0328705
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0328708
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0328720
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0328724
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0331776 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331776
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331777
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331780
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331784
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331785
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331808
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331812
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331816
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331904
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331905
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331908
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331936
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0331940
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0332032
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0332036
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0332040
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0332064
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0332068
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0332072
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0332800
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0332801
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0332804
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0335872 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335872
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335873
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335876
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335880
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335881
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335888
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335892
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335896
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335904
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335908
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0335912
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336128
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336132
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336136
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336144
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336148
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336152
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336160
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336164
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336168
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336896
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336897
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336900
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336912
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0336916
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0339968 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0339968
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0339969
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0339972
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0339976
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0339977
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340000
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340004
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340008
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340224
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340228
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340232
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340256
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340260
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340264
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340992
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340993
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0340996
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0344064 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344064
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344065
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344068
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344072
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344073
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344080
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344084
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344088
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344096
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344100
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344104
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344192
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344193
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344196
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344224
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344228
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344320
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344324
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344328
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344336
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344340
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344344
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344352
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344356
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0344360
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0345088
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0345089
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0345092
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0345104
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0345108
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0348160 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348160
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348161
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348164
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348168
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348169
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348192
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348196
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348200
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348288
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348289
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348292
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348320
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348324
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348416
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348420
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348424
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348448
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348452
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0348456
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0349184
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0349185
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0349188
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0352256 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352256
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352257
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352260
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352264
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352265
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352272
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352276
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352280
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352288
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352292
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352296
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352512
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352516
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352520
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352528
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352532
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352536
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352544
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352548
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0352552
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0353280
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0353281
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0353284
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0353296
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0353300
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0356352 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons true).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons true).cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356352
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356353
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356356
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356360
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356361
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356384
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356388
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356392
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356608
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356612
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356616
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356640
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356644
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0356648
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0357376
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0357377
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0357380
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
        ·
          decide +revert
      ·
        decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0360448 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360448
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360449
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360452
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360456
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360457
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360464
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360468
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360472
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360576
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360577
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360580
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360704
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360708
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360712
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360720
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360724
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0360728
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0364544 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364544
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364545
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364548
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364552
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364553
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364672
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364673
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364676
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364800
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364804
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0364808
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0368640 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368640
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368641
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368644
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368648
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368649
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368656
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368660
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368664
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368896
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368900
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368904
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368912
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368916
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0368920
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0372736 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0372736
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0372737
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0372740
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0372744
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0372745
                      ·
                        decide +revert
                    ·
                      decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0372992
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0372996
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0373000
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0376832 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376832
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376833
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376836
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376840
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376841
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376848
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376852
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376856
                        ·
                          decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376960
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376961
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0376964
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0377088
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0377092
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0377096
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0377104
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0377108
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0377112
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0380928 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons false).cons true).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons false).cons true).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0380928
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0380929
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0380932
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0380936
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0380937
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0381056
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0381057
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0381060
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0381184
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0381188
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0381192
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0385024 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385024
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385025
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385028
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385032
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385033
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385040
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385044
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385048
                        ·
                          decide +revert
                      ·
                        decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385280
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385284
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385288
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385296
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385300
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0385304
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_0389120 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons true).cons true).cons true).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons true).cons true).cons true).cons true).cons true).cons false).cons true).cons false).cons false).cons false).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0389120
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0389121
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0389124
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0389128
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0389129
                      ·
                        decide +revert
                    ·
                      decide +revert
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0389376
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0389380
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_0389384
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
              ·
                decide +revert
            ·
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
