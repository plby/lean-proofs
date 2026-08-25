/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.AtomLeaves
import ErdosProblems.Erdos232.Independence

namespace Erdos232

theorem certificateAtomInt_suffix_3178496 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178496
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178497
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178498
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178500
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178504
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178505
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178512
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178514
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178516
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178520
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178560
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178561
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178562
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178564
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178624
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178625
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178626
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178628
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178688
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178689
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178690
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178692
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178752
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178754
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178756
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178760
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178768
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178770
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178772
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178776
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178816
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178818
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3178820
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180544
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180545
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180548
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180552
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180553
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180560
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180564
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180568
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180608
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180609
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180612
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180672
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180673
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180676
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180736
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180737
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180740
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180800
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180804
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180808
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180816
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180820
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180824
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180864
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3180868
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert

theorem certificateAtomInt_suffix_3186688 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186688
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186689
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186690
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186692
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186696
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186697
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186704
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186706
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186708
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186712
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186752
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186753
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186754
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186756
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186944
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186946
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186948
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186952
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186960
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186962
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186964
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3186968
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3187008
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3187010
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3187012
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3194880 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194880
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194881
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194882
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194884
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194888
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194889
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194896
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194898
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194900
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194904
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194944
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194945
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194946
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3194948
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195008
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195009
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195010
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195012
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195072
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195073
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195074
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195076
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195136
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195138
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195140
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195144
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195152
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195154
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195156
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195160
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195200
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195202
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3195204
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3203072 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons true).cons false).cons false).cons false).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203072
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203073
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203074
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203076
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203080
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203081
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203088
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203090
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203092
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203096
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203136
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203137
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203138
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203140
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203328
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203330
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203332
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203336
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203344
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203346
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203348
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203352
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203392
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203394
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3203396
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3276800 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276800
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276801
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276802
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276804
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276808
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276809
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276832
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276834
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276836
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276840
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276864
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276865
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276866
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276868
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276928
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276929
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276930
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276932
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276960
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276962
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276964
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276992
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276993
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276994
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3276996
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277056
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277058
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277060
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277064
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277088
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277090
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277092
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277096
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277120
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277122
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277124
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277312
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277313
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277314
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277316
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277320
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277321
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277344
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277346
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277348
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277352
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277376
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277377
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277378
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277380
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277568
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277570
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277572
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277576
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277600
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277602
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277604
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277608
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277632
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277634
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3277636
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3293184 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293184
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293185
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293186
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293188
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293192
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293193
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293216
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293218
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293220
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293224
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293248
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293249
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293250
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293252
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293312
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293313
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293314
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293316
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293344
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293346
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293348
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293376
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293377
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293378
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293380
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293440
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293442
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293444
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293448
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293472
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293474
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293476
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293480
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293504
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293506
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3293508
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3309568 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons true).cons false).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309568
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309569
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309570
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309572
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309576
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309577
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309632
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309633
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309634
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309636
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309696
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309697
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309698
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309700
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309760
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309761
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309762
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309764
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309824
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309826
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309828
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309832
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309888
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309890
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3309892
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3325952 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons true).cons false).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3325952
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3325953
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3325954
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3325956
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3325960
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3325961
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326016
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326017
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326018
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326020
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326080
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326081
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326082
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326084
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326144
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326145
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326146
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326148
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326208
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326210
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326212
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326216
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326272
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326274
                        ·
                          decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3326276
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    decide +revert
                ·
                  decide +revert
              ·
                decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3407872 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407872
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407873
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407876
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407880
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407881
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407888
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407892
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407896
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407904
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407908
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3407912
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408000
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408001
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408004
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408032
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408036
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408128
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408132
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408136
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408144
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408148
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408152
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408160
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408164
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408168
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408384
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408385
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408388
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408392
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408393
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408416
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408420
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408424
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408640
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408644
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408648
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408672
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408676
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3408680
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409920
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409921
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409924
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409928
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409929
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409936
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409940
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409944
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409952
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409956
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3409960
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410048
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410049
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410052
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410080
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410084
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410176
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410180
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410184
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410192
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410196
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410200
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410208
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410212
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3410216
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert

theorem certificateAtomInt_suffix_3416064 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416064
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416065
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416068
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416072
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416073
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416080
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416084
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416088
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416096
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416100
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416104
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416320
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416324
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416328
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416336
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416340
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416344
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416352
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416356
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416360
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416576
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416577
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416580
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416584
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416585
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416608
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416612
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416616
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416832
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416836
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416840
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416864
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416868
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3416872
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3424256 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424256
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424257
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424260
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424264
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424265
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424272
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424276
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424280
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424288
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424292
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424296
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424384
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424385
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424388
                        ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424416
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424420
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424512
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424516
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424520
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424528
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424532
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424536
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424544
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424548
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3424552
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3432448 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons false).cons false).cons false).cons true).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432448
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432449
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432452
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432456
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432457
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432464
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432468
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432472
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432480
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432484
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432488
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432704
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432708
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432712
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432720
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432724
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432728
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432736
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432740
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3432744
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
                ·
                  decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3440640 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440640
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440641
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440644
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440648
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440649
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440656
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440660
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440664
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440768
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440769
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440772
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440896
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440900
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440904
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440912
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440916
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3440920
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442688
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442689
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442692
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442696
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442697
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442704
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442708
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442712
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442816
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442817
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442820
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442944
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442948
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442952
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442960
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442964
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3442968
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert

theorem certificateAtomInt_suffix_3448832 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons false).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3448832
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3448833
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3448836
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3448840
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3448841
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3448848
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3448852
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3448856
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3449088
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3449092
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3449096
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3449104
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3449108
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3449112
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3457024 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons false).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457024
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457025
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457028
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457032
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457033
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457040
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457044
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457048
                        ·
                          decide +revert
                      ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457152
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457153
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457156
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457280
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457284
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457288
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457296
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457300
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3457304
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
              decide +revert
          ·
            decide +revert
      ·
        decide +revert
    ·
      decide +revert
  ·
    decide +revert

theorem certificateAtomInt_suffix_3465216 :
    ∀ s : BitVec 12, independentMaskBV (((((((((((s.cons false).cons true).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false) = true →
      0 ≤ certificateAtomInt (((((((((((s.cons false).cons true).cons true).cons true).cons false).cons false).cons true).cons false).cons true).cons true).cons false).toNat := by
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465216
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465217
                      ·
                        decide +revert
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465220
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465224
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465225
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465232
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465236
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465240
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465472
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465476
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465480
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465488
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
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465492
                        ·
                          decide +revert
                      ·
                        decide +revert
                  ·
                    rw [BitVec.forall_cons_iff]
                    intro b2
                    cases b2
                    ·
                      rw [BitVec.forall_cons_iff]
                      intro b1
                      cases b1
                      ·
                        rw [BitVec.forall_cons_iff]
                        intro b0 s0
                        cases b0
                        ·
                          have hs0 : s0 = 0#0 := by
                            apply BitVec.eq_of_getLsbD_eq
                            intro i hi
                            omega
                          subst s0
                          intro _
                          simpa [BitVec.toNat_cons'] using certificateAtomInt_nonnegative_3465496
                        ·
                          decide +revert
                      ·
                        decide +revert
                    ·
                      decide +revert
              ·
                decide +revert
            ·
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
