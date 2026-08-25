/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.AtomSuffixes.Block00
import ErdosProblems.Erdos232.AtomSuffixes.Block01
import ErdosProblems.Erdos232.AtomSuffixes.Block02
import ErdosProblems.Erdos232.AtomSuffixes.Block03
import ErdosProblems.Erdos232.AtomSuffixes.Block04
import ErdosProblems.Erdos232.AtomSuffixes.Block05
import ErdosProblems.Erdos232.AtomSuffixes.Block06
import ErdosProblems.Erdos232.AtomSuffixes.Block07
import ErdosProblems.Erdos232.AtomSuffixes.Block08
import ErdosProblems.Erdos232.AtomSuffixes.Block09
import ErdosProblems.Erdos232.AtomSuffixes.Block10
import ErdosProblems.Erdos232.AtomSuffixes.Block11
import ErdosProblems.Erdos232.AtomSuffixes.Block12
import ErdosProblems.Erdos232.AtomSuffixes.Block13
import ErdosProblems.Erdos232.AtomSuffixes.Block14
import ErdosProblems.Erdos232.AtomSuffixes.Block15
import ErdosProblems.Erdos232.AtomSuffixes.Block16
import ErdosProblems.Erdos232.AtomSuffixes.Block17
import ErdosProblems.Erdos232.AtomSuffixes.Block18
import ErdosProblems.Erdos232.AtomSuffixes.Block19
import ErdosProblems.Erdos232.AtomSuffixes.Block20
import ErdosProblems.Erdos232.AtomSuffixes.Block21
import ErdosProblems.Erdos232.AtomSuffixes.Block22
import ErdosProblems.Erdos232.AtomSuffixes.Block23
import ErdosProblems.Erdos232.AtomSuffixes.Block24
import ErdosProblems.Erdos232.AtomSuffixes.Block25
import ErdosProblems.Erdos232.AtomSuffixes.Block26

namespace Erdos232

private theorem certificateAtomInt_nonnegative_prefix_0000 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons false).cons false).cons false).cons false) = true →
        0 ≤ certificateAtomInt ((((s.cons false).cons false).cons false).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0000000
              ·
                exact certificateAtomInt_suffix_0004096
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0008192
              ·
                exact certificateAtomInt_suffix_0012288
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0016384
              ·
                exact certificateAtomInt_suffix_0020480
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0024576
              ·
                exact certificateAtomInt_suffix_0028672
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0032768
              ·
                exact certificateAtomInt_suffix_0036864
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0040960
              ·
                exact certificateAtomInt_suffix_0045056
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0049152
              ·
                exact certificateAtomInt_suffix_0053248
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0057344
              ·
                exact certificateAtomInt_suffix_0061440
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0065536
              ·
                exact certificateAtomInt_suffix_0069632
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0073728
              ·
                exact certificateAtomInt_suffix_0077824
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0081920
              ·
                exact certificateAtomInt_suffix_0086016
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0090112
              ·
                exact certificateAtomInt_suffix_0094208
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0098304
              ·
                exact certificateAtomInt_suffix_0102400
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0106496
              ·
                exact certificateAtomInt_suffix_0110592
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0114688
              ·
                exact certificateAtomInt_suffix_0118784
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0122880
              ·
                exact certificateAtomInt_suffix_0126976
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0131072
              ·
                exact certificateAtomInt_suffix_0135168
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0147456
              ·
                exact certificateAtomInt_suffix_0151552
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0163840
              ·
                exact certificateAtomInt_suffix_0167936
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0180224
              ·
                exact certificateAtomInt_suffix_0184320
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0196608
              ·
                exact certificateAtomInt_suffix_0200704
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0212992
              ·
                exact certificateAtomInt_suffix_0217088
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0229376
              ·
                exact certificateAtomInt_suffix_0233472
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0245760
              ·
                exact certificateAtomInt_suffix_0249856
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0262144
              ·
                exact certificateAtomInt_suffix_0266240
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0270336
              ·
                exact certificateAtomInt_suffix_0274432
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0278528
              ·
                exact certificateAtomInt_suffix_0282624
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0286720
              ·
                exact certificateAtomInt_suffix_0290816
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0294912
              ·
                exact certificateAtomInt_suffix_0299008
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0303104
              ·
                exact certificateAtomInt_suffix_0307200
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0311296
              ·
                exact certificateAtomInt_suffix_0315392
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0319488
              ·
                exact certificateAtomInt_suffix_0323584
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0327680
              ·
                exact certificateAtomInt_suffix_0331776
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0335872
              ·
                exact certificateAtomInt_suffix_0339968
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0344064
              ·
                exact certificateAtomInt_suffix_0348160
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0352256
              ·
                exact certificateAtomInt_suffix_0356352
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0360448
              ·
                exact certificateAtomInt_suffix_0364544
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0368640
              ·
                exact certificateAtomInt_suffix_0372736
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0376832
              ·
                exact certificateAtomInt_suffix_0380928
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0385024
              ·
                exact certificateAtomInt_suffix_0389120
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0393216
              ·
                exact certificateAtomInt_suffix_0397312
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0409600
              ·
                exact certificateAtomInt_suffix_0413696
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0425984
              ·
                exact certificateAtomInt_suffix_0430080
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0442368
              ·
                exact certificateAtomInt_suffix_0446464
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0458752
              ·
                exact certificateAtomInt_suffix_0462848
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0475136
              ·
                exact certificateAtomInt_suffix_0479232
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0491520
              ·
                exact certificateAtomInt_suffix_0495616
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0507904
              ·
                exact certificateAtomInt_suffix_0512000
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_0001 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons true).cons false).cons false).cons false) = true →
        0 ≤ certificateAtomInt ((((s.cons true).cons false).cons false).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0524288
              ·
                exact certificateAtomInt_suffix_0528384
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0532480
              ·
                exact certificateAtomInt_suffix_0536576
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0540672
              ·
                exact certificateAtomInt_suffix_0544768
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0548864
              ·
                exact certificateAtomInt_suffix_0552960
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0557056
              ·
                exact certificateAtomInt_suffix_0561152
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0565248
              ·
                exact certificateAtomInt_suffix_0569344
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0573440
              ·
                exact certificateAtomInt_suffix_0577536
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0581632
              ·
                exact certificateAtomInt_suffix_0585728
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0589824
              ·
                exact certificateAtomInt_suffix_0593920
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0598016
              ·
                exact certificateAtomInt_suffix_0602112
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0606208
              ·
                exact certificateAtomInt_suffix_0610304
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0614400
              ·
                exact certificateAtomInt_suffix_0618496
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0622592
              ·
                exact certificateAtomInt_suffix_0626688
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0630784
              ·
                exact certificateAtomInt_suffix_0634880
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0638976
              ·
                exact certificateAtomInt_suffix_0643072
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0647168
              ·
                exact certificateAtomInt_suffix_0651264
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0655360
              ·
                exact certificateAtomInt_suffix_0659456
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0671744
              ·
                exact certificateAtomInt_suffix_0675840
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0688128
              ·
                exact certificateAtomInt_suffix_0692224
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0704512
              ·
                exact certificateAtomInt_suffix_0708608
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0720896
              ·
                exact certificateAtomInt_suffix_0724992
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0737280
              ·
                exact certificateAtomInt_suffix_0741376
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0753664
              ·
                exact certificateAtomInt_suffix_0757760
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_0770048
              ·
                exact certificateAtomInt_suffix_0774144
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
  ·
    intro v hv
    simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
    norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_0010 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons false).cons true).cons false).cons false) = true →
        0 ≤ certificateAtomInt ((((s.cons false).cons true).cons false).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1048576
              ·
                exact certificateAtomInt_suffix_1052672
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1056768
              ·
                exact certificateAtomInt_suffix_1060864
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1064960
              ·
                exact certificateAtomInt_suffix_1069056
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1073152
              ·
                exact certificateAtomInt_suffix_1077248
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1081344
              ·
                exact certificateAtomInt_suffix_1085440
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1089536
              ·
                exact certificateAtomInt_suffix_1093632
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1097728
              ·
                exact certificateAtomInt_suffix_1101824
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1105920
              ·
                exact certificateAtomInt_suffix_1110016
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1179648
              ·
                exact certificateAtomInt_suffix_1183744
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1196032
              ·
                exact certificateAtomInt_suffix_1200128
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1212416
              ·
                exact certificateAtomInt_suffix_1216512
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1228800
              ·
                exact certificateAtomInt_suffix_1232896
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1310720
              ·
                exact certificateAtomInt_suffix_1314816
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1318912
              ·
                exact certificateAtomInt_suffix_1323008
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1327104
              ·
                exact certificateAtomInt_suffix_1331200
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1335296
              ·
                exact certificateAtomInt_suffix_1339392
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1343488
              ·
                exact certificateAtomInt_suffix_1347584
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1351680
              ·
                exact certificateAtomInt_suffix_1355776
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1359872
              ·
                exact certificateAtomInt_suffix_1363968
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1368064
              ·
                exact certificateAtomInt_suffix_1372160
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1441792
              ·
                exact certificateAtomInt_suffix_1445888
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1458176
              ·
                exact certificateAtomInt_suffix_1462272
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1474560
              ·
                exact certificateAtomInt_suffix_1478656
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1490944
              ·
                exact certificateAtomInt_suffix_1495040
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_0011 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons true).cons true).cons false).cons false) = true →
        0 ≤ certificateAtomInt ((((s.cons true).cons true).cons false).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1572864
              ·
                exact certificateAtomInt_suffix_1576960
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1581056
              ·
                exact certificateAtomInt_suffix_1585152
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1589248
              ·
                exact certificateAtomInt_suffix_1593344
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1597440
              ·
                exact certificateAtomInt_suffix_1601536
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1605632
              ·
                exact certificateAtomInt_suffix_1609728
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1613824
              ·
                exact certificateAtomInt_suffix_1617920
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1622016
              ·
                exact certificateAtomInt_suffix_1626112
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1630208
              ·
                exact certificateAtomInt_suffix_1634304
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1703936
              ·
                exact certificateAtomInt_suffix_1708032
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1720320
              ·
                exact certificateAtomInt_suffix_1724416
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1736704
              ·
                exact certificateAtomInt_suffix_1740800
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_1753088
              ·
                exact certificateAtomInt_suffix_1757184
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
  ·
    intro v hv
    simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
    norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_0100 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons false).cons false).cons true).cons false) = true →
        0 ≤ certificateAtomInt ((((s.cons false).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2097152
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2105344
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2113536
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2121728
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2129920
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2138112
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2146304
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2154496
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2228224
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2244608
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2260992
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2277376
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2359296
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2367488
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2375680
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2383872
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2392064
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2400256
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2408448
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2416640
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2490368
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2506752
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2523136
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2539520
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_0101 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons true).cons false).cons true).cons false) = true →
        0 ≤ certificateAtomInt ((((s.cons true).cons false).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2621440
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2629632
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2637824
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2646016
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2654208
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2662400
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2670592
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2678784
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2752512
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2768896
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2785280
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_2801664
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
  ·
    intro v hv
    simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
    norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_0110 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons false).cons true).cons true).cons false) = true →
        0 ≤ certificateAtomInt ((((s.cons false).cons true).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3145728
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3153920
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3162112
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3170304
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3178496
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3186688
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3194880
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3203072
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3276800
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3293184
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3309568
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3325952
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3407872
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3416064
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3424256
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3432448
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3440640
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3448832
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3457024
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3465216
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3538944
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3555328
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3571712
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3588096
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_0111 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons true).cons true).cons true).cons false) = true →
        0 ≤ certificateAtomInt ((((s.cons true).cons true).cons true).cons false).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3670016
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3678208
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3686400
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3694592
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3702784
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3710976
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3719168
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3727360
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3801088
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3817472
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3833856
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_3850240
              ·
                intro v hv
                simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
                norm_num at hv
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
  ·
    intro v hv
    simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
    norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_1000 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons false).cons false).cons false).cons true) = true →
        0 ≤ certificateAtomInt ((((s.cons false).cons false).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4194304
              ·
                exact certificateAtomInt_suffix_4198400
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4202496
              ·
                exact certificateAtomInt_suffix_4206592
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4210688
              ·
                exact certificateAtomInt_suffix_4214784
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4218880
              ·
                exact certificateAtomInt_suffix_4222976
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4227072
              ·
                exact certificateAtomInt_suffix_4231168
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4235264
              ·
                exact certificateAtomInt_suffix_4239360
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4243456
              ·
                exact certificateAtomInt_suffix_4247552
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4251648
              ·
                exact certificateAtomInt_suffix_4255744
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4325376
              ·
                exact certificateAtomInt_suffix_4329472
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4341760
              ·
                exact certificateAtomInt_suffix_4345856
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4358144
              ·
                exact certificateAtomInt_suffix_4362240
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4374528
              ·
                exact certificateAtomInt_suffix_4378624
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4456448
              ·
                exact certificateAtomInt_suffix_4460544
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4464640
              ·
                exact certificateAtomInt_suffix_4468736
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4472832
              ·
                exact certificateAtomInt_suffix_4476928
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4481024
              ·
                exact certificateAtomInt_suffix_4485120
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4489216
              ·
                exact certificateAtomInt_suffix_4493312
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4497408
              ·
                exact certificateAtomInt_suffix_4501504
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4505600
              ·
                exact certificateAtomInt_suffix_4509696
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4513792
              ·
                exact certificateAtomInt_suffix_4517888
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4587520
              ·
                exact certificateAtomInt_suffix_4591616
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4603904
              ·
                exact certificateAtomInt_suffix_4608000
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4620288
              ·
                exact certificateAtomInt_suffix_4624384
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4636672
              ·
                exact certificateAtomInt_suffix_4640768
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_1001 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons true).cons false).cons false).cons true) = true →
        0 ≤ certificateAtomInt ((((s.cons true).cons false).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4718592
              ·
                exact certificateAtomInt_suffix_4722688
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4726784
              ·
                exact certificateAtomInt_suffix_4730880
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4734976
              ·
                exact certificateAtomInt_suffix_4739072
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4743168
              ·
                exact certificateAtomInt_suffix_4747264
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4751360
              ·
                exact certificateAtomInt_suffix_4755456
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4759552
              ·
                exact certificateAtomInt_suffix_4763648
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4767744
              ·
                exact certificateAtomInt_suffix_4771840
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4775936
              ·
                exact certificateAtomInt_suffix_4780032
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4849664
              ·
                exact certificateAtomInt_suffix_4853760
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4866048
              ·
                exact certificateAtomInt_suffix_4870144
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4882432
              ·
                exact certificateAtomInt_suffix_4886528
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_4898816
              ·
                exact certificateAtomInt_suffix_4902912
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
  ·
    intro v hv
    simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
    norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_1010 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons false).cons true).cons false).cons true) = true →
        0 ≤ certificateAtomInt ((((s.cons false).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5242880
              ·
                exact certificateAtomInt_suffix_5246976
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5251072
              ·
                exact certificateAtomInt_suffix_5255168
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5259264
              ·
                exact certificateAtomInt_suffix_5263360
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5267456
              ·
                exact certificateAtomInt_suffix_5271552
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5275648
              ·
                exact certificateAtomInt_suffix_5279744
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5283840
              ·
                exact certificateAtomInt_suffix_5287936
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5292032
              ·
                exact certificateAtomInt_suffix_5296128
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5300224
              ·
                exact certificateAtomInt_suffix_5304320
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5373952
              ·
                exact certificateAtomInt_suffix_5378048
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5390336
              ·
                exact certificateAtomInt_suffix_5394432
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5406720
              ·
                exact certificateAtomInt_suffix_5410816
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5423104
              ·
                exact certificateAtomInt_suffix_5427200
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5505024
              ·
                exact certificateAtomInt_suffix_5509120
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5513216
              ·
                exact certificateAtomInt_suffix_5517312
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5521408
              ·
                exact certificateAtomInt_suffix_5525504
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5529600
              ·
                exact certificateAtomInt_suffix_5533696
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5537792
              ·
                exact certificateAtomInt_suffix_5541888
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5545984
              ·
                exact certificateAtomInt_suffix_5550080
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5554176
              ·
                exact certificateAtomInt_suffix_5558272
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5562368
              ·
                exact certificateAtomInt_suffix_5566464
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5636096
              ·
                exact certificateAtomInt_suffix_5640192
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5652480
              ·
                exact certificateAtomInt_suffix_5656576
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5668864
              ·
                exact certificateAtomInt_suffix_5672960
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5685248
              ·
                exact certificateAtomInt_suffix_5689344
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv

private theorem certificateAtomInt_nonnegative_prefix_1011 :
    ∀ s : BitVec 19,
      independentMaskBV ((((s.cons true).cons true).cons false).cons true) = true →
        0 ≤ certificateAtomInt ((((s.cons true).cons true).cons false).cons true).toNat := by
  rw [BitVec.forall_cons_iff]
  intro b18
  cases b18
  ·
    rw [BitVec.forall_cons_iff]
    intro b17
    cases b17
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5767168
              ·
                exact certificateAtomInt_suffix_5771264
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5775360
              ·
                exact certificateAtomInt_suffix_5779456
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5783552
              ·
                exact certificateAtomInt_suffix_5787648
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5791744
              ·
                exact certificateAtomInt_suffix_5795840
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5799936
              ·
                exact certificateAtomInt_suffix_5804032
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5808128
              ·
                exact certificateAtomInt_suffix_5812224
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5816320
              ·
                exact certificateAtomInt_suffix_5820416
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5824512
              ·
                exact certificateAtomInt_suffix_5828608
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
    ·
      rw [BitVec.forall_cons_iff]
      intro b16
      cases b16
      ·
        rw [BitVec.forall_cons_iff]
        intro b15
        cases b15
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5898240
              ·
                exact certificateAtomInt_suffix_5902336
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5914624
              ·
                exact certificateAtomInt_suffix_5918720
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
        ·
          rw [BitVec.forall_cons_iff]
          intro b14
          cases b14
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5931008
              ·
                exact certificateAtomInt_suffix_5935104
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
          ·
            rw [BitVec.forall_cons_iff]
            intro b13
            cases b13
            ·
              rw [BitVec.forall_cons_iff]
              intro b12
              cases b12
              ·
                exact certificateAtomInt_suffix_5947392
              ·
                exact certificateAtomInt_suffix_5951488
            ·
              intro v hv
              simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
              norm_num at hv
      ·
        intro v hv
        simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
        norm_num at hv
  ·
    intro v hv
    simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
    norm_num at hv

theorem certificateAtomInt_nonnegative :
    ∀ s : BitVec 23, independentMaskBV s = true → 0 ≤ certificateAtomInt s.toNat := by
  rw [BitVec.forall_cons_iff]
  intro b22
  cases b22
  ·
    rw [BitVec.forall_cons_iff]
    intro b21
    cases b21
    ·
      rw [BitVec.forall_cons_iff]
      intro b20
      cases b20
      ·
        rw [BitVec.forall_cons_iff]
        intro b19
        cases b19
        ·
          exact certificateAtomInt_nonnegative_prefix_0000
        ·
          exact certificateAtomInt_nonnegative_prefix_0001
      ·
        rw [BitVec.forall_cons_iff]
        intro b19
        cases b19
        ·
          exact certificateAtomInt_nonnegative_prefix_0010
        ·
          exact certificateAtomInt_nonnegative_prefix_0011
    ·
      rw [BitVec.forall_cons_iff]
      intro b20
      cases b20
      ·
        rw [BitVec.forall_cons_iff]
        intro b19
        cases b19
        ·
          exact certificateAtomInt_nonnegative_prefix_0100
        ·
          exact certificateAtomInt_nonnegative_prefix_0101
      ·
        rw [BitVec.forall_cons_iff]
        intro b19
        cases b19
        ·
          exact certificateAtomInt_nonnegative_prefix_0110
        ·
          exact certificateAtomInt_nonnegative_prefix_0111
  ·
    rw [BitVec.forall_cons_iff]
    intro b21
    cases b21
    ·
      rw [BitVec.forall_cons_iff]
      intro b20
      cases b20
      ·
        rw [BitVec.forall_cons_iff]
        intro b19
        cases b19
        ·
          exact certificateAtomInt_nonnegative_prefix_1000
        ·
          exact certificateAtomInt_nonnegative_prefix_1001
      ·
        rw [BitVec.forall_cons_iff]
        intro b19
        cases b19
        ·
          exact certificateAtomInt_nonnegative_prefix_1010
        ·
          exact certificateAtomInt_nonnegative_prefix_1011
    ·
      intro v hv
      simp only [independentMaskBV, BitVec.getLsbD_cons] at hv
      norm_num at hv

end Erdos232
