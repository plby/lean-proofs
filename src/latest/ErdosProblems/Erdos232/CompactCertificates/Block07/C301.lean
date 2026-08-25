/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate301 : CompactCertificate where
  left := 174
  right := 175
  center := 349 / 2
  grid := fun i =>
    match i.val with
    | 0 => 56
    | 1 => 41
    | 2 => 66
    | 3 => 12
    | 4 => 32
    | 5 => 87
    | 6 => 64
    | 7 => 110
    | 8 => 81
    | 9 => 124
    | 10 => 72
    | 11 => 127
    | 12 => 119
    | 13 => 85
    | 14 => 96
    | 15 => 80
    | 16 => 71
    | 17 => 103
    | 18 => 57
    | 19 => 48
    | 20 => 30
    | 21 => 16
    | 22 => 44
    | 23 => 60
    | 24 => 25
    | 25 => 103
    | _ => 69
  point := fun i =>
    match i.val with
    | 0 => 349 / 2
    | 1 => 514143640817449 / 4000000000000
    | 2 => 166263489692617 / 800000000000
    | 3 => 150025832098043 / 4000000000000
    | 4 => 402990487894271 / 4000000000000
    | 5 => 1094197567447107 / 4000000000000
    | 6 => 805980975788891 / 4000000000000
    | 7 => 1381062139519943 / 4000000000000
    | 8 => 1017284121214037 / 4000000000000
    | 9 => 1560775448294651 / 4000000000000
    | 10 => 901114125217379 / 4000000000000
    | 11 => 1599042828240511 / 4000000000000
    | 12 => 1494033232522459 / 4000000000000
    | 13 => 1066212611692747 / 4000000000000
    | 14 => 1208971463682813 / 4000000000000
    | 15 => 1007914364807597 / 4000000000000
    | 16 => 890522908283537 / 4000000000000
    | 17 => 258108248618163 / 800000000000
    | 18 => 713940999170761 / 4000000000000
    | 19 => 605215691677121 / 4000000000000
    | 20 => 378715878785963 / 4000000000000
    | 21 => 203674659163221 / 4000000000000
    | 22 => 553016319992663 / 4000000000000
    | 23 => 755096506130551 / 4000000000000
    | 24 => 319284121214037 / 4000000000000
    | 25 => 1297872226610677 / 4000000000000
    | _ => 866918498702843 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-36288958826 / 1000000000000) (-36288944401 / 1000000000000), orderedInterval (48388202596 / 1000000000000) (48388217021 / 1000000000000))
    | 1 => (orderedInterval (-34665033238 / 1000000000000) (-34665033237 / 1000000000000), orderedInterval (-61112279709 / 1000000000000) (-61112279708 / 1000000000000))
    | 2 => (orderedInterval (52845274932 / 1000000000000) (52845274933 / 1000000000000), orderedInterval (16321407315 / 1000000000000) (16321407317 / 1000000000000))
    | 3 => (orderedInterval (72417470572 / 1000000000000) (72417470573 / 1000000000000), orderedInterval (107339386458 / 1000000000000) (107339386459 / 1000000000000))
    | 4 => (orderedInterval (66924644700 / 1000000000000) (66924644701 / 1000000000000), orderedInterval (42563267154 / 1000000000000) (42563267155 / 1000000000000))
    | 5 => (orderedInterval (-40999955205 / 1000000000000) (-40999955204 / 1000000000000), orderedInterval (-25346685676 / 1000000000000) (-25346685675 / 1000000000000))
    | 6 => (orderedInterval (52749021102 / 1000000000000) (52749021103 / 1000000000000), orderedInterval (19285885102 / 1000000000000) (19285885103 / 1000000000000))
    | 7 => (orderedInterval (19652641663 / 1000000000000) (19652641664 / 1000000000000), orderedInterval (38150465319 / 1000000000000) (38150465320 / 1000000000000))
    | 8 => (orderedInterval (-29755666582 / 1000000000000) (-29755666581 / 1000000000000), orderedInterval (-40163570701 / 1000000000000) (-40163570700 / 1000000000000))
    | 9 => (orderedInterval (39942779800 / 1000000000000) (39942779832 / 1000000000000), orderedInterval (5958844921 / 1000000000000) (5958844953 / 1000000000000))
    | 10 => (orderedInterval (-6959597436 / 1000000000000) (-6959597417 / 1000000000000), orderedInterval (52717378957 / 1000000000000) (52717378976 / 1000000000000))
    | 11 => (orderedInterval (-39905096116 / 1000000000000) (-39905095866 / 1000000000000), orderedInterval (-240236099 / 1000000000000) (-240235848 / 1000000000000))
    | 12 => (orderedInterval (-17728329014 / 1000000000000) (-17728329013 / 1000000000000), orderedInterval (-37260849262 / 1000000000000) (-37260849261 / 1000000000000))
    | 13 => (orderedInterval (-14568564689 / 1000000000000) (-14568564688 / 1000000000000), orderedInterval (-46621372118 / 1000000000000) (-46621372117 / 1000000000000))
    | 14 => (orderedInterval (45471827333 / 1000000000000) (45471827352 / 1000000000000), orderedInterval (6139979251 / 1000000000000) (6139979270 / 1000000000000))
    | 15 => (orderedInterval (49808676169 / 1000000000000) (49808676183 / 1000000000000), orderedInterval (6652058520 / 1000000000000) (6652058534 / 1000000000000))
    | 16 => (orderedInterval (-18962024406 / 1000000000000) (-18962024405 / 1000000000000), orderedInterval (-49957208007 / 1000000000000) (-49957208006 / 1000000000000))
    | 17 => (orderedInterval (7240165107 / 1000000000000) (7240165122 / 1000000000000), orderedInterval (-43837800900 / 1000000000000) (-43837800885 / 1000000000000))
    | 18 => (orderedInterval (-11816232988 / 1000000000000) (-11816232986 / 1000000000000), orderedInterval (-58509034088 / 1000000000000) (-58509034087 / 1000000000000))
    | 19 => (orderedInterval (62361724254 / 1000000000000) (62361724255 / 1000000000000), orderedInterval (17641950356 / 1000000000000) (17641950357 / 1000000000000))
    | 20 => (orderedInterval (76871311319 / 1000000000000) (76871311320 / 1000000000000), orderedInterval (28137237737 / 1000000000000) (28137237738 / 1000000000000))
    | 21 => (orderedInterval (110800299863 / 1000000000000) (110800299866 / 1000000000000), orderedInterval (13925182737 / 1000000000000) (13925182741 / 1000000000000))
    | 22 => (orderedInterval (49078157789 / 1000000000000) (49078157790 / 1000000000000), orderedInterval (46684453653 / 1000000000000) (46684453654 / 1000000000000))
    | 23 => (orderedInterval (50753081409 / 1000000000000) (50753081410 / 1000000000000), orderedInterval (28088035640 / 1000000000000) (28088035641 / 1000000000000))
    | 24 => (orderedInterval (-78617656128 / 1000000000000) (-78617644143 / 1000000000000), orderedInterval (42857144750 / 1000000000000) (42857156736 / 1000000000000))
    | 25 => (orderedInterval (-44081379288 / 1000000000000) (-44081378696 / 1000000000000), orderedInterval (4412025170 / 1000000000000) (4412025762 / 1000000000000))
    | _ => (orderedInterval (-36726656964 / 1000000000000) (-36726656963 / 1000000000000), orderedInterval (-39771824982 / 1000000000000) (-39771824981 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-11605662800 / 1000000000000) (-11605657070 / 1000000000000)
      | 1 => orderedInterval (4572529502 / 1000000000000) (4572529524 / 1000000000000)
      | 2 => orderedInterval (-1325301858 / 1000000000000) (-1325301847 / 1000000000000)
      | 3 => orderedInterval (-13285743175 / 1000000000000) (-13285743063 / 1000000000000)
      | 4 => orderedInterval (-1287707831 / 1000000000000) (-1287707809 / 1000000000000)
      | 5 => orderedInterval (1845684618 / 1000000000000) (1845684636 / 1000000000000)
      | 6 => orderedInterval (862221848 / 1000000000000) (862221893 / 1000000000000)
      | 7 => orderedInterval (-7049028713 / 1000000000000) (-7049028691 / 1000000000000)
      | _ => orderedInterval (10005264611 / 1000000000000) (10005264780 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (19900626798 / 1000000000000) (19900632530 / 1000000000000)
      | 1 => orderedInterval (3471601267 / 1000000000000) (3471601292 / 1000000000000)
      | 2 => orderedInterval (-3742930199 / 1000000000000) (-3742930181 / 1000000000000)
      | 3 => orderedInterval (2596708009 / 1000000000000) (2596708249 / 1000000000000)
      | 4 => orderedInterval (-5348320220 / 1000000000000) (-5348320185 / 1000000000000)
      | 5 => orderedInterval (1683088670 / 1000000000000) (1683088695 / 1000000000000)
      | 6 => orderedInterval (9200011690 / 1000000000000) (9200011731 / 1000000000000)
      | 7 => orderedInterval (-3242881123 / 1000000000000) (-3242881104 / 1000000000000)
      | _ => orderedInterval (8718516771 / 1000000000000) (8718516962 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10046146883 / 1000000000000) (10046152650 / 1000000000000)
      | 1 => orderedInterval (-7960704076 / 1000000000000) (-7960704042 / 1000000000000)
      | 2 => orderedInterval (3922013126 / 1000000000000) (3922013157 / 1000000000000)
      | 3 => orderedInterval (66102909377 / 1000000000000) (66102909903 / 1000000000000)
      | 4 => orderedInterval (2469175262 / 1000000000000) (2469175319 / 1000000000000)
      | 5 => orderedInterval (-3608966302 / 1000000000000) (-3608966263 / 1000000000000)
      | 6 => orderedInterval (-112399576 / 1000000000000) (-112399536 / 1000000000000)
      | 7 => orderedInterval (5443742380 / 1000000000000) (5443742399 / 1000000000000)
      | _ => orderedInterval (-22986800057 / 1000000000000) (-22986799773 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-20626774042 / 1000000000000) (-20626768273 / 1000000000000)
      | 1 => orderedInterval (-7183203496 / 1000000000000) (-7183203446 / 1000000000000)
      | 2 => orderedInterval (12097061885 / 1000000000000) (12097061941 / 1000000000000)
      | 3 => orderedInterval (3465568597 / 1000000000000) (3465569768 / 1000000000000)
      | 4 => orderedInterval (9263975165 / 1000000000000) (9263975261 / 1000000000000)
      | 5 => orderedInterval (946694056 / 1000000000000) (946694115 / 1000000000000)
      | 6 => orderedInterval (-9505309834 / 1000000000000) (-9505309796 / 1000000000000)
      | 7 => orderedInterval (3227106097 / 1000000000000) (3227106117 / 1000000000000)
      | _ => orderedInterval (-11880614018 / 1000000000000) (-11880613545 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-8002514844 / 1000000000000) (-8002509040 / 1000000000000)
      | 1 => orderedInterval (17953447189 / 1000000000000) (17953447266 / 1000000000000)
      | 2 => orderedInterval (-12673249343 / 1000000000000) (-12673249240 / 1000000000000)
      | 3 => orderedInterval (-335150734446 / 1000000000000) (-335150731819 / 1000000000000)
      | 4 => orderedInterval (-2959652748 / 1000000000000) (-2959652581 / 1000000000000)
      | 5 => orderedInterval (7531132352 / 1000000000000) (7531132446 / 1000000000000)
      | 6 => orderedInterval (398693728 / 1000000000000) (398693766 / 1000000000000)
      | 7 => orderedInterval (-5817573664 / 1000000000000) (-5817573643 / 1000000000000)
      | _ => orderedInterval (59405619889 / 1000000000000) (59405620722 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-17267743798 / 1000000000000) (-17267737647 / 1000000000000)
    | 1 => orderedInterval (33236421663 / 1000000000000) (33236427989 / 1000000000000)
    | 2 => orderedInterval (53315117017 / 1000000000000) (53315123814 / 1000000000000)
    | 3 => orderedInterval (-20195495590 / 1000000000000) (-20195487858 / 1000000000000)
    | _ => orderedInterval (-279314831887 / 1000000000000) (-279314822123 / 1000000000000)

theorem compactCertificate301_stateChecks0 :
    compactCertificate301.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (349 / 2)) (orderedInterval (-36288958826 / 1000000000000) (-36288944401 / 1000000000000), orderedInterval (48388202596 / 1000000000000) (48388217021 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (514143640817449 / 4000000000000)) (orderedInterval (-34665033238 / 1000000000000) (-34665033237 / 1000000000000), orderedInterval (-61112279709 / 1000000000000) (-61112279708 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (166263489692617 / 800000000000)) (orderedInterval (52845274932 / 1000000000000) (52845274933 / 1000000000000), orderedInterval (16321407315 / 1000000000000) (16321407317 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_stateChecks1 :
    compactCertificate301.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (150025832098043 / 4000000000000)) (orderedInterval (72417470572 / 1000000000000) (72417470573 / 1000000000000), orderedInterval (107339386458 / 1000000000000) (107339386459 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (402990487894271 / 4000000000000)) (orderedInterval (66924644700 / 1000000000000) (66924644701 / 1000000000000), orderedInterval (42563267154 / 1000000000000) (42563267155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1094197567447107 / 4000000000000)) (orderedInterval (-40999955205 / 1000000000000) (-40999955204 / 1000000000000), orderedInterval (-25346685676 / 1000000000000) (-25346685675 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_stateChecks2 :
    compactCertificate301.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (805980975788891 / 4000000000000)) (orderedInterval (52749021102 / 1000000000000) (52749021103 / 1000000000000), orderedInterval (19285885102 / 1000000000000) (19285885103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1381062139519943 / 4000000000000)) (orderedInterval (19652641663 / 1000000000000) (19652641664 / 1000000000000), orderedInterval (38150465319 / 1000000000000) (38150465320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1017284121214037 / 4000000000000)) (orderedInterval (-29755666582 / 1000000000000) (-29755666581 / 1000000000000), orderedInterval (-40163570701 / 1000000000000) (-40163570700 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_stateChecks3 :
    compactCertificate301.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1560775448294651 / 4000000000000)) (orderedInterval (39942779800 / 1000000000000) (39942779832 / 1000000000000), orderedInterval (5958844921 / 1000000000000) (5958844953 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (901114125217379 / 4000000000000)) (orderedInterval (-6959597436 / 1000000000000) (-6959597417 / 1000000000000), orderedInterval (52717378957 / 1000000000000) (52717378976 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1599042828240511 / 4000000000000)) (orderedInterval (-39905096116 / 1000000000000) (-39905095866 / 1000000000000), orderedInterval (-240236099 / 1000000000000) (-240235848 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_stateChecks4 :
    compactCertificate301.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1494033232522459 / 4000000000000)) (orderedInterval (-17728329014 / 1000000000000) (-17728329013 / 1000000000000), orderedInterval (-37260849262 / 1000000000000) (-37260849261 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1066212611692747 / 4000000000000)) (orderedInterval (-14568564689 / 1000000000000) (-14568564688 / 1000000000000), orderedInterval (-46621372118 / 1000000000000) (-46621372117 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1208971463682813 / 4000000000000)) (orderedInterval (45471827333 / 1000000000000) (45471827352 / 1000000000000), orderedInterval (6139979251 / 1000000000000) (6139979270 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_stateChecks5 :
    compactCertificate301.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1007914364807597 / 4000000000000)) (orderedInterval (49808676169 / 1000000000000) (49808676183 / 1000000000000), orderedInterval (6652058520 / 1000000000000) (6652058534 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (890522908283537 / 4000000000000)) (orderedInterval (-18962024406 / 1000000000000) (-18962024405 / 1000000000000), orderedInterval (-49957208007 / 1000000000000) (-49957208006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (258108248618163 / 800000000000)) (orderedInterval (7240165107 / 1000000000000) (7240165122 / 1000000000000), orderedInterval (-43837800900 / 1000000000000) (-43837800885 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_stateChecks6 :
    compactCertificate301.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (713940999170761 / 4000000000000)) (orderedInterval (-11816232988 / 1000000000000) (-11816232986 / 1000000000000), orderedInterval (-58509034088 / 1000000000000) (-58509034087 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (605215691677121 / 4000000000000)) (orderedInterval (62361724254 / 1000000000000) (62361724255 / 1000000000000), orderedInterval (17641950356 / 1000000000000) (17641950357 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (378715878785963 / 4000000000000)) (orderedInterval (76871311319 / 1000000000000) (76871311320 / 1000000000000), orderedInterval (28137237737 / 1000000000000) (28137237738 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_stateChecks7 :
    compactCertificate301.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (203674659163221 / 4000000000000)) (orderedInterval (110800299863 / 1000000000000) (110800299866 / 1000000000000), orderedInterval (13925182737 / 1000000000000) (13925182741 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (553016319992663 / 4000000000000)) (orderedInterval (49078157789 / 1000000000000) (49078157790 / 1000000000000), orderedInterval (46684453653 / 1000000000000) (46684453654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (755096506130551 / 4000000000000)) (orderedInterval (50753081409 / 1000000000000) (50753081410 / 1000000000000), orderedInterval (28088035640 / 1000000000000) (28088035641 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_stateChecks8 :
    compactCertificate301.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (319284121214037 / 4000000000000)) (orderedInterval (-78617656128 / 1000000000000) (-78617644143 / 1000000000000), orderedInterval (42857144750 / 1000000000000) (42857156736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1297872226610677 / 4000000000000)) (orderedInterval (-44081379288 / 1000000000000) (-44081378696 / 1000000000000), orderedInterval (4412025170 / 1000000000000) (4412025762 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (866918498702843 / 4000000000000)) (orderedInterval (-36726656964 / 1000000000000) (-36726656963 / 1000000000000), orderedInterval (-39771824982 / 1000000000000) (-39771824981 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_states : ∀ j,
    BesselStateValid (compactCertificate301.point j) (compactCertificate301.state j) :=
  compactCertificate301.statesValid_of_checks3 compactCertificate301_stateChecks0
    compactCertificate301_stateChecks1 compactCertificate301_stateChecks2
    compactCertificate301_stateChecks3 compactCertificate301_stateChecks4
    compactCertificate301_stateChecks5 compactCertificate301_stateChecks6
    compactCertificate301_stateChecks7 compactCertificate301_stateChecks8

theorem compactCertificate301_chunkChecks0_0 :
    compactCertificate301.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (349 / 2) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36288958826 / 1000000000000) (-36288944401 / 1000000000000), orderedInterval (48388202596 / 1000000000000) (48388217021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (514143640817449 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-34665033238 / 1000000000000) (-34665033237 / 1000000000000), orderedInterval (-61112279709 / 1000000000000) (-61112279708 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (166263489692617 / 800000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52845274932 / 1000000000000) (52845274933 / 1000000000000), orderedInterval (16321407315 / 1000000000000) (16321407317 / 1000000000000)))) (orderedInterval (-11605662800 / 1000000000000) (-11605657070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (150025832098043 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72417470572 / 1000000000000) (72417470573 / 1000000000000), orderedInterval (107339386458 / 1000000000000) (107339386459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (402990487894271 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (66924644700 / 1000000000000) (66924644701 / 1000000000000), orderedInterval (42563267154 / 1000000000000) (42563267155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1094197567447107 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40999955205 / 1000000000000) (-40999955204 / 1000000000000), orderedInterval (-25346685676 / 1000000000000) (-25346685675 / 1000000000000)))) (orderedInterval (4572529502 / 1000000000000) (4572529524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (805980975788891 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52749021102 / 1000000000000) (52749021103 / 1000000000000), orderedInterval (19285885102 / 1000000000000) (19285885103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1381062139519943 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19652641663 / 1000000000000) (19652641664 / 1000000000000), orderedInterval (38150465319 / 1000000000000) (38150465320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1017284121214037 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29755666582 / 1000000000000) (-29755666581 / 1000000000000), orderedInterval (-40163570701 / 1000000000000) (-40163570700 / 1000000000000)))) (orderedInterval (-1325301858 / 1000000000000) (-1325301847 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_chunkChecks0_1 :
    compactCertificate301.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1560775448294651 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (39942779800 / 1000000000000) (39942779832 / 1000000000000), orderedInterval (5958844921 / 1000000000000) (5958844953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (901114125217379 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6959597436 / 1000000000000) (-6959597417 / 1000000000000), orderedInterval (52717378957 / 1000000000000) (52717378976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1599042828240511 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-39905096116 / 1000000000000) (-39905095866 / 1000000000000), orderedInterval (-240236099 / 1000000000000) (-240235848 / 1000000000000)))) (orderedInterval (-13285743175 / 1000000000000) (-13285743063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1494033232522459 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17728329014 / 1000000000000) (-17728329013 / 1000000000000), orderedInterval (-37260849262 / 1000000000000) (-37260849261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1066212611692747 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14568564689 / 1000000000000) (-14568564688 / 1000000000000), orderedInterval (-46621372118 / 1000000000000) (-46621372117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1208971463682813 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (45471827333 / 1000000000000) (45471827352 / 1000000000000), orderedInterval (6139979251 / 1000000000000) (6139979270 / 1000000000000)))) (orderedInterval (-1287707831 / 1000000000000) (-1287707809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1007914364807597 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (49808676169 / 1000000000000) (49808676183 / 1000000000000), orderedInterval (6652058520 / 1000000000000) (6652058534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (890522908283537 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18962024406 / 1000000000000) (-18962024405 / 1000000000000), orderedInterval (-49957208007 / 1000000000000) (-49957208006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (258108248618163 / 800000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7240165107 / 1000000000000) (7240165122 / 1000000000000), orderedInterval (-43837800900 / 1000000000000) (-43837800885 / 1000000000000)))) (orderedInterval (1845684618 / 1000000000000) (1845684636 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_chunkChecks0_2 :
    compactCertificate301.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (713940999170761 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11816232988 / 1000000000000) (-11816232986 / 1000000000000), orderedInterval (-58509034088 / 1000000000000) (-58509034087 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (605215691677121 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (62361724254 / 1000000000000) (62361724255 / 1000000000000), orderedInterval (17641950356 / 1000000000000) (17641950357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (378715878785963 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (76871311319 / 1000000000000) (76871311320 / 1000000000000), orderedInterval (28137237737 / 1000000000000) (28137237738 / 1000000000000)))) (orderedInterval (862221848 / 1000000000000) (862221893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (203674659163221 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (110800299863 / 1000000000000) (110800299866 / 1000000000000), orderedInterval (13925182737 / 1000000000000) (13925182741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (553016319992663 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49078157789 / 1000000000000) (49078157790 / 1000000000000), orderedInterval (46684453653 / 1000000000000) (46684453654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (755096506130551 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (50753081409 / 1000000000000) (50753081410 / 1000000000000), orderedInterval (28088035640 / 1000000000000) (28088035641 / 1000000000000)))) (orderedInterval (-7049028713 / 1000000000000) (-7049028691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (319284121214037 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-78617656128 / 1000000000000) (-78617644143 / 1000000000000), orderedInterval (42857144750 / 1000000000000) (42857156736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1297872226610677 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-44081379288 / 1000000000000) (-44081378696 / 1000000000000), orderedInterval (4412025170 / 1000000000000) (4412025762 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (866918498702843 / 4000000000000) 0 (IntervalRat.scale (349 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36726656964 / 1000000000000) (-36726656963 / 1000000000000), orderedInterval (-39771824982 / 1000000000000) (-39771824981 / 1000000000000)))) (orderedInterval (10005264611 / 1000000000000) (10005264780 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_chunkChecks0 :
    compactCertificate301.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate301.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate301_chunkChecks0_0
    compactCertificate301_chunkChecks0_1 compactCertificate301_chunkChecks0_2

theorem compactCertificate301_chunkChecks1_0 :
    compactCertificate301.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (349 / 2) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36288958826 / 1000000000000) (-36288944401 / 1000000000000), orderedInterval (48388202596 / 1000000000000) (48388217021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (514143640817449 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-34665033238 / 1000000000000) (-34665033237 / 1000000000000), orderedInterval (-61112279709 / 1000000000000) (-61112279708 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (166263489692617 / 800000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52845274932 / 1000000000000) (52845274933 / 1000000000000), orderedInterval (16321407315 / 1000000000000) (16321407317 / 1000000000000)))) (orderedInterval (19900626798 / 1000000000000) (19900632530 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (150025832098043 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72417470572 / 1000000000000) (72417470573 / 1000000000000), orderedInterval (107339386458 / 1000000000000) (107339386459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (402990487894271 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (66924644700 / 1000000000000) (66924644701 / 1000000000000), orderedInterval (42563267154 / 1000000000000) (42563267155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1094197567447107 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40999955205 / 1000000000000) (-40999955204 / 1000000000000), orderedInterval (-25346685676 / 1000000000000) (-25346685675 / 1000000000000)))) (orderedInterval (3471601267 / 1000000000000) (3471601292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (805980975788891 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52749021102 / 1000000000000) (52749021103 / 1000000000000), orderedInterval (19285885102 / 1000000000000) (19285885103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1381062139519943 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19652641663 / 1000000000000) (19652641664 / 1000000000000), orderedInterval (38150465319 / 1000000000000) (38150465320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1017284121214037 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29755666582 / 1000000000000) (-29755666581 / 1000000000000), orderedInterval (-40163570701 / 1000000000000) (-40163570700 / 1000000000000)))) (orderedInterval (-3742930199 / 1000000000000) (-3742930181 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_chunkChecks1_1 :
    compactCertificate301.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1560775448294651 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (39942779800 / 1000000000000) (39942779832 / 1000000000000), orderedInterval (5958844921 / 1000000000000) (5958844953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (901114125217379 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6959597436 / 1000000000000) (-6959597417 / 1000000000000), orderedInterval (52717378957 / 1000000000000) (52717378976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1599042828240511 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-39905096116 / 1000000000000) (-39905095866 / 1000000000000), orderedInterval (-240236099 / 1000000000000) (-240235848 / 1000000000000)))) (orderedInterval (2596708009 / 1000000000000) (2596708249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1494033232522459 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17728329014 / 1000000000000) (-17728329013 / 1000000000000), orderedInterval (-37260849262 / 1000000000000) (-37260849261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1066212611692747 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14568564689 / 1000000000000) (-14568564688 / 1000000000000), orderedInterval (-46621372118 / 1000000000000) (-46621372117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1208971463682813 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (45471827333 / 1000000000000) (45471827352 / 1000000000000), orderedInterval (6139979251 / 1000000000000) (6139979270 / 1000000000000)))) (orderedInterval (-5348320220 / 1000000000000) (-5348320185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1007914364807597 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (49808676169 / 1000000000000) (49808676183 / 1000000000000), orderedInterval (6652058520 / 1000000000000) (6652058534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (890522908283537 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18962024406 / 1000000000000) (-18962024405 / 1000000000000), orderedInterval (-49957208007 / 1000000000000) (-49957208006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (258108248618163 / 800000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7240165107 / 1000000000000) (7240165122 / 1000000000000), orderedInterval (-43837800900 / 1000000000000) (-43837800885 / 1000000000000)))) (orderedInterval (1683088670 / 1000000000000) (1683088695 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_chunkChecks1_2 :
    compactCertificate301.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (713940999170761 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11816232988 / 1000000000000) (-11816232986 / 1000000000000), orderedInterval (-58509034088 / 1000000000000) (-58509034087 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (605215691677121 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (62361724254 / 1000000000000) (62361724255 / 1000000000000), orderedInterval (17641950356 / 1000000000000) (17641950357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (378715878785963 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (76871311319 / 1000000000000) (76871311320 / 1000000000000), orderedInterval (28137237737 / 1000000000000) (28137237738 / 1000000000000)))) (orderedInterval (9200011690 / 1000000000000) (9200011731 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (203674659163221 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (110800299863 / 1000000000000) (110800299866 / 1000000000000), orderedInterval (13925182737 / 1000000000000) (13925182741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (553016319992663 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49078157789 / 1000000000000) (49078157790 / 1000000000000), orderedInterval (46684453653 / 1000000000000) (46684453654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (755096506130551 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (50753081409 / 1000000000000) (50753081410 / 1000000000000), orderedInterval (28088035640 / 1000000000000) (28088035641 / 1000000000000)))) (orderedInterval (-3242881123 / 1000000000000) (-3242881104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (319284121214037 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-78617656128 / 1000000000000) (-78617644143 / 1000000000000), orderedInterval (42857144750 / 1000000000000) (42857156736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1297872226610677 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-44081379288 / 1000000000000) (-44081378696 / 1000000000000), orderedInterval (4412025170 / 1000000000000) (4412025762 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (866918498702843 / 4000000000000) 1 (IntervalRat.scale (349 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36726656964 / 1000000000000) (-36726656963 / 1000000000000), orderedInterval (-39771824982 / 1000000000000) (-39771824981 / 1000000000000)))) (orderedInterval (8718516771 / 1000000000000) (8718516962 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_chunkChecks1 :
    compactCertificate301.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate301.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate301_chunkChecks1_0
    compactCertificate301_chunkChecks1_1 compactCertificate301_chunkChecks1_2

theorem compactCertificate301_chunkChecks2_0 :
    compactCertificate301.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (349 / 2) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36288958826 / 1000000000000) (-36288944401 / 1000000000000), orderedInterval (48388202596 / 1000000000000) (48388217021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (514143640817449 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-34665033238 / 1000000000000) (-34665033237 / 1000000000000), orderedInterval (-61112279709 / 1000000000000) (-61112279708 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (166263489692617 / 800000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52845274932 / 1000000000000) (52845274933 / 1000000000000), orderedInterval (16321407315 / 1000000000000) (16321407317 / 1000000000000)))) (orderedInterval (10046146883 / 1000000000000) (10046152650 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (150025832098043 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72417470572 / 1000000000000) (72417470573 / 1000000000000), orderedInterval (107339386458 / 1000000000000) (107339386459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (402990487894271 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (66924644700 / 1000000000000) (66924644701 / 1000000000000), orderedInterval (42563267154 / 1000000000000) (42563267155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1094197567447107 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40999955205 / 1000000000000) (-40999955204 / 1000000000000), orderedInterval (-25346685676 / 1000000000000) (-25346685675 / 1000000000000)))) (orderedInterval (-7960704076 / 1000000000000) (-7960704042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (805980975788891 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52749021102 / 1000000000000) (52749021103 / 1000000000000), orderedInterval (19285885102 / 1000000000000) (19285885103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1381062139519943 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19652641663 / 1000000000000) (19652641664 / 1000000000000), orderedInterval (38150465319 / 1000000000000) (38150465320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1017284121214037 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29755666582 / 1000000000000) (-29755666581 / 1000000000000), orderedInterval (-40163570701 / 1000000000000) (-40163570700 / 1000000000000)))) (orderedInterval (3922013126 / 1000000000000) (3922013157 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_chunkChecks2_1 :
    compactCertificate301.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1560775448294651 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (39942779800 / 1000000000000) (39942779832 / 1000000000000), orderedInterval (5958844921 / 1000000000000) (5958844953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (901114125217379 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6959597436 / 1000000000000) (-6959597417 / 1000000000000), orderedInterval (52717378957 / 1000000000000) (52717378976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1599042828240511 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-39905096116 / 1000000000000) (-39905095866 / 1000000000000), orderedInterval (-240236099 / 1000000000000) (-240235848 / 1000000000000)))) (orderedInterval (66102909377 / 1000000000000) (66102909903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1494033232522459 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17728329014 / 1000000000000) (-17728329013 / 1000000000000), orderedInterval (-37260849262 / 1000000000000) (-37260849261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1066212611692747 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14568564689 / 1000000000000) (-14568564688 / 1000000000000), orderedInterval (-46621372118 / 1000000000000) (-46621372117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1208971463682813 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (45471827333 / 1000000000000) (45471827352 / 1000000000000), orderedInterval (6139979251 / 1000000000000) (6139979270 / 1000000000000)))) (orderedInterval (2469175262 / 1000000000000) (2469175319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1007914364807597 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (49808676169 / 1000000000000) (49808676183 / 1000000000000), orderedInterval (6652058520 / 1000000000000) (6652058534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (890522908283537 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18962024406 / 1000000000000) (-18962024405 / 1000000000000), orderedInterval (-49957208007 / 1000000000000) (-49957208006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (258108248618163 / 800000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7240165107 / 1000000000000) (7240165122 / 1000000000000), orderedInterval (-43837800900 / 1000000000000) (-43837800885 / 1000000000000)))) (orderedInterval (-3608966302 / 1000000000000) (-3608966263 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_chunkChecks2_2 :
    compactCertificate301.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (713940999170761 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11816232988 / 1000000000000) (-11816232986 / 1000000000000), orderedInterval (-58509034088 / 1000000000000) (-58509034087 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (605215691677121 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (62361724254 / 1000000000000) (62361724255 / 1000000000000), orderedInterval (17641950356 / 1000000000000) (17641950357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (378715878785963 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (76871311319 / 1000000000000) (76871311320 / 1000000000000), orderedInterval (28137237737 / 1000000000000) (28137237738 / 1000000000000)))) (orderedInterval (-112399576 / 1000000000000) (-112399536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (203674659163221 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (110800299863 / 1000000000000) (110800299866 / 1000000000000), orderedInterval (13925182737 / 1000000000000) (13925182741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (553016319992663 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49078157789 / 1000000000000) (49078157790 / 1000000000000), orderedInterval (46684453653 / 1000000000000) (46684453654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (755096506130551 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (50753081409 / 1000000000000) (50753081410 / 1000000000000), orderedInterval (28088035640 / 1000000000000) (28088035641 / 1000000000000)))) (orderedInterval (5443742380 / 1000000000000) (5443742399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (319284121214037 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-78617656128 / 1000000000000) (-78617644143 / 1000000000000), orderedInterval (42857144750 / 1000000000000) (42857156736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1297872226610677 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-44081379288 / 1000000000000) (-44081378696 / 1000000000000), orderedInterval (4412025170 / 1000000000000) (4412025762 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (866918498702843 / 4000000000000) 2 (IntervalRat.scale (349 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36726656964 / 1000000000000) (-36726656963 / 1000000000000), orderedInterval (-39771824982 / 1000000000000) (-39771824981 / 1000000000000)))) (orderedInterval (-22986800057 / 1000000000000) (-22986799773 / 1000000000000))) = true
  rfl'

theorem compactCertificate301_chunkChecks2 :
    compactCertificate301.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate301.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate301_chunkChecks2_0
    compactCertificate301_chunkChecks2_1 compactCertificate301_chunkChecks2_2

theorem compactCertificate301_chunkChecks3_0 :
    compactCertificate301.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (349 / 2) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36288958826 / 1000000000000) (-36288944401 / 1000000000000), orderedInterval (48388202596 / 1000000000000) (48388217021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (514143640817449 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-34665033238 / 1000000000000) (-34665033237 / 1000000000000), orderedInterval (-61112279709 / 1000000000000) (-61112279708 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (166263489692617 / 800000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52845274932 / 1000000000000) (52845274933 / 1000000000000), orderedInterval (16321407315 / 1000000000000) (16321407317 / 1000000000000)))) (orderedInterval (-20626774042 / 1000000000000) (-20626768273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (150025832098043 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72417470572 / 1000000000000) (72417470573 / 1000000000000), orderedInterval (107339386458 / 1000000000000) (107339386459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (402990487894271 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (66924644700 / 1000000000000) (66924644701 / 1000000000000), orderedInterval (42563267154 / 1000000000000) (42563267155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1094197567447107 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40999955205 / 1000000000000) (-40999955204 / 1000000000000), orderedInterval (-25346685676 / 1000000000000) (-25346685675 / 1000000000000)))) (orderedInterval (-7183203496 / 1000000000000) (-7183203446 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (805980975788891 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52749021102 / 1000000000000) (52749021103 / 1000000000000), orderedInterval (19285885102 / 1000000000000) (19285885103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1381062139519943 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19652641663 / 1000000000000) (19652641664 / 1000000000000), orderedInterval (38150465319 / 1000000000000) (38150465320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1017284121214037 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29755666582 / 1000000000000) (-29755666581 / 1000000000000), orderedInterval (-40163570701 / 1000000000000) (-40163570700 / 1000000000000)))) (orderedInterval (12097061885 / 1000000000000) (12097061941 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate301_chunkChecks3_1 :
    compactCertificate301.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1560775448294651 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (39942779800 / 1000000000000) (39942779832 / 1000000000000), orderedInterval (5958844921 / 1000000000000) (5958844953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (901114125217379 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6959597436 / 1000000000000) (-6959597417 / 1000000000000), orderedInterval (52717378957 / 1000000000000) (52717378976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1599042828240511 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-39905096116 / 1000000000000) (-39905095866 / 1000000000000), orderedInterval (-240236099 / 1000000000000) (-240235848 / 1000000000000)))) (orderedInterval (3465568597 / 1000000000000) (3465569768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1494033232522459 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17728329014 / 1000000000000) (-17728329013 / 1000000000000), orderedInterval (-37260849262 / 1000000000000) (-37260849261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1066212611692747 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14568564689 / 1000000000000) (-14568564688 / 1000000000000), orderedInterval (-46621372118 / 1000000000000) (-46621372117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1208971463682813 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (45471827333 / 1000000000000) (45471827352 / 1000000000000), orderedInterval (6139979251 / 1000000000000) (6139979270 / 1000000000000)))) (orderedInterval (9263975165 / 1000000000000) (9263975261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1007914364807597 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (49808676169 / 1000000000000) (49808676183 / 1000000000000), orderedInterval (6652058520 / 1000000000000) (6652058534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (890522908283537 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18962024406 / 1000000000000) (-18962024405 / 1000000000000), orderedInterval (-49957208007 / 1000000000000) (-49957208006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (258108248618163 / 800000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7240165107 / 1000000000000) (7240165122 / 1000000000000), orderedInterval (-43837800900 / 1000000000000) (-43837800885 / 1000000000000)))) (orderedInterval (946694056 / 1000000000000) (946694115 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate301_chunkChecks3_2 :
    compactCertificate301.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (713940999170761 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11816232988 / 1000000000000) (-11816232986 / 1000000000000), orderedInterval (-58509034088 / 1000000000000) (-58509034087 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (605215691677121 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (62361724254 / 1000000000000) (62361724255 / 1000000000000), orderedInterval (17641950356 / 1000000000000) (17641950357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (378715878785963 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (76871311319 / 1000000000000) (76871311320 / 1000000000000), orderedInterval (28137237737 / 1000000000000) (28137237738 / 1000000000000)))) (orderedInterval (-9505309834 / 1000000000000) (-9505309796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (203674659163221 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (110800299863 / 1000000000000) (110800299866 / 1000000000000), orderedInterval (13925182737 / 1000000000000) (13925182741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (553016319992663 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49078157789 / 1000000000000) (49078157790 / 1000000000000), orderedInterval (46684453653 / 1000000000000) (46684453654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (755096506130551 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (50753081409 / 1000000000000) (50753081410 / 1000000000000), orderedInterval (28088035640 / 1000000000000) (28088035641 / 1000000000000)))) (orderedInterval (3227106097 / 1000000000000) (3227106117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (319284121214037 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-78617656128 / 1000000000000) (-78617644143 / 1000000000000), orderedInterval (42857144750 / 1000000000000) (42857156736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1297872226610677 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-44081379288 / 1000000000000) (-44081378696 / 1000000000000), orderedInterval (4412025170 / 1000000000000) (4412025762 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (866918498702843 / 4000000000000) 3 (IntervalRat.scale (349 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36726656964 / 1000000000000) (-36726656963 / 1000000000000), orderedInterval (-39771824982 / 1000000000000) (-39771824981 / 1000000000000)))) (orderedInterval (-11880614018 / 1000000000000) (-11880613545 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate301_chunkChecks3 :
    compactCertificate301.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate301.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate301_chunkChecks3_0
    compactCertificate301_chunkChecks3_1 compactCertificate301_chunkChecks3_2

theorem compactCertificate301_chunkChecks4_0 :
    compactCertificate301.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (349 / 2) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36288958826 / 1000000000000) (-36288944401 / 1000000000000), orderedInterval (48388202596 / 1000000000000) (48388217021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (514143640817449 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-34665033238 / 1000000000000) (-34665033237 / 1000000000000), orderedInterval (-61112279709 / 1000000000000) (-61112279708 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (166263489692617 / 800000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (52845274932 / 1000000000000) (52845274933 / 1000000000000), orderedInterval (16321407315 / 1000000000000) (16321407317 / 1000000000000)))) (orderedInterval (-8002514844 / 1000000000000) (-8002509040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (150025832098043 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72417470572 / 1000000000000) (72417470573 / 1000000000000), orderedInterval (107339386458 / 1000000000000) (107339386459 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (402990487894271 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (66924644700 / 1000000000000) (66924644701 / 1000000000000), orderedInterval (42563267154 / 1000000000000) (42563267155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1094197567447107 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40999955205 / 1000000000000) (-40999955204 / 1000000000000), orderedInterval (-25346685676 / 1000000000000) (-25346685675 / 1000000000000)))) (orderedInterval (17953447189 / 1000000000000) (17953447266 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (805980975788891 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (52749021102 / 1000000000000) (52749021103 / 1000000000000), orderedInterval (19285885102 / 1000000000000) (19285885103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1381062139519943 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19652641663 / 1000000000000) (19652641664 / 1000000000000), orderedInterval (38150465319 / 1000000000000) (38150465320 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1017284121214037 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29755666582 / 1000000000000) (-29755666581 / 1000000000000), orderedInterval (-40163570701 / 1000000000000) (-40163570700 / 1000000000000)))) (orderedInterval (-12673249343 / 1000000000000) (-12673249240 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate301_chunkChecks4_1 :
    compactCertificate301.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1560775448294651 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (39942779800 / 1000000000000) (39942779832 / 1000000000000), orderedInterval (5958844921 / 1000000000000) (5958844953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (901114125217379 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-6959597436 / 1000000000000) (-6959597417 / 1000000000000), orderedInterval (52717378957 / 1000000000000) (52717378976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1599042828240511 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-39905096116 / 1000000000000) (-39905095866 / 1000000000000), orderedInterval (-240236099 / 1000000000000) (-240235848 / 1000000000000)))) (orderedInterval (-335150734446 / 1000000000000) (-335150731819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1494033232522459 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17728329014 / 1000000000000) (-17728329013 / 1000000000000), orderedInterval (-37260849262 / 1000000000000) (-37260849261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1066212611692747 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14568564689 / 1000000000000) (-14568564688 / 1000000000000), orderedInterval (-46621372118 / 1000000000000) (-46621372117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1208971463682813 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (45471827333 / 1000000000000) (45471827352 / 1000000000000), orderedInterval (6139979251 / 1000000000000) (6139979270 / 1000000000000)))) (orderedInterval (-2959652748 / 1000000000000) (-2959652581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1007914364807597 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (49808676169 / 1000000000000) (49808676183 / 1000000000000), orderedInterval (6652058520 / 1000000000000) (6652058534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (890522908283537 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-18962024406 / 1000000000000) (-18962024405 / 1000000000000), orderedInterval (-49957208007 / 1000000000000) (-49957208006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (258108248618163 / 800000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (7240165107 / 1000000000000) (7240165122 / 1000000000000), orderedInterval (-43837800900 / 1000000000000) (-43837800885 / 1000000000000)))) (orderedInterval (7531132352 / 1000000000000) (7531132446 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate301_chunkChecks4_2 :
    compactCertificate301.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (713940999170761 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11816232988 / 1000000000000) (-11816232986 / 1000000000000), orderedInterval (-58509034088 / 1000000000000) (-58509034087 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (605215691677121 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (62361724254 / 1000000000000) (62361724255 / 1000000000000), orderedInterval (17641950356 / 1000000000000) (17641950357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (378715878785963 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (76871311319 / 1000000000000) (76871311320 / 1000000000000), orderedInterval (28137237737 / 1000000000000) (28137237738 / 1000000000000)))) (orderedInterval (398693728 / 1000000000000) (398693766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (203674659163221 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (110800299863 / 1000000000000) (110800299866 / 1000000000000), orderedInterval (13925182737 / 1000000000000) (13925182741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (553016319992663 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (49078157789 / 1000000000000) (49078157790 / 1000000000000), orderedInterval (46684453653 / 1000000000000) (46684453654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (755096506130551 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (50753081409 / 1000000000000) (50753081410 / 1000000000000), orderedInterval (28088035640 / 1000000000000) (28088035641 / 1000000000000)))) (orderedInterval (-5817573664 / 1000000000000) (-5817573643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (319284121214037 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-78617656128 / 1000000000000) (-78617644143 / 1000000000000), orderedInterval (42857144750 / 1000000000000) (42857156736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1297872226610677 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-44081379288 / 1000000000000) (-44081378696 / 1000000000000), orderedInterval (4412025170 / 1000000000000) (4412025762 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (866918498702843 / 4000000000000) 4 (IntervalRat.scale (349 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36726656964 / 1000000000000) (-36726656963 / 1000000000000), orderedInterval (-39771824982 / 1000000000000) (-39771824981 / 1000000000000)))) (orderedInterval (59405619889 / 1000000000000) (59405620722 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate301_chunkChecks4 :
    compactCertificate301.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate301.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate301_chunkChecks4_0
    compactCertificate301_chunkChecks4_1 compactCertificate301_chunkChecks4_2

theorem compactCertificate301_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate301.chunkCheck r b = true :=
  compactCertificate301.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate301_chunkChecks0
    · exact compactCertificate301_chunkChecks1
    · exact compactCertificate301_chunkChecks2
    · exact compactCertificate301_chunkChecks3
    · exact compactCertificate301_chunkChecks4)

theorem compactCertificate301_coefficient0 :
    compactCertificate301.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate301_coefficient1 :
    compactCertificate301.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate301_coefficient2 :
    compactCertificate301.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate301_coefficient3 :
    compactCertificate301.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate301_coefficient4 :
    compactCertificate301.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate301_coefficients : ∀ r : Fin 5,
    compactCertificate301.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate301_coefficient0
  · exact compactCertificate301_coefficient1
  · exact compactCertificate301_coefficient2
  · exact compactCertificate301_coefficient3
  · exact compactCertificate301_coefficient4

theorem compactCertificate301_lower : (1 : ℚ) ≤ compactCertificate301.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate301, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate301_proves {t : ℝ} (ht : t ∈ compactCertificate301.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate301.proves compactCertificate301_states compactCertificate301_chunks
    compactCertificate301_coefficients compactCertificate301_lower ht

end Erdos232
