/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate367 : CompactCertificate where
  left := 238
  right := 239
  center := 477 / 2
  grid := fun i =>
    match i.val with
    | 0 => 76
    | 1 => 56
    | 2 => 90
    | 3 => 16
    | 4 => 44
    | 5 => 119
    | 6 => 88
    | 7 => 150
    | 8 => 111
    | 9 => 170
    | 10 => 98
    | 11 => 174
    | 12 => 163
    | 13 => 116
    | 14 => 132
    | 15 => 110
    | 16 => 97
    | 17 => 140
    | 18 => 78
    | 19 => 66
    | 20 => 41
    | 21 => 22
    | 22 => 60
    | 23 => 82
    | 24 => 35
    | 25 => 141
    | _ => 94
  point := fun i =>
    match i.val with
    | 0 => 477 / 2
    | 1 => 702712082148777 / 4000000000000
    | 2 => 227242649236041 / 800000000000
    | 3 => 205049632982139 / 4000000000000
    | 4 => 550792156806783 / 4000000000000
    | 5 => 1495507850063811 / 4000000000000
    | 6 => 1101584313614043 / 4000000000000
    | 7 => 1887583497280839 / 4000000000000
    | 8 => 1390385460799701 / 4000000000000
    | 9 => 2133208850534523 / 4000000000000
    | 10 => 1231608704093667 / 4000000000000
    | 11 => 2185511258082303 / 4000000000000
    | 12 => 2041988114364507 / 4000000000000
    | 13 => 1457259070995531 / 4000000000000
    | 14 => 1652376470420349 / 4000000000000
    | 15 => 1377579232129581 / 4000000000000
    | 16 => 1217133029373201 / 4000000000000
    | 17 => 352772591950899 / 800000000000
    | 18 => 975787554740553 / 4000000000000
    | 19 => 827185916704833 / 4000000000000
    | 20 => 517614539200299 / 4000000000000
    | 21 => 278374820690133 / 4000000000000
    | 22 => 755841789789399 / 4000000000000
    | 23 => 1032037345055223 / 4000000000000
    | 24 => 436385460799701 / 4000000000000
    | 25 => 1773882670754421 / 4000000000000
    | _ => 1184871415132539 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (25842889837 / 1000000000000) (25842889838 / 1000000000000), orderedInterval (44682979850 / 1000000000000) (44682979851 / 1000000000000))
    | 1 => (orderedInterval (30614547438 / 1000000000000) (30614547439 / 1000000000000), orderedInterval (51744748577 / 1000000000000) (51744748578 / 1000000000000))
    | 2 => (orderedInterval (40986023992 / 1000000000000) (40986065433 / 1000000000000), orderedInterval (-23764791395 / 1000000000000) (-23764749955 / 1000000000000))
    | 3 => (orderedInterval (109010139571 / 1000000000000) (109010140001 / 1000000000000), orderedInterval (-24195219648 / 1000000000000) (-24195219219 / 1000000000000))
    | 4 => (orderedInterval (16983690999 / 1000000000000) (16983691000 / 1000000000000), orderedInterval (65778166879 / 1000000000000) (65778166880 / 1000000000000))
    | 5 => (orderedInterval (-29958326301 / 1000000000000) (-29958326300 / 1000000000000), orderedInterval (-28336874780 / 1000000000000) (-28336874779 / 1000000000000))
    | 6 => (orderedInterval (-13246902003 / 1000000000000) (-13246901887 / 1000000000000), orderedInterval (46242816961 / 1000000000000) (46242817077 / 1000000000000))
    | 7 => (orderedInterval (36425947685 / 1000000000000) (36425947763 / 1000000000000), orderedInterval (4674993096 / 1000000000000) (4674993174 / 1000000000000))
    | 8 => (orderedInterval (14085363944 / 1000000000000) (14085364096 / 1000000000000), orderedInterval (-40431836927 / 1000000000000) (-40431836774 / 1000000000000))
    | 9 => (orderedInterval (574384508 / 1000000000000) (574384510 / 1000000000000), orderedInterval (34545117300 / 1000000000000) (34545117301 / 1000000000000))
    | 10 => (orderedInterval (32968074717 / 1000000000000) (32968074718 / 1000000000000), orderedInterval (31262751864 / 1000000000000) (31262751865 / 1000000000000))
    | 11 => (orderedInterval (17134111428 / 1000000000000) (17134111429 / 1000000000000), orderedInterval (29506963974 / 1000000000000) (29506963975 / 1000000000000))
    | 12 => (orderedInterval (25268953790 / 1000000000000) (25268966006 / 1000000000000), orderedInterval (-24693325733 / 1000000000000) (-24693313516 / 1000000000000))
    | 13 => (orderedInterval (26124669941 / 1000000000000) (26124669942 / 1000000000000), orderedInterval (32597660559 / 1000000000000) (32597660560 / 1000000000000))
    | 14 => (orderedInterval (-28460756027 / 1000000000000) (-28460733680 / 1000000000000), orderedInterval (27073056580 / 1000000000000) (27073078926 / 1000000000000))
    | 15 => (orderedInterval (-16558418549 / 1000000000000) (-16558418204 / 1000000000000), orderedInterval (39701961532 / 1000000000000) (39701961877 / 1000000000000))
    | 16 => (orderedInterval (-14984367330 / 1000000000000) (-14984367329 / 1000000000000), orderedInterval (-43191873397 / 1000000000000) (-43191873396 / 1000000000000))
    | 17 => (orderedInterval (35599137124 / 1000000000000) (35599155598 / 1000000000000), orderedInterval (-13321731727 / 1000000000000) (-13321713253 / 1000000000000))
    | 18 => (orderedInterval (-15703137373 / 1000000000000) (-15703137147 / 1000000000000), orderedInterval (48643720956 / 1000000000000) (48643721182 / 1000000000000))
    | 19 => (orderedInterval (12981525402 / 1000000000000) (12981525403 / 1000000000000), orderedInterval (53912774772 / 1000000000000) (53912774773 / 1000000000000))
    | 20 => (orderedInterval (-68903675403 / 1000000000000) (-68903675401 / 1000000000000), orderedInterval (-12844566658 / 1000000000000) (-12844566655 / 1000000000000))
    | 21 => (orderedInterval (91126130365 / 1000000000000) (91126130366 / 1000000000000), orderedInterval (28388387589 / 1000000000000) (28388387590 / 1000000000000))
    | 22 => (orderedInterval (55075551771 / 1000000000000) (55075551773 / 1000000000000), orderedInterval (18177417049 / 1000000000000) (18177417050 / 1000000000000))
    | 23 => (orderedInterval (45996921193 / 1000000000000) (45996921194 / 1000000000000), orderedInterval (18664772151 / 1000000000000) (18664772152 / 1000000000000))
    | 24 => (orderedInterval (5733369254 / 1000000000000) (5733369273 / 1000000000000), orderedInterval (-76200933668 / 1000000000000) (-76200933648 / 1000000000000))
    | 25 => (orderedInterval (-36417385245 / 1000000000000) (-36417385239 / 1000000000000), orderedInterval (-10414227752 / 1000000000000) (-10414227746 / 1000000000000))
    | _ => (orderedInterval (46012600406 / 1000000000000) (46012601074 / 1000000000000), orderedInterval (-5734371773 / 1000000000000) (-5734371105 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (12933591643 / 1000000000000) (12933594092 / 1000000000000)
      | 1 => orderedInterval (1567148128 / 1000000000000) (1567148162 / 1000000000000)
      | 2 => orderedInterval (-783106520 / 1000000000000) (-783106500 / 1000000000000)
      | 3 => orderedInterval (4776316696 / 1000000000000) (4776316792 / 1000000000000)
      | 4 => orderedInterval (2158268538 / 1000000000000) (2158268901 / 1000000000000)
      | 5 => orderedInterval (1577772911 / 1000000000000) (1577773412 / 1000000000000)
      | 6 => orderedInterval (-467118677 / 1000000000000) (-467118580 / 1000000000000)
      | 7 => orderedInterval (-6457298180 / 1000000000000) (-6457298151 / 1000000000000)
      | _ => orderedInterval (-5634182068 / 1000000000000) (-5634181876 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16405024301 / 1000000000000) (16405027217 / 1000000000000)
      | 1 => orderedInterval (4600930815 / 1000000000000) (4600930849 / 1000000000000)
      | 2 => orderedInterval (-1709441239 / 1000000000000) (-1709441205 / 1000000000000)
      | 3 => orderedInterval (-1125846973 / 1000000000000) (-1125846776 / 1000000000000)
      | 4 => orderedInterval (5425531071 / 1000000000000) (5425531786 / 1000000000000)
      | 5 => orderedInterval (3184862606 / 1000000000000) (3184863520 / 1000000000000)
      | 6 => orderedInterval (-10828107825 / 1000000000000) (-10828107732 / 1000000000000)
      | 7 => orderedInterval (-2027146695 / 1000000000000) (-2027146668 / 1000000000000)
      | _ => orderedInterval (2702465874 / 1000000000000) (2702466124 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13878376783 / 1000000000000) (-13878373299 / 1000000000000)
      | 1 => orderedInterval (-5405003238 / 1000000000000) (-5405003192 / 1000000000000)
      | 2 => orderedInterval (3682517797 / 1000000000000) (3682517856 / 1000000000000)
      | 3 => orderedInterval (-16339167367 / 1000000000000) (-16339166944 / 1000000000000)
      | 4 => orderedInterval (-4129143847 / 1000000000000) (-4129142418 / 1000000000000)
      | 5 => orderedInterval (-4126300354 / 1000000000000) (-4126298675 / 1000000000000)
      | 6 => orderedInterval (-1368650455 / 1000000000000) (-1368650363 / 1000000000000)
      | 7 => orderedInterval (5061555359 / 1000000000000) (5061555385 / 1000000000000)
      | _ => orderedInterval (3049418440 / 1000000000000) (3049418774 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15489038350 / 1000000000000) (-15489034201 / 1000000000000)
      | 1 => orderedInterval (-8202378916 / 1000000000000) (-8202378847 / 1000000000000)
      | 2 => orderedInterval (4126456052 / 1000000000000) (4126456158 / 1000000000000)
      | 3 => orderedInterval (13280623431 / 1000000000000) (13280624355 / 1000000000000)
      | 4 => orderedInterval (-14629168852 / 1000000000000) (-14629165966 / 1000000000000)
      | 5 => orderedInterval (-4340202726 / 1000000000000) (-4340199641 / 1000000000000)
      | 6 => orderedInterval (10384423751 / 1000000000000) (10384423842 / 1000000000000)
      | 7 => orderedInterval (2007837120 / 1000000000000) (2007837147 / 1000000000000)
      | _ => orderedInterval (-7480031815 / 1000000000000) (-7480031359 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15296111640 / 1000000000000) (15296116597 / 1000000000000)
      | 1 => orderedInterval (12996372525 / 1000000000000) (12996372630 / 1000000000000)
      | 2 => orderedInterval (-15717852429 / 1000000000000) (-15717852236 / 1000000000000)
      | 3 => orderedInterval (71210035518 / 1000000000000) (71210037575 / 1000000000000)
      | 4 => orderedInterval (5293507584 / 1000000000000) (5293513479 / 1000000000000)
      | 5 => orderedInterval (12128439999 / 1000000000000) (12128445690 / 1000000000000)
      | 6 => orderedInterval (2051356364 / 1000000000000) (2051356454 / 1000000000000)
      | 7 => orderedInterval (-5349271112 / 1000000000000) (-5349271084 / 1000000000000)
      | _ => orderedInterval (14957688605 / 1000000000000) (14957689251 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (9671392471 / 1000000000000) (9671396252 / 1000000000000)
    | 1 => orderedInterval (16628271935 / 1000000000000) (16628277115 / 1000000000000)
    | 2 => orderedInterval (-33453150448 / 1000000000000) (-33453142876 / 1000000000000)
    | 3 => orderedInterval (-20341480305 / 1000000000000) (-20341468512 / 1000000000000)
    | _ => orderedInterval (112866388694 / 1000000000000) (112866408356 / 1000000000000)

theorem compactCertificate367_stateChecks0 :
    compactCertificate367.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (477 / 2)) (orderedInterval (25842889837 / 1000000000000) (25842889838 / 1000000000000), orderedInterval (44682979850 / 1000000000000) (44682979851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (702712082148777 / 4000000000000)) (orderedInterval (30614547438 / 1000000000000) (30614547439 / 1000000000000), orderedInterval (51744748577 / 1000000000000) (51744748578 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (227242649236041 / 800000000000)) (orderedInterval (40986023992 / 1000000000000) (40986065433 / 1000000000000), orderedInterval (-23764791395 / 1000000000000) (-23764749955 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_stateChecks1 :
    compactCertificate367.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (205049632982139 / 4000000000000)) (orderedInterval (109010139571 / 1000000000000) (109010140001 / 1000000000000), orderedInterval (-24195219648 / 1000000000000) (-24195219219 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (550792156806783 / 4000000000000)) (orderedInterval (16983690999 / 1000000000000) (16983691000 / 1000000000000), orderedInterval (65778166879 / 1000000000000) (65778166880 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1495507850063811 / 4000000000000)) (orderedInterval (-29958326301 / 1000000000000) (-29958326300 / 1000000000000), orderedInterval (-28336874780 / 1000000000000) (-28336874779 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_stateChecks2 :
    compactCertificate367.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1101584313614043 / 4000000000000)) (orderedInterval (-13246902003 / 1000000000000) (-13246901887 / 1000000000000), orderedInterval (46242816961 / 1000000000000) (46242817077 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1887583497280839 / 4000000000000)) (orderedInterval (36425947685 / 1000000000000) (36425947763 / 1000000000000), orderedInterval (4674993096 / 1000000000000) (4674993174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1390385460799701 / 4000000000000)) (orderedInterval (14085363944 / 1000000000000) (14085364096 / 1000000000000), orderedInterval (-40431836927 / 1000000000000) (-40431836774 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_stateChecks3 :
    compactCertificate367.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2133208850534523 / 4000000000000)) (orderedInterval (574384508 / 1000000000000) (574384510 / 1000000000000), orderedInterval (34545117300 / 1000000000000) (34545117301 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1231608704093667 / 4000000000000)) (orderedInterval (32968074717 / 1000000000000) (32968074718 / 1000000000000), orderedInterval (31262751864 / 1000000000000) (31262751865 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2185511258082303 / 4000000000000)) (orderedInterval (17134111428 / 1000000000000) (17134111429 / 1000000000000), orderedInterval (29506963974 / 1000000000000) (29506963975 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_stateChecks4 :
    compactCertificate367.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2041988114364507 / 4000000000000)) (orderedInterval (25268953790 / 1000000000000) (25268966006 / 1000000000000), orderedInterval (-24693325733 / 1000000000000) (-24693313516 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1457259070995531 / 4000000000000)) (orderedInterval (26124669941 / 1000000000000) (26124669942 / 1000000000000), orderedInterval (32597660559 / 1000000000000) (32597660560 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1652376470420349 / 4000000000000)) (orderedInterval (-28460756027 / 1000000000000) (-28460733680 / 1000000000000), orderedInterval (27073056580 / 1000000000000) (27073078926 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_stateChecks5 :
    compactCertificate367.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1377579232129581 / 4000000000000)) (orderedInterval (-16558418549 / 1000000000000) (-16558418204 / 1000000000000), orderedInterval (39701961532 / 1000000000000) (39701961877 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1217133029373201 / 4000000000000)) (orderedInterval (-14984367330 / 1000000000000) (-14984367329 / 1000000000000), orderedInterval (-43191873397 / 1000000000000) (-43191873396 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (352772591950899 / 800000000000)) (orderedInterval (35599137124 / 1000000000000) (35599155598 / 1000000000000), orderedInterval (-13321731727 / 1000000000000) (-13321713253 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_stateChecks6 :
    compactCertificate367.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (975787554740553 / 4000000000000)) (orderedInterval (-15703137373 / 1000000000000) (-15703137147 / 1000000000000), orderedInterval (48643720956 / 1000000000000) (48643721182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (827185916704833 / 4000000000000)) (orderedInterval (12981525402 / 1000000000000) (12981525403 / 1000000000000), orderedInterval (53912774772 / 1000000000000) (53912774773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (517614539200299 / 4000000000000)) (orderedInterval (-68903675403 / 1000000000000) (-68903675401 / 1000000000000), orderedInterval (-12844566658 / 1000000000000) (-12844566655 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_stateChecks7 :
    compactCertificate367.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (278374820690133 / 4000000000000)) (orderedInterval (91126130365 / 1000000000000) (91126130366 / 1000000000000), orderedInterval (28388387589 / 1000000000000) (28388387590 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (755841789789399 / 4000000000000)) (orderedInterval (55075551771 / 1000000000000) (55075551773 / 1000000000000), orderedInterval (18177417049 / 1000000000000) (18177417050 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1032037345055223 / 4000000000000)) (orderedInterval (45996921193 / 1000000000000) (45996921194 / 1000000000000), orderedInterval (18664772151 / 1000000000000) (18664772152 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_stateChecks8 :
    compactCertificate367.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (436385460799701 / 4000000000000)) (orderedInterval (5733369254 / 1000000000000) (5733369273 / 1000000000000), orderedInterval (-76200933668 / 1000000000000) (-76200933648 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1773882670754421 / 4000000000000)) (orderedInterval (-36417385245 / 1000000000000) (-36417385239 / 1000000000000), orderedInterval (-10414227752 / 1000000000000) (-10414227746 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1184871415132539 / 4000000000000)) (orderedInterval (46012600406 / 1000000000000) (46012601074 / 1000000000000), orderedInterval (-5734371773 / 1000000000000) (-5734371105 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_states : ∀ j,
    BesselStateValid (compactCertificate367.point j) (compactCertificate367.state j) :=
  compactCertificate367.statesValid_of_checks3 compactCertificate367_stateChecks0
    compactCertificate367_stateChecks1 compactCertificate367_stateChecks2
    compactCertificate367_stateChecks3 compactCertificate367_stateChecks4
    compactCertificate367_stateChecks5 compactCertificate367_stateChecks6
    compactCertificate367_stateChecks7 compactCertificate367_stateChecks8

theorem compactCertificate367_chunkChecks0_0 :
    compactCertificate367.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (477 / 2) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25842889837 / 1000000000000) (25842889838 / 1000000000000), orderedInterval (44682979850 / 1000000000000) (44682979851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (702712082148777 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30614547438 / 1000000000000) (30614547439 / 1000000000000), orderedInterval (51744748577 / 1000000000000) (51744748578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (227242649236041 / 800000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (40986023992 / 1000000000000) (40986065433 / 1000000000000), orderedInterval (-23764791395 / 1000000000000) (-23764749955 / 1000000000000)))) (orderedInterval (12933591643 / 1000000000000) (12933594092 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (205049632982139 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (109010139571 / 1000000000000) (109010140001 / 1000000000000), orderedInterval (-24195219648 / 1000000000000) (-24195219219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (550792156806783 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16983690999 / 1000000000000) (16983691000 / 1000000000000), orderedInterval (65778166879 / 1000000000000) (65778166880 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1495507850063811 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29958326301 / 1000000000000) (-29958326300 / 1000000000000), orderedInterval (-28336874780 / 1000000000000) (-28336874779 / 1000000000000)))) (orderedInterval (1567148128 / 1000000000000) (1567148162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1101584313614043 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13246902003 / 1000000000000) (-13246901887 / 1000000000000), orderedInterval (46242816961 / 1000000000000) (46242817077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1887583497280839 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36425947685 / 1000000000000) (36425947763 / 1000000000000), orderedInterval (4674993096 / 1000000000000) (4674993174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1390385460799701 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14085363944 / 1000000000000) (14085364096 / 1000000000000), orderedInterval (-40431836927 / 1000000000000) (-40431836774 / 1000000000000)))) (orderedInterval (-783106520 / 1000000000000) (-783106500 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_chunkChecks0_1 :
    compactCertificate367.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2133208850534523 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (574384508 / 1000000000000) (574384510 / 1000000000000), orderedInterval (34545117300 / 1000000000000) (34545117301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1231608704093667 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32968074717 / 1000000000000) (32968074718 / 1000000000000), orderedInterval (31262751864 / 1000000000000) (31262751865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2185511258082303 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17134111428 / 1000000000000) (17134111429 / 1000000000000), orderedInterval (29506963974 / 1000000000000) (29506963975 / 1000000000000)))) (orderedInterval (4776316696 / 1000000000000) (4776316792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2041988114364507 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25268953790 / 1000000000000) (25268966006 / 1000000000000), orderedInterval (-24693325733 / 1000000000000) (-24693313516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1457259070995531 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26124669941 / 1000000000000) (26124669942 / 1000000000000), orderedInterval (32597660559 / 1000000000000) (32597660560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1652376470420349 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28460756027 / 1000000000000) (-28460733680 / 1000000000000), orderedInterval (27073056580 / 1000000000000) (27073078926 / 1000000000000)))) (orderedInterval (2158268538 / 1000000000000) (2158268901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1377579232129581 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16558418549 / 1000000000000) (-16558418204 / 1000000000000), orderedInterval (39701961532 / 1000000000000) (39701961877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1217133029373201 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14984367330 / 1000000000000) (-14984367329 / 1000000000000), orderedInterval (-43191873397 / 1000000000000) (-43191873396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (352772591950899 / 800000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35599137124 / 1000000000000) (35599155598 / 1000000000000), orderedInterval (-13321731727 / 1000000000000) (-13321713253 / 1000000000000)))) (orderedInterval (1577772911 / 1000000000000) (1577773412 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_chunkChecks0_2 :
    compactCertificate367.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (975787554740553 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-15703137373 / 1000000000000) (-15703137147 / 1000000000000), orderedInterval (48643720956 / 1000000000000) (48643721182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (827185916704833 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12981525402 / 1000000000000) (12981525403 / 1000000000000), orderedInterval (53912774772 / 1000000000000) (53912774773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (517614539200299 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68903675403 / 1000000000000) (-68903675401 / 1000000000000), orderedInterval (-12844566658 / 1000000000000) (-12844566655 / 1000000000000)))) (orderedInterval (-467118677 / 1000000000000) (-467118580 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (278374820690133 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (91126130365 / 1000000000000) (91126130366 / 1000000000000), orderedInterval (28388387589 / 1000000000000) (28388387590 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (755841789789399 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (55075551771 / 1000000000000) (55075551773 / 1000000000000), orderedInterval (18177417049 / 1000000000000) (18177417050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1032037345055223 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45996921193 / 1000000000000) (45996921194 / 1000000000000), orderedInterval (18664772151 / 1000000000000) (18664772152 / 1000000000000)))) (orderedInterval (-6457298180 / 1000000000000) (-6457298151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (436385460799701 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5733369254 / 1000000000000) (5733369273 / 1000000000000), orderedInterval (-76200933668 / 1000000000000) (-76200933648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1773882670754421 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36417385245 / 1000000000000) (-36417385239 / 1000000000000), orderedInterval (-10414227752 / 1000000000000) (-10414227746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1184871415132539 / 4000000000000) 0 (IntervalRat.scale (477 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46012600406 / 1000000000000) (46012601074 / 1000000000000), orderedInterval (-5734371773 / 1000000000000) (-5734371105 / 1000000000000)))) (orderedInterval (-5634182068 / 1000000000000) (-5634181876 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_chunkChecks0 :
    compactCertificate367.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate367.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate367_chunkChecks0_0
    compactCertificate367_chunkChecks0_1 compactCertificate367_chunkChecks0_2

theorem compactCertificate367_chunkChecks1_0 :
    compactCertificate367.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (477 / 2) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25842889837 / 1000000000000) (25842889838 / 1000000000000), orderedInterval (44682979850 / 1000000000000) (44682979851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (702712082148777 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30614547438 / 1000000000000) (30614547439 / 1000000000000), orderedInterval (51744748577 / 1000000000000) (51744748578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (227242649236041 / 800000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (40986023992 / 1000000000000) (40986065433 / 1000000000000), orderedInterval (-23764791395 / 1000000000000) (-23764749955 / 1000000000000)))) (orderedInterval (16405024301 / 1000000000000) (16405027217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (205049632982139 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (109010139571 / 1000000000000) (109010140001 / 1000000000000), orderedInterval (-24195219648 / 1000000000000) (-24195219219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (550792156806783 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16983690999 / 1000000000000) (16983691000 / 1000000000000), orderedInterval (65778166879 / 1000000000000) (65778166880 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1495507850063811 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29958326301 / 1000000000000) (-29958326300 / 1000000000000), orderedInterval (-28336874780 / 1000000000000) (-28336874779 / 1000000000000)))) (orderedInterval (4600930815 / 1000000000000) (4600930849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1101584313614043 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13246902003 / 1000000000000) (-13246901887 / 1000000000000), orderedInterval (46242816961 / 1000000000000) (46242817077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1887583497280839 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36425947685 / 1000000000000) (36425947763 / 1000000000000), orderedInterval (4674993096 / 1000000000000) (4674993174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1390385460799701 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14085363944 / 1000000000000) (14085364096 / 1000000000000), orderedInterval (-40431836927 / 1000000000000) (-40431836774 / 1000000000000)))) (orderedInterval (-1709441239 / 1000000000000) (-1709441205 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_chunkChecks1_1 :
    compactCertificate367.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2133208850534523 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (574384508 / 1000000000000) (574384510 / 1000000000000), orderedInterval (34545117300 / 1000000000000) (34545117301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1231608704093667 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32968074717 / 1000000000000) (32968074718 / 1000000000000), orderedInterval (31262751864 / 1000000000000) (31262751865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2185511258082303 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17134111428 / 1000000000000) (17134111429 / 1000000000000), orderedInterval (29506963974 / 1000000000000) (29506963975 / 1000000000000)))) (orderedInterval (-1125846973 / 1000000000000) (-1125846776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2041988114364507 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25268953790 / 1000000000000) (25268966006 / 1000000000000), orderedInterval (-24693325733 / 1000000000000) (-24693313516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1457259070995531 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26124669941 / 1000000000000) (26124669942 / 1000000000000), orderedInterval (32597660559 / 1000000000000) (32597660560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1652376470420349 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28460756027 / 1000000000000) (-28460733680 / 1000000000000), orderedInterval (27073056580 / 1000000000000) (27073078926 / 1000000000000)))) (orderedInterval (5425531071 / 1000000000000) (5425531786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1377579232129581 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16558418549 / 1000000000000) (-16558418204 / 1000000000000), orderedInterval (39701961532 / 1000000000000) (39701961877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1217133029373201 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14984367330 / 1000000000000) (-14984367329 / 1000000000000), orderedInterval (-43191873397 / 1000000000000) (-43191873396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (352772591950899 / 800000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35599137124 / 1000000000000) (35599155598 / 1000000000000), orderedInterval (-13321731727 / 1000000000000) (-13321713253 / 1000000000000)))) (orderedInterval (3184862606 / 1000000000000) (3184863520 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_chunkChecks1_2 :
    compactCertificate367.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (975787554740553 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-15703137373 / 1000000000000) (-15703137147 / 1000000000000), orderedInterval (48643720956 / 1000000000000) (48643721182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (827185916704833 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12981525402 / 1000000000000) (12981525403 / 1000000000000), orderedInterval (53912774772 / 1000000000000) (53912774773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (517614539200299 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68903675403 / 1000000000000) (-68903675401 / 1000000000000), orderedInterval (-12844566658 / 1000000000000) (-12844566655 / 1000000000000)))) (orderedInterval (-10828107825 / 1000000000000) (-10828107732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (278374820690133 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (91126130365 / 1000000000000) (91126130366 / 1000000000000), orderedInterval (28388387589 / 1000000000000) (28388387590 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (755841789789399 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (55075551771 / 1000000000000) (55075551773 / 1000000000000), orderedInterval (18177417049 / 1000000000000) (18177417050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1032037345055223 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45996921193 / 1000000000000) (45996921194 / 1000000000000), orderedInterval (18664772151 / 1000000000000) (18664772152 / 1000000000000)))) (orderedInterval (-2027146695 / 1000000000000) (-2027146668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (436385460799701 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5733369254 / 1000000000000) (5733369273 / 1000000000000), orderedInterval (-76200933668 / 1000000000000) (-76200933648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1773882670754421 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36417385245 / 1000000000000) (-36417385239 / 1000000000000), orderedInterval (-10414227752 / 1000000000000) (-10414227746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1184871415132539 / 4000000000000) 1 (IntervalRat.scale (477 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46012600406 / 1000000000000) (46012601074 / 1000000000000), orderedInterval (-5734371773 / 1000000000000) (-5734371105 / 1000000000000)))) (orderedInterval (2702465874 / 1000000000000) (2702466124 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_chunkChecks1 :
    compactCertificate367.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate367.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate367_chunkChecks1_0
    compactCertificate367_chunkChecks1_1 compactCertificate367_chunkChecks1_2

theorem compactCertificate367_chunkChecks2_0 :
    compactCertificate367.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (477 / 2) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25842889837 / 1000000000000) (25842889838 / 1000000000000), orderedInterval (44682979850 / 1000000000000) (44682979851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (702712082148777 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30614547438 / 1000000000000) (30614547439 / 1000000000000), orderedInterval (51744748577 / 1000000000000) (51744748578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (227242649236041 / 800000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (40986023992 / 1000000000000) (40986065433 / 1000000000000), orderedInterval (-23764791395 / 1000000000000) (-23764749955 / 1000000000000)))) (orderedInterval (-13878376783 / 1000000000000) (-13878373299 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (205049632982139 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (109010139571 / 1000000000000) (109010140001 / 1000000000000), orderedInterval (-24195219648 / 1000000000000) (-24195219219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (550792156806783 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16983690999 / 1000000000000) (16983691000 / 1000000000000), orderedInterval (65778166879 / 1000000000000) (65778166880 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1495507850063811 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29958326301 / 1000000000000) (-29958326300 / 1000000000000), orderedInterval (-28336874780 / 1000000000000) (-28336874779 / 1000000000000)))) (orderedInterval (-5405003238 / 1000000000000) (-5405003192 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1101584313614043 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13246902003 / 1000000000000) (-13246901887 / 1000000000000), orderedInterval (46242816961 / 1000000000000) (46242817077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1887583497280839 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36425947685 / 1000000000000) (36425947763 / 1000000000000), orderedInterval (4674993096 / 1000000000000) (4674993174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1390385460799701 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14085363944 / 1000000000000) (14085364096 / 1000000000000), orderedInterval (-40431836927 / 1000000000000) (-40431836774 / 1000000000000)))) (orderedInterval (3682517797 / 1000000000000) (3682517856 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_chunkChecks2_1 :
    compactCertificate367.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2133208850534523 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (574384508 / 1000000000000) (574384510 / 1000000000000), orderedInterval (34545117300 / 1000000000000) (34545117301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1231608704093667 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32968074717 / 1000000000000) (32968074718 / 1000000000000), orderedInterval (31262751864 / 1000000000000) (31262751865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2185511258082303 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17134111428 / 1000000000000) (17134111429 / 1000000000000), orderedInterval (29506963974 / 1000000000000) (29506963975 / 1000000000000)))) (orderedInterval (-16339167367 / 1000000000000) (-16339166944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2041988114364507 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25268953790 / 1000000000000) (25268966006 / 1000000000000), orderedInterval (-24693325733 / 1000000000000) (-24693313516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1457259070995531 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26124669941 / 1000000000000) (26124669942 / 1000000000000), orderedInterval (32597660559 / 1000000000000) (32597660560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1652376470420349 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28460756027 / 1000000000000) (-28460733680 / 1000000000000), orderedInterval (27073056580 / 1000000000000) (27073078926 / 1000000000000)))) (orderedInterval (-4129143847 / 1000000000000) (-4129142418 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1377579232129581 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16558418549 / 1000000000000) (-16558418204 / 1000000000000), orderedInterval (39701961532 / 1000000000000) (39701961877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1217133029373201 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14984367330 / 1000000000000) (-14984367329 / 1000000000000), orderedInterval (-43191873397 / 1000000000000) (-43191873396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (352772591950899 / 800000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35599137124 / 1000000000000) (35599155598 / 1000000000000), orderedInterval (-13321731727 / 1000000000000) (-13321713253 / 1000000000000)))) (orderedInterval (-4126300354 / 1000000000000) (-4126298675 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_chunkChecks2_2 :
    compactCertificate367.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (975787554740553 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-15703137373 / 1000000000000) (-15703137147 / 1000000000000), orderedInterval (48643720956 / 1000000000000) (48643721182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (827185916704833 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12981525402 / 1000000000000) (12981525403 / 1000000000000), orderedInterval (53912774772 / 1000000000000) (53912774773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (517614539200299 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68903675403 / 1000000000000) (-68903675401 / 1000000000000), orderedInterval (-12844566658 / 1000000000000) (-12844566655 / 1000000000000)))) (orderedInterval (-1368650455 / 1000000000000) (-1368650363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (278374820690133 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (91126130365 / 1000000000000) (91126130366 / 1000000000000), orderedInterval (28388387589 / 1000000000000) (28388387590 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (755841789789399 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (55075551771 / 1000000000000) (55075551773 / 1000000000000), orderedInterval (18177417049 / 1000000000000) (18177417050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1032037345055223 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45996921193 / 1000000000000) (45996921194 / 1000000000000), orderedInterval (18664772151 / 1000000000000) (18664772152 / 1000000000000)))) (orderedInterval (5061555359 / 1000000000000) (5061555385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (436385460799701 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5733369254 / 1000000000000) (5733369273 / 1000000000000), orderedInterval (-76200933668 / 1000000000000) (-76200933648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1773882670754421 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36417385245 / 1000000000000) (-36417385239 / 1000000000000), orderedInterval (-10414227752 / 1000000000000) (-10414227746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1184871415132539 / 4000000000000) 2 (IntervalRat.scale (477 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46012600406 / 1000000000000) (46012601074 / 1000000000000), orderedInterval (-5734371773 / 1000000000000) (-5734371105 / 1000000000000)))) (orderedInterval (3049418440 / 1000000000000) (3049418774 / 1000000000000))) = true
  rfl'

theorem compactCertificate367_chunkChecks2 :
    compactCertificate367.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate367.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate367_chunkChecks2_0
    compactCertificate367_chunkChecks2_1 compactCertificate367_chunkChecks2_2

theorem compactCertificate367_chunkChecks3_0 :
    compactCertificate367.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (477 / 2) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25842889837 / 1000000000000) (25842889838 / 1000000000000), orderedInterval (44682979850 / 1000000000000) (44682979851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (702712082148777 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30614547438 / 1000000000000) (30614547439 / 1000000000000), orderedInterval (51744748577 / 1000000000000) (51744748578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (227242649236041 / 800000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (40986023992 / 1000000000000) (40986065433 / 1000000000000), orderedInterval (-23764791395 / 1000000000000) (-23764749955 / 1000000000000)))) (orderedInterval (-15489038350 / 1000000000000) (-15489034201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (205049632982139 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (109010139571 / 1000000000000) (109010140001 / 1000000000000), orderedInterval (-24195219648 / 1000000000000) (-24195219219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (550792156806783 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16983690999 / 1000000000000) (16983691000 / 1000000000000), orderedInterval (65778166879 / 1000000000000) (65778166880 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1495507850063811 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29958326301 / 1000000000000) (-29958326300 / 1000000000000), orderedInterval (-28336874780 / 1000000000000) (-28336874779 / 1000000000000)))) (orderedInterval (-8202378916 / 1000000000000) (-8202378847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1101584313614043 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13246902003 / 1000000000000) (-13246901887 / 1000000000000), orderedInterval (46242816961 / 1000000000000) (46242817077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1887583497280839 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36425947685 / 1000000000000) (36425947763 / 1000000000000), orderedInterval (4674993096 / 1000000000000) (4674993174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1390385460799701 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14085363944 / 1000000000000) (14085364096 / 1000000000000), orderedInterval (-40431836927 / 1000000000000) (-40431836774 / 1000000000000)))) (orderedInterval (4126456052 / 1000000000000) (4126456158 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate367_chunkChecks3_1 :
    compactCertificate367.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2133208850534523 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (574384508 / 1000000000000) (574384510 / 1000000000000), orderedInterval (34545117300 / 1000000000000) (34545117301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1231608704093667 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32968074717 / 1000000000000) (32968074718 / 1000000000000), orderedInterval (31262751864 / 1000000000000) (31262751865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2185511258082303 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17134111428 / 1000000000000) (17134111429 / 1000000000000), orderedInterval (29506963974 / 1000000000000) (29506963975 / 1000000000000)))) (orderedInterval (13280623431 / 1000000000000) (13280624355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2041988114364507 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25268953790 / 1000000000000) (25268966006 / 1000000000000), orderedInterval (-24693325733 / 1000000000000) (-24693313516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1457259070995531 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26124669941 / 1000000000000) (26124669942 / 1000000000000), orderedInterval (32597660559 / 1000000000000) (32597660560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1652376470420349 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28460756027 / 1000000000000) (-28460733680 / 1000000000000), orderedInterval (27073056580 / 1000000000000) (27073078926 / 1000000000000)))) (orderedInterval (-14629168852 / 1000000000000) (-14629165966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1377579232129581 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16558418549 / 1000000000000) (-16558418204 / 1000000000000), orderedInterval (39701961532 / 1000000000000) (39701961877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1217133029373201 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14984367330 / 1000000000000) (-14984367329 / 1000000000000), orderedInterval (-43191873397 / 1000000000000) (-43191873396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (352772591950899 / 800000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35599137124 / 1000000000000) (35599155598 / 1000000000000), orderedInterval (-13321731727 / 1000000000000) (-13321713253 / 1000000000000)))) (orderedInterval (-4340202726 / 1000000000000) (-4340199641 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate367_chunkChecks3_2 :
    compactCertificate367.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (975787554740553 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-15703137373 / 1000000000000) (-15703137147 / 1000000000000), orderedInterval (48643720956 / 1000000000000) (48643721182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (827185916704833 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12981525402 / 1000000000000) (12981525403 / 1000000000000), orderedInterval (53912774772 / 1000000000000) (53912774773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (517614539200299 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68903675403 / 1000000000000) (-68903675401 / 1000000000000), orderedInterval (-12844566658 / 1000000000000) (-12844566655 / 1000000000000)))) (orderedInterval (10384423751 / 1000000000000) (10384423842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (278374820690133 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (91126130365 / 1000000000000) (91126130366 / 1000000000000), orderedInterval (28388387589 / 1000000000000) (28388387590 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (755841789789399 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (55075551771 / 1000000000000) (55075551773 / 1000000000000), orderedInterval (18177417049 / 1000000000000) (18177417050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1032037345055223 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45996921193 / 1000000000000) (45996921194 / 1000000000000), orderedInterval (18664772151 / 1000000000000) (18664772152 / 1000000000000)))) (orderedInterval (2007837120 / 1000000000000) (2007837147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (436385460799701 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5733369254 / 1000000000000) (5733369273 / 1000000000000), orderedInterval (-76200933668 / 1000000000000) (-76200933648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1773882670754421 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36417385245 / 1000000000000) (-36417385239 / 1000000000000), orderedInterval (-10414227752 / 1000000000000) (-10414227746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1184871415132539 / 4000000000000) 3 (IntervalRat.scale (477 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46012600406 / 1000000000000) (46012601074 / 1000000000000), orderedInterval (-5734371773 / 1000000000000) (-5734371105 / 1000000000000)))) (orderedInterval (-7480031815 / 1000000000000) (-7480031359 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate367_chunkChecks3 :
    compactCertificate367.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate367.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate367_chunkChecks3_0
    compactCertificate367_chunkChecks3_1 compactCertificate367_chunkChecks3_2

theorem compactCertificate367_chunkChecks4_0 :
    compactCertificate367.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (477 / 2) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25842889837 / 1000000000000) (25842889838 / 1000000000000), orderedInterval (44682979850 / 1000000000000) (44682979851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (702712082148777 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (30614547438 / 1000000000000) (30614547439 / 1000000000000), orderedInterval (51744748577 / 1000000000000) (51744748578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (227242649236041 / 800000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (40986023992 / 1000000000000) (40986065433 / 1000000000000), orderedInterval (-23764791395 / 1000000000000) (-23764749955 / 1000000000000)))) (orderedInterval (15296111640 / 1000000000000) (15296116597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (205049632982139 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (109010139571 / 1000000000000) (109010140001 / 1000000000000), orderedInterval (-24195219648 / 1000000000000) (-24195219219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (550792156806783 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (16983690999 / 1000000000000) (16983691000 / 1000000000000), orderedInterval (65778166879 / 1000000000000) (65778166880 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1495507850063811 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29958326301 / 1000000000000) (-29958326300 / 1000000000000), orderedInterval (-28336874780 / 1000000000000) (-28336874779 / 1000000000000)))) (orderedInterval (12996372525 / 1000000000000) (12996372630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1101584313614043 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-13246902003 / 1000000000000) (-13246901887 / 1000000000000), orderedInterval (46242816961 / 1000000000000) (46242817077 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1887583497280839 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36425947685 / 1000000000000) (36425947763 / 1000000000000), orderedInterval (4674993096 / 1000000000000) (4674993174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1390385460799701 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (14085363944 / 1000000000000) (14085364096 / 1000000000000), orderedInterval (-40431836927 / 1000000000000) (-40431836774 / 1000000000000)))) (orderedInterval (-15717852429 / 1000000000000) (-15717852236 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate367_chunkChecks4_1 :
    compactCertificate367.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2133208850534523 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (574384508 / 1000000000000) (574384510 / 1000000000000), orderedInterval (34545117300 / 1000000000000) (34545117301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1231608704093667 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32968074717 / 1000000000000) (32968074718 / 1000000000000), orderedInterval (31262751864 / 1000000000000) (31262751865 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2185511258082303 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17134111428 / 1000000000000) (17134111429 / 1000000000000), orderedInterval (29506963974 / 1000000000000) (29506963975 / 1000000000000)))) (orderedInterval (71210035518 / 1000000000000) (71210037575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2041988114364507 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25268953790 / 1000000000000) (25268966006 / 1000000000000), orderedInterval (-24693325733 / 1000000000000) (-24693313516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1457259070995531 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26124669941 / 1000000000000) (26124669942 / 1000000000000), orderedInterval (32597660559 / 1000000000000) (32597660560 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1652376470420349 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28460756027 / 1000000000000) (-28460733680 / 1000000000000), orderedInterval (27073056580 / 1000000000000) (27073078926 / 1000000000000)))) (orderedInterval (5293507584 / 1000000000000) (5293513479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1377579232129581 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16558418549 / 1000000000000) (-16558418204 / 1000000000000), orderedInterval (39701961532 / 1000000000000) (39701961877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1217133029373201 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14984367330 / 1000000000000) (-14984367329 / 1000000000000), orderedInterval (-43191873397 / 1000000000000) (-43191873396 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (352772591950899 / 800000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35599137124 / 1000000000000) (35599155598 / 1000000000000), orderedInterval (-13321731727 / 1000000000000) (-13321713253 / 1000000000000)))) (orderedInterval (12128439999 / 1000000000000) (12128445690 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate367_chunkChecks4_2 :
    compactCertificate367.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (975787554740553 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-15703137373 / 1000000000000) (-15703137147 / 1000000000000), orderedInterval (48643720956 / 1000000000000) (48643721182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (827185916704833 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12981525402 / 1000000000000) (12981525403 / 1000000000000), orderedInterval (53912774772 / 1000000000000) (53912774773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (517614539200299 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-68903675403 / 1000000000000) (-68903675401 / 1000000000000), orderedInterval (-12844566658 / 1000000000000) (-12844566655 / 1000000000000)))) (orderedInterval (2051356364 / 1000000000000) (2051356454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (278374820690133 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (91126130365 / 1000000000000) (91126130366 / 1000000000000), orderedInterval (28388387589 / 1000000000000) (28388387590 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (755841789789399 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (55075551771 / 1000000000000) (55075551773 / 1000000000000), orderedInterval (18177417049 / 1000000000000) (18177417050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1032037345055223 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45996921193 / 1000000000000) (45996921194 / 1000000000000), orderedInterval (18664772151 / 1000000000000) (18664772152 / 1000000000000)))) (orderedInterval (-5349271112 / 1000000000000) (-5349271084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (436385460799701 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (5733369254 / 1000000000000) (5733369273 / 1000000000000), orderedInterval (-76200933668 / 1000000000000) (-76200933648 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1773882670754421 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36417385245 / 1000000000000) (-36417385239 / 1000000000000), orderedInterval (-10414227752 / 1000000000000) (-10414227746 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1184871415132539 / 4000000000000) 4 (IntervalRat.scale (477 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46012600406 / 1000000000000) (46012601074 / 1000000000000), orderedInterval (-5734371773 / 1000000000000) (-5734371105 / 1000000000000)))) (orderedInterval (14957688605 / 1000000000000) (14957689251 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate367_chunkChecks4 :
    compactCertificate367.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate367.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate367_chunkChecks4_0
    compactCertificate367_chunkChecks4_1 compactCertificate367_chunkChecks4_2

theorem compactCertificate367_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate367.chunkCheck r b = true :=
  compactCertificate367.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate367_chunkChecks0
    · exact compactCertificate367_chunkChecks1
    · exact compactCertificate367_chunkChecks2
    · exact compactCertificate367_chunkChecks3
    · exact compactCertificate367_chunkChecks4)

theorem compactCertificate367_coefficient0 :
    compactCertificate367.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate367_coefficient1 :
    compactCertificate367.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate367_coefficient2 :
    compactCertificate367.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate367_coefficient3 :
    compactCertificate367.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate367_coefficient4 :
    compactCertificate367.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate367_coefficients : ∀ r : Fin 5,
    compactCertificate367.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate367_coefficient0
  · exact compactCertificate367_coefficient1
  · exact compactCertificate367_coefficient2
  · exact compactCertificate367_coefficient3
  · exact compactCertificate367_coefficient4

theorem compactCertificate367_lower : (1 : ℚ) ≤ compactCertificate367.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate367, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate367_proves {t : ℝ} (ht : t ∈ compactCertificate367.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate367.proves compactCertificate367_states compactCertificate367_chunks
    compactCertificate367_coefficients compactCertificate367_lower ht

end Erdos232
