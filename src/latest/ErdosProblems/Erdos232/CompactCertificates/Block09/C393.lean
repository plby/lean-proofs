/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate393 : CompactCertificate where
  left := 264
  right := 265
  center := 529 / 2
  grid := fun i =>
    match i.val with
    | 0 => 84
    | 1 => 62
    | 2 => 100
    | 3 => 18
    | 4 => 49
    | 5 => 132
    | 6 => 97
    | 7 => 167
    | 8 => 123
    | 9 => 188
    | 10 => 109
    | 11 => 193
    | 12 => 180
    | 13 => 129
    | 14 => 146
    | 15 => 122
    | 16 => 107
    | 17 => 156
    | 18 => 86
    | 19 => 73
    | 20 => 46
    | 21 => 25
    | 22 => 67
    | 23 => 91
    | 24 => 39
    | 25 => 157
    | _ => 105
  point := fun i =>
    match i.val with
    | 0 => 529 / 2
    | 1 => 779318011439629 / 4000000000000
    | 2 => 252015432800557 / 800000000000
    | 3 => 227403052091303 / 4000000000000
    | 4 => 610836584802491 / 4000000000000
    | 5 => 1658540152376847 / 4000000000000
    | 6 => 1221673169605511 / 4000000000000
    | 7 => 2093357798871203 / 4000000000000
    | 8 => 1541957880006377 / 4000000000000
    | 9 => 2365759920194471 / 4000000000000
    | 10 => 1365872126762159 / 4000000000000
    | 11 => 2423764057705531 / 4000000000000
    | 12 => 2264594785112839 / 4000000000000
    | 13 => 1616121695087287 / 4000000000000
    | 14 => 1832509754407473 / 4000000000000
    | 15 => 1527755584479137 / 4000000000000
    | 16 => 1349818391065877 / 4000000000000
    | 17 => 391229981429823 / 800000000000
    | 18 => 1082162717940781 / 4000000000000
    | 19 => 917361320622341 / 4000000000000
    | 20 => 574042119993623 / 4000000000000
    | 21 => 308721761310441 / 4000000000000
    | 22 => 838239636894323 / 4000000000000
    | 23 => 1144544560868371 / 4000000000000
    | 24 => 483957880006377 / 4000000000000
    | 25 => 1967261913687817 / 4000000000000
    | _ => 1314039787432103 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (48270331964 / 1000000000000) (48270331972 / 1000000000000), orderedInterval (8675226419 / 1000000000000) (8675226426 / 1000000000000))
    | 1 => (orderedInterval (42394187115 / 1000000000000) (42394187116 / 1000000000000), orderedInterval (38235766541 / 1000000000000) (38235766542 / 1000000000000))
    | 2 => (orderedInterval (44830500472 / 1000000000000) (44830500885 / 1000000000000), orderedInterval (-3405083681 / 1000000000000) (-3405083268 / 1000000000000))
    | 3 => (orderedInterval (93590647145 / 1000000000000) (93590647146 / 1000000000000), orderedInterval (48559456205 / 1000000000000) (48559456206 / 1000000000000))
    | 4 => (orderedInterval (27753127698 / 1000000000000) (27753129695 / 1000000000000), orderedInterval (-58388523219 / 1000000000000) (-58388521223 / 1000000000000))
    | 5 => (orderedInterval (26127719480 / 1000000000000) (26127719481 / 1000000000000), orderedInterval (29169797826 / 1000000000000) (29169797827 / 1000000000000))
    | 6 => (orderedInterval (-45418105202 / 1000000000000) (-45418105168 / 1000000000000), orderedInterval (-4574544046 / 1000000000000) (-4574544013 / 1000000000000))
    | 7 => (orderedInterval (17371323993 / 1000000000000) (17371324532 / 1000000000000), orderedInterval (-30260506304 / 1000000000000) (-30260505764 / 1000000000000))
    | 8 => (orderedInterval (5725189608 / 1000000000000) (5725189615 / 1000000000000), orderedInterval (-40240270723 / 1000000000000) (-40240270716 / 1000000000000))
    | 9 => (orderedInterval (32788330944 / 1000000000000) (32788332346 / 1000000000000), orderedInterval (-1174193725 / 1000000000000) (-1174192323 / 1000000000000))
    | 10 => (orderedInterval (7752924750 / 1000000000000) (7752924767 / 1000000000000), orderedInterval (-42487878726 / 1000000000000) (-42487878710 / 1000000000000))
    | 11 => (orderedInterval (-12587265797 / 1000000000000) (-12587265796 / 1000000000000), orderedInterval (-29859178757 / 1000000000000) (-29859178756 / 1000000000000))
    | 12 => (orderedInterval (33277360522 / 1000000000000) (33277360685 / 1000000000000), orderedInterval (4104778850 / 1000000000000) (4104779013 / 1000000000000))
    | 13 => (orderedInterval (17263686321 / 1000000000000) (17263686791 / 1000000000000), orderedInterval (-35765437247 / 1000000000000) (-35765436777 / 1000000000000))
    | 14 => (orderedInterval (8862281019 / 1000000000000) (8862281020 / 1000000000000), orderedInterval (36199077385 / 1000000000000) (36199077386 / 1000000000000))
    | 15 => (orderedInterval (-21351248330 / 1000000000000) (-21351246542 / 1000000000000), orderedInterval (34826447331 / 1000000000000) (34826449118 / 1000000000000))
    | 16 => (orderedInterval (-37727238042 / 1000000000000) (-37727187979 / 1000000000000), orderedInterval (21577743551 / 1000000000000) (21577793614 / 1000000000000))
    | 17 => (orderedInterval (-9478796029 / 1000000000000) (-9478796009 / 1000000000000), orderedInterval (34822536151 / 1000000000000) (34822536170 / 1000000000000))
    | 18 => (orderedInterval (44250533491 / 1000000000000) (44250533492 / 1000000000000), orderedInterval (19793490324 / 1000000000000) (19793490325 / 1000000000000))
    | 19 => (orderedInterval (-37385938390 / 1000000000000) (-37385938389 / 1000000000000), orderedInterval (-37042140066 / 1000000000000) (-37042140065 / 1000000000000))
    | 20 => (orderedInterval (-14418148614 / 1000000000000) (-14418148489 / 1000000000000), orderedInterval (65074771497 / 1000000000000) (65074771622 / 1000000000000))
    | 21 => (orderedInterval (49436626729 / 1000000000000) (49436638542 / 1000000000000), orderedInterval (-76507854690 / 1000000000000) (-76507842877 / 1000000000000))
    | 22 => (orderedInterval (7800163766 / 1000000000000) (7800163791 / 1000000000000), orderedInterval (-54581005150 / 1000000000000) (-54581005125 / 1000000000000))
    | 23 => (orderedInterval (-40586687666 / 1000000000000) (-40586687665 / 1000000000000), orderedInterval (-23962457800 / 1000000000000) (-23962457799 / 1000000000000))
    | 24 => (orderedInterval (49353109746 / 1000000000000) (49353158043 / 1000000000000), orderedInterval (-53364578912 / 1000000000000) (-53364530615 / 1000000000000))
    | 25 => (orderedInterval (21179595346 / 1000000000000) (21179597673 / 1000000000000), orderedInterval (-29105085050 / 1000000000000) (-29105082723 / 1000000000000))
    | _ => (orderedInterval (23839300568 / 1000000000000) (23839303653 / 1000000000000), orderedInterval (-37044252858 / 1000000000000) (-37044249773 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (22158406235 / 1000000000000) (22158406282 / 1000000000000)
      | 1 => orderedInterval (-1859487231 / 1000000000000) (-1859487125 / 1000000000000)
      | 2 => orderedInterval (-397434622 / 1000000000000) (-397434590 / 1000000000000)
      | 3 => orderedInterval (-7041016896 / 1000000000000) (-7041016540 / 1000000000000)
      | 4 => orderedInterval (986896339 / 1000000000000) (986896419 / 1000000000000)
      | 5 => orderedInterval (1669749798 / 1000000000000) (1669752710 / 1000000000000)
      | 6 => orderedInterval (-5428670161 / 1000000000000) (-5428670090 / 1000000000000)
      | 7 => orderedInterval (2020703309 / 1000000000000) (2020703560 / 1000000000000)
      | _ => orderedInterval (-5899425941 / 1000000000000) (-5899424808 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (3463014071 / 1000000000000) (3463014124 / 1000000000000)
      | 1 => orderedInterval (-4594794033 / 1000000000000) (-4594793954 / 1000000000000)
      | 2 => orderedInterval (429346849 / 1000000000000) (429346908 / 1000000000000)
      | 3 => orderedInterval (-13321575459 / 1000000000000) (-13321574682 / 1000000000000)
      | 4 => orderedInterval (-5642122899 / 1000000000000) (-5642122773 / 1000000000000)
      | 5 => orderedInterval (653791254 / 1000000000000) (653794977 / 1000000000000)
      | 6 => orderedInterval (-269765875 / 1000000000000) (-269765811 / 1000000000000)
      | 7 => orderedInterval (3379974615 / 1000000000000) (3379974708 / 1000000000000)
      | _ => orderedInterval (12890709991 / 1000000000000) (12890711298 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-23091695878 / 1000000000000) (-23091695816 / 1000000000000)
      | 1 => orderedInterval (4290958905 / 1000000000000) (4290958980 / 1000000000000)
      | 2 => orderedInterval (1802056567 / 1000000000000) (1802056679 / 1000000000000)
      | 3 => orderedInterval (37614302992 / 1000000000000) (37614304708 / 1000000000000)
      | 4 => orderedInterval (-900909188 / 1000000000000) (-900908986 / 1000000000000)
      | 5 => orderedInterval (-2172969646 / 1000000000000) (-2172964869 / 1000000000000)
      | 6 => orderedInterval (5950523689 / 1000000000000) (5950523749 / 1000000000000)
      | 7 => orderedInterval (-3464184129 / 1000000000000) (-3464184081 / 1000000000000)
      | _ => orderedInterval (12749563221 / 1000000000000) (12749564987 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3156026790 / 1000000000000) (-3156026718 / 1000000000000)
      | 1 => orderedInterval (8387637244 / 1000000000000) (8387637334 / 1000000000000)
      | 2 => orderedInterval (-4225840904 / 1000000000000) (-4225840690 / 1000000000000)
      | 3 => orderedInterval (55332018797 / 1000000000000) (55332022612 / 1000000000000)
      | 4 => orderedInterval (13736403795 / 1000000000000) (13736404127 / 1000000000000)
      | 5 => orderedInterval (-4273643519 / 1000000000000) (-4273637402 / 1000000000000)
      | 6 => orderedInterval (1659061375 / 1000000000000) (1659061434 / 1000000000000)
      | 7 => orderedInterval (-2962780632 / 1000000000000) (-2962780597 / 1000000000000)
      | _ => orderedInterval (-28564665969 / 1000000000000) (-28564663374 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (24565691698 / 1000000000000) (24565691783 / 1000000000000)
      | 1 => orderedInterval (-11169741160 / 1000000000000) (-11169741036 / 1000000000000)
      | 2 => orderedInterval (-7555475520 / 1000000000000) (-7555475108 / 1000000000000)
      | 3 => orderedInterval (-193759511206 / 1000000000000) (-193759502683 / 1000000000000)
      | 4 => orderedInterval (-4229571364 / 1000000000000) (-4229570809 / 1000000000000)
      | 5 => orderedInterval (1844370942 / 1000000000000) (1844378807 / 1000000000000)
      | 6 => orderedInterval (-6601259685 / 1000000000000) (-6601259627 / 1000000000000)
      | 7 => orderedInterval (4206117395 / 1000000000000) (4206117428 / 1000000000000)
      | _ => orderedInterval (-31023209003 / 1000000000000) (-31023204954 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (6209720830 / 1000000000000) (6209725818 / 1000000000000)
    | 1 => orderedInterval (-3011421486 / 1000000000000) (-3011415205 / 1000000000000)
    | 2 => orderedInterval (32777646533 / 1000000000000) (32777655351 / 1000000000000)
    | 3 => orderedInterval (35932163397 / 1000000000000) (35932176726 / 1000000000000)
    | _ => orderedInterval (-223722587903 / 1000000000000) (-223722566199 / 1000000000000)

theorem compactCertificate393_stateChecks0 :
    compactCertificate393.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (529 / 2)) (orderedInterval (48270331964 / 1000000000000) (48270331972 / 1000000000000), orderedInterval (8675226419 / 1000000000000) (8675226426 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (779318011439629 / 4000000000000)) (orderedInterval (42394187115 / 1000000000000) (42394187116 / 1000000000000), orderedInterval (38235766541 / 1000000000000) (38235766542 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (252015432800557 / 800000000000)) (orderedInterval (44830500472 / 1000000000000) (44830500885 / 1000000000000), orderedInterval (-3405083681 / 1000000000000) (-3405083268 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_stateChecks1 :
    compactCertificate393.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (227403052091303 / 4000000000000)) (orderedInterval (93590647145 / 1000000000000) (93590647146 / 1000000000000), orderedInterval (48559456205 / 1000000000000) (48559456206 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (610836584802491 / 4000000000000)) (orderedInterval (27753127698 / 1000000000000) (27753129695 / 1000000000000), orderedInterval (-58388523219 / 1000000000000) (-58388521223 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1658540152376847 / 4000000000000)) (orderedInterval (26127719480 / 1000000000000) (26127719481 / 1000000000000), orderedInterval (29169797826 / 1000000000000) (29169797827 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_stateChecks2 :
    compactCertificate393.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1221673169605511 / 4000000000000)) (orderedInterval (-45418105202 / 1000000000000) (-45418105168 / 1000000000000), orderedInterval (-4574544046 / 1000000000000) (-4574544013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2093357798871203 / 4000000000000)) (orderedInterval (17371323993 / 1000000000000) (17371324532 / 1000000000000), orderedInterval (-30260506304 / 1000000000000) (-30260505764 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1541957880006377 / 4000000000000)) (orderedInterval (5725189608 / 1000000000000) (5725189615 / 1000000000000), orderedInterval (-40240270723 / 1000000000000) (-40240270716 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_stateChecks3 :
    compactCertificate393.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2365759920194471 / 4000000000000)) (orderedInterval (32788330944 / 1000000000000) (32788332346 / 1000000000000), orderedInterval (-1174193725 / 1000000000000) (-1174192323 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1365872126762159 / 4000000000000)) (orderedInterval (7752924750 / 1000000000000) (7752924767 / 1000000000000), orderedInterval (-42487878726 / 1000000000000) (-42487878710 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2423764057705531 / 4000000000000)) (orderedInterval (-12587265797 / 1000000000000) (-12587265796 / 1000000000000), orderedInterval (-29859178757 / 1000000000000) (-29859178756 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_stateChecks4 :
    compactCertificate393.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2264594785112839 / 4000000000000)) (orderedInterval (33277360522 / 1000000000000) (33277360685 / 1000000000000), orderedInterval (4104778850 / 1000000000000) (4104779013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1616121695087287 / 4000000000000)) (orderedInterval (17263686321 / 1000000000000) (17263686791 / 1000000000000), orderedInterval (-35765437247 / 1000000000000) (-35765436777 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1832509754407473 / 4000000000000)) (orderedInterval (8862281019 / 1000000000000) (8862281020 / 1000000000000), orderedInterval (36199077385 / 1000000000000) (36199077386 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_stateChecks5 :
    compactCertificate393.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1527755584479137 / 4000000000000)) (orderedInterval (-21351248330 / 1000000000000) (-21351246542 / 1000000000000), orderedInterval (34826447331 / 1000000000000) (34826449118 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1349818391065877 / 4000000000000)) (orderedInterval (-37727238042 / 1000000000000) (-37727187979 / 1000000000000), orderedInterval (21577743551 / 1000000000000) (21577793614 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (391229981429823 / 800000000000)) (orderedInterval (-9478796029 / 1000000000000) (-9478796009 / 1000000000000), orderedInterval (34822536151 / 1000000000000) (34822536170 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_stateChecks6 :
    compactCertificate393.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1082162717940781 / 4000000000000)) (orderedInterval (44250533491 / 1000000000000) (44250533492 / 1000000000000), orderedInterval (19793490324 / 1000000000000) (19793490325 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (917361320622341 / 4000000000000)) (orderedInterval (-37385938390 / 1000000000000) (-37385938389 / 1000000000000), orderedInterval (-37042140066 / 1000000000000) (-37042140065 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (574042119993623 / 4000000000000)) (orderedInterval (-14418148614 / 1000000000000) (-14418148489 / 1000000000000), orderedInterval (65074771497 / 1000000000000) (65074771622 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_stateChecks7 :
    compactCertificate393.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (308721761310441 / 4000000000000)) (orderedInterval (49436626729 / 1000000000000) (49436638542 / 1000000000000), orderedInterval (-76507854690 / 1000000000000) (-76507842877 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (838239636894323 / 4000000000000)) (orderedInterval (7800163766 / 1000000000000) (7800163791 / 1000000000000), orderedInterval (-54581005150 / 1000000000000) (-54581005125 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1144544560868371 / 4000000000000)) (orderedInterval (-40586687666 / 1000000000000) (-40586687665 / 1000000000000), orderedInterval (-23962457800 / 1000000000000) (-23962457799 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_stateChecks8 :
    compactCertificate393.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (483957880006377 / 4000000000000)) (orderedInterval (49353109746 / 1000000000000) (49353158043 / 1000000000000), orderedInterval (-53364578912 / 1000000000000) (-53364530615 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1967261913687817 / 4000000000000)) (orderedInterval (21179595346 / 1000000000000) (21179597673 / 1000000000000), orderedInterval (-29105085050 / 1000000000000) (-29105082723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1314039787432103 / 4000000000000)) (orderedInterval (23839300568 / 1000000000000) (23839303653 / 1000000000000), orderedInterval (-37044252858 / 1000000000000) (-37044249773 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_states : ∀ j,
    BesselStateValid (compactCertificate393.point j) (compactCertificate393.state j) :=
  compactCertificate393.statesValid_of_checks3 compactCertificate393_stateChecks0
    compactCertificate393_stateChecks1 compactCertificate393_stateChecks2
    compactCertificate393_stateChecks3 compactCertificate393_stateChecks4
    compactCertificate393_stateChecks5 compactCertificate393_stateChecks6
    compactCertificate393_stateChecks7 compactCertificate393_stateChecks8

theorem compactCertificate393_chunkChecks0_0 :
    compactCertificate393.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (529 / 2) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (48270331964 / 1000000000000) (48270331972 / 1000000000000), orderedInterval (8675226419 / 1000000000000) (8675226426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (779318011439629 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42394187115 / 1000000000000) (42394187116 / 1000000000000), orderedInterval (38235766541 / 1000000000000) (38235766542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (252015432800557 / 800000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44830500472 / 1000000000000) (44830500885 / 1000000000000), orderedInterval (-3405083681 / 1000000000000) (-3405083268 / 1000000000000)))) (orderedInterval (22158406235 / 1000000000000) (22158406282 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (227403052091303 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (93590647145 / 1000000000000) (93590647146 / 1000000000000), orderedInterval (48559456205 / 1000000000000) (48559456206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (610836584802491 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (27753127698 / 1000000000000) (27753129695 / 1000000000000), orderedInterval (-58388523219 / 1000000000000) (-58388521223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1658540152376847 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26127719480 / 1000000000000) (26127719481 / 1000000000000), orderedInterval (29169797826 / 1000000000000) (29169797827 / 1000000000000)))) (orderedInterval (-1859487231 / 1000000000000) (-1859487125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1221673169605511 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45418105202 / 1000000000000) (-45418105168 / 1000000000000), orderedInterval (-4574544046 / 1000000000000) (-4574544013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2093357798871203 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17371323993 / 1000000000000) (17371324532 / 1000000000000), orderedInterval (-30260506304 / 1000000000000) (-30260505764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1541957880006377 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5725189608 / 1000000000000) (5725189615 / 1000000000000), orderedInterval (-40240270723 / 1000000000000) (-40240270716 / 1000000000000)))) (orderedInterval (-397434622 / 1000000000000) (-397434590 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_chunkChecks0_1 :
    compactCertificate393.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2365759920194471 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32788330944 / 1000000000000) (32788332346 / 1000000000000), orderedInterval (-1174193725 / 1000000000000) (-1174192323 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1365872126762159 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7752924750 / 1000000000000) (7752924767 / 1000000000000), orderedInterval (-42487878726 / 1000000000000) (-42487878710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2423764057705531 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12587265797 / 1000000000000) (-12587265796 / 1000000000000), orderedInterval (-29859178757 / 1000000000000) (-29859178756 / 1000000000000)))) (orderedInterval (-7041016896 / 1000000000000) (-7041016540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2264594785112839 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33277360522 / 1000000000000) (33277360685 / 1000000000000), orderedInterval (4104778850 / 1000000000000) (4104779013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1616121695087287 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17263686321 / 1000000000000) (17263686791 / 1000000000000), orderedInterval (-35765437247 / 1000000000000) (-35765436777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1832509754407473 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8862281019 / 1000000000000) (8862281020 / 1000000000000), orderedInterval (36199077385 / 1000000000000) (36199077386 / 1000000000000)))) (orderedInterval (986896339 / 1000000000000) (986896419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1527755584479137 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21351248330 / 1000000000000) (-21351246542 / 1000000000000), orderedInterval (34826447331 / 1000000000000) (34826449118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1349818391065877 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37727238042 / 1000000000000) (-37727187979 / 1000000000000), orderedInterval (21577743551 / 1000000000000) (21577793614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (391229981429823 / 800000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9478796029 / 1000000000000) (-9478796009 / 1000000000000), orderedInterval (34822536151 / 1000000000000) (34822536170 / 1000000000000)))) (orderedInterval (1669749798 / 1000000000000) (1669752710 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_chunkChecks0_2 :
    compactCertificate393.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1082162717940781 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44250533491 / 1000000000000) (44250533492 / 1000000000000), orderedInterval (19793490324 / 1000000000000) (19793490325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (917361320622341 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37385938390 / 1000000000000) (-37385938389 / 1000000000000), orderedInterval (-37042140066 / 1000000000000) (-37042140065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (574042119993623 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14418148614 / 1000000000000) (-14418148489 / 1000000000000), orderedInterval (65074771497 / 1000000000000) (65074771622 / 1000000000000)))) (orderedInterval (-5428670161 / 1000000000000) (-5428670090 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (308721761310441 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49436626729 / 1000000000000) (49436638542 / 1000000000000), orderedInterval (-76507854690 / 1000000000000) (-76507842877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (838239636894323 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7800163766 / 1000000000000) (7800163791 / 1000000000000), orderedInterval (-54581005150 / 1000000000000) (-54581005125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1144544560868371 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40586687666 / 1000000000000) (-40586687665 / 1000000000000), orderedInterval (-23962457800 / 1000000000000) (-23962457799 / 1000000000000)))) (orderedInterval (2020703309 / 1000000000000) (2020703560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (483957880006377 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (49353109746 / 1000000000000) (49353158043 / 1000000000000), orderedInterval (-53364578912 / 1000000000000) (-53364530615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1967261913687817 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21179595346 / 1000000000000) (21179597673 / 1000000000000), orderedInterval (-29105085050 / 1000000000000) (-29105082723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1314039787432103 / 4000000000000) 0 (IntervalRat.scale (529 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23839300568 / 1000000000000) (23839303653 / 1000000000000), orderedInterval (-37044252858 / 1000000000000) (-37044249773 / 1000000000000)))) (orderedInterval (-5899425941 / 1000000000000) (-5899424808 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_chunkChecks0 :
    compactCertificate393.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate393.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate393_chunkChecks0_0
    compactCertificate393_chunkChecks0_1 compactCertificate393_chunkChecks0_2

theorem compactCertificate393_chunkChecks1_0 :
    compactCertificate393.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (529 / 2) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (48270331964 / 1000000000000) (48270331972 / 1000000000000), orderedInterval (8675226419 / 1000000000000) (8675226426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (779318011439629 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42394187115 / 1000000000000) (42394187116 / 1000000000000), orderedInterval (38235766541 / 1000000000000) (38235766542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (252015432800557 / 800000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44830500472 / 1000000000000) (44830500885 / 1000000000000), orderedInterval (-3405083681 / 1000000000000) (-3405083268 / 1000000000000)))) (orderedInterval (3463014071 / 1000000000000) (3463014124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (227403052091303 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (93590647145 / 1000000000000) (93590647146 / 1000000000000), orderedInterval (48559456205 / 1000000000000) (48559456206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (610836584802491 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (27753127698 / 1000000000000) (27753129695 / 1000000000000), orderedInterval (-58388523219 / 1000000000000) (-58388521223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1658540152376847 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26127719480 / 1000000000000) (26127719481 / 1000000000000), orderedInterval (29169797826 / 1000000000000) (29169797827 / 1000000000000)))) (orderedInterval (-4594794033 / 1000000000000) (-4594793954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1221673169605511 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45418105202 / 1000000000000) (-45418105168 / 1000000000000), orderedInterval (-4574544046 / 1000000000000) (-4574544013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2093357798871203 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17371323993 / 1000000000000) (17371324532 / 1000000000000), orderedInterval (-30260506304 / 1000000000000) (-30260505764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1541957880006377 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5725189608 / 1000000000000) (5725189615 / 1000000000000), orderedInterval (-40240270723 / 1000000000000) (-40240270716 / 1000000000000)))) (orderedInterval (429346849 / 1000000000000) (429346908 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_chunkChecks1_1 :
    compactCertificate393.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2365759920194471 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32788330944 / 1000000000000) (32788332346 / 1000000000000), orderedInterval (-1174193725 / 1000000000000) (-1174192323 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1365872126762159 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7752924750 / 1000000000000) (7752924767 / 1000000000000), orderedInterval (-42487878726 / 1000000000000) (-42487878710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2423764057705531 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12587265797 / 1000000000000) (-12587265796 / 1000000000000), orderedInterval (-29859178757 / 1000000000000) (-29859178756 / 1000000000000)))) (orderedInterval (-13321575459 / 1000000000000) (-13321574682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2264594785112839 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33277360522 / 1000000000000) (33277360685 / 1000000000000), orderedInterval (4104778850 / 1000000000000) (4104779013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1616121695087287 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17263686321 / 1000000000000) (17263686791 / 1000000000000), orderedInterval (-35765437247 / 1000000000000) (-35765436777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1832509754407473 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8862281019 / 1000000000000) (8862281020 / 1000000000000), orderedInterval (36199077385 / 1000000000000) (36199077386 / 1000000000000)))) (orderedInterval (-5642122899 / 1000000000000) (-5642122773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1527755584479137 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21351248330 / 1000000000000) (-21351246542 / 1000000000000), orderedInterval (34826447331 / 1000000000000) (34826449118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1349818391065877 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37727238042 / 1000000000000) (-37727187979 / 1000000000000), orderedInterval (21577743551 / 1000000000000) (21577793614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (391229981429823 / 800000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9478796029 / 1000000000000) (-9478796009 / 1000000000000), orderedInterval (34822536151 / 1000000000000) (34822536170 / 1000000000000)))) (orderedInterval (653791254 / 1000000000000) (653794977 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_chunkChecks1_2 :
    compactCertificate393.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1082162717940781 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44250533491 / 1000000000000) (44250533492 / 1000000000000), orderedInterval (19793490324 / 1000000000000) (19793490325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (917361320622341 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37385938390 / 1000000000000) (-37385938389 / 1000000000000), orderedInterval (-37042140066 / 1000000000000) (-37042140065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (574042119993623 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14418148614 / 1000000000000) (-14418148489 / 1000000000000), orderedInterval (65074771497 / 1000000000000) (65074771622 / 1000000000000)))) (orderedInterval (-269765875 / 1000000000000) (-269765811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (308721761310441 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49436626729 / 1000000000000) (49436638542 / 1000000000000), orderedInterval (-76507854690 / 1000000000000) (-76507842877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (838239636894323 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7800163766 / 1000000000000) (7800163791 / 1000000000000), orderedInterval (-54581005150 / 1000000000000) (-54581005125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1144544560868371 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40586687666 / 1000000000000) (-40586687665 / 1000000000000), orderedInterval (-23962457800 / 1000000000000) (-23962457799 / 1000000000000)))) (orderedInterval (3379974615 / 1000000000000) (3379974708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (483957880006377 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (49353109746 / 1000000000000) (49353158043 / 1000000000000), orderedInterval (-53364578912 / 1000000000000) (-53364530615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1967261913687817 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21179595346 / 1000000000000) (21179597673 / 1000000000000), orderedInterval (-29105085050 / 1000000000000) (-29105082723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1314039787432103 / 4000000000000) 1 (IntervalRat.scale (529 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23839300568 / 1000000000000) (23839303653 / 1000000000000), orderedInterval (-37044252858 / 1000000000000) (-37044249773 / 1000000000000)))) (orderedInterval (12890709991 / 1000000000000) (12890711298 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_chunkChecks1 :
    compactCertificate393.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate393.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate393_chunkChecks1_0
    compactCertificate393_chunkChecks1_1 compactCertificate393_chunkChecks1_2

theorem compactCertificate393_chunkChecks2_0 :
    compactCertificate393.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (529 / 2) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (48270331964 / 1000000000000) (48270331972 / 1000000000000), orderedInterval (8675226419 / 1000000000000) (8675226426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (779318011439629 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42394187115 / 1000000000000) (42394187116 / 1000000000000), orderedInterval (38235766541 / 1000000000000) (38235766542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (252015432800557 / 800000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44830500472 / 1000000000000) (44830500885 / 1000000000000), orderedInterval (-3405083681 / 1000000000000) (-3405083268 / 1000000000000)))) (orderedInterval (-23091695878 / 1000000000000) (-23091695816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (227403052091303 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (93590647145 / 1000000000000) (93590647146 / 1000000000000), orderedInterval (48559456205 / 1000000000000) (48559456206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (610836584802491 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (27753127698 / 1000000000000) (27753129695 / 1000000000000), orderedInterval (-58388523219 / 1000000000000) (-58388521223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1658540152376847 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26127719480 / 1000000000000) (26127719481 / 1000000000000), orderedInterval (29169797826 / 1000000000000) (29169797827 / 1000000000000)))) (orderedInterval (4290958905 / 1000000000000) (4290958980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1221673169605511 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45418105202 / 1000000000000) (-45418105168 / 1000000000000), orderedInterval (-4574544046 / 1000000000000) (-4574544013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2093357798871203 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17371323993 / 1000000000000) (17371324532 / 1000000000000), orderedInterval (-30260506304 / 1000000000000) (-30260505764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1541957880006377 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5725189608 / 1000000000000) (5725189615 / 1000000000000), orderedInterval (-40240270723 / 1000000000000) (-40240270716 / 1000000000000)))) (orderedInterval (1802056567 / 1000000000000) (1802056679 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_chunkChecks2_1 :
    compactCertificate393.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2365759920194471 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32788330944 / 1000000000000) (32788332346 / 1000000000000), orderedInterval (-1174193725 / 1000000000000) (-1174192323 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1365872126762159 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7752924750 / 1000000000000) (7752924767 / 1000000000000), orderedInterval (-42487878726 / 1000000000000) (-42487878710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2423764057705531 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12587265797 / 1000000000000) (-12587265796 / 1000000000000), orderedInterval (-29859178757 / 1000000000000) (-29859178756 / 1000000000000)))) (orderedInterval (37614302992 / 1000000000000) (37614304708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2264594785112839 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33277360522 / 1000000000000) (33277360685 / 1000000000000), orderedInterval (4104778850 / 1000000000000) (4104779013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1616121695087287 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17263686321 / 1000000000000) (17263686791 / 1000000000000), orderedInterval (-35765437247 / 1000000000000) (-35765436777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1832509754407473 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8862281019 / 1000000000000) (8862281020 / 1000000000000), orderedInterval (36199077385 / 1000000000000) (36199077386 / 1000000000000)))) (orderedInterval (-900909188 / 1000000000000) (-900908986 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1527755584479137 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21351248330 / 1000000000000) (-21351246542 / 1000000000000), orderedInterval (34826447331 / 1000000000000) (34826449118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1349818391065877 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37727238042 / 1000000000000) (-37727187979 / 1000000000000), orderedInterval (21577743551 / 1000000000000) (21577793614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (391229981429823 / 800000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9478796029 / 1000000000000) (-9478796009 / 1000000000000), orderedInterval (34822536151 / 1000000000000) (34822536170 / 1000000000000)))) (orderedInterval (-2172969646 / 1000000000000) (-2172964869 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_chunkChecks2_2 :
    compactCertificate393.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1082162717940781 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44250533491 / 1000000000000) (44250533492 / 1000000000000), orderedInterval (19793490324 / 1000000000000) (19793490325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (917361320622341 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37385938390 / 1000000000000) (-37385938389 / 1000000000000), orderedInterval (-37042140066 / 1000000000000) (-37042140065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (574042119993623 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14418148614 / 1000000000000) (-14418148489 / 1000000000000), orderedInterval (65074771497 / 1000000000000) (65074771622 / 1000000000000)))) (orderedInterval (5950523689 / 1000000000000) (5950523749 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (308721761310441 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49436626729 / 1000000000000) (49436638542 / 1000000000000), orderedInterval (-76507854690 / 1000000000000) (-76507842877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (838239636894323 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7800163766 / 1000000000000) (7800163791 / 1000000000000), orderedInterval (-54581005150 / 1000000000000) (-54581005125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1144544560868371 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40586687666 / 1000000000000) (-40586687665 / 1000000000000), orderedInterval (-23962457800 / 1000000000000) (-23962457799 / 1000000000000)))) (orderedInterval (-3464184129 / 1000000000000) (-3464184081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (483957880006377 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (49353109746 / 1000000000000) (49353158043 / 1000000000000), orderedInterval (-53364578912 / 1000000000000) (-53364530615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1967261913687817 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21179595346 / 1000000000000) (21179597673 / 1000000000000), orderedInterval (-29105085050 / 1000000000000) (-29105082723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1314039787432103 / 4000000000000) 2 (IntervalRat.scale (529 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23839300568 / 1000000000000) (23839303653 / 1000000000000), orderedInterval (-37044252858 / 1000000000000) (-37044249773 / 1000000000000)))) (orderedInterval (12749563221 / 1000000000000) (12749564987 / 1000000000000))) = true
  rfl'

theorem compactCertificate393_chunkChecks2 :
    compactCertificate393.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate393.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate393_chunkChecks2_0
    compactCertificate393_chunkChecks2_1 compactCertificate393_chunkChecks2_2

theorem compactCertificate393_chunkChecks3_0 :
    compactCertificate393.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (529 / 2) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (48270331964 / 1000000000000) (48270331972 / 1000000000000), orderedInterval (8675226419 / 1000000000000) (8675226426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (779318011439629 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42394187115 / 1000000000000) (42394187116 / 1000000000000), orderedInterval (38235766541 / 1000000000000) (38235766542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (252015432800557 / 800000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44830500472 / 1000000000000) (44830500885 / 1000000000000), orderedInterval (-3405083681 / 1000000000000) (-3405083268 / 1000000000000)))) (orderedInterval (-3156026790 / 1000000000000) (-3156026718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (227403052091303 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (93590647145 / 1000000000000) (93590647146 / 1000000000000), orderedInterval (48559456205 / 1000000000000) (48559456206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (610836584802491 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (27753127698 / 1000000000000) (27753129695 / 1000000000000), orderedInterval (-58388523219 / 1000000000000) (-58388521223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1658540152376847 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26127719480 / 1000000000000) (26127719481 / 1000000000000), orderedInterval (29169797826 / 1000000000000) (29169797827 / 1000000000000)))) (orderedInterval (8387637244 / 1000000000000) (8387637334 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1221673169605511 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45418105202 / 1000000000000) (-45418105168 / 1000000000000), orderedInterval (-4574544046 / 1000000000000) (-4574544013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2093357798871203 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17371323993 / 1000000000000) (17371324532 / 1000000000000), orderedInterval (-30260506304 / 1000000000000) (-30260505764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1541957880006377 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5725189608 / 1000000000000) (5725189615 / 1000000000000), orderedInterval (-40240270723 / 1000000000000) (-40240270716 / 1000000000000)))) (orderedInterval (-4225840904 / 1000000000000) (-4225840690 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate393_chunkChecks3_1 :
    compactCertificate393.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2365759920194471 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32788330944 / 1000000000000) (32788332346 / 1000000000000), orderedInterval (-1174193725 / 1000000000000) (-1174192323 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1365872126762159 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7752924750 / 1000000000000) (7752924767 / 1000000000000), orderedInterval (-42487878726 / 1000000000000) (-42487878710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2423764057705531 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12587265797 / 1000000000000) (-12587265796 / 1000000000000), orderedInterval (-29859178757 / 1000000000000) (-29859178756 / 1000000000000)))) (orderedInterval (55332018797 / 1000000000000) (55332022612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2264594785112839 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33277360522 / 1000000000000) (33277360685 / 1000000000000), orderedInterval (4104778850 / 1000000000000) (4104779013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1616121695087287 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17263686321 / 1000000000000) (17263686791 / 1000000000000), orderedInterval (-35765437247 / 1000000000000) (-35765436777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1832509754407473 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8862281019 / 1000000000000) (8862281020 / 1000000000000), orderedInterval (36199077385 / 1000000000000) (36199077386 / 1000000000000)))) (orderedInterval (13736403795 / 1000000000000) (13736404127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1527755584479137 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21351248330 / 1000000000000) (-21351246542 / 1000000000000), orderedInterval (34826447331 / 1000000000000) (34826449118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1349818391065877 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37727238042 / 1000000000000) (-37727187979 / 1000000000000), orderedInterval (21577743551 / 1000000000000) (21577793614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (391229981429823 / 800000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9478796029 / 1000000000000) (-9478796009 / 1000000000000), orderedInterval (34822536151 / 1000000000000) (34822536170 / 1000000000000)))) (orderedInterval (-4273643519 / 1000000000000) (-4273637402 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate393_chunkChecks3_2 :
    compactCertificate393.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1082162717940781 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44250533491 / 1000000000000) (44250533492 / 1000000000000), orderedInterval (19793490324 / 1000000000000) (19793490325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (917361320622341 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37385938390 / 1000000000000) (-37385938389 / 1000000000000), orderedInterval (-37042140066 / 1000000000000) (-37042140065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (574042119993623 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14418148614 / 1000000000000) (-14418148489 / 1000000000000), orderedInterval (65074771497 / 1000000000000) (65074771622 / 1000000000000)))) (orderedInterval (1659061375 / 1000000000000) (1659061434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (308721761310441 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49436626729 / 1000000000000) (49436638542 / 1000000000000), orderedInterval (-76507854690 / 1000000000000) (-76507842877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (838239636894323 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7800163766 / 1000000000000) (7800163791 / 1000000000000), orderedInterval (-54581005150 / 1000000000000) (-54581005125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1144544560868371 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40586687666 / 1000000000000) (-40586687665 / 1000000000000), orderedInterval (-23962457800 / 1000000000000) (-23962457799 / 1000000000000)))) (orderedInterval (-2962780632 / 1000000000000) (-2962780597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (483957880006377 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (49353109746 / 1000000000000) (49353158043 / 1000000000000), orderedInterval (-53364578912 / 1000000000000) (-53364530615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1967261913687817 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21179595346 / 1000000000000) (21179597673 / 1000000000000), orderedInterval (-29105085050 / 1000000000000) (-29105082723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1314039787432103 / 4000000000000) 3 (IntervalRat.scale (529 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23839300568 / 1000000000000) (23839303653 / 1000000000000), orderedInterval (-37044252858 / 1000000000000) (-37044249773 / 1000000000000)))) (orderedInterval (-28564665969 / 1000000000000) (-28564663374 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate393_chunkChecks3 :
    compactCertificate393.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate393.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate393_chunkChecks3_0
    compactCertificate393_chunkChecks3_1 compactCertificate393_chunkChecks3_2

theorem compactCertificate393_chunkChecks4_0 :
    compactCertificate393.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (529 / 2) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (48270331964 / 1000000000000) (48270331972 / 1000000000000), orderedInterval (8675226419 / 1000000000000) (8675226426 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (779318011439629 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42394187115 / 1000000000000) (42394187116 / 1000000000000), orderedInterval (38235766541 / 1000000000000) (38235766542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (252015432800557 / 800000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (44830500472 / 1000000000000) (44830500885 / 1000000000000), orderedInterval (-3405083681 / 1000000000000) (-3405083268 / 1000000000000)))) (orderedInterval (24565691698 / 1000000000000) (24565691783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (227403052091303 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (93590647145 / 1000000000000) (93590647146 / 1000000000000), orderedInterval (48559456205 / 1000000000000) (48559456206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (610836584802491 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (27753127698 / 1000000000000) (27753129695 / 1000000000000), orderedInterval (-58388523219 / 1000000000000) (-58388521223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1658540152376847 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (26127719480 / 1000000000000) (26127719481 / 1000000000000), orderedInterval (29169797826 / 1000000000000) (29169797827 / 1000000000000)))) (orderedInterval (-11169741160 / 1000000000000) (-11169741036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1221673169605511 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45418105202 / 1000000000000) (-45418105168 / 1000000000000), orderedInterval (-4574544046 / 1000000000000) (-4574544013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2093357798871203 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17371323993 / 1000000000000) (17371324532 / 1000000000000), orderedInterval (-30260506304 / 1000000000000) (-30260505764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1541957880006377 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (5725189608 / 1000000000000) (5725189615 / 1000000000000), orderedInterval (-40240270723 / 1000000000000) (-40240270716 / 1000000000000)))) (orderedInterval (-7555475520 / 1000000000000) (-7555475108 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate393_chunkChecks4_1 :
    compactCertificate393.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2365759920194471 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (32788330944 / 1000000000000) (32788332346 / 1000000000000), orderedInterval (-1174193725 / 1000000000000) (-1174192323 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1365872126762159 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (7752924750 / 1000000000000) (7752924767 / 1000000000000), orderedInterval (-42487878726 / 1000000000000) (-42487878710 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2423764057705531 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12587265797 / 1000000000000) (-12587265796 / 1000000000000), orderedInterval (-29859178757 / 1000000000000) (-29859178756 / 1000000000000)))) (orderedInterval (-193759511206 / 1000000000000) (-193759502683 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2264594785112839 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33277360522 / 1000000000000) (33277360685 / 1000000000000), orderedInterval (4104778850 / 1000000000000) (4104779013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1616121695087287 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17263686321 / 1000000000000) (17263686791 / 1000000000000), orderedInterval (-35765437247 / 1000000000000) (-35765436777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1832509754407473 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8862281019 / 1000000000000) (8862281020 / 1000000000000), orderedInterval (36199077385 / 1000000000000) (36199077386 / 1000000000000)))) (orderedInterval (-4229571364 / 1000000000000) (-4229570809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1527755584479137 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21351248330 / 1000000000000) (-21351246542 / 1000000000000), orderedInterval (34826447331 / 1000000000000) (34826449118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1349818391065877 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37727238042 / 1000000000000) (-37727187979 / 1000000000000), orderedInterval (21577743551 / 1000000000000) (21577793614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (391229981429823 / 800000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9478796029 / 1000000000000) (-9478796009 / 1000000000000), orderedInterval (34822536151 / 1000000000000) (34822536170 / 1000000000000)))) (orderedInterval (1844370942 / 1000000000000) (1844378807 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate393_chunkChecks4_2 :
    compactCertificate393.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1082162717940781 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (44250533491 / 1000000000000) (44250533492 / 1000000000000), orderedInterval (19793490324 / 1000000000000) (19793490325 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (917361320622341 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37385938390 / 1000000000000) (-37385938389 / 1000000000000), orderedInterval (-37042140066 / 1000000000000) (-37042140065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (574042119993623 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-14418148614 / 1000000000000) (-14418148489 / 1000000000000), orderedInterval (65074771497 / 1000000000000) (65074771622 / 1000000000000)))) (orderedInterval (-6601259685 / 1000000000000) (-6601259627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (308721761310441 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (49436626729 / 1000000000000) (49436638542 / 1000000000000), orderedInterval (-76507854690 / 1000000000000) (-76507842877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (838239636894323 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7800163766 / 1000000000000) (7800163791 / 1000000000000), orderedInterval (-54581005150 / 1000000000000) (-54581005125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1144544560868371 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40586687666 / 1000000000000) (-40586687665 / 1000000000000), orderedInterval (-23962457800 / 1000000000000) (-23962457799 / 1000000000000)))) (orderedInterval (4206117395 / 1000000000000) (4206117428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (483957880006377 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (49353109746 / 1000000000000) (49353158043 / 1000000000000), orderedInterval (-53364578912 / 1000000000000) (-53364530615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1967261913687817 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21179595346 / 1000000000000) (21179597673 / 1000000000000), orderedInterval (-29105085050 / 1000000000000) (-29105082723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1314039787432103 / 4000000000000) 4 (IntervalRat.scale (529 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (23839300568 / 1000000000000) (23839303653 / 1000000000000), orderedInterval (-37044252858 / 1000000000000) (-37044249773 / 1000000000000)))) (orderedInterval (-31023209003 / 1000000000000) (-31023204954 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate393_chunkChecks4 :
    compactCertificate393.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate393.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate393_chunkChecks4_0
    compactCertificate393_chunkChecks4_1 compactCertificate393_chunkChecks4_2

theorem compactCertificate393_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate393.chunkCheck r b = true :=
  compactCertificate393.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate393_chunkChecks0
    · exact compactCertificate393_chunkChecks1
    · exact compactCertificate393_chunkChecks2
    · exact compactCertificate393_chunkChecks3
    · exact compactCertificate393_chunkChecks4)

theorem compactCertificate393_coefficient0 :
    compactCertificate393.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate393_coefficient1 :
    compactCertificate393.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate393_coefficient2 :
    compactCertificate393.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate393_coefficient3 :
    compactCertificate393.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate393_coefficient4 :
    compactCertificate393.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate393_coefficients : ∀ r : Fin 5,
    compactCertificate393.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate393_coefficient0
  · exact compactCertificate393_coefficient1
  · exact compactCertificate393_coefficient2
  · exact compactCertificate393_coefficient3
  · exact compactCertificate393_coefficient4

theorem compactCertificate393_lower : (1 : ℚ) ≤ compactCertificate393.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate393, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate393_proves {t : ℝ} (ht : t ∈ compactCertificate393.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate393.proves compactCertificate393_states compactCertificate393_chunks
    compactCertificate393_coefficients compactCertificate393_lower ht

end Erdos232
