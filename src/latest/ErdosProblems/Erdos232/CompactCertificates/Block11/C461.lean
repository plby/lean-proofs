/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate461 : CompactCertificate where
  left := 332
  right := 333
  center := 665 / 2
  grid := fun i =>
    match i.val with
    | 0 => 106
    | 1 => 78
    | 2 => 126
    | 3 => 23
    | 4 => 61
    | 5 => 166
    | 6 => 122
    | 7 => 210
    | 8 => 154
    | 9 => 237
    | 10 => 137
    | 11 => 243
    | 12 => 227
    | 13 => 162
    | 14 => 183
    | 15 => 153
    | 16 => 135
    | 17 => 196
    | 18 => 108
    | 19 => 92
    | 20 => 57
    | 21 => 31
    | 22 => 84
    | 23 => 115
    | 24 => 48
    | 25 => 197
    | _ => 132
  point := fun i =>
    match i.val with
    | 0 => 665 / 2
    | 1 => 195934396070833 / 800000000000
    | 2 => 63361157963089 / 160000000000
    | 3 => 57173168106131 / 800000000000
    | 4 => 153575171604407 / 800000000000
    | 5 => 416986465531419 / 800000000000
    | 6 => 307150343208947 / 800000000000
    | 7 => 526307348298431 / 800000000000
    | 8 => 387675610663229 / 800000000000
    | 9 => 594794082014867 / 800000000000
    | 10 => 343404523363643 / 800000000000
    | 11 => 609377352882487 / 800000000000
    | 12 => 569359369414003 / 800000000000
    | 13 => 406321711619299 / 800000000000
    | 14 => 460725514813221 / 800000000000
    | 15 => 384104901201749 / 800000000000
    | 16 => 339368328944729 / 800000000000
    | 17 => 98362169244171 / 160000000000
    | 18 => 272074936646737 / 800000000000
    | 19 => 230640936942857 / 800000000000
    | 20 => 144324389336771 / 800000000000
    | 21 => 77618136586557 / 800000000000
    | 22 => 210748339710671 / 800000000000
    | 23 => 287758840445167 / 800000000000
    | 24 => 121675610663229 / 800000000000
    | 25 => 494604602118109 / 800000000000
    | _ => 330372952227731 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (11932548457 / 1000000000000) (11932548458 / 1000000000000), orderedInterval (42080299338 / 1000000000000) (42080299339 / 1000000000000))
    | 1 => (orderedInterval (31204651451 / 1000000000000) (31204651452 / 1000000000000), orderedInterval (40254891746 / 1000000000000) (40254891747 / 1000000000000))
    | 2 => (orderedInterval (32652084024 / 1000000000000) (32652084025 / 1000000000000), orderedInterval (23227578697 / 1000000000000) (23227578698 / 1000000000000))
    | 3 => (orderedInterval (615512275 / 1000000000000) (615512284 / 1000000000000), orderedInterval (-94385399200 / 1000000000000) (-94385399191 / 1000000000000))
    | 4 => (orderedInterval (-51747384390 / 1000000000000) (-51747384389 / 1000000000000), orderedInterval (-25133091703 / 1000000000000) (-25133091702 / 1000000000000))
    | 5 => (orderedInterval (17178481733 / 1000000000000) (17178481734 / 1000000000000), orderedInterval (30418248100 / 1000000000000) (30418248101 / 1000000000000))
    | 6 => (orderedInterval (40416998103 / 1000000000000) (40416998147 / 1000000000000), orderedInterval (4906892906 / 1000000000000) (4906892951 / 1000000000000))
    | 7 => (orderedInterval (-27213502060 / 1000000000000) (-27213430420 / 1000000000000), orderedInterval (15090637201 / 1000000000000) (15090708841 / 1000000000000))
    | 8 => (orderedInterval (36244982975 / 1000000000000) (36244983476 / 1000000000000), orderedInterval (-167465567 / 1000000000000) (-167465067 / 1000000000000))
    | 9 => (orderedInterval (8076167185 / 1000000000000) (8076167188 / 1000000000000), orderedInterval (-28130711305 / 1000000000000) (-28130711302 / 1000000000000))
    | 10 => (orderedInterval (13473755359 / 1000000000000) (13473755475 / 1000000000000), orderedInterval (-36092515678 / 1000000000000) (-36092515561 / 1000000000000))
    | 11 => (orderedInterval (22647261847 / 1000000000000) (22647271413 / 1000000000000), orderedInterval (-17983330062 / 1000000000000) (-17983320496 / 1000000000000))
    | 12 => (orderedInterval (18268641894 / 1000000000000) (18268642777 / 1000000000000), orderedInterval (-23693281441 / 1000000000000) (-23693280558 / 1000000000000))
    | 13 => (orderedInterval (-8783679289 / 1000000000000) (-8783679275 / 1000000000000), orderedInterval (34305549172 / 1000000000000) (34305549185 / 1000000000000))
    | 14 => (orderedInterval (-32518678202 / 1000000000000) (-32518669674 / 1000000000000), orderedInterval (6953313157 / 1000000000000) (6953321685 / 1000000000000))
    | 15 => (orderedInterval (-9100083099 / 1000000000000) (-9100083098 / 1000000000000), orderedInterval (-35248403198 / 1000000000000) (-35248403197 / 1000000000000))
    | 16 => (orderedInterval (-29870207999 / 1000000000000) (-29870207998 / 1000000000000), orderedInterval (-24632331996 / 1000000000000) (-24632331995 / 1000000000000))
    | 17 => (orderedInterval (-6500607526 / 1000000000000) (-6500607523 / 1000000000000), orderedInterval (31521864380 / 1000000000000) (31521864383 / 1000000000000))
    | 18 => (orderedInterval (43259914996 / 1000000000000) (43259915224 / 1000000000000), orderedInterval (-751427001 / 1000000000000) (-751426773 / 1000000000000))
    | 19 => (orderedInterval (2799563722 / 1000000000000) (2799563723 / 1000000000000), orderedInterval (46902946836 / 1000000000000) (46902946837 / 1000000000000))
    | 20 => (orderedInterval (-50686201102 / 1000000000000) (-50686168870 / 1000000000000), orderedInterval (31119994438 / 1000000000000) (31120026669 / 1000000000000))
    | 21 => (orderedInterval (-32837982395 / 1000000000000) (-32837982394 / 1000000000000), orderedInterval (-73879964284 / 1000000000000) (-73879964283 / 1000000000000))
    | 22 => (orderedInterval (15769789983 / 1000000000000) (15769789984 / 1000000000000), orderedInterval (46531036948 / 1000000000000) (46531036949 / 1000000000000))
    | 23 => (orderedInterval (30165941356 / 1000000000000) (30165967194 / 1000000000000), orderedInterval (-29365747466 / 1000000000000) (-29365721627 / 1000000000000))
    | 24 => (orderedInterval (56405279426 / 1000000000000) (56405299504 / 1000000000000), orderedInterval (-31873238527 / 1000000000000) (-31873218450 / 1000000000000))
    | 25 => (orderedInterval (-4706327255 / 1000000000000) (-4706327254 / 1000000000000), orderedInterval (-31738181143 / 1000000000000) (-31738181142 / 1000000000000))
    | _ => (orderedInterval (-31682668001 / 1000000000000) (-31682597583 / 1000000000000), orderedInterval (23228597618 / 1000000000000) (23228668036 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (6936472802 / 1000000000000) (6936472826 / 1000000000000)
      | 1 => orderedInterval (-3117277346 / 1000000000000) (-3117277306 / 1000000000000)
      | 2 => orderedInterval (1715340793 / 1000000000000) (1715343034 / 1000000000000)
      | 3 => orderedInterval (2782698642 / 1000000000000) (2782700143 / 1000000000000)
      | 4 => orderedInterval (-995852088 / 1000000000000) (-995851987 / 1000000000000)
      | 5 => orderedInterval (1437846742 / 1000000000000) (1437846775 / 1000000000000)
      | 6 => orderedInterval (-8725491724 / 1000000000000) (-8725490555 / 1000000000000)
      | 7 => orderedInterval (-2063295520 / 1000000000000) (-2063293500 / 1000000000000)
      | _ => orderedInterval (6667628632 / 1000000000000) (6667642057 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (18578809350 / 1000000000000) (18578809377 / 1000000000000)
      | 1 => orderedInterval (-3699561719 / 1000000000000) (-3699561673 / 1000000000000)
      | 2 => orderedInterval (-926853118 / 1000000000000) (-926848696 / 1000000000000)
      | 3 => orderedInterval (1868114290 / 1000000000000) (1868117691 / 1000000000000)
      | 4 => orderedInterval (5809940938 / 1000000000000) (5809941113 / 1000000000000)
      | 5 => orderedInterval (2702896577 / 1000000000000) (2702896624 / 1000000000000)
      | 6 => orderedInterval (-1629235259 / 1000000000000) (-1629234575 / 1000000000000)
      | 7 => orderedInterval (1996349913 / 1000000000000) (1996352092 / 1000000000000)
      | _ => orderedInterval (-697049987 / 1000000000000) (-697033392 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-7661176057 / 1000000000000) (-7661176026 / 1000000000000)
      | 1 => orderedInterval (3642270475 / 1000000000000) (3642270538 / 1000000000000)
      | 2 => orderedInterval (-5143878426 / 1000000000000) (-5143869678 / 1000000000000)
      | 3 => orderedInterval (-11390496744 / 1000000000000) (-11390488995 / 1000000000000)
      | 4 => orderedInterval (2937936605 / 1000000000000) (2937936918 / 1000000000000)
      | 5 => orderedInterval (-2002414083 / 1000000000000) (-2002414014 / 1000000000000)
      | 6 => orderedInterval (7846274850 / 1000000000000) (7846275273 / 1000000000000)
      | 7 => orderedInterval (2872522169 / 1000000000000) (2872524529 / 1000000000000)
      | _ => orderedInterval (-10563441878 / 1000000000000) (-10563421231 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-19108556202 / 1000000000000) (-19108556166 / 1000000000000)
      | 1 => orderedInterval (8485762834 / 1000000000000) (8485762929 / 1000000000000)
      | 2 => orderedInterval (3633376376 / 1000000000000) (3633393661 / 1000000000000)
      | 3 => orderedInterval (-19360545247 / 1000000000000) (-19360527568 / 1000000000000)
      | 4 => orderedInterval (-15583006711 / 1000000000000) (-15583006145 / 1000000000000)
      | 5 => orderedInterval (-6796873771 / 1000000000000) (-6796873665 / 1000000000000)
      | 6 => orderedInterval (1416532830 / 1000000000000) (1416533109 / 1000000000000)
      | 7 => orderedInterval (-2366763273 / 1000000000000) (-2366760721 / 1000000000000)
      | _ => orderedInterval (-8208935856 / 1000000000000) (-8208910175 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (8785385649 / 1000000000000) (8785385691 / 1000000000000)
      | 1 => orderedInterval (-7635791743 / 1000000000000) (-7635791598 / 1000000000000)
      | 2 => orderedInterval (16794547368 / 1000000000000) (16794581585 / 1000000000000)
      | 3 => orderedInterval (55688059187 / 1000000000000) (55688099627 / 1000000000000)
      | 4 => orderedInterval (-9870106896 / 1000000000000) (-9870105850 / 1000000000000)
      | 5 => orderedInterval (2167870630 / 1000000000000) (2167870799 / 1000000000000)
      | 6 => orderedInterval (-7811804302 / 1000000000000) (-7811804099 / 1000000000000)
      | 7 => orderedInterval (-3288630960 / 1000000000000) (-3288628194 / 1000000000000)
      | _ => orderedInterval (18788823003 / 1000000000000) (18788855073 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (4638070933 / 1000000000000) (4638091487 / 1000000000000)
    | 1 => orderedInterval (24003410985 / 1000000000000) (24003438561 / 1000000000000)
    | 2 => orderedInterval (-19462403089 / 1000000000000) (-19462362686 / 1000000000000)
    | 3 => orderedInterval (-57889009020 / 1000000000000) (-57888944741 / 1000000000000)
    | _ => orderedInterval (73618351936 / 1000000000000) (73618463034 / 1000000000000)

theorem compactCertificate461_stateChecks0 :
    compactCertificate461.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (665 / 2)) (orderedInterval (11932548457 / 1000000000000) (11932548458 / 1000000000000), orderedInterval (42080299338 / 1000000000000) (42080299339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (195934396070833 / 800000000000)) (orderedInterval (31204651451 / 1000000000000) (31204651452 / 1000000000000), orderedInterval (40254891746 / 1000000000000) (40254891747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (63361157963089 / 160000000000)) (orderedInterval (32652084024 / 1000000000000) (32652084025 / 1000000000000), orderedInterval (23227578697 / 1000000000000) (23227578698 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_stateChecks1 :
    compactCertificate461.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (57173168106131 / 800000000000)) (orderedInterval (615512275 / 1000000000000) (615512284 / 1000000000000), orderedInterval (-94385399200 / 1000000000000) (-94385399191 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (153575171604407 / 800000000000)) (orderedInterval (-51747384390 / 1000000000000) (-51747384389 / 1000000000000), orderedInterval (-25133091703 / 1000000000000) (-25133091702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (416986465531419 / 800000000000)) (orderedInterval (17178481733 / 1000000000000) (17178481734 / 1000000000000), orderedInterval (30418248100 / 1000000000000) (30418248101 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_stateChecks2 :
    compactCertificate461.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (307150343208947 / 800000000000)) (orderedInterval (40416998103 / 1000000000000) (40416998147 / 1000000000000), orderedInterval (4906892906 / 1000000000000) (4906892951 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (526307348298431 / 800000000000)) (orderedInterval (-27213502060 / 1000000000000) (-27213430420 / 1000000000000), orderedInterval (15090637201 / 1000000000000) (15090708841 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (387675610663229 / 800000000000)) (orderedInterval (36244982975 / 1000000000000) (36244983476 / 1000000000000), orderedInterval (-167465567 / 1000000000000) (-167465067 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_stateChecks3 :
    compactCertificate461.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (594794082014867 / 800000000000)) (orderedInterval (8076167185 / 1000000000000) (8076167188 / 1000000000000), orderedInterval (-28130711305 / 1000000000000) (-28130711302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (343404523363643 / 800000000000)) (orderedInterval (13473755359 / 1000000000000) (13473755475 / 1000000000000), orderedInterval (-36092515678 / 1000000000000) (-36092515561 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (609377352882487 / 800000000000)) (orderedInterval (22647261847 / 1000000000000) (22647271413 / 1000000000000), orderedInterval (-17983330062 / 1000000000000) (-17983320496 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_stateChecks4 :
    compactCertificate461.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (569359369414003 / 800000000000)) (orderedInterval (18268641894 / 1000000000000) (18268642777 / 1000000000000), orderedInterval (-23693281441 / 1000000000000) (-23693280558 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (406321711619299 / 800000000000)) (orderedInterval (-8783679289 / 1000000000000) (-8783679275 / 1000000000000), orderedInterval (34305549172 / 1000000000000) (34305549185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (460725514813221 / 800000000000)) (orderedInterval (-32518678202 / 1000000000000) (-32518669674 / 1000000000000), orderedInterval (6953313157 / 1000000000000) (6953321685 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_stateChecks5 :
    compactCertificate461.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (384104901201749 / 800000000000)) (orderedInterval (-9100083099 / 1000000000000) (-9100083098 / 1000000000000), orderedInterval (-35248403198 / 1000000000000) (-35248403197 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (339368328944729 / 800000000000)) (orderedInterval (-29870207999 / 1000000000000) (-29870207998 / 1000000000000), orderedInterval (-24632331996 / 1000000000000) (-24632331995 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (98362169244171 / 160000000000)) (orderedInterval (-6500607526 / 1000000000000) (-6500607523 / 1000000000000), orderedInterval (31521864380 / 1000000000000) (31521864383 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_stateChecks6 :
    compactCertificate461.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (272074936646737 / 800000000000)) (orderedInterval (43259914996 / 1000000000000) (43259915224 / 1000000000000), orderedInterval (-751427001 / 1000000000000) (-751426773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (230640936942857 / 800000000000)) (orderedInterval (2799563722 / 1000000000000) (2799563723 / 1000000000000), orderedInterval (46902946836 / 1000000000000) (46902946837 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (144324389336771 / 800000000000)) (orderedInterval (-50686201102 / 1000000000000) (-50686168870 / 1000000000000), orderedInterval (31119994438 / 1000000000000) (31120026669 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_stateChecks7 :
    compactCertificate461.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (77618136586557 / 800000000000)) (orderedInterval (-32837982395 / 1000000000000) (-32837982394 / 1000000000000), orderedInterval (-73879964284 / 1000000000000) (-73879964283 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (210748339710671 / 800000000000)) (orderedInterval (15769789983 / 1000000000000) (15769789984 / 1000000000000), orderedInterval (46531036948 / 1000000000000) (46531036949 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (287758840445167 / 800000000000)) (orderedInterval (30165941356 / 1000000000000) (30165967194 / 1000000000000), orderedInterval (-29365747466 / 1000000000000) (-29365721627 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_stateChecks8 :
    compactCertificate461.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (121675610663229 / 800000000000)) (orderedInterval (56405279426 / 1000000000000) (56405299504 / 1000000000000), orderedInterval (-31873238527 / 1000000000000) (-31873218450 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (494604602118109 / 800000000000)) (orderedInterval (-4706327255 / 1000000000000) (-4706327254 / 1000000000000), orderedInterval (-31738181143 / 1000000000000) (-31738181142 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (330372952227731 / 800000000000)) (orderedInterval (-31682668001 / 1000000000000) (-31682597583 / 1000000000000), orderedInterval (23228597618 / 1000000000000) (23228668036 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_states : ∀ j,
    BesselStateValid (compactCertificate461.point j) (compactCertificate461.state j) :=
  compactCertificate461.statesValid_of_checks3 compactCertificate461_stateChecks0
    compactCertificate461_stateChecks1 compactCertificate461_stateChecks2
    compactCertificate461_stateChecks3 compactCertificate461_stateChecks4
    compactCertificate461_stateChecks5 compactCertificate461_stateChecks6
    compactCertificate461_stateChecks7 compactCertificate461_stateChecks8

theorem compactCertificate461_chunkChecks0_0 :
    compactCertificate461.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (665 / 2) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11932548457 / 1000000000000) (11932548458 / 1000000000000), orderedInterval (42080299338 / 1000000000000) (42080299339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (195934396070833 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31204651451 / 1000000000000) (31204651452 / 1000000000000), orderedInterval (40254891746 / 1000000000000) (40254891747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (63361157963089 / 160000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32652084024 / 1000000000000) (32652084025 / 1000000000000), orderedInterval (23227578697 / 1000000000000) (23227578698 / 1000000000000)))) (orderedInterval (6936472802 / 1000000000000) (6936472826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (57173168106131 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (615512275 / 1000000000000) (615512284 / 1000000000000), orderedInterval (-94385399200 / 1000000000000) (-94385399191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (153575171604407 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51747384390 / 1000000000000) (-51747384389 / 1000000000000), orderedInterval (-25133091703 / 1000000000000) (-25133091702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (416986465531419 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (17178481733 / 1000000000000) (17178481734 / 1000000000000), orderedInterval (30418248100 / 1000000000000) (30418248101 / 1000000000000)))) (orderedInterval (-3117277346 / 1000000000000) (-3117277306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (307150343208947 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40416998103 / 1000000000000) (40416998147 / 1000000000000), orderedInterval (4906892906 / 1000000000000) (4906892951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (526307348298431 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27213502060 / 1000000000000) (-27213430420 / 1000000000000), orderedInterval (15090637201 / 1000000000000) (15090708841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (387675610663229 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36244982975 / 1000000000000) (36244983476 / 1000000000000), orderedInterval (-167465567 / 1000000000000) (-167465067 / 1000000000000)))) (orderedInterval (1715340793 / 1000000000000) (1715343034 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_chunkChecks0_1 :
    compactCertificate461.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (594794082014867 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8076167185 / 1000000000000) (8076167188 / 1000000000000), orderedInterval (-28130711305 / 1000000000000) (-28130711302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (343404523363643 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (13473755359 / 1000000000000) (13473755475 / 1000000000000), orderedInterval (-36092515678 / 1000000000000) (-36092515561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (609377352882487 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22647261847 / 1000000000000) (22647271413 / 1000000000000), orderedInterval (-17983330062 / 1000000000000) (-17983320496 / 1000000000000)))) (orderedInterval (2782698642 / 1000000000000) (2782700143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (569359369414003 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18268641894 / 1000000000000) (18268642777 / 1000000000000), orderedInterval (-23693281441 / 1000000000000) (-23693280558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (406321711619299 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8783679289 / 1000000000000) (-8783679275 / 1000000000000), orderedInterval (34305549172 / 1000000000000) (34305549185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (460725514813221 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32518678202 / 1000000000000) (-32518669674 / 1000000000000), orderedInterval (6953313157 / 1000000000000) (6953321685 / 1000000000000)))) (orderedInterval (-995852088 / 1000000000000) (-995851987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (384104901201749 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-9100083099 / 1000000000000) (-9100083098 / 1000000000000), orderedInterval (-35248403198 / 1000000000000) (-35248403197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (339368328944729 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29870207999 / 1000000000000) (-29870207998 / 1000000000000), orderedInterval (-24632331996 / 1000000000000) (-24632331995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (98362169244171 / 160000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-6500607526 / 1000000000000) (-6500607523 / 1000000000000), orderedInterval (31521864380 / 1000000000000) (31521864383 / 1000000000000)))) (orderedInterval (1437846742 / 1000000000000) (1437846775 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_chunkChecks0_2 :
    compactCertificate461.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (272074936646737 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43259914996 / 1000000000000) (43259915224 / 1000000000000), orderedInterval (-751427001 / 1000000000000) (-751426773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (230640936942857 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2799563722 / 1000000000000) (2799563723 / 1000000000000), orderedInterval (46902946836 / 1000000000000) (46902946837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (144324389336771 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50686201102 / 1000000000000) (-50686168870 / 1000000000000), orderedInterval (31119994438 / 1000000000000) (31120026669 / 1000000000000)))) (orderedInterval (-8725491724 / 1000000000000) (-8725490555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (77618136586557 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-32837982395 / 1000000000000) (-32837982394 / 1000000000000), orderedInterval (-73879964284 / 1000000000000) (-73879964283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (210748339710671 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (15769789983 / 1000000000000) (15769789984 / 1000000000000), orderedInterval (46531036948 / 1000000000000) (46531036949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (287758840445167 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30165941356 / 1000000000000) (30165967194 / 1000000000000), orderedInterval (-29365747466 / 1000000000000) (-29365721627 / 1000000000000)))) (orderedInterval (-2063295520 / 1000000000000) (-2063293500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (121675610663229 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56405279426 / 1000000000000) (56405299504 / 1000000000000), orderedInterval (-31873238527 / 1000000000000) (-31873218450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (494604602118109 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4706327255 / 1000000000000) (-4706327254 / 1000000000000), orderedInterval (-31738181143 / 1000000000000) (-31738181142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (330372952227731 / 800000000000) 0 (IntervalRat.scale (665 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31682668001 / 1000000000000) (-31682597583 / 1000000000000), orderedInterval (23228597618 / 1000000000000) (23228668036 / 1000000000000)))) (orderedInterval (6667628632 / 1000000000000) (6667642057 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_chunkChecks0 :
    compactCertificate461.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate461.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate461_chunkChecks0_0
    compactCertificate461_chunkChecks0_1 compactCertificate461_chunkChecks0_2

theorem compactCertificate461_chunkChecks1_0 :
    compactCertificate461.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (665 / 2) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11932548457 / 1000000000000) (11932548458 / 1000000000000), orderedInterval (42080299338 / 1000000000000) (42080299339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (195934396070833 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31204651451 / 1000000000000) (31204651452 / 1000000000000), orderedInterval (40254891746 / 1000000000000) (40254891747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (63361157963089 / 160000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32652084024 / 1000000000000) (32652084025 / 1000000000000), orderedInterval (23227578697 / 1000000000000) (23227578698 / 1000000000000)))) (orderedInterval (18578809350 / 1000000000000) (18578809377 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (57173168106131 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (615512275 / 1000000000000) (615512284 / 1000000000000), orderedInterval (-94385399200 / 1000000000000) (-94385399191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (153575171604407 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51747384390 / 1000000000000) (-51747384389 / 1000000000000), orderedInterval (-25133091703 / 1000000000000) (-25133091702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (416986465531419 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (17178481733 / 1000000000000) (17178481734 / 1000000000000), orderedInterval (30418248100 / 1000000000000) (30418248101 / 1000000000000)))) (orderedInterval (-3699561719 / 1000000000000) (-3699561673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (307150343208947 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40416998103 / 1000000000000) (40416998147 / 1000000000000), orderedInterval (4906892906 / 1000000000000) (4906892951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (526307348298431 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27213502060 / 1000000000000) (-27213430420 / 1000000000000), orderedInterval (15090637201 / 1000000000000) (15090708841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (387675610663229 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36244982975 / 1000000000000) (36244983476 / 1000000000000), orderedInterval (-167465567 / 1000000000000) (-167465067 / 1000000000000)))) (orderedInterval (-926853118 / 1000000000000) (-926848696 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_chunkChecks1_1 :
    compactCertificate461.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (594794082014867 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8076167185 / 1000000000000) (8076167188 / 1000000000000), orderedInterval (-28130711305 / 1000000000000) (-28130711302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (343404523363643 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (13473755359 / 1000000000000) (13473755475 / 1000000000000), orderedInterval (-36092515678 / 1000000000000) (-36092515561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (609377352882487 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22647261847 / 1000000000000) (22647271413 / 1000000000000), orderedInterval (-17983330062 / 1000000000000) (-17983320496 / 1000000000000)))) (orderedInterval (1868114290 / 1000000000000) (1868117691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (569359369414003 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18268641894 / 1000000000000) (18268642777 / 1000000000000), orderedInterval (-23693281441 / 1000000000000) (-23693280558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (406321711619299 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8783679289 / 1000000000000) (-8783679275 / 1000000000000), orderedInterval (34305549172 / 1000000000000) (34305549185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (460725514813221 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32518678202 / 1000000000000) (-32518669674 / 1000000000000), orderedInterval (6953313157 / 1000000000000) (6953321685 / 1000000000000)))) (orderedInterval (5809940938 / 1000000000000) (5809941113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (384104901201749 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-9100083099 / 1000000000000) (-9100083098 / 1000000000000), orderedInterval (-35248403198 / 1000000000000) (-35248403197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (339368328944729 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29870207999 / 1000000000000) (-29870207998 / 1000000000000), orderedInterval (-24632331996 / 1000000000000) (-24632331995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (98362169244171 / 160000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-6500607526 / 1000000000000) (-6500607523 / 1000000000000), orderedInterval (31521864380 / 1000000000000) (31521864383 / 1000000000000)))) (orderedInterval (2702896577 / 1000000000000) (2702896624 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_chunkChecks1_2 :
    compactCertificate461.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (272074936646737 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43259914996 / 1000000000000) (43259915224 / 1000000000000), orderedInterval (-751427001 / 1000000000000) (-751426773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (230640936942857 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2799563722 / 1000000000000) (2799563723 / 1000000000000), orderedInterval (46902946836 / 1000000000000) (46902946837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (144324389336771 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50686201102 / 1000000000000) (-50686168870 / 1000000000000), orderedInterval (31119994438 / 1000000000000) (31120026669 / 1000000000000)))) (orderedInterval (-1629235259 / 1000000000000) (-1629234575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (77618136586557 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-32837982395 / 1000000000000) (-32837982394 / 1000000000000), orderedInterval (-73879964284 / 1000000000000) (-73879964283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (210748339710671 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (15769789983 / 1000000000000) (15769789984 / 1000000000000), orderedInterval (46531036948 / 1000000000000) (46531036949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (287758840445167 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30165941356 / 1000000000000) (30165967194 / 1000000000000), orderedInterval (-29365747466 / 1000000000000) (-29365721627 / 1000000000000)))) (orderedInterval (1996349913 / 1000000000000) (1996352092 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (121675610663229 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56405279426 / 1000000000000) (56405299504 / 1000000000000), orderedInterval (-31873238527 / 1000000000000) (-31873218450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (494604602118109 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4706327255 / 1000000000000) (-4706327254 / 1000000000000), orderedInterval (-31738181143 / 1000000000000) (-31738181142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (330372952227731 / 800000000000) 1 (IntervalRat.scale (665 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31682668001 / 1000000000000) (-31682597583 / 1000000000000), orderedInterval (23228597618 / 1000000000000) (23228668036 / 1000000000000)))) (orderedInterval (-697049987 / 1000000000000) (-697033392 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_chunkChecks1 :
    compactCertificate461.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate461.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate461_chunkChecks1_0
    compactCertificate461_chunkChecks1_1 compactCertificate461_chunkChecks1_2

theorem compactCertificate461_chunkChecks2_0 :
    compactCertificate461.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (665 / 2) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11932548457 / 1000000000000) (11932548458 / 1000000000000), orderedInterval (42080299338 / 1000000000000) (42080299339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (195934396070833 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31204651451 / 1000000000000) (31204651452 / 1000000000000), orderedInterval (40254891746 / 1000000000000) (40254891747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (63361157963089 / 160000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32652084024 / 1000000000000) (32652084025 / 1000000000000), orderedInterval (23227578697 / 1000000000000) (23227578698 / 1000000000000)))) (orderedInterval (-7661176057 / 1000000000000) (-7661176026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (57173168106131 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (615512275 / 1000000000000) (615512284 / 1000000000000), orderedInterval (-94385399200 / 1000000000000) (-94385399191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (153575171604407 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51747384390 / 1000000000000) (-51747384389 / 1000000000000), orderedInterval (-25133091703 / 1000000000000) (-25133091702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (416986465531419 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (17178481733 / 1000000000000) (17178481734 / 1000000000000), orderedInterval (30418248100 / 1000000000000) (30418248101 / 1000000000000)))) (orderedInterval (3642270475 / 1000000000000) (3642270538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (307150343208947 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40416998103 / 1000000000000) (40416998147 / 1000000000000), orderedInterval (4906892906 / 1000000000000) (4906892951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (526307348298431 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27213502060 / 1000000000000) (-27213430420 / 1000000000000), orderedInterval (15090637201 / 1000000000000) (15090708841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (387675610663229 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36244982975 / 1000000000000) (36244983476 / 1000000000000), orderedInterval (-167465567 / 1000000000000) (-167465067 / 1000000000000)))) (orderedInterval (-5143878426 / 1000000000000) (-5143869678 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_chunkChecks2_1 :
    compactCertificate461.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (594794082014867 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8076167185 / 1000000000000) (8076167188 / 1000000000000), orderedInterval (-28130711305 / 1000000000000) (-28130711302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (343404523363643 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (13473755359 / 1000000000000) (13473755475 / 1000000000000), orderedInterval (-36092515678 / 1000000000000) (-36092515561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (609377352882487 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22647261847 / 1000000000000) (22647271413 / 1000000000000), orderedInterval (-17983330062 / 1000000000000) (-17983320496 / 1000000000000)))) (orderedInterval (-11390496744 / 1000000000000) (-11390488995 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (569359369414003 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18268641894 / 1000000000000) (18268642777 / 1000000000000), orderedInterval (-23693281441 / 1000000000000) (-23693280558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (406321711619299 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8783679289 / 1000000000000) (-8783679275 / 1000000000000), orderedInterval (34305549172 / 1000000000000) (34305549185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (460725514813221 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32518678202 / 1000000000000) (-32518669674 / 1000000000000), orderedInterval (6953313157 / 1000000000000) (6953321685 / 1000000000000)))) (orderedInterval (2937936605 / 1000000000000) (2937936918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (384104901201749 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-9100083099 / 1000000000000) (-9100083098 / 1000000000000), orderedInterval (-35248403198 / 1000000000000) (-35248403197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (339368328944729 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29870207999 / 1000000000000) (-29870207998 / 1000000000000), orderedInterval (-24632331996 / 1000000000000) (-24632331995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (98362169244171 / 160000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-6500607526 / 1000000000000) (-6500607523 / 1000000000000), orderedInterval (31521864380 / 1000000000000) (31521864383 / 1000000000000)))) (orderedInterval (-2002414083 / 1000000000000) (-2002414014 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_chunkChecks2_2 :
    compactCertificate461.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (272074936646737 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43259914996 / 1000000000000) (43259915224 / 1000000000000), orderedInterval (-751427001 / 1000000000000) (-751426773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (230640936942857 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2799563722 / 1000000000000) (2799563723 / 1000000000000), orderedInterval (46902946836 / 1000000000000) (46902946837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (144324389336771 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50686201102 / 1000000000000) (-50686168870 / 1000000000000), orderedInterval (31119994438 / 1000000000000) (31120026669 / 1000000000000)))) (orderedInterval (7846274850 / 1000000000000) (7846275273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (77618136586557 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-32837982395 / 1000000000000) (-32837982394 / 1000000000000), orderedInterval (-73879964284 / 1000000000000) (-73879964283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (210748339710671 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (15769789983 / 1000000000000) (15769789984 / 1000000000000), orderedInterval (46531036948 / 1000000000000) (46531036949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (287758840445167 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30165941356 / 1000000000000) (30165967194 / 1000000000000), orderedInterval (-29365747466 / 1000000000000) (-29365721627 / 1000000000000)))) (orderedInterval (2872522169 / 1000000000000) (2872524529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (121675610663229 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56405279426 / 1000000000000) (56405299504 / 1000000000000), orderedInterval (-31873238527 / 1000000000000) (-31873218450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (494604602118109 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4706327255 / 1000000000000) (-4706327254 / 1000000000000), orderedInterval (-31738181143 / 1000000000000) (-31738181142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (330372952227731 / 800000000000) 2 (IntervalRat.scale (665 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31682668001 / 1000000000000) (-31682597583 / 1000000000000), orderedInterval (23228597618 / 1000000000000) (23228668036 / 1000000000000)))) (orderedInterval (-10563441878 / 1000000000000) (-10563421231 / 1000000000000))) = true
  rfl'

theorem compactCertificate461_chunkChecks2 :
    compactCertificate461.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate461.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate461_chunkChecks2_0
    compactCertificate461_chunkChecks2_1 compactCertificate461_chunkChecks2_2

theorem compactCertificate461_chunkChecks3_0 :
    compactCertificate461.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (665 / 2) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11932548457 / 1000000000000) (11932548458 / 1000000000000), orderedInterval (42080299338 / 1000000000000) (42080299339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (195934396070833 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31204651451 / 1000000000000) (31204651452 / 1000000000000), orderedInterval (40254891746 / 1000000000000) (40254891747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (63361157963089 / 160000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32652084024 / 1000000000000) (32652084025 / 1000000000000), orderedInterval (23227578697 / 1000000000000) (23227578698 / 1000000000000)))) (orderedInterval (-19108556202 / 1000000000000) (-19108556166 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (57173168106131 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (615512275 / 1000000000000) (615512284 / 1000000000000), orderedInterval (-94385399200 / 1000000000000) (-94385399191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (153575171604407 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51747384390 / 1000000000000) (-51747384389 / 1000000000000), orderedInterval (-25133091703 / 1000000000000) (-25133091702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (416986465531419 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (17178481733 / 1000000000000) (17178481734 / 1000000000000), orderedInterval (30418248100 / 1000000000000) (30418248101 / 1000000000000)))) (orderedInterval (8485762834 / 1000000000000) (8485762929 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (307150343208947 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40416998103 / 1000000000000) (40416998147 / 1000000000000), orderedInterval (4906892906 / 1000000000000) (4906892951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (526307348298431 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27213502060 / 1000000000000) (-27213430420 / 1000000000000), orderedInterval (15090637201 / 1000000000000) (15090708841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (387675610663229 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36244982975 / 1000000000000) (36244983476 / 1000000000000), orderedInterval (-167465567 / 1000000000000) (-167465067 / 1000000000000)))) (orderedInterval (3633376376 / 1000000000000) (3633393661 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate461_chunkChecks3_1 :
    compactCertificate461.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (594794082014867 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8076167185 / 1000000000000) (8076167188 / 1000000000000), orderedInterval (-28130711305 / 1000000000000) (-28130711302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (343404523363643 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (13473755359 / 1000000000000) (13473755475 / 1000000000000), orderedInterval (-36092515678 / 1000000000000) (-36092515561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (609377352882487 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22647261847 / 1000000000000) (22647271413 / 1000000000000), orderedInterval (-17983330062 / 1000000000000) (-17983320496 / 1000000000000)))) (orderedInterval (-19360545247 / 1000000000000) (-19360527568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (569359369414003 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18268641894 / 1000000000000) (18268642777 / 1000000000000), orderedInterval (-23693281441 / 1000000000000) (-23693280558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (406321711619299 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8783679289 / 1000000000000) (-8783679275 / 1000000000000), orderedInterval (34305549172 / 1000000000000) (34305549185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (460725514813221 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32518678202 / 1000000000000) (-32518669674 / 1000000000000), orderedInterval (6953313157 / 1000000000000) (6953321685 / 1000000000000)))) (orderedInterval (-15583006711 / 1000000000000) (-15583006145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (384104901201749 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-9100083099 / 1000000000000) (-9100083098 / 1000000000000), orderedInterval (-35248403198 / 1000000000000) (-35248403197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (339368328944729 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29870207999 / 1000000000000) (-29870207998 / 1000000000000), orderedInterval (-24632331996 / 1000000000000) (-24632331995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (98362169244171 / 160000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-6500607526 / 1000000000000) (-6500607523 / 1000000000000), orderedInterval (31521864380 / 1000000000000) (31521864383 / 1000000000000)))) (orderedInterval (-6796873771 / 1000000000000) (-6796873665 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate461_chunkChecks3_2 :
    compactCertificate461.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (272074936646737 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43259914996 / 1000000000000) (43259915224 / 1000000000000), orderedInterval (-751427001 / 1000000000000) (-751426773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (230640936942857 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2799563722 / 1000000000000) (2799563723 / 1000000000000), orderedInterval (46902946836 / 1000000000000) (46902946837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (144324389336771 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50686201102 / 1000000000000) (-50686168870 / 1000000000000), orderedInterval (31119994438 / 1000000000000) (31120026669 / 1000000000000)))) (orderedInterval (1416532830 / 1000000000000) (1416533109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (77618136586557 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-32837982395 / 1000000000000) (-32837982394 / 1000000000000), orderedInterval (-73879964284 / 1000000000000) (-73879964283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (210748339710671 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (15769789983 / 1000000000000) (15769789984 / 1000000000000), orderedInterval (46531036948 / 1000000000000) (46531036949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (287758840445167 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30165941356 / 1000000000000) (30165967194 / 1000000000000), orderedInterval (-29365747466 / 1000000000000) (-29365721627 / 1000000000000)))) (orderedInterval (-2366763273 / 1000000000000) (-2366760721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (121675610663229 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56405279426 / 1000000000000) (56405299504 / 1000000000000), orderedInterval (-31873238527 / 1000000000000) (-31873218450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (494604602118109 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4706327255 / 1000000000000) (-4706327254 / 1000000000000), orderedInterval (-31738181143 / 1000000000000) (-31738181142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (330372952227731 / 800000000000) 3 (IntervalRat.scale (665 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31682668001 / 1000000000000) (-31682597583 / 1000000000000), orderedInterval (23228597618 / 1000000000000) (23228668036 / 1000000000000)))) (orderedInterval (-8208935856 / 1000000000000) (-8208910175 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate461_chunkChecks3 :
    compactCertificate461.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate461.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate461_chunkChecks3_0
    compactCertificate461_chunkChecks3_1 compactCertificate461_chunkChecks3_2

theorem compactCertificate461_chunkChecks4_0 :
    compactCertificate461.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (665 / 2) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11932548457 / 1000000000000) (11932548458 / 1000000000000), orderedInterval (42080299338 / 1000000000000) (42080299339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (195934396070833 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (31204651451 / 1000000000000) (31204651452 / 1000000000000), orderedInterval (40254891746 / 1000000000000) (40254891747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (63361157963089 / 160000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32652084024 / 1000000000000) (32652084025 / 1000000000000), orderedInterval (23227578697 / 1000000000000) (23227578698 / 1000000000000)))) (orderedInterval (8785385649 / 1000000000000) (8785385691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (57173168106131 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (615512275 / 1000000000000) (615512284 / 1000000000000), orderedInterval (-94385399200 / 1000000000000) (-94385399191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (153575171604407 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-51747384390 / 1000000000000) (-51747384389 / 1000000000000), orderedInterval (-25133091703 / 1000000000000) (-25133091702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (416986465531419 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (17178481733 / 1000000000000) (17178481734 / 1000000000000), orderedInterval (30418248100 / 1000000000000) (30418248101 / 1000000000000)))) (orderedInterval (-7635791743 / 1000000000000) (-7635791598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (307150343208947 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40416998103 / 1000000000000) (40416998147 / 1000000000000), orderedInterval (4906892906 / 1000000000000) (4906892951 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (526307348298431 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27213502060 / 1000000000000) (-27213430420 / 1000000000000), orderedInterval (15090637201 / 1000000000000) (15090708841 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (387675610663229 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36244982975 / 1000000000000) (36244983476 / 1000000000000), orderedInterval (-167465567 / 1000000000000) (-167465067 / 1000000000000)))) (orderedInterval (16794547368 / 1000000000000) (16794581585 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate461_chunkChecks4_1 :
    compactCertificate461.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (594794082014867 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8076167185 / 1000000000000) (8076167188 / 1000000000000), orderedInterval (-28130711305 / 1000000000000) (-28130711302 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (343404523363643 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (13473755359 / 1000000000000) (13473755475 / 1000000000000), orderedInterval (-36092515678 / 1000000000000) (-36092515561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (609377352882487 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22647261847 / 1000000000000) (22647271413 / 1000000000000), orderedInterval (-17983330062 / 1000000000000) (-17983320496 / 1000000000000)))) (orderedInterval (55688059187 / 1000000000000) (55688099627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (569359369414003 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18268641894 / 1000000000000) (18268642777 / 1000000000000), orderedInterval (-23693281441 / 1000000000000) (-23693280558 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (406321711619299 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-8783679289 / 1000000000000) (-8783679275 / 1000000000000), orderedInterval (34305549172 / 1000000000000) (34305549185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (460725514813221 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32518678202 / 1000000000000) (-32518669674 / 1000000000000), orderedInterval (6953313157 / 1000000000000) (6953321685 / 1000000000000)))) (orderedInterval (-9870106896 / 1000000000000) (-9870105850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (384104901201749 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-9100083099 / 1000000000000) (-9100083098 / 1000000000000), orderedInterval (-35248403198 / 1000000000000) (-35248403197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (339368328944729 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29870207999 / 1000000000000) (-29870207998 / 1000000000000), orderedInterval (-24632331996 / 1000000000000) (-24632331995 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (98362169244171 / 160000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-6500607526 / 1000000000000) (-6500607523 / 1000000000000), orderedInterval (31521864380 / 1000000000000) (31521864383 / 1000000000000)))) (orderedInterval (2167870630 / 1000000000000) (2167870799 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate461_chunkChecks4_2 :
    compactCertificate461.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (272074936646737 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43259914996 / 1000000000000) (43259915224 / 1000000000000), orderedInterval (-751427001 / 1000000000000) (-751426773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (230640936942857 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (2799563722 / 1000000000000) (2799563723 / 1000000000000), orderedInterval (46902946836 / 1000000000000) (46902946837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (144324389336771 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-50686201102 / 1000000000000) (-50686168870 / 1000000000000), orderedInterval (31119994438 / 1000000000000) (31120026669 / 1000000000000)))) (orderedInterval (-7811804302 / 1000000000000) (-7811804099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (77618136586557 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-32837982395 / 1000000000000) (-32837982394 / 1000000000000), orderedInterval (-73879964284 / 1000000000000) (-73879964283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (210748339710671 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (15769789983 / 1000000000000) (15769789984 / 1000000000000), orderedInterval (46531036948 / 1000000000000) (46531036949 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (287758840445167 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30165941356 / 1000000000000) (30165967194 / 1000000000000), orderedInterval (-29365747466 / 1000000000000) (-29365721627 / 1000000000000)))) (orderedInterval (-3288630960 / 1000000000000) (-3288628194 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (121675610663229 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56405279426 / 1000000000000) (56405299504 / 1000000000000), orderedInterval (-31873238527 / 1000000000000) (-31873218450 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (494604602118109 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-4706327255 / 1000000000000) (-4706327254 / 1000000000000), orderedInterval (-31738181143 / 1000000000000) (-31738181142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (330372952227731 / 800000000000) 4 (IntervalRat.scale (665 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31682668001 / 1000000000000) (-31682597583 / 1000000000000), orderedInterval (23228597618 / 1000000000000) (23228668036 / 1000000000000)))) (orderedInterval (18788823003 / 1000000000000) (18788855073 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate461_chunkChecks4 :
    compactCertificate461.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate461.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate461_chunkChecks4_0
    compactCertificate461_chunkChecks4_1 compactCertificate461_chunkChecks4_2

theorem compactCertificate461_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate461.chunkCheck r b = true :=
  compactCertificate461.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate461_chunkChecks0
    · exact compactCertificate461_chunkChecks1
    · exact compactCertificate461_chunkChecks2
    · exact compactCertificate461_chunkChecks3
    · exact compactCertificate461_chunkChecks4)

theorem compactCertificate461_coefficient0 :
    compactCertificate461.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate461_coefficient1 :
    compactCertificate461.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate461_coefficient2 :
    compactCertificate461.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate461_coefficient3 :
    compactCertificate461.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate461_coefficient4 :
    compactCertificate461.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate461_coefficients : ∀ r : Fin 5,
    compactCertificate461.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate461_coefficient0
  · exact compactCertificate461_coefficient1
  · exact compactCertificate461_coefficient2
  · exact compactCertificate461_coefficient3
  · exact compactCertificate461_coefficient4

theorem compactCertificate461_lower : (1 : ℚ) ≤ compactCertificate461.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate461, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate461_proves {t : ℝ} (ht : t ∈ compactCertificate461.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate461.proves compactCertificate461_states compactCertificate461_chunks
    compactCertificate461_coefficients compactCertificate461_lower ht

end Erdos232
