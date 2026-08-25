/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate353 : CompactCertificate where
  left := 224
  right := 225
  center := 449 / 2
  grid := fun i =>
    match i.val with
    | 0 => 71
    | 1 => 53
    | 2 => 85
    | 3 => 15
    | 4 => 41
    | 5 => 112
    | 6 => 83
    | 7 => 141
    | 8 => 104
    | 9 => 160
    | 10 => 92
    | 11 => 164
    | 12 => 153
    | 13 => 109
    | 14 => 124
    | 15 => 103
    | 16 => 91
    | 17 => 132
    | 18 => 73
    | 19 => 62
    | 20 => 39
    | 21 => 21
    | 22 => 57
    | 23 => 77
    | 24 => 33
    | 25 => 133
    | _ => 89
  point := fun i =>
    match i.val with
    | 0 => 449 / 2
    | 1 => 661462735607549 / 4000000000000
    | 2 => 213903458085917 / 800000000000
    | 3 => 193013176538743 / 4000000000000
    | 4 => 518460541732171 / 4000000000000
    | 5 => 1407721225741407 / 4000000000000
    | 6 => 1036921083464791 / 4000000000000
    | 7 => 1776781950270643 / 4000000000000
    | 8 => 1308769542765337 / 4000000000000
    | 9 => 2007989043794551 / 4000000000000
    | 10 => 1159313014964479 / 4000000000000
    | 11 => 2057221289054411 / 4000000000000
    | 12 => 1922122983961559 / 4000000000000
    | 13 => 1371717658023047 / 4000000000000
    | 14 => 1555381625196513 / 4000000000000
    | 15 => 1296715042402897 / 4000000000000
    | 16 => 1145687065384837 / 4000000000000
    | 17 => 332064766846863 / 800000000000
    | 18 => 918508620709661 / 4000000000000
    | 19 => 778629929980021 / 4000000000000
    | 20 => 487230457234663 / 4000000000000
    | 21 => 262034160356121 / 4000000000000
    | 22 => 711473718271363 / 4000000000000
    | 23 => 971456536540451 / 4000000000000
    | 24 => 410769542765337 / 4000000000000
    | 25 => 1669755386097977 / 4000000000000
    | _ => 1115319214663543 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-42036693504 / 1000000000000) (-42036589423 / 1000000000000), orderedInterval (32783653940 / 1000000000000) (32783758022 / 1000000000000))
    | 1 => (orderedInterval (21513446970 / 1000000000000) (21513447610 / 1000000000000), orderedInterval (-58262594907 / 1000000000000) (-58262594268 / 1000000000000))
    | 2 => (orderedInterval (-44107446082 / 1000000000000) (-44107446081 / 1000000000000), orderedInterval (-20785956753 / 1000000000000) (-20785956752 / 1000000000000))
    | 3 => (orderedInterval (-108229476998 / 1000000000000) (-108229474946 / 1000000000000), orderedInterval (39580717589 / 1000000000000) (39580719641 / 1000000000000))
    | 4 => (orderedInterval (-70063353536 / 1000000000000) (-70063353478 / 1000000000000), orderedInterval (1915259711 / 1000000000000) (1915259769 / 1000000000000))
    | 5 => (orderedInterval (32148074756 / 1000000000000) (32148074757 / 1000000000000), orderedInterval (27801015107 / 1000000000000) (27801015108 / 1000000000000))
    | 6 => (orderedInterval (33305230700 / 1000000000000) (33305253867 / 1000000000000), orderedInterval (-36759879515 / 1000000000000) (-36759856348 / 1000000000000))
    | 7 => (orderedInterval (-34166701617 / 1000000000000) (-34166659363 / 1000000000000), orderedInterval (16342873230 / 1000000000000) (16342915484 / 1000000000000))
    | 8 => (orderedInterval (41884318675 / 1000000000000) (41884318677 / 1000000000000), orderedInterval (13770977479 / 1000000000000) (13770977480 / 1000000000000))
    | 9 => (orderedInterval (4531185332 / 1000000000000) (4531185333 / 1000000000000), orderedInterval (35317473836 / 1000000000000) (35317473837 / 1000000000000))
    | 10 => (orderedInterval (46861315615 / 1000000000000) (46861315776 / 1000000000000), orderedInterval (-826009422 / 1000000000000) (-826009260 / 1000000000000))
    | 11 => (orderedInterval (-4585922285 / 1000000000000) (-4585922282 / 1000000000000), orderedInterval (34887039506 / 1000000000000) (34887039509 / 1000000000000))
    | 12 => (orderedInterval (-22091593740 / 1000000000000) (-22091593739 / 1000000000000), orderedInterval (-28904301162 / 1000000000000) (-28904301161 / 1000000000000))
    | 13 => (orderedInterval (-41287665700 / 1000000000000) (-41287665697 / 1000000000000), orderedInterval (-12258217189 / 1000000000000) (-12258217186 / 1000000000000))
    | 14 => (orderedInterval (2950886832 / 1000000000000) (2950886833 / 1000000000000), orderedInterval (40350869969 / 1000000000000) (40350869970 / 1000000000000))
    | 15 => (orderedInterval (-43508243841 / 1000000000000) (-43508243831 / 1000000000000), orderedInterval (-8348529572 / 1000000000000) (-8348529562 / 1000000000000))
    | 16 => (orderedInterval (-45691134257 / 1000000000000) (-45691134254 / 1000000000000), orderedInterval (-11538446120 / 1000000000000) (-11538446116 / 1000000000000))
    | 17 => (orderedInterval (36147546843 / 1000000000000) (36147546845 / 1000000000000), orderedInterval (15025578754 / 1000000000000) (15025578756 / 1000000000000))
    | 18 => (orderedInterval (-46332227888 / 1000000000000) (-46332227887 / 1000000000000), orderedInterval (-24913657603 / 1000000000000) (-24913657602 / 1000000000000))
    | 19 => (orderedInterval (35220473595 / 1000000000000) (35220473596 / 1000000000000), orderedInterval (44964856452 / 1000000000000) (44964856453 / 1000000000000))
    | 20 => (orderedInterval (-5047261161 / 1000000000000) (-5047261159 / 1000000000000), orderedInterval (-72097278153 / 1000000000000) (-72097278151 / 1000000000000))
    | 21 => (orderedInterval (-30877207633 / 1000000000000) (-30877207632 / 1000000000000), orderedInterval (-93385621566 / 1000000000000) (-93385621565 / 1000000000000))
    | 22 => (orderedInterval (24266569023 / 1000000000000) (24266570294 / 1000000000000), orderedInterval (-54751889273 / 1000000000000) (-54751888002 / 1000000000000))
    | 23 => (orderedInterval (-50411359297 / 1000000000000) (-50411358378 / 1000000000000), orderedInterval (9047483351 / 1000000000000) (9047484270 / 1000000000000))
    | 24 => (orderedInterval (15332757861 / 1000000000000) (15332757983 / 1000000000000), orderedInterval (-77303295676 / 1000000000000) (-77303295554 / 1000000000000))
    | 25 => (orderedInterval (-14923748273 / 1000000000000) (-14923748272 / 1000000000000), orderedInterval (-36070123685 / 1000000000000) (-36070123684 / 1000000000000))
    | _ => (orderedInterval (-621508470 / 1000000000000) (-621508468 / 1000000000000), orderedInterval (-47777557423 / 1000000000000) (-47777557421 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-19049685363 / 1000000000000) (-19049644087 / 1000000000000)
      | 1 => orderedInterval (-3669317407 / 1000000000000) (-3669317355 / 1000000000000)
      | 2 => orderedInterval (2066097813 / 1000000000000) (2066099130 / 1000000000000)
      | 3 => orderedInterval (2014985023 / 1000000000000) (2014985125 / 1000000000000)
      | 4 => orderedInterval (-3520391758 / 1000000000000) (-3520391730 / 1000000000000)
      | 5 => orderedInterval (3037852910 / 1000000000000) (3037852933 / 1000000000000)
      | 6 => orderedInterval (5250380821 / 1000000000000) (5250380878 / 1000000000000)
      | 7 => orderedInterval (3883088448 / 1000000000000) (3883088574 / 1000000000000)
      | _ => orderedInterval (1423861966 / 1000000000000) (1423862030 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11141685521 / 1000000000000) (11141726798 / 1000000000000)
      | 1 => orderedInterval (-3150109576 / 1000000000000) (-3150109538 / 1000000000000)
      | 2 => orderedInterval (-512316970 / 1000000000000) (-512314369 / 1000000000000)
      | 3 => orderedInterval (-2749981659 / 1000000000000) (-2749981457 / 1000000000000)
      | 4 => orderedInterval (-1007435662 / 1000000000000) (-1007435617 / 1000000000000)
      | 5 => orderedInterval (1414525613 / 1000000000000) (1414525645 / 1000000000000)
      | 6 => orderedInterval (594279333 / 1000000000000) (594279386 / 1000000000000)
      | 7 => orderedInterval (737198554 / 1000000000000) (737198678 / 1000000000000)
      | _ => orderedInterval (16380138282 / 1000000000000) (16380138371 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (20174851625 / 1000000000000) (20174893087 / 1000000000000)
      | 1 => orderedInterval (6428689235 / 1000000000000) (6428689280 / 1000000000000)
      | 2 => orderedInterval (-6273477287 / 1000000000000) (-6273472134 / 1000000000000)
      | 3 => orderedInterval (1672580753 / 1000000000000) (1672581172 / 1000000000000)
      | 4 => orderedInterval (7332064889 / 1000000000000) (7332064963 / 1000000000000)
      | 5 => orderedInterval (-6378635317 / 1000000000000) (-6378635270 / 1000000000000)
      | 6 => orderedInterval (-6205968530 / 1000000000000) (-6205968480 / 1000000000000)
      | 7 => orderedInterval (-4227636229 / 1000000000000) (-4227636103 / 1000000000000)
      | _ => orderedInterval (-4472335036 / 1000000000000) (-4472334905 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10806363414 / 1000000000000) (-10806321951 / 1000000000000)
      | 1 => orderedInterval (7575670872 / 1000000000000) (7575670937 / 1000000000000)
      | 2 => orderedInterval (2902191059 / 1000000000000) (2902201248 / 1000000000000)
      | 3 => orderedInterval (10659267796 / 1000000000000) (10659268696 / 1000000000000)
      | 4 => orderedInterval (42765349 / 1000000000000) (42765473 / 1000000000000)
      | 5 => orderedInterval (-3484103674 / 1000000000000) (-3484103601 / 1000000000000)
      | 6 => orderedInterval (-2201131433 / 1000000000000) (-2201131384 / 1000000000000)
      | 7 => orderedInterval (236086689 / 1000000000000) (236086818 / 1000000000000)
      | _ => orderedInterval (-35985802593 / 1000000000000) (-35985802392 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-21714015345 / 1000000000000) (-21713973696 / 1000000000000)
      | 1 => orderedInterval (-14150474811 / 1000000000000) (-14150474712 / 1000000000000)
      | 2 => orderedInterval (20692301340 / 1000000000000) (20692321536 / 1000000000000)
      | 3 => orderedInterval (-28534828037 / 1000000000000) (-28534826064 / 1000000000000)
      | 4 => orderedInterval (-13019874653 / 1000000000000) (-13019874439 / 1000000000000)
      | 5 => orderedInterval (15589806289 / 1000000000000) (15589806404 / 1000000000000)
      | 6 => orderedInterval (6986955236 / 1000000000000) (6986955284 / 1000000000000)
      | 7 => orderedInterval (5076359360 / 1000000000000) (5076359495 / 1000000000000)
      | _ => orderedInterval (15123736799 / 1000000000000) (15123737120 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-8563127547 / 1000000000000) (-8563084502 / 1000000000000)
    | 1 => orderedInterval (22847983436 / 1000000000000) (22848027897 / 1000000000000)
    | 2 => orderedInterval (8050134103 / 1000000000000) (8050181610 / 1000000000000)
    | 3 => orderedInterval (-31061419349 / 1000000000000) (-31061366156 / 1000000000000)
    | _ => orderedInterval (-13950033822 / 1000000000000) (-13949969072 / 1000000000000)

theorem compactCertificate353_stateChecks0 :
    compactCertificate353.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (449 / 2)) (orderedInterval (-42036693504 / 1000000000000) (-42036589423 / 1000000000000), orderedInterval (32783653940 / 1000000000000) (32783758022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (661462735607549 / 4000000000000)) (orderedInterval (21513446970 / 1000000000000) (21513447610 / 1000000000000), orderedInterval (-58262594907 / 1000000000000) (-58262594268 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (213903458085917 / 800000000000)) (orderedInterval (-44107446082 / 1000000000000) (-44107446081 / 1000000000000), orderedInterval (-20785956753 / 1000000000000) (-20785956752 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_stateChecks1 :
    compactCertificate353.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (193013176538743 / 4000000000000)) (orderedInterval (-108229476998 / 1000000000000) (-108229474946 / 1000000000000), orderedInterval (39580717589 / 1000000000000) (39580719641 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (518460541732171 / 4000000000000)) (orderedInterval (-70063353536 / 1000000000000) (-70063353478 / 1000000000000), orderedInterval (1915259711 / 1000000000000) (1915259769 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1407721225741407 / 4000000000000)) (orderedInterval (32148074756 / 1000000000000) (32148074757 / 1000000000000), orderedInterval (27801015107 / 1000000000000) (27801015108 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_stateChecks2 :
    compactCertificate353.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1036921083464791 / 4000000000000)) (orderedInterval (33305230700 / 1000000000000) (33305253867 / 1000000000000), orderedInterval (-36759879515 / 1000000000000) (-36759856348 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1776781950270643 / 4000000000000)) (orderedInterval (-34166701617 / 1000000000000) (-34166659363 / 1000000000000), orderedInterval (16342873230 / 1000000000000) (16342915484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1308769542765337 / 4000000000000)) (orderedInterval (41884318675 / 1000000000000) (41884318677 / 1000000000000), orderedInterval (13770977479 / 1000000000000) (13770977480 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_stateChecks3 :
    compactCertificate353.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2007989043794551 / 4000000000000)) (orderedInterval (4531185332 / 1000000000000) (4531185333 / 1000000000000), orderedInterval (35317473836 / 1000000000000) (35317473837 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1159313014964479 / 4000000000000)) (orderedInterval (46861315615 / 1000000000000) (46861315776 / 1000000000000), orderedInterval (-826009422 / 1000000000000) (-826009260 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2057221289054411 / 4000000000000)) (orderedInterval (-4585922285 / 1000000000000) (-4585922282 / 1000000000000), orderedInterval (34887039506 / 1000000000000) (34887039509 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_stateChecks4 :
    compactCertificate353.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1922122983961559 / 4000000000000)) (orderedInterval (-22091593740 / 1000000000000) (-22091593739 / 1000000000000), orderedInterval (-28904301162 / 1000000000000) (-28904301161 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1371717658023047 / 4000000000000)) (orderedInterval (-41287665700 / 1000000000000) (-41287665697 / 1000000000000), orderedInterval (-12258217189 / 1000000000000) (-12258217186 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1555381625196513 / 4000000000000)) (orderedInterval (2950886832 / 1000000000000) (2950886833 / 1000000000000), orderedInterval (40350869969 / 1000000000000) (40350869970 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_stateChecks5 :
    compactCertificate353.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1296715042402897 / 4000000000000)) (orderedInterval (-43508243841 / 1000000000000) (-43508243831 / 1000000000000), orderedInterval (-8348529572 / 1000000000000) (-8348529562 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1145687065384837 / 4000000000000)) (orderedInterval (-45691134257 / 1000000000000) (-45691134254 / 1000000000000), orderedInterval (-11538446120 / 1000000000000) (-11538446116 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (332064766846863 / 800000000000)) (orderedInterval (36147546843 / 1000000000000) (36147546845 / 1000000000000), orderedInterval (15025578754 / 1000000000000) (15025578756 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_stateChecks6 :
    compactCertificate353.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (918508620709661 / 4000000000000)) (orderedInterval (-46332227888 / 1000000000000) (-46332227887 / 1000000000000), orderedInterval (-24913657603 / 1000000000000) (-24913657602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (778629929980021 / 4000000000000)) (orderedInterval (35220473595 / 1000000000000) (35220473596 / 1000000000000), orderedInterval (44964856452 / 1000000000000) (44964856453 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (487230457234663 / 4000000000000)) (orderedInterval (-5047261161 / 1000000000000) (-5047261159 / 1000000000000), orderedInterval (-72097278153 / 1000000000000) (-72097278151 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_stateChecks7 :
    compactCertificate353.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (262034160356121 / 4000000000000)) (orderedInterval (-30877207633 / 1000000000000) (-30877207632 / 1000000000000), orderedInterval (-93385621566 / 1000000000000) (-93385621565 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (711473718271363 / 4000000000000)) (orderedInterval (24266569023 / 1000000000000) (24266570294 / 1000000000000), orderedInterval (-54751889273 / 1000000000000) (-54751888002 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (971456536540451 / 4000000000000)) (orderedInterval (-50411359297 / 1000000000000) (-50411358378 / 1000000000000), orderedInterval (9047483351 / 1000000000000) (9047484270 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_stateChecks8 :
    compactCertificate353.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (410769542765337 / 4000000000000)) (orderedInterval (15332757861 / 1000000000000) (15332757983 / 1000000000000), orderedInterval (-77303295676 / 1000000000000) (-77303295554 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1669755386097977 / 4000000000000)) (orderedInterval (-14923748273 / 1000000000000) (-14923748272 / 1000000000000), orderedInterval (-36070123685 / 1000000000000) (-36070123684 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1115319214663543 / 4000000000000)) (orderedInterval (-621508470 / 1000000000000) (-621508468 / 1000000000000), orderedInterval (-47777557423 / 1000000000000) (-47777557421 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_states : ∀ j,
    BesselStateValid (compactCertificate353.point j) (compactCertificate353.state j) :=
  compactCertificate353.statesValid_of_checks3 compactCertificate353_stateChecks0
    compactCertificate353_stateChecks1 compactCertificate353_stateChecks2
    compactCertificate353_stateChecks3 compactCertificate353_stateChecks4
    compactCertificate353_stateChecks5 compactCertificate353_stateChecks6
    compactCertificate353_stateChecks7 compactCertificate353_stateChecks8

theorem compactCertificate353_chunkChecks0_0 :
    compactCertificate353.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (449 / 2) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42036693504 / 1000000000000) (-42036589423 / 1000000000000), orderedInterval (32783653940 / 1000000000000) (32783758022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (661462735607549 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21513446970 / 1000000000000) (21513447610 / 1000000000000), orderedInterval (-58262594907 / 1000000000000) (-58262594268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (213903458085917 / 800000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-44107446082 / 1000000000000) (-44107446081 / 1000000000000), orderedInterval (-20785956753 / 1000000000000) (-20785956752 / 1000000000000)))) (orderedInterval (-19049685363 / 1000000000000) (-19049644087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (193013176538743 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-108229476998 / 1000000000000) (-108229474946 / 1000000000000), orderedInterval (39580717589 / 1000000000000) (39580719641 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (518460541732171 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-70063353536 / 1000000000000) (-70063353478 / 1000000000000), orderedInterval (1915259711 / 1000000000000) (1915259769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1407721225741407 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (32148074756 / 1000000000000) (32148074757 / 1000000000000), orderedInterval (27801015107 / 1000000000000) (27801015108 / 1000000000000)))) (orderedInterval (-3669317407 / 1000000000000) (-3669317355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1036921083464791 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33305230700 / 1000000000000) (33305253867 / 1000000000000), orderedInterval (-36759879515 / 1000000000000) (-36759856348 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1776781950270643 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34166701617 / 1000000000000) (-34166659363 / 1000000000000), orderedInterval (16342873230 / 1000000000000) (16342915484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1308769542765337 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41884318675 / 1000000000000) (41884318677 / 1000000000000), orderedInterval (13770977479 / 1000000000000) (13770977480 / 1000000000000)))) (orderedInterval (2066097813 / 1000000000000) (2066099130 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_chunkChecks0_1 :
    compactCertificate353.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2007989043794551 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4531185332 / 1000000000000) (4531185333 / 1000000000000), orderedInterval (35317473836 / 1000000000000) (35317473837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1159313014964479 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (46861315615 / 1000000000000) (46861315776 / 1000000000000), orderedInterval (-826009422 / 1000000000000) (-826009260 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2057221289054411 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4585922285 / 1000000000000) (-4585922282 / 1000000000000), orderedInterval (34887039506 / 1000000000000) (34887039509 / 1000000000000)))) (orderedInterval (2014985023 / 1000000000000) (2014985125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1922122983961559 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22091593740 / 1000000000000) (-22091593739 / 1000000000000), orderedInterval (-28904301162 / 1000000000000) (-28904301161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1371717658023047 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41287665700 / 1000000000000) (-41287665697 / 1000000000000), orderedInterval (-12258217189 / 1000000000000) (-12258217186 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1555381625196513 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2950886832 / 1000000000000) (2950886833 / 1000000000000), orderedInterval (40350869969 / 1000000000000) (40350869970 / 1000000000000)))) (orderedInterval (-3520391758 / 1000000000000) (-3520391730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1296715042402897 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43508243841 / 1000000000000) (-43508243831 / 1000000000000), orderedInterval (-8348529572 / 1000000000000) (-8348529562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1145687065384837 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45691134257 / 1000000000000) (-45691134254 / 1000000000000), orderedInterval (-11538446120 / 1000000000000) (-11538446116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (332064766846863 / 800000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36147546843 / 1000000000000) (36147546845 / 1000000000000), orderedInterval (15025578754 / 1000000000000) (15025578756 / 1000000000000)))) (orderedInterval (3037852910 / 1000000000000) (3037852933 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_chunkChecks0_2 :
    compactCertificate353.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (918508620709661 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46332227888 / 1000000000000) (-46332227887 / 1000000000000), orderedInterval (-24913657603 / 1000000000000) (-24913657602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (778629929980021 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35220473595 / 1000000000000) (35220473596 / 1000000000000), orderedInterval (44964856452 / 1000000000000) (44964856453 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (487230457234663 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-5047261161 / 1000000000000) (-5047261159 / 1000000000000), orderedInterval (-72097278153 / 1000000000000) (-72097278151 / 1000000000000)))) (orderedInterval (5250380821 / 1000000000000) (5250380878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (262034160356121 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30877207633 / 1000000000000) (-30877207632 / 1000000000000), orderedInterval (-93385621566 / 1000000000000) (-93385621565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (711473718271363 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24266569023 / 1000000000000) (24266570294 / 1000000000000), orderedInterval (-54751889273 / 1000000000000) (-54751888002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (971456536540451 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-50411359297 / 1000000000000) (-50411358378 / 1000000000000), orderedInterval (9047483351 / 1000000000000) (9047484270 / 1000000000000)))) (orderedInterval (3883088448 / 1000000000000) (3883088574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (410769542765337 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (15332757861 / 1000000000000) (15332757983 / 1000000000000), orderedInterval (-77303295676 / 1000000000000) (-77303295554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1669755386097977 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14923748273 / 1000000000000) (-14923748272 / 1000000000000), orderedInterval (-36070123685 / 1000000000000) (-36070123684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1115319214663543 / 4000000000000) 0 (IntervalRat.scale (449 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-621508470 / 1000000000000) (-621508468 / 1000000000000), orderedInterval (-47777557423 / 1000000000000) (-47777557421 / 1000000000000)))) (orderedInterval (1423861966 / 1000000000000) (1423862030 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_chunkChecks0 :
    compactCertificate353.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate353.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate353_chunkChecks0_0
    compactCertificate353_chunkChecks0_1 compactCertificate353_chunkChecks0_2

theorem compactCertificate353_chunkChecks1_0 :
    compactCertificate353.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (449 / 2) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42036693504 / 1000000000000) (-42036589423 / 1000000000000), orderedInterval (32783653940 / 1000000000000) (32783758022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (661462735607549 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21513446970 / 1000000000000) (21513447610 / 1000000000000), orderedInterval (-58262594907 / 1000000000000) (-58262594268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (213903458085917 / 800000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-44107446082 / 1000000000000) (-44107446081 / 1000000000000), orderedInterval (-20785956753 / 1000000000000) (-20785956752 / 1000000000000)))) (orderedInterval (11141685521 / 1000000000000) (11141726798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (193013176538743 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-108229476998 / 1000000000000) (-108229474946 / 1000000000000), orderedInterval (39580717589 / 1000000000000) (39580719641 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (518460541732171 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-70063353536 / 1000000000000) (-70063353478 / 1000000000000), orderedInterval (1915259711 / 1000000000000) (1915259769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1407721225741407 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (32148074756 / 1000000000000) (32148074757 / 1000000000000), orderedInterval (27801015107 / 1000000000000) (27801015108 / 1000000000000)))) (orderedInterval (-3150109576 / 1000000000000) (-3150109538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1036921083464791 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33305230700 / 1000000000000) (33305253867 / 1000000000000), orderedInterval (-36759879515 / 1000000000000) (-36759856348 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1776781950270643 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34166701617 / 1000000000000) (-34166659363 / 1000000000000), orderedInterval (16342873230 / 1000000000000) (16342915484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1308769542765337 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41884318675 / 1000000000000) (41884318677 / 1000000000000), orderedInterval (13770977479 / 1000000000000) (13770977480 / 1000000000000)))) (orderedInterval (-512316970 / 1000000000000) (-512314369 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_chunkChecks1_1 :
    compactCertificate353.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2007989043794551 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4531185332 / 1000000000000) (4531185333 / 1000000000000), orderedInterval (35317473836 / 1000000000000) (35317473837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1159313014964479 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (46861315615 / 1000000000000) (46861315776 / 1000000000000), orderedInterval (-826009422 / 1000000000000) (-826009260 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2057221289054411 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4585922285 / 1000000000000) (-4585922282 / 1000000000000), orderedInterval (34887039506 / 1000000000000) (34887039509 / 1000000000000)))) (orderedInterval (-2749981659 / 1000000000000) (-2749981457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1922122983961559 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22091593740 / 1000000000000) (-22091593739 / 1000000000000), orderedInterval (-28904301162 / 1000000000000) (-28904301161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1371717658023047 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41287665700 / 1000000000000) (-41287665697 / 1000000000000), orderedInterval (-12258217189 / 1000000000000) (-12258217186 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1555381625196513 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2950886832 / 1000000000000) (2950886833 / 1000000000000), orderedInterval (40350869969 / 1000000000000) (40350869970 / 1000000000000)))) (orderedInterval (-1007435662 / 1000000000000) (-1007435617 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1296715042402897 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43508243841 / 1000000000000) (-43508243831 / 1000000000000), orderedInterval (-8348529572 / 1000000000000) (-8348529562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1145687065384837 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45691134257 / 1000000000000) (-45691134254 / 1000000000000), orderedInterval (-11538446120 / 1000000000000) (-11538446116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (332064766846863 / 800000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36147546843 / 1000000000000) (36147546845 / 1000000000000), orderedInterval (15025578754 / 1000000000000) (15025578756 / 1000000000000)))) (orderedInterval (1414525613 / 1000000000000) (1414525645 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_chunkChecks1_2 :
    compactCertificate353.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (918508620709661 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46332227888 / 1000000000000) (-46332227887 / 1000000000000), orderedInterval (-24913657603 / 1000000000000) (-24913657602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (778629929980021 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35220473595 / 1000000000000) (35220473596 / 1000000000000), orderedInterval (44964856452 / 1000000000000) (44964856453 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (487230457234663 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-5047261161 / 1000000000000) (-5047261159 / 1000000000000), orderedInterval (-72097278153 / 1000000000000) (-72097278151 / 1000000000000)))) (orderedInterval (594279333 / 1000000000000) (594279386 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (262034160356121 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30877207633 / 1000000000000) (-30877207632 / 1000000000000), orderedInterval (-93385621566 / 1000000000000) (-93385621565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (711473718271363 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24266569023 / 1000000000000) (24266570294 / 1000000000000), orderedInterval (-54751889273 / 1000000000000) (-54751888002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (971456536540451 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-50411359297 / 1000000000000) (-50411358378 / 1000000000000), orderedInterval (9047483351 / 1000000000000) (9047484270 / 1000000000000)))) (orderedInterval (737198554 / 1000000000000) (737198678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (410769542765337 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (15332757861 / 1000000000000) (15332757983 / 1000000000000), orderedInterval (-77303295676 / 1000000000000) (-77303295554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1669755386097977 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14923748273 / 1000000000000) (-14923748272 / 1000000000000), orderedInterval (-36070123685 / 1000000000000) (-36070123684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1115319214663543 / 4000000000000) 1 (IntervalRat.scale (449 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-621508470 / 1000000000000) (-621508468 / 1000000000000), orderedInterval (-47777557423 / 1000000000000) (-47777557421 / 1000000000000)))) (orderedInterval (16380138282 / 1000000000000) (16380138371 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_chunkChecks1 :
    compactCertificate353.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate353.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate353_chunkChecks1_0
    compactCertificate353_chunkChecks1_1 compactCertificate353_chunkChecks1_2

theorem compactCertificate353_chunkChecks2_0 :
    compactCertificate353.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (449 / 2) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42036693504 / 1000000000000) (-42036589423 / 1000000000000), orderedInterval (32783653940 / 1000000000000) (32783758022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (661462735607549 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21513446970 / 1000000000000) (21513447610 / 1000000000000), orderedInterval (-58262594907 / 1000000000000) (-58262594268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (213903458085917 / 800000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-44107446082 / 1000000000000) (-44107446081 / 1000000000000), orderedInterval (-20785956753 / 1000000000000) (-20785956752 / 1000000000000)))) (orderedInterval (20174851625 / 1000000000000) (20174893087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (193013176538743 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-108229476998 / 1000000000000) (-108229474946 / 1000000000000), orderedInterval (39580717589 / 1000000000000) (39580719641 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (518460541732171 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-70063353536 / 1000000000000) (-70063353478 / 1000000000000), orderedInterval (1915259711 / 1000000000000) (1915259769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1407721225741407 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (32148074756 / 1000000000000) (32148074757 / 1000000000000), orderedInterval (27801015107 / 1000000000000) (27801015108 / 1000000000000)))) (orderedInterval (6428689235 / 1000000000000) (6428689280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1036921083464791 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33305230700 / 1000000000000) (33305253867 / 1000000000000), orderedInterval (-36759879515 / 1000000000000) (-36759856348 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1776781950270643 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34166701617 / 1000000000000) (-34166659363 / 1000000000000), orderedInterval (16342873230 / 1000000000000) (16342915484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1308769542765337 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41884318675 / 1000000000000) (41884318677 / 1000000000000), orderedInterval (13770977479 / 1000000000000) (13770977480 / 1000000000000)))) (orderedInterval (-6273477287 / 1000000000000) (-6273472134 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_chunkChecks2_1 :
    compactCertificate353.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2007989043794551 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4531185332 / 1000000000000) (4531185333 / 1000000000000), orderedInterval (35317473836 / 1000000000000) (35317473837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1159313014964479 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (46861315615 / 1000000000000) (46861315776 / 1000000000000), orderedInterval (-826009422 / 1000000000000) (-826009260 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2057221289054411 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4585922285 / 1000000000000) (-4585922282 / 1000000000000), orderedInterval (34887039506 / 1000000000000) (34887039509 / 1000000000000)))) (orderedInterval (1672580753 / 1000000000000) (1672581172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1922122983961559 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22091593740 / 1000000000000) (-22091593739 / 1000000000000), orderedInterval (-28904301162 / 1000000000000) (-28904301161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1371717658023047 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41287665700 / 1000000000000) (-41287665697 / 1000000000000), orderedInterval (-12258217189 / 1000000000000) (-12258217186 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1555381625196513 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2950886832 / 1000000000000) (2950886833 / 1000000000000), orderedInterval (40350869969 / 1000000000000) (40350869970 / 1000000000000)))) (orderedInterval (7332064889 / 1000000000000) (7332064963 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1296715042402897 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43508243841 / 1000000000000) (-43508243831 / 1000000000000), orderedInterval (-8348529572 / 1000000000000) (-8348529562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1145687065384837 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45691134257 / 1000000000000) (-45691134254 / 1000000000000), orderedInterval (-11538446120 / 1000000000000) (-11538446116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (332064766846863 / 800000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36147546843 / 1000000000000) (36147546845 / 1000000000000), orderedInterval (15025578754 / 1000000000000) (15025578756 / 1000000000000)))) (orderedInterval (-6378635317 / 1000000000000) (-6378635270 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_chunkChecks2_2 :
    compactCertificate353.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (918508620709661 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46332227888 / 1000000000000) (-46332227887 / 1000000000000), orderedInterval (-24913657603 / 1000000000000) (-24913657602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (778629929980021 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35220473595 / 1000000000000) (35220473596 / 1000000000000), orderedInterval (44964856452 / 1000000000000) (44964856453 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (487230457234663 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-5047261161 / 1000000000000) (-5047261159 / 1000000000000), orderedInterval (-72097278153 / 1000000000000) (-72097278151 / 1000000000000)))) (orderedInterval (-6205968530 / 1000000000000) (-6205968480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (262034160356121 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30877207633 / 1000000000000) (-30877207632 / 1000000000000), orderedInterval (-93385621566 / 1000000000000) (-93385621565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (711473718271363 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24266569023 / 1000000000000) (24266570294 / 1000000000000), orderedInterval (-54751889273 / 1000000000000) (-54751888002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (971456536540451 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-50411359297 / 1000000000000) (-50411358378 / 1000000000000), orderedInterval (9047483351 / 1000000000000) (9047484270 / 1000000000000)))) (orderedInterval (-4227636229 / 1000000000000) (-4227636103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (410769542765337 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (15332757861 / 1000000000000) (15332757983 / 1000000000000), orderedInterval (-77303295676 / 1000000000000) (-77303295554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1669755386097977 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14923748273 / 1000000000000) (-14923748272 / 1000000000000), orderedInterval (-36070123685 / 1000000000000) (-36070123684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1115319214663543 / 4000000000000) 2 (IntervalRat.scale (449 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-621508470 / 1000000000000) (-621508468 / 1000000000000), orderedInterval (-47777557423 / 1000000000000) (-47777557421 / 1000000000000)))) (orderedInterval (-4472335036 / 1000000000000) (-4472334905 / 1000000000000))) = true
  rfl'

theorem compactCertificate353_chunkChecks2 :
    compactCertificate353.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate353.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate353_chunkChecks2_0
    compactCertificate353_chunkChecks2_1 compactCertificate353_chunkChecks2_2

theorem compactCertificate353_chunkChecks3_0 :
    compactCertificate353.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (449 / 2) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42036693504 / 1000000000000) (-42036589423 / 1000000000000), orderedInterval (32783653940 / 1000000000000) (32783758022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (661462735607549 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21513446970 / 1000000000000) (21513447610 / 1000000000000), orderedInterval (-58262594907 / 1000000000000) (-58262594268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (213903458085917 / 800000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-44107446082 / 1000000000000) (-44107446081 / 1000000000000), orderedInterval (-20785956753 / 1000000000000) (-20785956752 / 1000000000000)))) (orderedInterval (-10806363414 / 1000000000000) (-10806321951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (193013176538743 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-108229476998 / 1000000000000) (-108229474946 / 1000000000000), orderedInterval (39580717589 / 1000000000000) (39580719641 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (518460541732171 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-70063353536 / 1000000000000) (-70063353478 / 1000000000000), orderedInterval (1915259711 / 1000000000000) (1915259769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1407721225741407 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (32148074756 / 1000000000000) (32148074757 / 1000000000000), orderedInterval (27801015107 / 1000000000000) (27801015108 / 1000000000000)))) (orderedInterval (7575670872 / 1000000000000) (7575670937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1036921083464791 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33305230700 / 1000000000000) (33305253867 / 1000000000000), orderedInterval (-36759879515 / 1000000000000) (-36759856348 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1776781950270643 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34166701617 / 1000000000000) (-34166659363 / 1000000000000), orderedInterval (16342873230 / 1000000000000) (16342915484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1308769542765337 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41884318675 / 1000000000000) (41884318677 / 1000000000000), orderedInterval (13770977479 / 1000000000000) (13770977480 / 1000000000000)))) (orderedInterval (2902191059 / 1000000000000) (2902201248 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate353_chunkChecks3_1 :
    compactCertificate353.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2007989043794551 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4531185332 / 1000000000000) (4531185333 / 1000000000000), orderedInterval (35317473836 / 1000000000000) (35317473837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1159313014964479 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (46861315615 / 1000000000000) (46861315776 / 1000000000000), orderedInterval (-826009422 / 1000000000000) (-826009260 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2057221289054411 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4585922285 / 1000000000000) (-4585922282 / 1000000000000), orderedInterval (34887039506 / 1000000000000) (34887039509 / 1000000000000)))) (orderedInterval (10659267796 / 1000000000000) (10659268696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1922122983961559 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22091593740 / 1000000000000) (-22091593739 / 1000000000000), orderedInterval (-28904301162 / 1000000000000) (-28904301161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1371717658023047 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41287665700 / 1000000000000) (-41287665697 / 1000000000000), orderedInterval (-12258217189 / 1000000000000) (-12258217186 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1555381625196513 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2950886832 / 1000000000000) (2950886833 / 1000000000000), orderedInterval (40350869969 / 1000000000000) (40350869970 / 1000000000000)))) (orderedInterval (42765349 / 1000000000000) (42765473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1296715042402897 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43508243841 / 1000000000000) (-43508243831 / 1000000000000), orderedInterval (-8348529572 / 1000000000000) (-8348529562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1145687065384837 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45691134257 / 1000000000000) (-45691134254 / 1000000000000), orderedInterval (-11538446120 / 1000000000000) (-11538446116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (332064766846863 / 800000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36147546843 / 1000000000000) (36147546845 / 1000000000000), orderedInterval (15025578754 / 1000000000000) (15025578756 / 1000000000000)))) (orderedInterval (-3484103674 / 1000000000000) (-3484103601 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate353_chunkChecks3_2 :
    compactCertificate353.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (918508620709661 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46332227888 / 1000000000000) (-46332227887 / 1000000000000), orderedInterval (-24913657603 / 1000000000000) (-24913657602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (778629929980021 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35220473595 / 1000000000000) (35220473596 / 1000000000000), orderedInterval (44964856452 / 1000000000000) (44964856453 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (487230457234663 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-5047261161 / 1000000000000) (-5047261159 / 1000000000000), orderedInterval (-72097278153 / 1000000000000) (-72097278151 / 1000000000000)))) (orderedInterval (-2201131433 / 1000000000000) (-2201131384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (262034160356121 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30877207633 / 1000000000000) (-30877207632 / 1000000000000), orderedInterval (-93385621566 / 1000000000000) (-93385621565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (711473718271363 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24266569023 / 1000000000000) (24266570294 / 1000000000000), orderedInterval (-54751889273 / 1000000000000) (-54751888002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (971456536540451 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-50411359297 / 1000000000000) (-50411358378 / 1000000000000), orderedInterval (9047483351 / 1000000000000) (9047484270 / 1000000000000)))) (orderedInterval (236086689 / 1000000000000) (236086818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (410769542765337 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (15332757861 / 1000000000000) (15332757983 / 1000000000000), orderedInterval (-77303295676 / 1000000000000) (-77303295554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1669755386097977 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14923748273 / 1000000000000) (-14923748272 / 1000000000000), orderedInterval (-36070123685 / 1000000000000) (-36070123684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1115319214663543 / 4000000000000) 3 (IntervalRat.scale (449 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-621508470 / 1000000000000) (-621508468 / 1000000000000), orderedInterval (-47777557423 / 1000000000000) (-47777557421 / 1000000000000)))) (orderedInterval (-35985802593 / 1000000000000) (-35985802392 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate353_chunkChecks3 :
    compactCertificate353.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate353.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate353_chunkChecks3_0
    compactCertificate353_chunkChecks3_1 compactCertificate353_chunkChecks3_2

theorem compactCertificate353_chunkChecks4_0 :
    compactCertificate353.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (449 / 2) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42036693504 / 1000000000000) (-42036589423 / 1000000000000), orderedInterval (32783653940 / 1000000000000) (32783758022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (661462735607549 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21513446970 / 1000000000000) (21513447610 / 1000000000000), orderedInterval (-58262594907 / 1000000000000) (-58262594268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (213903458085917 / 800000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-44107446082 / 1000000000000) (-44107446081 / 1000000000000), orderedInterval (-20785956753 / 1000000000000) (-20785956752 / 1000000000000)))) (orderedInterval (-21714015345 / 1000000000000) (-21713973696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (193013176538743 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-108229476998 / 1000000000000) (-108229474946 / 1000000000000), orderedInterval (39580717589 / 1000000000000) (39580719641 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (518460541732171 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-70063353536 / 1000000000000) (-70063353478 / 1000000000000), orderedInterval (1915259711 / 1000000000000) (1915259769 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1407721225741407 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (32148074756 / 1000000000000) (32148074757 / 1000000000000), orderedInterval (27801015107 / 1000000000000) (27801015108 / 1000000000000)))) (orderedInterval (-14150474811 / 1000000000000) (-14150474712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1036921083464791 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33305230700 / 1000000000000) (33305253867 / 1000000000000), orderedInterval (-36759879515 / 1000000000000) (-36759856348 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1776781950270643 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-34166701617 / 1000000000000) (-34166659363 / 1000000000000), orderedInterval (16342873230 / 1000000000000) (16342915484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1308769542765337 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41884318675 / 1000000000000) (41884318677 / 1000000000000), orderedInterval (13770977479 / 1000000000000) (13770977480 / 1000000000000)))) (orderedInterval (20692301340 / 1000000000000) (20692321536 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate353_chunkChecks4_1 :
    compactCertificate353.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2007989043794551 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4531185332 / 1000000000000) (4531185333 / 1000000000000), orderedInterval (35317473836 / 1000000000000) (35317473837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1159313014964479 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (46861315615 / 1000000000000) (46861315776 / 1000000000000), orderedInterval (-826009422 / 1000000000000) (-826009260 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2057221289054411 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4585922285 / 1000000000000) (-4585922282 / 1000000000000), orderedInterval (34887039506 / 1000000000000) (34887039509 / 1000000000000)))) (orderedInterval (-28534828037 / 1000000000000) (-28534826064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1922122983961559 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22091593740 / 1000000000000) (-22091593739 / 1000000000000), orderedInterval (-28904301162 / 1000000000000) (-28904301161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1371717658023047 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41287665700 / 1000000000000) (-41287665697 / 1000000000000), orderedInterval (-12258217189 / 1000000000000) (-12258217186 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1555381625196513 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (2950886832 / 1000000000000) (2950886833 / 1000000000000), orderedInterval (40350869969 / 1000000000000) (40350869970 / 1000000000000)))) (orderedInterval (-13019874653 / 1000000000000) (-13019874439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1296715042402897 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-43508243841 / 1000000000000) (-43508243831 / 1000000000000), orderedInterval (-8348529572 / 1000000000000) (-8348529562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1145687065384837 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45691134257 / 1000000000000) (-45691134254 / 1000000000000), orderedInterval (-11538446120 / 1000000000000) (-11538446116 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (332064766846863 / 800000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36147546843 / 1000000000000) (36147546845 / 1000000000000), orderedInterval (15025578754 / 1000000000000) (15025578756 / 1000000000000)))) (orderedInterval (15589806289 / 1000000000000) (15589806404 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate353_chunkChecks4_2 :
    compactCertificate353.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (918508620709661 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46332227888 / 1000000000000) (-46332227887 / 1000000000000), orderedInterval (-24913657603 / 1000000000000) (-24913657602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (778629929980021 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35220473595 / 1000000000000) (35220473596 / 1000000000000), orderedInterval (44964856452 / 1000000000000) (44964856453 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (487230457234663 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-5047261161 / 1000000000000) (-5047261159 / 1000000000000), orderedInterval (-72097278153 / 1000000000000) (-72097278151 / 1000000000000)))) (orderedInterval (6986955236 / 1000000000000) (6986955284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (262034160356121 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-30877207633 / 1000000000000) (-30877207632 / 1000000000000), orderedInterval (-93385621566 / 1000000000000) (-93385621565 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (711473718271363 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24266569023 / 1000000000000) (24266570294 / 1000000000000), orderedInterval (-54751889273 / 1000000000000) (-54751888002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (971456536540451 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-50411359297 / 1000000000000) (-50411358378 / 1000000000000), orderedInterval (9047483351 / 1000000000000) (9047484270 / 1000000000000)))) (orderedInterval (5076359360 / 1000000000000) (5076359495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (410769542765337 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (15332757861 / 1000000000000) (15332757983 / 1000000000000), orderedInterval (-77303295676 / 1000000000000) (-77303295554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1669755386097977 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14923748273 / 1000000000000) (-14923748272 / 1000000000000), orderedInterval (-36070123685 / 1000000000000) (-36070123684 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1115319214663543 / 4000000000000) 4 (IntervalRat.scale (449 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-621508470 / 1000000000000) (-621508468 / 1000000000000), orderedInterval (-47777557423 / 1000000000000) (-47777557421 / 1000000000000)))) (orderedInterval (15123736799 / 1000000000000) (15123737120 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate353_chunkChecks4 :
    compactCertificate353.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate353.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate353_chunkChecks4_0
    compactCertificate353_chunkChecks4_1 compactCertificate353_chunkChecks4_2

theorem compactCertificate353_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate353.chunkCheck r b = true :=
  compactCertificate353.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate353_chunkChecks0
    · exact compactCertificate353_chunkChecks1
    · exact compactCertificate353_chunkChecks2
    · exact compactCertificate353_chunkChecks3
    · exact compactCertificate353_chunkChecks4)

theorem compactCertificate353_coefficient0 :
    compactCertificate353.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate353_coefficient1 :
    compactCertificate353.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate353_coefficient2 :
    compactCertificate353.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate353_coefficient3 :
    compactCertificate353.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate353_coefficient4 :
    compactCertificate353.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate353_coefficients : ∀ r : Fin 5,
    compactCertificate353.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate353_coefficient0
  · exact compactCertificate353_coefficient1
  · exact compactCertificate353_coefficient2
  · exact compactCertificate353_coefficient3
  · exact compactCertificate353_coefficient4

theorem compactCertificate353_lower : (1 : ℚ) ≤ compactCertificate353.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate353, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate353_proves {t : ℝ} (ht : t ∈ compactCertificate353.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate353.proves compactCertificate353_states compactCertificate353_chunks
    compactCertificate353_coefficients compactCertificate353_lower ht

end Erdos232
