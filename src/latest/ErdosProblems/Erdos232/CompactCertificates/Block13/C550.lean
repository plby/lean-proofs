/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate550 : CompactCertificate where
  left := 421
  right := 422
  center := 843 / 2
  grid := fun i =>
    match i.val with
    | 0 => 134
    | 1 => 99
    | 2 => 160
    | 3 => 29
    | 4 => 78
    | 5 => 210
    | 6 => 155
    | 7 => 266
    | 8 => 196
    | 9 => 300
    | 10 => 173
    | 11 => 308
    | 12 => 287
    | 13 => 205
    | 14 => 233
    | 15 => 194
    | 16 => 171
    | 17 => 248
    | 18 => 137
    | 19 => 116
    | 20 => 73
    | 21 => 39
    | 22 => 106
    | 23 => 145
    | 24 => 61
    | 25 => 250
    | _ => 167
  point := fun i =>
    match i.val with
    | 0 => 843 / 2
    | 1 => 1241899969080543 / 4000000000000
    | 2 => 401604933555519 / 800000000000
    | 3 => 362383313635101 / 4000000000000
    | 4 => 973412553853497 / 4000000000000
    | 5 => 2643004439420949 / 4000000000000
    | 6 => 1946825107707837 / 4000000000000
    | 7 => 3335918004628401 / 4000000000000
    | 8 => 2457222103677459 / 4000000000000
    | 9 => 3770010610064157 / 4000000000000
    | 10 => 2176616640568053 / 4000000000000
    | 11 => 3862444424661177 / 4000000000000
    | 12 => 3608796604631613 / 4000000000000
    | 13 => 2575407540564429 / 4000000000000
    | 14 => 2920237661560491 / 4000000000000
    | 15 => 2434589712128379 / 4000000000000
    | 16 => 2151033844363959 / 4000000000000
    | 17 => 623453448667941 / 800000000000
    | 18 => 1724505049572927 / 4000000000000
    | 19 => 1461882028893447 / 4000000000000
    | 20 => 914777896322541 / 4000000000000
    | 21 => 491970595056147 / 4000000000000
    | 22 => 1335795867489441 / 4000000000000
    | 23 => 1823915056355457 / 4000000000000
    | 24 => 771222103677459 / 4000000000000
    | 25 => 3134975034477939 / 4000000000000
    | _ => 2094018035548701 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (37566102642 / 1000000000000) (37566102649 / 1000000000000), orderedInterval (9913058015 / 1000000000000) (9913058022 / 1000000000000))
    | 1 => (orderedInterval (-10865471679 / 1000000000000) (-10865471678 / 1000000000000), orderedInterval (-43941735839 / 1000000000000) (-43941735838 / 1000000000000))
    | 2 => (orderedInterval (4845535959 / 1000000000000) (4845535960 / 1000000000000), orderedInterval (35275092842 / 1000000000000) (35275092843 / 1000000000000))
    | 3 => (orderedInterval (-22654767060 / 1000000000000) (-22654767059 / 1000000000000), orderedInterval (-80583612893 / 1000000000000) (-80583612892 / 1000000000000))
    | 4 => (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000))
    | 5 => (orderedInterval (30214995097 / 1000000000000) (30215011157 / 1000000000000), orderedInterval (-7131476416 / 1000000000000) (-7131460355 / 1000000000000))
    | 6 => (orderedInterval (-18735663648 / 1000000000000) (-18735663647 / 1000000000000), orderedInterval (-30916033232 / 1000000000000) (-30916033231 / 1000000000000))
    | 7 => (orderedInterval (-21623434753 / 1000000000000) (-21623428239 / 1000000000000), orderedInterval (17211187330 / 1000000000000) (17211193844 / 1000000000000))
    | 8 => (orderedInterval (-19774038427 / 1000000000000) (-19774036770 / 1000000000000), orderedInterval (25419083096 / 1000000000000) (25419084753 / 1000000000000))
    | 9 => (orderedInterval (18826082542 / 1000000000000) (18826082543 / 1000000000000), orderedInterval (17907472217 / 1000000000000) (17907472218 / 1000000000000))
    | 10 => (orderedInterval (-33928709975 / 1000000000000) (-33928709841 / 1000000000000), orderedInterval (-4300979089 / 1000000000000) (-4300978956 / 1000000000000))
    | 11 => (orderedInterval (-24061069218 / 1000000000000) (-24061001716 / 1000000000000), orderedInterval (8976718833 / 1000000000000) (8976786335 / 1000000000000))
    | 12 => (orderedInterval (-25903148856 / 1000000000000) (-25903148444 / 1000000000000), orderedInterval (-5872739367 / 1000000000000) (-5872738955 / 1000000000000))
    | 13 => (orderedInterval (-18028963528 / 1000000000000) (-18028963527 / 1000000000000), orderedInterval (-25748840683 / 1000000000000) (-25748840682 / 1000000000000))
    | 14 => (orderedInterval (26910666713 / 1000000000000) (26910771302 / 1000000000000), orderedInterval (-12176767345 / 1000000000000) (-12176662756 / 1000000000000))
    | 15 => (orderedInterval (-1175474792 / 1000000000000) (-1175474791 / 1000000000000), orderedInterval (32320879285 / 1000000000000) (32320879286 / 1000000000000))
    | 16 => (orderedInterval (-33424766577 / 1000000000000) (-33424766552 / 1000000000000), orderedInterval (-8131283737 / 1000000000000) (-8131283712 / 1000000000000))
    | 17 => (orderedInterval (23848721597 / 1000000000000) (23848721599 / 1000000000000), orderedInterval (15736940456 / 1000000000000) (15736940458 / 1000000000000))
    | 18 => (orderedInterval (-38363334936 / 1000000000000) (-38363334779 / 1000000000000), orderedInterval (-2168425680 / 1000000000000) (-2168425522 / 1000000000000))
    | 19 => (orderedInterval (40333309661 / 1000000000000) (40333314425 / 1000000000000), orderedInterval (-10785552182 / 1000000000000) (-10785547418 / 1000000000000))
    | 20 => (orderedInterval (-7522348068 / 1000000000000) (-7522348067 / 1000000000000), orderedInterval (-52205518775 / 1000000000000) (-52205518774 / 1000000000000))
    | 21 => (orderedInterval (-68385119043 / 1000000000000) (-68385119042 / 1000000000000), orderedInterval (-22071962617 / 1000000000000) (-22071962616 / 1000000000000))
    | 22 => (orderedInterval (43142392462 / 1000000000000) (43142393695 / 1000000000000), orderedInterval (-6778042548 / 1000000000000) (-6778041315 / 1000000000000))
    | 23 => (orderedInterval (-35253038142 / 1000000000000) (-35253038138 / 1000000000000), orderedInterval (-12346159231 / 1000000000000) (-12346159227 / 1000000000000))
    | 24 => (orderedInterval (-53313036004 / 1000000000000) (-53313029144 / 1000000000000), orderedInterval (21576247392 / 1000000000000) (21576254253 / 1000000000000))
    | 25 => (orderedInterval (-21768451700 / 1000000000000) (-21768445466 / 1000000000000), orderedInterval (18409946825 / 1000000000000) (18409953059 / 1000000000000))
    | _ => (orderedInterval (12163908142 / 1000000000000) (12163908200 / 1000000000000), orderedInterval (-32693614336 / 1000000000000) (-32693614278 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (15072984453 / 1000000000000) (15072984485 / 1000000000000)
      | 1 => orderedInterval (-3372201560 / 1000000000000) (-3372196344 / 1000000000000)
      | 2 => orderedInterval (189053536 / 1000000000000) (189053801 / 1000000000000)
      | 3 => orderedInterval (-9279428612 / 1000000000000) (-9279418839 / 1000000000000)
      | 4 => orderedInterval (-1373422724 / 1000000000000) (-1373422137 / 1000000000000)
      | 5 => orderedInterval (2509835779 / 1000000000000) (2509835821 / 1000000000000)
      | 6 => orderedInterval (3606251326 / 1000000000000) (3606251727 / 1000000000000)
      | 7 => orderedInterval (2985726674 / 1000000000000) (2985726753 / 1000000000000)
      | _ => orderedInterval (-831670233 / 1000000000000) (-831669556 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (6092936576 / 1000000000000) (6092936613 / 1000000000000)
      | 1 => orderedInterval (1649355531 / 1000000000000) (1649359702 / 1000000000000)
      | 2 => orderedInterval (-155023366 / 1000000000000) (-155022869 / 1000000000000)
      | 3 => orderedInterval (-4603042703 / 1000000000000) (-4603020360 / 1000000000000)
      | 4 => orderedInterval (-3385683823 / 1000000000000) (-3385682808 / 1000000000000)
      | 5 => orderedInterval (1877598102 / 1000000000000) (1877598163 / 1000000000000)
      | 6 => orderedInterval (-38191093 / 1000000000000) (-38190735 / 1000000000000)
      | 7 => orderedInterval (1264351954 / 1000000000000) (1264352023 / 1000000000000)
      | _ => orderedInterval (4891656044 / 1000000000000) (4891657184 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-15252743127 / 1000000000000) (-15252743086 / 1000000000000)
      | 1 => orderedInterval (5753223265 / 1000000000000) (5753227502 / 1000000000000)
      | 2 => orderedInterval (-1595553707 / 1000000000000) (-1595552761 / 1000000000000)
      | 3 => orderedInterval (38877458106 / 1000000000000) (38877509278 / 1000000000000)
      | 4 => orderedInterval (2252149158 / 1000000000000) (2252150917 / 1000000000000)
      | 5 => orderedInterval (-5177028885 / 1000000000000) (-5177028795 / 1000000000000)
      | 6 => orderedInterval (-4628916474 / 1000000000000) (-4628916150 / 1000000000000)
      | 7 => orderedInterval (-2657965972 / 1000000000000) (-2657965909 / 1000000000000)
      | _ => orderedInterval (-2550316142 / 1000000000000) (-2550314118 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-7226372193 / 1000000000000) (-7226372145 / 1000000000000)
      | 1 => orderedInterval (-2197576269 / 1000000000000) (-2197570967 / 1000000000000)
      | 2 => orderedInterval (2214015804 / 1000000000000) (2214017619 / 1000000000000)
      | 3 => orderedInterval (20825959671 / 1000000000000) (20826076810 / 1000000000000)
      | 4 => orderedInterval (7313222774 / 1000000000000) (7313225830 / 1000000000000)
      | 5 => orderedInterval (-4624515466 / 1000000000000) (-4624515328 / 1000000000000)
      | 6 => orderedInterval (-486515583 / 1000000000000) (-486515289 / 1000000000000)
      | 7 => orderedInterval (-1278193315 / 1000000000000) (-1278193253 / 1000000000000)
      | _ => orderedInterval (-2124541392 / 1000000000000) (-2124537727 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15466404658 / 1000000000000) (15466404713 / 1000000000000)
      | 1 => orderedInterval (-13123855879 / 1000000000000) (-13123848329 / 1000000000000)
      | 2 => orderedInterval (8055088824 / 1000000000000) (8055092338 / 1000000000000)
      | 3 => orderedInterval (-184920995055 / 1000000000000) (-184920726564 / 1000000000000)
      | 4 => orderedInterval (-726670198 / 1000000000000) (-726664867 / 1000000000000)
      | 5 => orderedInterval (12166490259 / 1000000000000) (12166490475 / 1000000000000)
      | 6 => orderedInterval (5404588530 / 1000000000000) (5404588801 / 1000000000000)
      | 7 => orderedInterval (3329814130 / 1000000000000) (3329814191 / 1000000000000)
      | _ => orderedInterval (15747278129 / 1000000000000) (15747284837 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (9507128639 / 1000000000000) (9507145711 / 1000000000000)
    | 1 => orderedInterval (7593957222 / 1000000000000) (7593986913 / 1000000000000)
    | 2 => orderedInterval (15020306222 / 1000000000000) (15020366878 / 1000000000000)
    | 3 => orderedInterval (12415484031 / 1000000000000) (12415615550 / 1000000000000)
    | _ => orderedInterval (-138601856602 / 1000000000000) (-138601564405 / 1000000000000)

theorem compactCertificate550_stateChecks0 :
    compactCertificate550.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (843 / 2)) (orderedInterval (37566102642 / 1000000000000) (37566102649 / 1000000000000), orderedInterval (9913058015 / 1000000000000) (9913058022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1241899969080543 / 4000000000000)) (orderedInterval (-10865471679 / 1000000000000) (-10865471678 / 1000000000000), orderedInterval (-43941735839 / 1000000000000) (-43941735838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (401604933555519 / 800000000000)) (orderedInterval (4845535959 / 1000000000000) (4845535960 / 1000000000000), orderedInterval (35275092842 / 1000000000000) (35275092843 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_stateChecks1 :
    compactCertificate550.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (362383313635101 / 4000000000000)) (orderedInterval (-22654767060 / 1000000000000) (-22654767059 / 1000000000000), orderedInterval (-80583612893 / 1000000000000) (-80583612892 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (973412553853497 / 4000000000000)) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2643004439420949 / 4000000000000)) (orderedInterval (30214995097 / 1000000000000) (30215011157 / 1000000000000), orderedInterval (-7131476416 / 1000000000000) (-7131460355 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_stateChecks2 :
    compactCertificate550.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1946825107707837 / 4000000000000)) (orderedInterval (-18735663648 / 1000000000000) (-18735663647 / 1000000000000), orderedInterval (-30916033232 / 1000000000000) (-30916033231 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (3335918004628401 / 4000000000000)) (orderedInterval (-21623434753 / 1000000000000) (-21623428239 / 1000000000000), orderedInterval (17211187330 / 1000000000000) (17211193844 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2457222103677459 / 4000000000000)) (orderedInterval (-19774038427 / 1000000000000) (-19774036770 / 1000000000000), orderedInterval (25419083096 / 1000000000000) (25419084753 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_stateChecks3 :
    compactCertificate550.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 300 12 (3770010610064157 / 4000000000000)) (orderedInterval (18826082542 / 1000000000000) (18826082543 / 1000000000000), orderedInterval (17907472217 / 1000000000000) (17907472218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2176616640568053 / 4000000000000)) (orderedInterval (-33928709975 / 1000000000000) (-33928709841 / 1000000000000), orderedInterval (-4300979089 / 1000000000000) (-4300978956 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 308 12 (3862444424661177 / 4000000000000)) (orderedInterval (-24061069218 / 1000000000000) (-24061001716 / 1000000000000), orderedInterval (8976718833 / 1000000000000) (8976786335 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_stateChecks4 :
    compactCertificate550.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 287 12 (3608796604631613 / 4000000000000)) (orderedInterval (-25903148856 / 1000000000000) (-25903148444 / 1000000000000), orderedInterval (-5872739367 / 1000000000000) (-5872738955 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2575407540564429 / 4000000000000)) (orderedInterval (-18028963528 / 1000000000000) (-18028963527 / 1000000000000), orderedInterval (-25748840683 / 1000000000000) (-25748840682 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (2920237661560491 / 4000000000000)) (orderedInterval (26910666713 / 1000000000000) (26910771302 / 1000000000000), orderedInterval (-12176767345 / 1000000000000) (-12176662756 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_stateChecks5 :
    compactCertificate550.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2434589712128379 / 4000000000000)) (orderedInterval (-1175474792 / 1000000000000) (-1175474791 / 1000000000000), orderedInterval (32320879285 / 1000000000000) (32320879286 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2151033844363959 / 4000000000000)) (orderedInterval (-33424766577 / 1000000000000) (-33424766552 / 1000000000000), orderedInterval (-8131283737 / 1000000000000) (-8131283712 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (623453448667941 / 800000000000)) (orderedInterval (23848721597 / 1000000000000) (23848721599 / 1000000000000), orderedInterval (15736940456 / 1000000000000) (15736940458 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_stateChecks6 :
    compactCertificate550.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1724505049572927 / 4000000000000)) (orderedInterval (-38363334936 / 1000000000000) (-38363334779 / 1000000000000), orderedInterval (-2168425680 / 1000000000000) (-2168425522 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1461882028893447 / 4000000000000)) (orderedInterval (40333309661 / 1000000000000) (40333314425 / 1000000000000), orderedInterval (-10785552182 / 1000000000000) (-10785547418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (914777896322541 / 4000000000000)) (orderedInterval (-7522348068 / 1000000000000) (-7522348067 / 1000000000000), orderedInterval (-52205518775 / 1000000000000) (-52205518774 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_stateChecks7 :
    compactCertificate550.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (491970595056147 / 4000000000000)) (orderedInterval (-68385119043 / 1000000000000) (-68385119042 / 1000000000000), orderedInterval (-22071962617 / 1000000000000) (-22071962616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1335795867489441 / 4000000000000)) (orderedInterval (43142392462 / 1000000000000) (43142393695 / 1000000000000), orderedInterval (-6778042548 / 1000000000000) (-6778041315 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1823915056355457 / 4000000000000)) (orderedInterval (-35253038142 / 1000000000000) (-35253038138 / 1000000000000), orderedInterval (-12346159231 / 1000000000000) (-12346159227 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_stateChecks8 :
    compactCertificate550.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (771222103677459 / 4000000000000)) (orderedInterval (-53313036004 / 1000000000000) (-53313029144 / 1000000000000), orderedInterval (21576247392 / 1000000000000) (21576254253 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (3134975034477939 / 4000000000000)) (orderedInterval (-21768451700 / 1000000000000) (-21768445466 / 1000000000000), orderedInterval (18409946825 / 1000000000000) (18409953059 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2094018035548701 / 4000000000000)) (orderedInterval (12163908142 / 1000000000000) (12163908200 / 1000000000000), orderedInterval (-32693614336 / 1000000000000) (-32693614278 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_states : ∀ j,
    BesselStateValid (compactCertificate550.point j) (compactCertificate550.state j) :=
  compactCertificate550.statesValid_of_checks3 compactCertificate550_stateChecks0
    compactCertificate550_stateChecks1 compactCertificate550_stateChecks2
    compactCertificate550_stateChecks3 compactCertificate550_stateChecks4
    compactCertificate550_stateChecks5 compactCertificate550_stateChecks6
    compactCertificate550_stateChecks7 compactCertificate550_stateChecks8

theorem compactCertificate550_chunkChecks0_0 :
    compactCertificate550.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (843 / 2) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37566102642 / 1000000000000) (37566102649 / 1000000000000), orderedInterval (9913058015 / 1000000000000) (9913058022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1241899969080543 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-10865471679 / 1000000000000) (-10865471678 / 1000000000000), orderedInterval (-43941735839 / 1000000000000) (-43941735838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (401604933555519 / 800000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4845535959 / 1000000000000) (4845535960 / 1000000000000), orderedInterval (35275092842 / 1000000000000) (35275092843 / 1000000000000)))) (orderedInterval (15072984453 / 1000000000000) (15072984485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (362383313635101 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-22654767060 / 1000000000000) (-22654767059 / 1000000000000), orderedInterval (-80583612893 / 1000000000000) (-80583612892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (973412553853497 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2643004439420949 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30214995097 / 1000000000000) (30215011157 / 1000000000000), orderedInterval (-7131476416 / 1000000000000) (-7131460355 / 1000000000000)))) (orderedInterval (-3372201560 / 1000000000000) (-3372196344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1946825107707837 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18735663648 / 1000000000000) (-18735663647 / 1000000000000), orderedInterval (-30916033232 / 1000000000000) (-30916033231 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3335918004628401 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21623434753 / 1000000000000) (-21623428239 / 1000000000000), orderedInterval (17211187330 / 1000000000000) (17211193844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2457222103677459 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19774038427 / 1000000000000) (-19774036770 / 1000000000000), orderedInterval (25419083096 / 1000000000000) (25419084753 / 1000000000000)))) (orderedInterval (189053536 / 1000000000000) (189053801 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_chunkChecks0_1 :
    compactCertificate550.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3770010610064157 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18826082542 / 1000000000000) (18826082543 / 1000000000000), orderedInterval (17907472217 / 1000000000000) (17907472218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2176616640568053 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33928709975 / 1000000000000) (-33928709841 / 1000000000000), orderedInterval (-4300979089 / 1000000000000) (-4300978956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3862444424661177 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24061069218 / 1000000000000) (-24061001716 / 1000000000000), orderedInterval (8976718833 / 1000000000000) (8976786335 / 1000000000000)))) (orderedInterval (-9279428612 / 1000000000000) (-9279418839 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3608796604631613 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25903148856 / 1000000000000) (-25903148444 / 1000000000000), orderedInterval (-5872739367 / 1000000000000) (-5872738955 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2575407540564429 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-18028963528 / 1000000000000) (-18028963527 / 1000000000000), orderedInterval (-25748840683 / 1000000000000) (-25748840682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2920237661560491 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26910666713 / 1000000000000) (26910771302 / 1000000000000), orderedInterval (-12176767345 / 1000000000000) (-12176662756 / 1000000000000)))) (orderedInterval (-1373422724 / 1000000000000) (-1373422137 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2434589712128379 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1175474792 / 1000000000000) (-1175474791 / 1000000000000), orderedInterval (32320879285 / 1000000000000) (32320879286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2151033844363959 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33424766577 / 1000000000000) (-33424766552 / 1000000000000), orderedInterval (-8131283737 / 1000000000000) (-8131283712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (623453448667941 / 800000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23848721597 / 1000000000000) (23848721599 / 1000000000000), orderedInterval (15736940456 / 1000000000000) (15736940458 / 1000000000000)))) (orderedInterval (2509835779 / 1000000000000) (2509835821 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_chunkChecks0_2 :
    compactCertificate550.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1724505049572927 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38363334936 / 1000000000000) (-38363334779 / 1000000000000), orderedInterval (-2168425680 / 1000000000000) (-2168425522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1461882028893447 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40333309661 / 1000000000000) (40333314425 / 1000000000000), orderedInterval (-10785552182 / 1000000000000) (-10785547418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (914777896322541 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7522348068 / 1000000000000) (-7522348067 / 1000000000000), orderedInterval (-52205518775 / 1000000000000) (-52205518774 / 1000000000000)))) (orderedInterval (3606251326 / 1000000000000) (3606251727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (491970595056147 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68385119043 / 1000000000000) (-68385119042 / 1000000000000), orderedInterval (-22071962617 / 1000000000000) (-22071962616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1335795867489441 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43142392462 / 1000000000000) (43142393695 / 1000000000000), orderedInterval (-6778042548 / 1000000000000) (-6778041315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1823915056355457 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35253038142 / 1000000000000) (-35253038138 / 1000000000000), orderedInterval (-12346159231 / 1000000000000) (-12346159227 / 1000000000000)))) (orderedInterval (2985726674 / 1000000000000) (2985726753 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (771222103677459 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53313036004 / 1000000000000) (-53313029144 / 1000000000000), orderedInterval (21576247392 / 1000000000000) (21576254253 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3134975034477939 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21768451700 / 1000000000000) (-21768445466 / 1000000000000), orderedInterval (18409946825 / 1000000000000) (18409953059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2094018035548701 / 4000000000000) 0 (IntervalRat.scale (843 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12163908142 / 1000000000000) (12163908200 / 1000000000000), orderedInterval (-32693614336 / 1000000000000) (-32693614278 / 1000000000000)))) (orderedInterval (-831670233 / 1000000000000) (-831669556 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_chunkChecks0 :
    compactCertificate550.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate550.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate550_chunkChecks0_0
    compactCertificate550_chunkChecks0_1 compactCertificate550_chunkChecks0_2

theorem compactCertificate550_chunkChecks1_0 :
    compactCertificate550.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (843 / 2) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37566102642 / 1000000000000) (37566102649 / 1000000000000), orderedInterval (9913058015 / 1000000000000) (9913058022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1241899969080543 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-10865471679 / 1000000000000) (-10865471678 / 1000000000000), orderedInterval (-43941735839 / 1000000000000) (-43941735838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (401604933555519 / 800000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4845535959 / 1000000000000) (4845535960 / 1000000000000), orderedInterval (35275092842 / 1000000000000) (35275092843 / 1000000000000)))) (orderedInterval (6092936576 / 1000000000000) (6092936613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (362383313635101 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-22654767060 / 1000000000000) (-22654767059 / 1000000000000), orderedInterval (-80583612893 / 1000000000000) (-80583612892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (973412553853497 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2643004439420949 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30214995097 / 1000000000000) (30215011157 / 1000000000000), orderedInterval (-7131476416 / 1000000000000) (-7131460355 / 1000000000000)))) (orderedInterval (1649355531 / 1000000000000) (1649359702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1946825107707837 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18735663648 / 1000000000000) (-18735663647 / 1000000000000), orderedInterval (-30916033232 / 1000000000000) (-30916033231 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3335918004628401 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21623434753 / 1000000000000) (-21623428239 / 1000000000000), orderedInterval (17211187330 / 1000000000000) (17211193844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2457222103677459 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19774038427 / 1000000000000) (-19774036770 / 1000000000000), orderedInterval (25419083096 / 1000000000000) (25419084753 / 1000000000000)))) (orderedInterval (-155023366 / 1000000000000) (-155022869 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_chunkChecks1_1 :
    compactCertificate550.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3770010610064157 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18826082542 / 1000000000000) (18826082543 / 1000000000000), orderedInterval (17907472217 / 1000000000000) (17907472218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2176616640568053 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33928709975 / 1000000000000) (-33928709841 / 1000000000000), orderedInterval (-4300979089 / 1000000000000) (-4300978956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3862444424661177 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24061069218 / 1000000000000) (-24061001716 / 1000000000000), orderedInterval (8976718833 / 1000000000000) (8976786335 / 1000000000000)))) (orderedInterval (-4603042703 / 1000000000000) (-4603020360 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3608796604631613 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25903148856 / 1000000000000) (-25903148444 / 1000000000000), orderedInterval (-5872739367 / 1000000000000) (-5872738955 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2575407540564429 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-18028963528 / 1000000000000) (-18028963527 / 1000000000000), orderedInterval (-25748840683 / 1000000000000) (-25748840682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2920237661560491 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26910666713 / 1000000000000) (26910771302 / 1000000000000), orderedInterval (-12176767345 / 1000000000000) (-12176662756 / 1000000000000)))) (orderedInterval (-3385683823 / 1000000000000) (-3385682808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2434589712128379 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1175474792 / 1000000000000) (-1175474791 / 1000000000000), orderedInterval (32320879285 / 1000000000000) (32320879286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2151033844363959 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33424766577 / 1000000000000) (-33424766552 / 1000000000000), orderedInterval (-8131283737 / 1000000000000) (-8131283712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (623453448667941 / 800000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23848721597 / 1000000000000) (23848721599 / 1000000000000), orderedInterval (15736940456 / 1000000000000) (15736940458 / 1000000000000)))) (orderedInterval (1877598102 / 1000000000000) (1877598163 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_chunkChecks1_2 :
    compactCertificate550.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1724505049572927 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38363334936 / 1000000000000) (-38363334779 / 1000000000000), orderedInterval (-2168425680 / 1000000000000) (-2168425522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1461882028893447 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40333309661 / 1000000000000) (40333314425 / 1000000000000), orderedInterval (-10785552182 / 1000000000000) (-10785547418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (914777896322541 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7522348068 / 1000000000000) (-7522348067 / 1000000000000), orderedInterval (-52205518775 / 1000000000000) (-52205518774 / 1000000000000)))) (orderedInterval (-38191093 / 1000000000000) (-38190735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (491970595056147 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68385119043 / 1000000000000) (-68385119042 / 1000000000000), orderedInterval (-22071962617 / 1000000000000) (-22071962616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1335795867489441 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43142392462 / 1000000000000) (43142393695 / 1000000000000), orderedInterval (-6778042548 / 1000000000000) (-6778041315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1823915056355457 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35253038142 / 1000000000000) (-35253038138 / 1000000000000), orderedInterval (-12346159231 / 1000000000000) (-12346159227 / 1000000000000)))) (orderedInterval (1264351954 / 1000000000000) (1264352023 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (771222103677459 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53313036004 / 1000000000000) (-53313029144 / 1000000000000), orderedInterval (21576247392 / 1000000000000) (21576254253 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3134975034477939 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21768451700 / 1000000000000) (-21768445466 / 1000000000000), orderedInterval (18409946825 / 1000000000000) (18409953059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2094018035548701 / 4000000000000) 1 (IntervalRat.scale (843 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12163908142 / 1000000000000) (12163908200 / 1000000000000), orderedInterval (-32693614336 / 1000000000000) (-32693614278 / 1000000000000)))) (orderedInterval (4891656044 / 1000000000000) (4891657184 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_chunkChecks1 :
    compactCertificate550.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate550.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate550_chunkChecks1_0
    compactCertificate550_chunkChecks1_1 compactCertificate550_chunkChecks1_2

theorem compactCertificate550_chunkChecks2_0 :
    compactCertificate550.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (843 / 2) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37566102642 / 1000000000000) (37566102649 / 1000000000000), orderedInterval (9913058015 / 1000000000000) (9913058022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1241899969080543 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-10865471679 / 1000000000000) (-10865471678 / 1000000000000), orderedInterval (-43941735839 / 1000000000000) (-43941735838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (401604933555519 / 800000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4845535959 / 1000000000000) (4845535960 / 1000000000000), orderedInterval (35275092842 / 1000000000000) (35275092843 / 1000000000000)))) (orderedInterval (-15252743127 / 1000000000000) (-15252743086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (362383313635101 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-22654767060 / 1000000000000) (-22654767059 / 1000000000000), orderedInterval (-80583612893 / 1000000000000) (-80583612892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (973412553853497 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2643004439420949 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30214995097 / 1000000000000) (30215011157 / 1000000000000), orderedInterval (-7131476416 / 1000000000000) (-7131460355 / 1000000000000)))) (orderedInterval (5753223265 / 1000000000000) (5753227502 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1946825107707837 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18735663648 / 1000000000000) (-18735663647 / 1000000000000), orderedInterval (-30916033232 / 1000000000000) (-30916033231 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3335918004628401 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21623434753 / 1000000000000) (-21623428239 / 1000000000000), orderedInterval (17211187330 / 1000000000000) (17211193844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2457222103677459 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19774038427 / 1000000000000) (-19774036770 / 1000000000000), orderedInterval (25419083096 / 1000000000000) (25419084753 / 1000000000000)))) (orderedInterval (-1595553707 / 1000000000000) (-1595552761 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_chunkChecks2_1 :
    compactCertificate550.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3770010610064157 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18826082542 / 1000000000000) (18826082543 / 1000000000000), orderedInterval (17907472217 / 1000000000000) (17907472218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2176616640568053 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33928709975 / 1000000000000) (-33928709841 / 1000000000000), orderedInterval (-4300979089 / 1000000000000) (-4300978956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3862444424661177 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24061069218 / 1000000000000) (-24061001716 / 1000000000000), orderedInterval (8976718833 / 1000000000000) (8976786335 / 1000000000000)))) (orderedInterval (38877458106 / 1000000000000) (38877509278 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3608796604631613 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25903148856 / 1000000000000) (-25903148444 / 1000000000000), orderedInterval (-5872739367 / 1000000000000) (-5872738955 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2575407540564429 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-18028963528 / 1000000000000) (-18028963527 / 1000000000000), orderedInterval (-25748840683 / 1000000000000) (-25748840682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2920237661560491 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26910666713 / 1000000000000) (26910771302 / 1000000000000), orderedInterval (-12176767345 / 1000000000000) (-12176662756 / 1000000000000)))) (orderedInterval (2252149158 / 1000000000000) (2252150917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2434589712128379 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1175474792 / 1000000000000) (-1175474791 / 1000000000000), orderedInterval (32320879285 / 1000000000000) (32320879286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2151033844363959 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33424766577 / 1000000000000) (-33424766552 / 1000000000000), orderedInterval (-8131283737 / 1000000000000) (-8131283712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (623453448667941 / 800000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23848721597 / 1000000000000) (23848721599 / 1000000000000), orderedInterval (15736940456 / 1000000000000) (15736940458 / 1000000000000)))) (orderedInterval (-5177028885 / 1000000000000) (-5177028795 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_chunkChecks2_2 :
    compactCertificate550.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1724505049572927 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38363334936 / 1000000000000) (-38363334779 / 1000000000000), orderedInterval (-2168425680 / 1000000000000) (-2168425522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1461882028893447 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40333309661 / 1000000000000) (40333314425 / 1000000000000), orderedInterval (-10785552182 / 1000000000000) (-10785547418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (914777896322541 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7522348068 / 1000000000000) (-7522348067 / 1000000000000), orderedInterval (-52205518775 / 1000000000000) (-52205518774 / 1000000000000)))) (orderedInterval (-4628916474 / 1000000000000) (-4628916150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (491970595056147 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68385119043 / 1000000000000) (-68385119042 / 1000000000000), orderedInterval (-22071962617 / 1000000000000) (-22071962616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1335795867489441 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43142392462 / 1000000000000) (43142393695 / 1000000000000), orderedInterval (-6778042548 / 1000000000000) (-6778041315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1823915056355457 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35253038142 / 1000000000000) (-35253038138 / 1000000000000), orderedInterval (-12346159231 / 1000000000000) (-12346159227 / 1000000000000)))) (orderedInterval (-2657965972 / 1000000000000) (-2657965909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (771222103677459 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53313036004 / 1000000000000) (-53313029144 / 1000000000000), orderedInterval (21576247392 / 1000000000000) (21576254253 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3134975034477939 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21768451700 / 1000000000000) (-21768445466 / 1000000000000), orderedInterval (18409946825 / 1000000000000) (18409953059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2094018035548701 / 4000000000000) 2 (IntervalRat.scale (843 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12163908142 / 1000000000000) (12163908200 / 1000000000000), orderedInterval (-32693614336 / 1000000000000) (-32693614278 / 1000000000000)))) (orderedInterval (-2550316142 / 1000000000000) (-2550314118 / 1000000000000))) = true
  rfl'

theorem compactCertificate550_chunkChecks2 :
    compactCertificate550.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate550.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate550_chunkChecks2_0
    compactCertificate550_chunkChecks2_1 compactCertificate550_chunkChecks2_2

theorem compactCertificate550_chunkChecks3_0 :
    compactCertificate550.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (843 / 2) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37566102642 / 1000000000000) (37566102649 / 1000000000000), orderedInterval (9913058015 / 1000000000000) (9913058022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1241899969080543 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-10865471679 / 1000000000000) (-10865471678 / 1000000000000), orderedInterval (-43941735839 / 1000000000000) (-43941735838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (401604933555519 / 800000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4845535959 / 1000000000000) (4845535960 / 1000000000000), orderedInterval (35275092842 / 1000000000000) (35275092843 / 1000000000000)))) (orderedInterval (-7226372193 / 1000000000000) (-7226372145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (362383313635101 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-22654767060 / 1000000000000) (-22654767059 / 1000000000000), orderedInterval (-80583612893 / 1000000000000) (-80583612892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (973412553853497 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2643004439420949 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30214995097 / 1000000000000) (30215011157 / 1000000000000), orderedInterval (-7131476416 / 1000000000000) (-7131460355 / 1000000000000)))) (orderedInterval (-2197576269 / 1000000000000) (-2197570967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1946825107707837 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18735663648 / 1000000000000) (-18735663647 / 1000000000000), orderedInterval (-30916033232 / 1000000000000) (-30916033231 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3335918004628401 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21623434753 / 1000000000000) (-21623428239 / 1000000000000), orderedInterval (17211187330 / 1000000000000) (17211193844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2457222103677459 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19774038427 / 1000000000000) (-19774036770 / 1000000000000), orderedInterval (25419083096 / 1000000000000) (25419084753 / 1000000000000)))) (orderedInterval (2214015804 / 1000000000000) (2214017619 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate550_chunkChecks3_1 :
    compactCertificate550.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3770010610064157 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18826082542 / 1000000000000) (18826082543 / 1000000000000), orderedInterval (17907472217 / 1000000000000) (17907472218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2176616640568053 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33928709975 / 1000000000000) (-33928709841 / 1000000000000), orderedInterval (-4300979089 / 1000000000000) (-4300978956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3862444424661177 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24061069218 / 1000000000000) (-24061001716 / 1000000000000), orderedInterval (8976718833 / 1000000000000) (8976786335 / 1000000000000)))) (orderedInterval (20825959671 / 1000000000000) (20826076810 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3608796604631613 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25903148856 / 1000000000000) (-25903148444 / 1000000000000), orderedInterval (-5872739367 / 1000000000000) (-5872738955 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2575407540564429 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-18028963528 / 1000000000000) (-18028963527 / 1000000000000), orderedInterval (-25748840683 / 1000000000000) (-25748840682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2920237661560491 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26910666713 / 1000000000000) (26910771302 / 1000000000000), orderedInterval (-12176767345 / 1000000000000) (-12176662756 / 1000000000000)))) (orderedInterval (7313222774 / 1000000000000) (7313225830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2434589712128379 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1175474792 / 1000000000000) (-1175474791 / 1000000000000), orderedInterval (32320879285 / 1000000000000) (32320879286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2151033844363959 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33424766577 / 1000000000000) (-33424766552 / 1000000000000), orderedInterval (-8131283737 / 1000000000000) (-8131283712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (623453448667941 / 800000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23848721597 / 1000000000000) (23848721599 / 1000000000000), orderedInterval (15736940456 / 1000000000000) (15736940458 / 1000000000000)))) (orderedInterval (-4624515466 / 1000000000000) (-4624515328 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate550_chunkChecks3_2 :
    compactCertificate550.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1724505049572927 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38363334936 / 1000000000000) (-38363334779 / 1000000000000), orderedInterval (-2168425680 / 1000000000000) (-2168425522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1461882028893447 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40333309661 / 1000000000000) (40333314425 / 1000000000000), orderedInterval (-10785552182 / 1000000000000) (-10785547418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (914777896322541 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7522348068 / 1000000000000) (-7522348067 / 1000000000000), orderedInterval (-52205518775 / 1000000000000) (-52205518774 / 1000000000000)))) (orderedInterval (-486515583 / 1000000000000) (-486515289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (491970595056147 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68385119043 / 1000000000000) (-68385119042 / 1000000000000), orderedInterval (-22071962617 / 1000000000000) (-22071962616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1335795867489441 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43142392462 / 1000000000000) (43142393695 / 1000000000000), orderedInterval (-6778042548 / 1000000000000) (-6778041315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1823915056355457 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35253038142 / 1000000000000) (-35253038138 / 1000000000000), orderedInterval (-12346159231 / 1000000000000) (-12346159227 / 1000000000000)))) (orderedInterval (-1278193315 / 1000000000000) (-1278193253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (771222103677459 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53313036004 / 1000000000000) (-53313029144 / 1000000000000), orderedInterval (21576247392 / 1000000000000) (21576254253 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3134975034477939 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21768451700 / 1000000000000) (-21768445466 / 1000000000000), orderedInterval (18409946825 / 1000000000000) (18409953059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2094018035548701 / 4000000000000) 3 (IntervalRat.scale (843 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12163908142 / 1000000000000) (12163908200 / 1000000000000), orderedInterval (-32693614336 / 1000000000000) (-32693614278 / 1000000000000)))) (orderedInterval (-2124541392 / 1000000000000) (-2124537727 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate550_chunkChecks3 :
    compactCertificate550.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate550.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate550_chunkChecks3_0
    compactCertificate550_chunkChecks3_1 compactCertificate550_chunkChecks3_2

theorem compactCertificate550_chunkChecks4_0 :
    compactCertificate550.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (843 / 2) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37566102642 / 1000000000000) (37566102649 / 1000000000000), orderedInterval (9913058015 / 1000000000000) (9913058022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1241899969080543 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-10865471679 / 1000000000000) (-10865471678 / 1000000000000), orderedInterval (-43941735839 / 1000000000000) (-43941735838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (401604933555519 / 800000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4845535959 / 1000000000000) (4845535960 / 1000000000000), orderedInterval (35275092842 / 1000000000000) (35275092843 / 1000000000000)))) (orderedInterval (15466404658 / 1000000000000) (15466404713 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (362383313635101 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-22654767060 / 1000000000000) (-22654767059 / 1000000000000), orderedInterval (-80583612893 / 1000000000000) (-80583612892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (973412553853497 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-40261438024 / 1000000000000) (-40261327831 / 1000000000000), orderedInterval (31627114024 / 1000000000000) (31627224217 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2643004439420949 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30214995097 / 1000000000000) (30215011157 / 1000000000000), orderedInterval (-7131476416 / 1000000000000) (-7131460355 / 1000000000000)))) (orderedInterval (-13123855879 / 1000000000000) (-13123848329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1946825107707837 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18735663648 / 1000000000000) (-18735663647 / 1000000000000), orderedInterval (-30916033232 / 1000000000000) (-30916033231 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3335918004628401 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21623434753 / 1000000000000) (-21623428239 / 1000000000000), orderedInterval (17211187330 / 1000000000000) (17211193844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2457222103677459 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19774038427 / 1000000000000) (-19774036770 / 1000000000000), orderedInterval (25419083096 / 1000000000000) (25419084753 / 1000000000000)))) (orderedInterval (8055088824 / 1000000000000) (8055092338 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate550_chunkChecks4_1 :
    compactCertificate550.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3770010610064157 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18826082542 / 1000000000000) (18826082543 / 1000000000000), orderedInterval (17907472217 / 1000000000000) (17907472218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2176616640568053 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33928709975 / 1000000000000) (-33928709841 / 1000000000000), orderedInterval (-4300979089 / 1000000000000) (-4300978956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3862444424661177 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24061069218 / 1000000000000) (-24061001716 / 1000000000000), orderedInterval (8976718833 / 1000000000000) (8976786335 / 1000000000000)))) (orderedInterval (-184920995055 / 1000000000000) (-184920726564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3608796604631613 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-25903148856 / 1000000000000) (-25903148444 / 1000000000000), orderedInterval (-5872739367 / 1000000000000) (-5872738955 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2575407540564429 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-18028963528 / 1000000000000) (-18028963527 / 1000000000000), orderedInterval (-25748840683 / 1000000000000) (-25748840682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2920237661560491 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26910666713 / 1000000000000) (26910771302 / 1000000000000), orderedInterval (-12176767345 / 1000000000000) (-12176662756 / 1000000000000)))) (orderedInterval (-726670198 / 1000000000000) (-726664867 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2434589712128379 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-1175474792 / 1000000000000) (-1175474791 / 1000000000000), orderedInterval (32320879285 / 1000000000000) (32320879286 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2151033844363959 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33424766577 / 1000000000000) (-33424766552 / 1000000000000), orderedInterval (-8131283737 / 1000000000000) (-8131283712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (623453448667941 / 800000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23848721597 / 1000000000000) (23848721599 / 1000000000000), orderedInterval (15736940456 / 1000000000000) (15736940458 / 1000000000000)))) (orderedInterval (12166490259 / 1000000000000) (12166490475 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate550_chunkChecks4_2 :
    compactCertificate550.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1724505049572927 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-38363334936 / 1000000000000) (-38363334779 / 1000000000000), orderedInterval (-2168425680 / 1000000000000) (-2168425522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1461882028893447 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40333309661 / 1000000000000) (40333314425 / 1000000000000), orderedInterval (-10785552182 / 1000000000000) (-10785547418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (914777896322541 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-7522348068 / 1000000000000) (-7522348067 / 1000000000000), orderedInterval (-52205518775 / 1000000000000) (-52205518774 / 1000000000000)))) (orderedInterval (5404588530 / 1000000000000) (5404588801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (491970595056147 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68385119043 / 1000000000000) (-68385119042 / 1000000000000), orderedInterval (-22071962617 / 1000000000000) (-22071962616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1335795867489441 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43142392462 / 1000000000000) (43142393695 / 1000000000000), orderedInterval (-6778042548 / 1000000000000) (-6778041315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1823915056355457 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35253038142 / 1000000000000) (-35253038138 / 1000000000000), orderedInterval (-12346159231 / 1000000000000) (-12346159227 / 1000000000000)))) (orderedInterval (3329814130 / 1000000000000) (3329814191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (771222103677459 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53313036004 / 1000000000000) (-53313029144 / 1000000000000), orderedInterval (21576247392 / 1000000000000) (21576254253 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3134975034477939 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-21768451700 / 1000000000000) (-21768445466 / 1000000000000), orderedInterval (18409946825 / 1000000000000) (18409953059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2094018035548701 / 4000000000000) 4 (IntervalRat.scale (843 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (12163908142 / 1000000000000) (12163908200 / 1000000000000), orderedInterval (-32693614336 / 1000000000000) (-32693614278 / 1000000000000)))) (orderedInterval (15747278129 / 1000000000000) (15747284837 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate550_chunkChecks4 :
    compactCertificate550.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate550.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate550_chunkChecks4_0
    compactCertificate550_chunkChecks4_1 compactCertificate550_chunkChecks4_2

theorem compactCertificate550_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate550.chunkCheck r b = true :=
  compactCertificate550.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate550_chunkChecks0
    · exact compactCertificate550_chunkChecks1
    · exact compactCertificate550_chunkChecks2
    · exact compactCertificate550_chunkChecks3
    · exact compactCertificate550_chunkChecks4)

theorem compactCertificate550_coefficient0 :
    compactCertificate550.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate550_coefficient1 :
    compactCertificate550.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate550_coefficient2 :
    compactCertificate550.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate550_coefficient3 :
    compactCertificate550.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate550_coefficient4 :
    compactCertificate550.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate550_coefficients : ∀ r : Fin 5,
    compactCertificate550.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate550_coefficient0
  · exact compactCertificate550_coefficient1
  · exact compactCertificate550_coefficient2
  · exact compactCertificate550_coefficient3
  · exact compactCertificate550_coefficient4

theorem compactCertificate550_lower : (1 : ℚ) ≤ compactCertificate550.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate550, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate550_proves {t : ℝ} (ht : t ∈ compactCertificate550.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate550.proves compactCertificate550_states compactCertificate550_chunks
    compactCertificate550_coefficients compactCertificate550_lower ht

end Erdos232
