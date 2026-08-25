/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate601 : CompactCertificate where
  left := 472
  right := 473
  center := 945 / 2
  grid := fun i =>
    match i.val with
    | 0 => 150
    | 1 => 111
    | 2 => 179
    | 3 => 32
    | 4 => 87
    | 5 => 236
    | 6 => 174
    | 7 => 298
    | 8 => 219
    | 9 => 336
    | 10 => 194
    | 11 => 345
    | 12 => 322
    | 13 => 230
    | 14 => 261
    | 15 => 217
    | 16 => 192
    | 17 => 278
    | 18 => 154
    | 19 => 130
    | 20 => 82
    | 21 => 44
    | 22 => 119
    | 23 => 163
    | 24 => 69
    | 25 => 280
    | _ => 187
  point := fun i =>
    match i.val with
    | 0 => 945 / 2
    | 1 => 278433089153289 / 800000000000
    | 2 => 90039540263337 / 160000000000
    | 3 => 81246080992923 / 800000000000
    | 4 => 218238401753631 / 800000000000
    | 5 => 592559714176227 / 800000000000
    | 6 => 436476803507451 / 800000000000
    | 7 => 747910442318823 / 800000000000
    | 8 => 550907446731957 / 800000000000
    | 9 => 845233695494811 / 800000000000
    | 10 => 487995901622019 / 800000000000
    | 11 => 865957290938271 / 800000000000
    | 12 => 809089630219899 / 800000000000
    | 13 => 577404537564267 / 800000000000
    | 14 => 654715205260893 / 800000000000
    | 15 => 545833280655117 / 800000000000
    | 16 => 482260256921457 / 800000000000
    | 17 => 139777819452243 / 160000000000
    | 18 => 386632804708521 / 800000000000
    | 19 => 327752910392481 / 800000000000
    | 20 => 205092553268043 / 800000000000
    | 21 => 110299457254581 / 800000000000
    | 22 => 299484482746743 / 800000000000
    | 23 => 408920457474711 / 800000000000
    | 24 => 172907446731957 / 800000000000
    | 25 => 702859171430997 / 800000000000
    | _ => 469477353165723 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (32635117923 / 1000000000000) (32635180432 / 1000000000000), orderedInterval (-16836052340 / 1000000000000) (-16835989831 / 1000000000000))
    | 1 => (orderedInterval (-4678729241 / 1000000000000) (-4678729240 / 1000000000000), orderedInterval (-42505172060 / 1000000000000) (-42505172059 / 1000000000000))
    | 2 => (orderedInterval (-31190206698 / 1000000000000) (-31190206695 / 1000000000000), orderedInterval (-12559668570 / 1000000000000) (-12559668566 / 1000000000000))
    | 3 => (orderedInterval (76904329903 / 1000000000000) (76904330753 / 1000000000000), orderedInterval (-19199220510 / 1000000000000) (-19199219660 / 1000000000000))
    | 4 => (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000))
    | 5 => (orderedInterval (2021437415 / 1000000000000) (2021437416 / 1000000000000), orderedInterval (29245829570 / 1000000000000) (29245829571 / 1000000000000))
    | 6 => (orderedInterval (-8647776697 / 1000000000000) (-8647776686 / 1000000000000), orderedInterval (33054105273 / 1000000000000) (33054105283 / 1000000000000))
    | 7 => (orderedInterval (-12995454172 / 1000000000000) (-12995454141 / 1000000000000), orderedInterval (22636057906 / 1000000000000) (22636057936 / 1000000000000))
    | 8 => (orderedInterval (-30016389527 / 1000000000000) (-30016389297 / 1000000000000), orderedInterval (-4824157917 / 1000000000000) (-4824157687 / 1000000000000))
    | 9 => (orderedInterval (24143786972 / 1000000000000) (24143850639 / 1000000000000), orderedInterval (-4441606020 / 1000000000000) (-4441542353 / 1000000000000))
    | 10 => (orderedInterval (31222225227 / 1000000000000) (31222225259 / 1000000000000), orderedInterval (8270194830 / 1000000000000) (8270194861 / 1000000000000))
    | 11 => (orderedInterval (14042894114 / 1000000000000) (14042894156 / 1000000000000), orderedInterval (-19778374701 / 1000000000000) (-19778374659 / 1000000000000))
    | 12 => (orderedInterval (13209447735 / 1000000000000) (13209447736 / 1000000000000), orderedInterval (21323688908 / 1000000000000) (21323688909 / 1000000000000))
    | 13 => (orderedInterval (-754676549 / 1000000000000) (-754676548 / 1000000000000), orderedInterval (29690150610 / 1000000000000) (29690150611 / 1000000000000))
    | 14 => (orderedInterval (19544028007 / 1000000000000) (19544029897 / 1000000000000), orderedInterval (-19909680678 / 1000000000000) (-19909678789 / 1000000000000))
    | 15 => (orderedInterval (-29812562353 / 1000000000000) (-29812562255 / 1000000000000), orderedInterval (-6631875891 / 1000000000000) (-6631875794 / 1000000000000))
    | 16 => (orderedInterval (13391001359 / 1000000000000) (13391001360 / 1000000000000), orderedInterval (29598712933 / 1000000000000) (29598712934 / 1000000000000))
    | 17 => (orderedInterval (23196251245 / 1000000000000) (23196251248 / 1000000000000), orderedInterval (13794540919 / 1000000000000) (13794540922 / 1000000000000))
    | 18 => (orderedInterval (9711431944 / 1000000000000) (9711431945 / 1000000000000), orderedInterval (34960632082 / 1000000000000) (34960632083 / 1000000000000))
    | 19 => (orderedInterval (34624262859 / 1000000000000) (34624320733 / 1000000000000), orderedInterval (-18885306492 / 1000000000000) (-18885248618 / 1000000000000))
    | 20 => (orderedInterval (-22122688698 / 1000000000000) (-22122687386 / 1000000000000), orderedInterval (44695561757 / 1000000000000) (44695563069 / 1000000000000))
    | 21 => (orderedInterval (28248788091 / 1000000000000) (28248788092 / 1000000000000), orderedInterval (61698995166 / 1000000000000) (61698995167 / 1000000000000))
    | 22 => (orderedInterval (-39635949764 / 1000000000000) (-39635949760 / 1000000000000), orderedInterval (-11329731335 / 1000000000000) (-11329731331 / 1000000000000))
    | 23 => (orderedInterval (5060084090 / 1000000000000) (5060084092 / 1000000000000), orderedInterval (-34931449486 / 1000000000000) (-34931449483 / 1000000000000))
    | 24 => (orderedInterval (-8069293178 / 1000000000000) (-8069293177 / 1000000000000), orderedInterval (-53650470157 / 1000000000000) (-53650470156 / 1000000000000))
    | 25 => (orderedInterval (-7612830945 / 1000000000000) (-7612830943 / 1000000000000), orderedInterval (25823911946 / 1000000000000) (25823911947 / 1000000000000))
    | _ => (orderedInterval (-5053838596 / 1000000000000) (-5053838595 / 1000000000000), orderedInterval (-32542176886 / 1000000000000) (-32542176885 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11061544705 / 1000000000000) (11061569515 / 1000000000000)
      | 1 => orderedInterval (-1438965543 / 1000000000000) (-1438965476 / 1000000000000)
      | 2 => orderedInterval (-324605126 / 1000000000000) (-324605092 / 1000000000000)
      | 3 => orderedInterval (19519261 / 1000000000000) (19530770 / 1000000000000)
      | 4 => orderedInterval (-408739750 / 1000000000000) (-408739684 / 1000000000000)
      | 5 => orderedInterval (-516672507 / 1000000000000) (-516672460 / 1000000000000)
      | 6 => orderedInterval (-4232729784 / 1000000000000) (-4232726347 / 1000000000000)
      | 7 => orderedInterval (-10201010 / 1000000000000) (-10200953 / 1000000000000)
      | _ => orderedInterval (1519287739 / 1000000000000) (1519287870 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-7842747101 / 1000000000000) (-7842722287 / 1000000000000)
      | 1 => orderedInterval (-4196893130 / 1000000000000) (-4196893063 / 1000000000000)
      | 2 => orderedInterval (-1551353335 / 1000000000000) (-1551353279 / 1000000000000)
      | 3 => orderedInterval (-3885316673 / 1000000000000) (-3885290972 / 1000000000000)
      | 4 => orderedInterval (3639186109 / 1000000000000) (3639186218 / 1000000000000)
      | 5 => orderedInterval (-1618590565 / 1000000000000) (-1618590497 / 1000000000000)
      | 6 => orderedInterval (-4001303628 / 1000000000000) (-4001300654 / 1000000000000)
      | 7 => orderedInterval (2767302036 / 1000000000000) (2767302087 / 1000000000000)
      | _ => orderedInterval (3526751960 / 1000000000000) (3526752145 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-10298980812 / 1000000000000) (-10298955940 / 1000000000000)
      | 1 => orderedInterval (554202960 / 1000000000000) (554203050 / 1000000000000)
      | 2 => orderedInterval (-25018804 / 1000000000000) (-25018706 / 1000000000000)
      | 3 => orderedInterval (7126150379 / 1000000000000) (7126207864 / 1000000000000)
      | 4 => orderedInterval (1548088163 / 1000000000000) (1548088343 / 1000000000000)
      | 5 => orderedInterval (-61661242 / 1000000000000) (-61661142 / 1000000000000)
      | 6 => orderedInterval (3318358127 / 1000000000000) (3318360713 / 1000000000000)
      | 7 => orderedInterval (-72059449 / 1000000000000) (-72059398 / 1000000000000)
      | _ => orderedInterval (-3602566737 / 1000000000000) (-3602566464 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (8098368719 / 1000000000000) (8098393597 / 1000000000000)
      | 1 => orderedInterval (8333467572 / 1000000000000) (8333467706 / 1000000000000)
      | 2 => orderedInterval (5769078398 / 1000000000000) (5769078572 / 1000000000000)
      | 3 => orderedInterval (23646827494 / 1000000000000) (23646955994 / 1000000000000)
      | 4 => orderedInterval (-6758565916 / 1000000000000) (-6758565609 / 1000000000000)
      | 5 => orderedInterval (1515904400 / 1000000000000) (1515904554 / 1000000000000)
      | 6 => orderedInterval (5045497489 / 1000000000000) (5045499739 / 1000000000000)
      | 7 => orderedInterval (-3488637006 / 1000000000000) (-3488636953 / 1000000000000)
      | _ => orderedInterval (1854703898 / 1000000000000) (1854704317 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9205590042 / 1000000000000) (9205614982 / 1000000000000)
      | 1 => orderedInterval (-956080392 / 1000000000000) (-956080185 / 1000000000000)
      | 2 => orderedInterval (2845754377 / 1000000000000) (2845754693 / 1000000000000)
      | 3 => orderedInterval (-45941483429 / 1000000000000) (-45941195854 / 1000000000000)
      | 4 => orderedInterval (-6255653518 / 1000000000000) (-6255652986 / 1000000000000)
      | 5 => orderedInterval (3406924661 / 1000000000000) (3406924905 / 1000000000000)
      | 6 => orderedInterval (-2891011438 / 1000000000000) (-2891009474 / 1000000000000)
      | 7 => orderedInterval (-165819647 / 1000000000000) (-165819592 / 1000000000000)
      | _ => orderedInterval (9654102865 / 1000000000000) (9654103540 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (5668437985 / 1000000000000) (5668478143 / 1000000000000)
    | 1 => orderedInterval (-13162964327 / 1000000000000) (-13162910302 / 1000000000000)
    | 2 => orderedInterval (-1513487415 / 1000000000000) (-1513401680 / 1000000000000)
    | 3 => orderedInterval (44016645048 / 1000000000000) (44016801917 / 1000000000000)
    | _ => orderedInterval (-31097676479 / 1000000000000) (-31097359971 / 1000000000000)

theorem compactCertificate601_stateChecks0 :
    compactCertificate601.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (945 / 2)) (orderedInterval (32635117923 / 1000000000000) (32635180432 / 1000000000000), orderedInterval (-16836052340 / 1000000000000) (-16835989831 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (278433089153289 / 800000000000)) (orderedInterval (-4678729241 / 1000000000000) (-4678729240 / 1000000000000), orderedInterval (-42505172060 / 1000000000000) (-42505172059 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (90039540263337 / 160000000000)) (orderedInterval (-31190206698 / 1000000000000) (-31190206695 / 1000000000000), orderedInterval (-12559668570 / 1000000000000) (-12559668566 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_stateChecks1 :
    compactCertificate601.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (81246080992923 / 800000000000)) (orderedInterval (76904329903 / 1000000000000) (76904330753 / 1000000000000), orderedInterval (-19199220510 / 1000000000000) (-19199219660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (218238401753631 / 800000000000)) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (592559714176227 / 800000000000)) (orderedInterval (2021437415 / 1000000000000) (2021437416 / 1000000000000), orderedInterval (29245829570 / 1000000000000) (29245829571 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_stateChecks2 :
    compactCertificate601.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (436476803507451 / 800000000000)) (orderedInterval (-8647776697 / 1000000000000) (-8647776686 / 1000000000000), orderedInterval (33054105273 / 1000000000000) (33054105283 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 298 12 (747910442318823 / 800000000000)) (orderedInterval (-12995454172 / 1000000000000) (-12995454141 / 1000000000000), orderedInterval (22636057906 / 1000000000000) (22636057936 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (550907446731957 / 800000000000)) (orderedInterval (-30016389527 / 1000000000000) (-30016389297 / 1000000000000), orderedInterval (-4824157917 / 1000000000000) (-4824157687 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_stateChecks3 :
    compactCertificate601.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 336 12 (845233695494811 / 800000000000)) (orderedInterval (24143786972 / 1000000000000) (24143850639 / 1000000000000), orderedInterval (-4441606020 / 1000000000000) (-4441542353 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (487995901622019 / 800000000000)) (orderedInterval (31222225227 / 1000000000000) (31222225259 / 1000000000000), orderedInterval (8270194830 / 1000000000000) (8270194861 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 345 12 (865957290938271 / 800000000000)) (orderedInterval (14042894114 / 1000000000000) (14042894156 / 1000000000000), orderedInterval (-19778374701 / 1000000000000) (-19778374659 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_stateChecks4 :
    compactCertificate601.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 322 12 (809089630219899 / 800000000000)) (orderedInterval (13209447735 / 1000000000000) (13209447736 / 1000000000000), orderedInterval (21323688908 / 1000000000000) (21323688909 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (577404537564267 / 800000000000)) (orderedInterval (-754676549 / 1000000000000) (-754676548 / 1000000000000), orderedInterval (29690150610 / 1000000000000) (29690150611 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (654715205260893 / 800000000000)) (orderedInterval (19544028007 / 1000000000000) (19544029897 / 1000000000000), orderedInterval (-19909680678 / 1000000000000) (-19909678789 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_stateChecks5 :
    compactCertificate601.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (545833280655117 / 800000000000)) (orderedInterval (-29812562353 / 1000000000000) (-29812562255 / 1000000000000), orderedInterval (-6631875891 / 1000000000000) (-6631875794 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (482260256921457 / 800000000000)) (orderedInterval (13391001359 / 1000000000000) (13391001360 / 1000000000000), orderedInterval (29598712933 / 1000000000000) (29598712934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 278 12 (139777819452243 / 160000000000)) (orderedInterval (23196251245 / 1000000000000) (23196251248 / 1000000000000), orderedInterval (13794540919 / 1000000000000) (13794540922 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_stateChecks6 :
    compactCertificate601.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (386632804708521 / 800000000000)) (orderedInterval (9711431944 / 1000000000000) (9711431945 / 1000000000000), orderedInterval (34960632082 / 1000000000000) (34960632083 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (327752910392481 / 800000000000)) (orderedInterval (34624262859 / 1000000000000) (34624320733 / 1000000000000), orderedInterval (-18885306492 / 1000000000000) (-18885248618 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (205092553268043 / 800000000000)) (orderedInterval (-22122688698 / 1000000000000) (-22122687386 / 1000000000000), orderedInterval (44695561757 / 1000000000000) (44695563069 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_stateChecks7 :
    compactCertificate601.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (110299457254581 / 800000000000)) (orderedInterval (28248788091 / 1000000000000) (28248788092 / 1000000000000), orderedInterval (61698995166 / 1000000000000) (61698995167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (299484482746743 / 800000000000)) (orderedInterval (-39635949764 / 1000000000000) (-39635949760 / 1000000000000), orderedInterval (-11329731335 / 1000000000000) (-11329731331 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (408920457474711 / 800000000000)) (orderedInterval (5060084090 / 1000000000000) (5060084092 / 1000000000000), orderedInterval (-34931449486 / 1000000000000) (-34931449483 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_stateChecks8 :
    compactCertificate601.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (172907446731957 / 800000000000)) (orderedInterval (-8069293178 / 1000000000000) (-8069293177 / 1000000000000), orderedInterval (-53650470157 / 1000000000000) (-53650470156 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 280 12 (702859171430997 / 800000000000)) (orderedInterval (-7612830945 / 1000000000000) (-7612830943 / 1000000000000), orderedInterval (25823911946 / 1000000000000) (25823911947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (469477353165723 / 800000000000)) (orderedInterval (-5053838596 / 1000000000000) (-5053838595 / 1000000000000), orderedInterval (-32542176886 / 1000000000000) (-32542176885 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_states : ∀ j,
    BesselStateValid (compactCertificate601.point j) (compactCertificate601.state j) :=
  compactCertificate601.statesValid_of_checks3 compactCertificate601_stateChecks0
    compactCertificate601_stateChecks1 compactCertificate601_stateChecks2
    compactCertificate601_stateChecks3 compactCertificate601_stateChecks4
    compactCertificate601_stateChecks5 compactCertificate601_stateChecks6
    compactCertificate601_stateChecks7 compactCertificate601_stateChecks8

theorem compactCertificate601_chunkChecks0_0 :
    compactCertificate601.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (945 / 2) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (32635117923 / 1000000000000) (32635180432 / 1000000000000), orderedInterval (-16836052340 / 1000000000000) (-16835989831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (278433089153289 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-4678729241 / 1000000000000) (-4678729240 / 1000000000000), orderedInterval (-42505172060 / 1000000000000) (-42505172059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (90039540263337 / 160000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31190206698 / 1000000000000) (-31190206695 / 1000000000000), orderedInterval (-12559668570 / 1000000000000) (-12559668566 / 1000000000000)))) (orderedInterval (11061544705 / 1000000000000) (11061569515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (81246080992923 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76904329903 / 1000000000000) (76904330753 / 1000000000000), orderedInterval (-19199220510 / 1000000000000) (-19199219660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (218238401753631 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (592559714176227 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2021437415 / 1000000000000) (2021437416 / 1000000000000), orderedInterval (29245829570 / 1000000000000) (29245829571 / 1000000000000)))) (orderedInterval (-1438965543 / 1000000000000) (-1438965476 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (436476803507451 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8647776697 / 1000000000000) (-8647776686 / 1000000000000), orderedInterval (33054105273 / 1000000000000) (33054105283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (747910442318823 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12995454172 / 1000000000000) (-12995454141 / 1000000000000), orderedInterval (22636057906 / 1000000000000) (22636057936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (550907446731957 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30016389527 / 1000000000000) (-30016389297 / 1000000000000), orderedInterval (-4824157917 / 1000000000000) (-4824157687 / 1000000000000)))) (orderedInterval (-324605126 / 1000000000000) (-324605092 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_chunkChecks0_1 :
    compactCertificate601.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (845233695494811 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24143786972 / 1000000000000) (24143850639 / 1000000000000), orderedInterval (-4441606020 / 1000000000000) (-4441542353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (487995901622019 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31222225227 / 1000000000000) (31222225259 / 1000000000000), orderedInterval (8270194830 / 1000000000000) (8270194861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (865957290938271 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14042894114 / 1000000000000) (14042894156 / 1000000000000), orderedInterval (-19778374701 / 1000000000000) (-19778374659 / 1000000000000)))) (orderedInterval (19519261 / 1000000000000) (19530770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (809089630219899 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13209447735 / 1000000000000) (13209447736 / 1000000000000), orderedInterval (21323688908 / 1000000000000) (21323688909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (577404537564267 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-754676549 / 1000000000000) (-754676548 / 1000000000000), orderedInterval (29690150610 / 1000000000000) (29690150611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (654715205260893 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19544028007 / 1000000000000) (19544029897 / 1000000000000), orderedInterval (-19909680678 / 1000000000000) (-19909678789 / 1000000000000)))) (orderedInterval (-408739750 / 1000000000000) (-408739684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (545833280655117 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29812562353 / 1000000000000) (-29812562255 / 1000000000000), orderedInterval (-6631875891 / 1000000000000) (-6631875794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (482260256921457 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13391001359 / 1000000000000) (13391001360 / 1000000000000), orderedInterval (29598712933 / 1000000000000) (29598712934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (139777819452243 / 160000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23196251245 / 1000000000000) (23196251248 / 1000000000000), orderedInterval (13794540919 / 1000000000000) (13794540922 / 1000000000000)))) (orderedInterval (-516672507 / 1000000000000) (-516672460 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_chunkChecks0_2 :
    compactCertificate601.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (386632804708521 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9711431944 / 1000000000000) (9711431945 / 1000000000000), orderedInterval (34960632082 / 1000000000000) (34960632083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (327752910392481 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34624262859 / 1000000000000) (34624320733 / 1000000000000), orderedInterval (-18885306492 / 1000000000000) (-18885248618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (205092553268043 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22122688698 / 1000000000000) (-22122687386 / 1000000000000), orderedInterval (44695561757 / 1000000000000) (44695563069 / 1000000000000)))) (orderedInterval (-4232729784 / 1000000000000) (-4232726347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (110299457254581 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28248788091 / 1000000000000) (28248788092 / 1000000000000), orderedInterval (61698995166 / 1000000000000) (61698995167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (299484482746743 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39635949764 / 1000000000000) (-39635949760 / 1000000000000), orderedInterval (-11329731335 / 1000000000000) (-11329731331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (408920457474711 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5060084090 / 1000000000000) (5060084092 / 1000000000000), orderedInterval (-34931449486 / 1000000000000) (-34931449483 / 1000000000000)))) (orderedInterval (-10201010 / 1000000000000) (-10200953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (172907446731957 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-8069293178 / 1000000000000) (-8069293177 / 1000000000000), orderedInterval (-53650470157 / 1000000000000) (-53650470156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (702859171430997 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7612830945 / 1000000000000) (-7612830943 / 1000000000000), orderedInterval (25823911946 / 1000000000000) (25823911947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (469477353165723 / 800000000000) 0 (IntervalRat.scale (945 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5053838596 / 1000000000000) (-5053838595 / 1000000000000), orderedInterval (-32542176886 / 1000000000000) (-32542176885 / 1000000000000)))) (orderedInterval (1519287739 / 1000000000000) (1519287870 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_chunkChecks0 :
    compactCertificate601.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate601.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate601_chunkChecks0_0
    compactCertificate601_chunkChecks0_1 compactCertificate601_chunkChecks0_2

theorem compactCertificate601_chunkChecks1_0 :
    compactCertificate601.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (945 / 2) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (32635117923 / 1000000000000) (32635180432 / 1000000000000), orderedInterval (-16836052340 / 1000000000000) (-16835989831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (278433089153289 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-4678729241 / 1000000000000) (-4678729240 / 1000000000000), orderedInterval (-42505172060 / 1000000000000) (-42505172059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (90039540263337 / 160000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31190206698 / 1000000000000) (-31190206695 / 1000000000000), orderedInterval (-12559668570 / 1000000000000) (-12559668566 / 1000000000000)))) (orderedInterval (-7842747101 / 1000000000000) (-7842722287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (81246080992923 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76904329903 / 1000000000000) (76904330753 / 1000000000000), orderedInterval (-19199220510 / 1000000000000) (-19199219660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (218238401753631 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (592559714176227 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2021437415 / 1000000000000) (2021437416 / 1000000000000), orderedInterval (29245829570 / 1000000000000) (29245829571 / 1000000000000)))) (orderedInterval (-4196893130 / 1000000000000) (-4196893063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (436476803507451 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8647776697 / 1000000000000) (-8647776686 / 1000000000000), orderedInterval (33054105273 / 1000000000000) (33054105283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (747910442318823 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12995454172 / 1000000000000) (-12995454141 / 1000000000000), orderedInterval (22636057906 / 1000000000000) (22636057936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (550907446731957 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30016389527 / 1000000000000) (-30016389297 / 1000000000000), orderedInterval (-4824157917 / 1000000000000) (-4824157687 / 1000000000000)))) (orderedInterval (-1551353335 / 1000000000000) (-1551353279 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_chunkChecks1_1 :
    compactCertificate601.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (845233695494811 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24143786972 / 1000000000000) (24143850639 / 1000000000000), orderedInterval (-4441606020 / 1000000000000) (-4441542353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (487995901622019 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31222225227 / 1000000000000) (31222225259 / 1000000000000), orderedInterval (8270194830 / 1000000000000) (8270194861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (865957290938271 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14042894114 / 1000000000000) (14042894156 / 1000000000000), orderedInterval (-19778374701 / 1000000000000) (-19778374659 / 1000000000000)))) (orderedInterval (-3885316673 / 1000000000000) (-3885290972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (809089630219899 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13209447735 / 1000000000000) (13209447736 / 1000000000000), orderedInterval (21323688908 / 1000000000000) (21323688909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (577404537564267 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-754676549 / 1000000000000) (-754676548 / 1000000000000), orderedInterval (29690150610 / 1000000000000) (29690150611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (654715205260893 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19544028007 / 1000000000000) (19544029897 / 1000000000000), orderedInterval (-19909680678 / 1000000000000) (-19909678789 / 1000000000000)))) (orderedInterval (3639186109 / 1000000000000) (3639186218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (545833280655117 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29812562353 / 1000000000000) (-29812562255 / 1000000000000), orderedInterval (-6631875891 / 1000000000000) (-6631875794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (482260256921457 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13391001359 / 1000000000000) (13391001360 / 1000000000000), orderedInterval (29598712933 / 1000000000000) (29598712934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (139777819452243 / 160000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23196251245 / 1000000000000) (23196251248 / 1000000000000), orderedInterval (13794540919 / 1000000000000) (13794540922 / 1000000000000)))) (orderedInterval (-1618590565 / 1000000000000) (-1618590497 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_chunkChecks1_2 :
    compactCertificate601.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (386632804708521 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9711431944 / 1000000000000) (9711431945 / 1000000000000), orderedInterval (34960632082 / 1000000000000) (34960632083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (327752910392481 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34624262859 / 1000000000000) (34624320733 / 1000000000000), orderedInterval (-18885306492 / 1000000000000) (-18885248618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (205092553268043 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22122688698 / 1000000000000) (-22122687386 / 1000000000000), orderedInterval (44695561757 / 1000000000000) (44695563069 / 1000000000000)))) (orderedInterval (-4001303628 / 1000000000000) (-4001300654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (110299457254581 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28248788091 / 1000000000000) (28248788092 / 1000000000000), orderedInterval (61698995166 / 1000000000000) (61698995167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (299484482746743 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39635949764 / 1000000000000) (-39635949760 / 1000000000000), orderedInterval (-11329731335 / 1000000000000) (-11329731331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (408920457474711 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5060084090 / 1000000000000) (5060084092 / 1000000000000), orderedInterval (-34931449486 / 1000000000000) (-34931449483 / 1000000000000)))) (orderedInterval (2767302036 / 1000000000000) (2767302087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (172907446731957 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-8069293178 / 1000000000000) (-8069293177 / 1000000000000), orderedInterval (-53650470157 / 1000000000000) (-53650470156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (702859171430997 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7612830945 / 1000000000000) (-7612830943 / 1000000000000), orderedInterval (25823911946 / 1000000000000) (25823911947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (469477353165723 / 800000000000) 1 (IntervalRat.scale (945 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5053838596 / 1000000000000) (-5053838595 / 1000000000000), orderedInterval (-32542176886 / 1000000000000) (-32542176885 / 1000000000000)))) (orderedInterval (3526751960 / 1000000000000) (3526752145 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_chunkChecks1 :
    compactCertificate601.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate601.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate601_chunkChecks1_0
    compactCertificate601_chunkChecks1_1 compactCertificate601_chunkChecks1_2

theorem compactCertificate601_chunkChecks2_0 :
    compactCertificate601.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (945 / 2) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (32635117923 / 1000000000000) (32635180432 / 1000000000000), orderedInterval (-16836052340 / 1000000000000) (-16835989831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (278433089153289 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-4678729241 / 1000000000000) (-4678729240 / 1000000000000), orderedInterval (-42505172060 / 1000000000000) (-42505172059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (90039540263337 / 160000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31190206698 / 1000000000000) (-31190206695 / 1000000000000), orderedInterval (-12559668570 / 1000000000000) (-12559668566 / 1000000000000)))) (orderedInterval (-10298980812 / 1000000000000) (-10298955940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (81246080992923 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76904329903 / 1000000000000) (76904330753 / 1000000000000), orderedInterval (-19199220510 / 1000000000000) (-19199219660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (218238401753631 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (592559714176227 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2021437415 / 1000000000000) (2021437416 / 1000000000000), orderedInterval (29245829570 / 1000000000000) (29245829571 / 1000000000000)))) (orderedInterval (554202960 / 1000000000000) (554203050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (436476803507451 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8647776697 / 1000000000000) (-8647776686 / 1000000000000), orderedInterval (33054105273 / 1000000000000) (33054105283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (747910442318823 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12995454172 / 1000000000000) (-12995454141 / 1000000000000), orderedInterval (22636057906 / 1000000000000) (22636057936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (550907446731957 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30016389527 / 1000000000000) (-30016389297 / 1000000000000), orderedInterval (-4824157917 / 1000000000000) (-4824157687 / 1000000000000)))) (orderedInterval (-25018804 / 1000000000000) (-25018706 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_chunkChecks2_1 :
    compactCertificate601.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (845233695494811 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24143786972 / 1000000000000) (24143850639 / 1000000000000), orderedInterval (-4441606020 / 1000000000000) (-4441542353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (487995901622019 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31222225227 / 1000000000000) (31222225259 / 1000000000000), orderedInterval (8270194830 / 1000000000000) (8270194861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (865957290938271 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14042894114 / 1000000000000) (14042894156 / 1000000000000), orderedInterval (-19778374701 / 1000000000000) (-19778374659 / 1000000000000)))) (orderedInterval (7126150379 / 1000000000000) (7126207864 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (809089630219899 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13209447735 / 1000000000000) (13209447736 / 1000000000000), orderedInterval (21323688908 / 1000000000000) (21323688909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (577404537564267 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-754676549 / 1000000000000) (-754676548 / 1000000000000), orderedInterval (29690150610 / 1000000000000) (29690150611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (654715205260893 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19544028007 / 1000000000000) (19544029897 / 1000000000000), orderedInterval (-19909680678 / 1000000000000) (-19909678789 / 1000000000000)))) (orderedInterval (1548088163 / 1000000000000) (1548088343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (545833280655117 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29812562353 / 1000000000000) (-29812562255 / 1000000000000), orderedInterval (-6631875891 / 1000000000000) (-6631875794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (482260256921457 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13391001359 / 1000000000000) (13391001360 / 1000000000000), orderedInterval (29598712933 / 1000000000000) (29598712934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (139777819452243 / 160000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23196251245 / 1000000000000) (23196251248 / 1000000000000), orderedInterval (13794540919 / 1000000000000) (13794540922 / 1000000000000)))) (orderedInterval (-61661242 / 1000000000000) (-61661142 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_chunkChecks2_2 :
    compactCertificate601.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (386632804708521 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9711431944 / 1000000000000) (9711431945 / 1000000000000), orderedInterval (34960632082 / 1000000000000) (34960632083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (327752910392481 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34624262859 / 1000000000000) (34624320733 / 1000000000000), orderedInterval (-18885306492 / 1000000000000) (-18885248618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (205092553268043 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22122688698 / 1000000000000) (-22122687386 / 1000000000000), orderedInterval (44695561757 / 1000000000000) (44695563069 / 1000000000000)))) (orderedInterval (3318358127 / 1000000000000) (3318360713 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (110299457254581 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28248788091 / 1000000000000) (28248788092 / 1000000000000), orderedInterval (61698995166 / 1000000000000) (61698995167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (299484482746743 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39635949764 / 1000000000000) (-39635949760 / 1000000000000), orderedInterval (-11329731335 / 1000000000000) (-11329731331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (408920457474711 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5060084090 / 1000000000000) (5060084092 / 1000000000000), orderedInterval (-34931449486 / 1000000000000) (-34931449483 / 1000000000000)))) (orderedInterval (-72059449 / 1000000000000) (-72059398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (172907446731957 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-8069293178 / 1000000000000) (-8069293177 / 1000000000000), orderedInterval (-53650470157 / 1000000000000) (-53650470156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (702859171430997 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7612830945 / 1000000000000) (-7612830943 / 1000000000000), orderedInterval (25823911946 / 1000000000000) (25823911947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (469477353165723 / 800000000000) 2 (IntervalRat.scale (945 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5053838596 / 1000000000000) (-5053838595 / 1000000000000), orderedInterval (-32542176886 / 1000000000000) (-32542176885 / 1000000000000)))) (orderedInterval (-3602566737 / 1000000000000) (-3602566464 / 1000000000000))) = true
  rfl'

theorem compactCertificate601_chunkChecks2 :
    compactCertificate601.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate601.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate601_chunkChecks2_0
    compactCertificate601_chunkChecks2_1 compactCertificate601_chunkChecks2_2

theorem compactCertificate601_chunkChecks3_0 :
    compactCertificate601.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (945 / 2) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (32635117923 / 1000000000000) (32635180432 / 1000000000000), orderedInterval (-16836052340 / 1000000000000) (-16835989831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (278433089153289 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-4678729241 / 1000000000000) (-4678729240 / 1000000000000), orderedInterval (-42505172060 / 1000000000000) (-42505172059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (90039540263337 / 160000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31190206698 / 1000000000000) (-31190206695 / 1000000000000), orderedInterval (-12559668570 / 1000000000000) (-12559668566 / 1000000000000)))) (orderedInterval (8098368719 / 1000000000000) (8098393597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (81246080992923 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76904329903 / 1000000000000) (76904330753 / 1000000000000), orderedInterval (-19199220510 / 1000000000000) (-19199219660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (218238401753631 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (592559714176227 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2021437415 / 1000000000000) (2021437416 / 1000000000000), orderedInterval (29245829570 / 1000000000000) (29245829571 / 1000000000000)))) (orderedInterval (8333467572 / 1000000000000) (8333467706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (436476803507451 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8647776697 / 1000000000000) (-8647776686 / 1000000000000), orderedInterval (33054105273 / 1000000000000) (33054105283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (747910442318823 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12995454172 / 1000000000000) (-12995454141 / 1000000000000), orderedInterval (22636057906 / 1000000000000) (22636057936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (550907446731957 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30016389527 / 1000000000000) (-30016389297 / 1000000000000), orderedInterval (-4824157917 / 1000000000000) (-4824157687 / 1000000000000)))) (orderedInterval (5769078398 / 1000000000000) (5769078572 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate601_chunkChecks3_1 :
    compactCertificate601.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (845233695494811 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24143786972 / 1000000000000) (24143850639 / 1000000000000), orderedInterval (-4441606020 / 1000000000000) (-4441542353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (487995901622019 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31222225227 / 1000000000000) (31222225259 / 1000000000000), orderedInterval (8270194830 / 1000000000000) (8270194861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (865957290938271 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14042894114 / 1000000000000) (14042894156 / 1000000000000), orderedInterval (-19778374701 / 1000000000000) (-19778374659 / 1000000000000)))) (orderedInterval (23646827494 / 1000000000000) (23646955994 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (809089630219899 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13209447735 / 1000000000000) (13209447736 / 1000000000000), orderedInterval (21323688908 / 1000000000000) (21323688909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (577404537564267 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-754676549 / 1000000000000) (-754676548 / 1000000000000), orderedInterval (29690150610 / 1000000000000) (29690150611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (654715205260893 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19544028007 / 1000000000000) (19544029897 / 1000000000000), orderedInterval (-19909680678 / 1000000000000) (-19909678789 / 1000000000000)))) (orderedInterval (-6758565916 / 1000000000000) (-6758565609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (545833280655117 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29812562353 / 1000000000000) (-29812562255 / 1000000000000), orderedInterval (-6631875891 / 1000000000000) (-6631875794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (482260256921457 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13391001359 / 1000000000000) (13391001360 / 1000000000000), orderedInterval (29598712933 / 1000000000000) (29598712934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (139777819452243 / 160000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23196251245 / 1000000000000) (23196251248 / 1000000000000), orderedInterval (13794540919 / 1000000000000) (13794540922 / 1000000000000)))) (orderedInterval (1515904400 / 1000000000000) (1515904554 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate601_chunkChecks3_2 :
    compactCertificate601.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (386632804708521 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9711431944 / 1000000000000) (9711431945 / 1000000000000), orderedInterval (34960632082 / 1000000000000) (34960632083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (327752910392481 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34624262859 / 1000000000000) (34624320733 / 1000000000000), orderedInterval (-18885306492 / 1000000000000) (-18885248618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (205092553268043 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22122688698 / 1000000000000) (-22122687386 / 1000000000000), orderedInterval (44695561757 / 1000000000000) (44695563069 / 1000000000000)))) (orderedInterval (5045497489 / 1000000000000) (5045499739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (110299457254581 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28248788091 / 1000000000000) (28248788092 / 1000000000000), orderedInterval (61698995166 / 1000000000000) (61698995167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (299484482746743 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39635949764 / 1000000000000) (-39635949760 / 1000000000000), orderedInterval (-11329731335 / 1000000000000) (-11329731331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (408920457474711 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5060084090 / 1000000000000) (5060084092 / 1000000000000), orderedInterval (-34931449486 / 1000000000000) (-34931449483 / 1000000000000)))) (orderedInterval (-3488637006 / 1000000000000) (-3488636953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (172907446731957 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-8069293178 / 1000000000000) (-8069293177 / 1000000000000), orderedInterval (-53650470157 / 1000000000000) (-53650470156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (702859171430997 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7612830945 / 1000000000000) (-7612830943 / 1000000000000), orderedInterval (25823911946 / 1000000000000) (25823911947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (469477353165723 / 800000000000) 3 (IntervalRat.scale (945 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5053838596 / 1000000000000) (-5053838595 / 1000000000000), orderedInterval (-32542176886 / 1000000000000) (-32542176885 / 1000000000000)))) (orderedInterval (1854703898 / 1000000000000) (1854704317 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate601_chunkChecks3 :
    compactCertificate601.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate601.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate601_chunkChecks3_0
    compactCertificate601_chunkChecks3_1 compactCertificate601_chunkChecks3_2

theorem compactCertificate601_chunkChecks4_0 :
    compactCertificate601.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (945 / 2) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (32635117923 / 1000000000000) (32635180432 / 1000000000000), orderedInterval (-16836052340 / 1000000000000) (-16835989831 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (278433089153289 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-4678729241 / 1000000000000) (-4678729240 / 1000000000000), orderedInterval (-42505172060 / 1000000000000) (-42505172059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (90039540263337 / 160000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31190206698 / 1000000000000) (-31190206695 / 1000000000000), orderedInterval (-12559668570 / 1000000000000) (-12559668566 / 1000000000000)))) (orderedInterval (9205590042 / 1000000000000) (9205614982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (81246080992923 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (76904329903 / 1000000000000) (76904330753 / 1000000000000), orderedInterval (-19199220510 / 1000000000000) (-19199219660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (218238401753631 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (592559714176227 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (2021437415 / 1000000000000) (2021437416 / 1000000000000), orderedInterval (29245829570 / 1000000000000) (29245829571 / 1000000000000)))) (orderedInterval (-956080392 / 1000000000000) (-956080185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (436476803507451 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-8647776697 / 1000000000000) (-8647776686 / 1000000000000), orderedInterval (33054105273 / 1000000000000) (33054105283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (747910442318823 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12995454172 / 1000000000000) (-12995454141 / 1000000000000), orderedInterval (22636057906 / 1000000000000) (22636057936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (550907446731957 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30016389527 / 1000000000000) (-30016389297 / 1000000000000), orderedInterval (-4824157917 / 1000000000000) (-4824157687 / 1000000000000)))) (orderedInterval (2845754377 / 1000000000000) (2845754693 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate601_chunkChecks4_1 :
    compactCertificate601.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (845233695494811 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24143786972 / 1000000000000) (24143850639 / 1000000000000), orderedInterval (-4441606020 / 1000000000000) (-4441542353 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (487995901622019 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31222225227 / 1000000000000) (31222225259 / 1000000000000), orderedInterval (8270194830 / 1000000000000) (8270194861 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (865957290938271 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14042894114 / 1000000000000) (14042894156 / 1000000000000), orderedInterval (-19778374701 / 1000000000000) (-19778374659 / 1000000000000)))) (orderedInterval (-45941483429 / 1000000000000) (-45941195854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (809089630219899 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13209447735 / 1000000000000) (13209447736 / 1000000000000), orderedInterval (21323688908 / 1000000000000) (21323688909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (577404537564267 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-754676549 / 1000000000000) (-754676548 / 1000000000000), orderedInterval (29690150610 / 1000000000000) (29690150611 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (654715205260893 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19544028007 / 1000000000000) (19544029897 / 1000000000000), orderedInterval (-19909680678 / 1000000000000) (-19909678789 / 1000000000000)))) (orderedInterval (-6255653518 / 1000000000000) (-6255652986 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (545833280655117 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29812562353 / 1000000000000) (-29812562255 / 1000000000000), orderedInterval (-6631875891 / 1000000000000) (-6631875794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (482260256921457 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13391001359 / 1000000000000) (13391001360 / 1000000000000), orderedInterval (29598712933 / 1000000000000) (29598712934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (139777819452243 / 160000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23196251245 / 1000000000000) (23196251248 / 1000000000000), orderedInterval (13794540919 / 1000000000000) (13794540922 / 1000000000000)))) (orderedInterval (3406924661 / 1000000000000) (3406924905 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate601_chunkChecks4_2 :
    compactCertificate601.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (386632804708521 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (9711431944 / 1000000000000) (9711431945 / 1000000000000), orderedInterval (34960632082 / 1000000000000) (34960632083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (327752910392481 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (34624262859 / 1000000000000) (34624320733 / 1000000000000), orderedInterval (-18885306492 / 1000000000000) (-18885248618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (205092553268043 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22122688698 / 1000000000000) (-22122687386 / 1000000000000), orderedInterval (44695561757 / 1000000000000) (44695563069 / 1000000000000)))) (orderedInterval (-2891011438 / 1000000000000) (-2891009474 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (110299457254581 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (28248788091 / 1000000000000) (28248788092 / 1000000000000), orderedInterval (61698995166 / 1000000000000) (61698995167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (299484482746743 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39635949764 / 1000000000000) (-39635949760 / 1000000000000), orderedInterval (-11329731335 / 1000000000000) (-11329731331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (408920457474711 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5060084090 / 1000000000000) (5060084092 / 1000000000000), orderedInterval (-34931449486 / 1000000000000) (-34931449483 / 1000000000000)))) (orderedInterval (-165819647 / 1000000000000) (-165819592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (172907446731957 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-8069293178 / 1000000000000) (-8069293177 / 1000000000000), orderedInterval (-53650470157 / 1000000000000) (-53650470156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (702859171430997 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7612830945 / 1000000000000) (-7612830943 / 1000000000000), orderedInterval (25823911946 / 1000000000000) (25823911947 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (469477353165723 / 800000000000) 4 (IntervalRat.scale (945 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5053838596 / 1000000000000) (-5053838595 / 1000000000000), orderedInterval (-32542176886 / 1000000000000) (-32542176885 / 1000000000000)))) (orderedInterval (9654102865 / 1000000000000) (9654103540 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate601_chunkChecks4 :
    compactCertificate601.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate601.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate601_chunkChecks4_0
    compactCertificate601_chunkChecks4_1 compactCertificate601_chunkChecks4_2

theorem compactCertificate601_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate601.chunkCheck r b = true :=
  compactCertificate601.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate601_chunkChecks0
    · exact compactCertificate601_chunkChecks1
    · exact compactCertificate601_chunkChecks2
    · exact compactCertificate601_chunkChecks3
    · exact compactCertificate601_chunkChecks4)

theorem compactCertificate601_coefficient0 :
    compactCertificate601.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate601_coefficient1 :
    compactCertificate601.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate601_coefficient2 :
    compactCertificate601.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate601_coefficient3 :
    compactCertificate601.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate601_coefficient4 :
    compactCertificate601.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate601_coefficients : ∀ r : Fin 5,
    compactCertificate601.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate601_coefficient0
  · exact compactCertificate601_coefficient1
  · exact compactCertificate601_coefficient2
  · exact compactCertificate601_coefficient3
  · exact compactCertificate601_coefficient4

theorem compactCertificate601_lower : (1 : ℚ) ≤ compactCertificate601.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate601, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate601_proves {t : ℝ} (ht : t ∈ compactCertificate601.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate601.proves compactCertificate601_states compactCertificate601_chunks
    compactCertificate601_coefficients compactCertificate601_lower ht

end Erdos232
