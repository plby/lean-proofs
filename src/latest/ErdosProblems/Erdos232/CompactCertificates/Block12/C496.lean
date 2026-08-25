/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate496 : CompactCertificate where
  left := 367
  right := 368
  center := 735 / 2
  grid := fun i =>
    match i.val with
    | 0 => 117
    | 1 => 86
    | 2 => 139
    | 3 => 25
    | 4 => 68
    | 5 => 183
    | 6 => 135
    | 7 => 232
    | 8 => 171
    | 9 => 262
    | 10 => 151
    | 11 => 268
    | 12 => 251
    | 13 => 179
    | 14 => 203
    | 15 => 169
    | 16 => 149
    | 17 => 216
    | 18 => 120
    | 19 => 101
    | 20 => 64
    | 21 => 34
    | 22 => 93
    | 23 => 127
    | 24 => 54
    | 25 => 218
    | _ => 145
  point := fun i =>
    match i.val with
    | 0 => 735 / 2
    | 1 => 216559069341447 / 800000000000
    | 2 => 70030753538151 / 160000000000
    | 3 => 63191396327829 / 800000000000
    | 4 => 169740979141713 / 800000000000
    | 5 => 460879777692621 / 800000000000
    | 6 => 339481958283573 / 800000000000
    | 7 => 581708121803529 / 800000000000
    | 8 => 428483569680411 / 800000000000
    | 9 => 657403985384853 / 800000000000
    | 10 => 379552367928237 / 800000000000
    | 11 => 673522337396433 / 800000000000
    | 12 => 629291934615477 / 800000000000
    | 13 => 449092418105541 / 800000000000
    | 14 => 509222937425139 / 800000000000
    | 15 => 424536996065091 / 800000000000
    | 16 => 375091310938911 / 800000000000
    | 17 => 108716081796189 / 160000000000
    | 18 => 300714403662183 / 800000000000
    | 19 => 254918930305263 / 800000000000
    | 20 => 159516430319589 / 800000000000
    | 21 => 85788466753563 / 800000000000
    | 22 => 232932375469689 / 800000000000
    | 23 => 318049244702553 / 800000000000
    | 24 => 134483569680411 / 800000000000
    | 25 => 546668244446331 / 800000000000
    | _ => 365149052462229 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-27404014723 / 1000000000000) (-27404014722 / 1000000000000), orderedInterval (-31288725505 / 1000000000000) (-31288725504 / 1000000000000))
    | 1 => (orderedInterval (46814896414 / 1000000000000) (46814896416 / 1000000000000), orderedInterval (12567619468 / 1000000000000) (12567619470 / 1000000000000))
    | 2 => (orderedInterval (-37175243002 / 1000000000000) (-37175238152 / 1000000000000), orderedInterval (8556719045 / 1000000000000) (8556723895 / 1000000000000))
    | 3 => (orderedInterval (-84708134242 / 1000000000000) (-84708134241 / 1000000000000), orderedInterval (-29195643946 / 1000000000000) (-29195643945 / 1000000000000))
    | 4 => (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000))
    | 5 => (orderedInterval (-30583787167 / 1000000000000) (-30583734795 / 1000000000000), orderedInterval (13052820367 / 1000000000000) (13052872739 / 1000000000000))
    | 6 => (orderedInterval (-33055799468 / 1000000000000) (-33055799467 / 1000000000000), orderedInterval (-20148382398 / 1000000000000) (-20148382397 / 1000000000000))
    | 7 => (orderedInterval (-23703630501 / 1000000000000) (-23703615382 / 1000000000000), orderedInterval (17726627529 / 1000000000000) (17726642648 / 1000000000000))
    | 8 => (orderedInterval (25270843410 / 1000000000000) (25270857224 / 1000000000000), orderedInterval (-23475349309 / 1000000000000) (-23475335495 / 1000000000000))
    | 9 => (orderedInterval (-14715114525 / 1000000000000) (-14715114407 / 1000000000000), orderedInterval (23634638575 / 1000000000000) (23634638692 / 1000000000000))
    | 10 => (orderedInterval (-27401475510 / 1000000000000) (-27401475509 / 1000000000000), orderedInterval (-24281446389 / 1000000000000) (-24281446388 / 1000000000000))
    | 11 => (orderedInterval (18569106564 / 1000000000000) (18569106565 / 1000000000000), orderedInterval (20270884211 / 1000000000000) (20270884212 / 1000000000000))
    | 12 => (orderedInterval (25844422206 / 1000000000000) (25844499753 / 1000000000000), orderedInterval (-11906770419 / 1000000000000) (-11906692871 / 1000000000000))
    | 13 => (orderedInterval (6504973273 / 1000000000000) (6504973277 / 1000000000000), orderedInterval (-33047304771 / 1000000000000) (-33047304767 / 1000000000000))
    | 14 => (orderedInterval (13167313071 / 1000000000000) (13167313144 / 1000000000000), orderedInterval (-28763867886 / 1000000000000) (-28763867813 / 1000000000000))
    | 15 => (orderedInterval (-17427360560 / 1000000000000) (-17427360559 / 1000000000000), orderedInterval (-29915793183 / 1000000000000) (-29915793182 / 1000000000000))
    | 16 => (orderedInterval (-36841679598 / 1000000000000) (-36841679258 / 1000000000000), orderedInterval (-654577604 / 1000000000000) (-654577264 / 1000000000000))
    | 17 => (orderedInterval (30437746503 / 1000000000000) (30437751525 / 1000000000000), orderedInterval (-3258353130 / 1000000000000) (-3258348109 / 1000000000000))
    | 18 => (orderedInterval (-12673666258 / 1000000000000) (-12673666166 / 1000000000000), orderedInterval (39170389534 / 1000000000000) (39170389625 / 1000000000000))
    | 19 => (orderedInterval (-37822357698 / 1000000000000) (-37822290330 / 1000000000000), orderedInterval (23878304036 / 1000000000000) (23878371404 / 1000000000000))
    | 20 => (orderedInterval (-43608417814 / 1000000000000) (-43608309796 / 1000000000000), orderedInterval (36040573959 / 1000000000000) (36040681978 / 1000000000000))
    | 21 => (orderedInterval (71969915366 / 1000000000000) (71969915367 / 1000000000000), orderedInterval (27176797351 / 1000000000000) (27176797352 / 1000000000000))
    | 22 => (orderedInterval (10098347743 / 1000000000000) (10098347786 / 1000000000000), orderedInterval (-45673445300 / 1000000000000) (-45673445258 / 1000000000000))
    | 23 => (orderedInterval (23757016244 / 1000000000000) (23757020435 / 1000000000000), orderedInterval (-32231055098 / 1000000000000) (-32231050907 / 1000000000000))
    | 24 => (orderedInterval (-42256383529 / 1000000000000) (-42256341256 / 1000000000000), orderedInterval (44863222453 / 1000000000000) (44863264726 / 1000000000000))
    | 25 => (orderedInterval (-20731150484 / 1000000000000) (-20731147575 / 1000000000000), orderedInterval (22417298758 / 1000000000000) (22417301667 / 1000000000000))
    | _ => (orderedInterval (-37079222832 / 1000000000000) (-37079221140 / 1000000000000), orderedInterval (4500653270 / 1000000000000) (4500654962 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12607253742 / 1000000000000) (-12607253431 / 1000000000000)
      | 1 => orderedInterval (1855543853 / 1000000000000) (1855548167 / 1000000000000)
      | 2 => orderedInterval (1341860752 / 1000000000000) (1341861573 / 1000000000000)
      | 3 => orderedInterval (3224182146 / 1000000000000) (3224182313 / 1000000000000)
      | 4 => orderedInterval (81921728 / 1000000000000) (81923173 / 1000000000000)
      | 5 => orderedInterval (2686407992 / 1000000000000) (2686408176 / 1000000000000)
      | 6 => orderedInterval (2747479495 / 1000000000000) (2747486932 / 1000000000000)
      | 7 => orderedInterval (-3378743953 / 1000000000000) (-3378743587 / 1000000000000)
      | _ => orderedInterval (8389862347 / 1000000000000) (8389863258 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-11717473680 / 1000000000000) (-11717473311 / 1000000000000)
      | 1 => orderedInterval (-477840693 / 1000000000000) (-477834491 / 1000000000000)
      | 2 => orderedInterval (-1908695453 / 1000000000000) (-1908694007 / 1000000000000)
      | 3 => orderedInterval (-5111645233 / 1000000000000) (-5111644884 / 1000000000000)
      | 4 => orderedInterval (-4061374234 / 1000000000000) (-4061371164 / 1000000000000)
      | 5 => orderedInterval (-605299522 / 1000000000000) (-605299208 / 1000000000000)
      | 6 => orderedInterval (-6941338456 / 1000000000000) (-6941333141 / 1000000000000)
      | 7 => orderedInterval (3346737029 / 1000000000000) (3346737417 / 1000000000000)
      | _ => orderedInterval (-4318166297 / 1000000000000) (-4318165203 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (13751584464 / 1000000000000) (13751584903 / 1000000000000)
      | 1 => orderedInterval (-4971516031 / 1000000000000) (-4971506613 / 1000000000000)
      | 2 => orderedInterval (-4154297565 / 1000000000000) (-4154294962 / 1000000000000)
      | 3 => orderedInterval (-23529557747 / 1000000000000) (-23529556994 / 1000000000000)
      | 4 => orderedInterval (913260474 / 1000000000000) (913267016 / 1000000000000)
      | 5 => orderedInterval (-5674601960 / 1000000000000) (-5674601412 / 1000000000000)
      | 6 => orderedInterval (-3292656545 / 1000000000000) (-3292652532 / 1000000000000)
      | 7 => orderedInterval (2378619075 / 1000000000000) (2378619493 / 1000000000000)
      | _ => orderedInterval (-16501289326 / 1000000000000) (-16501287751 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11469164825 / 1000000000000) (11469165346 / 1000000000000)
      | 1 => orderedInterval (3282110754 / 1000000000000) (3282125331 / 1000000000000)
      | 2 => orderedInterval (6002813869 / 1000000000000) (6002818638 / 1000000000000)
      | 3 => orderedInterval (16241902383 / 1000000000000) (16241904036 / 1000000000000)
      | 4 => orderedInterval (8271550924 / 1000000000000) (8271564873 / 1000000000000)
      | 5 => orderedInterval (1505099410 / 1000000000000) (1505100381 / 1000000000000)
      | 6 => orderedInterval (7404548505 / 1000000000000) (7404551658 / 1000000000000)
      | 7 => orderedInterval (-3636575469 / 1000000000000) (-3636575020 / 1000000000000)
      | _ => orderedInterval (13368149824 / 1000000000000) (13368152308 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-15185219526 / 1000000000000) (-15185218904 / 1000000000000)
      | 1 => orderedInterval (12976344740 / 1000000000000) (12976367523 / 1000000000000)
      | 2 => orderedInterval (13927970228 / 1000000000000) (13927979121 / 1000000000000)
      | 3 => orderedInterval (132346098581 / 1000000000000) (132346102259 / 1000000000000)
      | 4 => orderedInterval (-7089203565 / 1000000000000) (-7089173753 / 1000000000000)
      | 5 => orderedInterval (13809939789 / 1000000000000) (13809941533 / 1000000000000)
      | 6 => orderedInterval (3264619292 / 1000000000000) (3264621863 / 1000000000000)
      | 7 => orderedInterval (-2573712405 / 1000000000000) (-2573711919 / 1000000000000)
      | _ => orderedInterval (36643145302 / 1000000000000) (36643149434 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (4341260618 / 1000000000000) (4341276574 / 1000000000000)
    | 1 => orderedInterval (-31795096539 / 1000000000000) (-31795077992 / 1000000000000)
    | 2 => orderedInterval (-41080455161 / 1000000000000) (-41080428852 / 1000000000000)
    | 3 => orderedInterval (63908765025 / 1000000000000) (63908807551 / 1000000000000)
    | _ => orderedInterval (188119982436 / 1000000000000) (188120057157 / 1000000000000)

theorem compactCertificate496_stateChecks0 :
    compactCertificate496.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (735 / 2)) (orderedInterval (-27404014723 / 1000000000000) (-27404014722 / 1000000000000), orderedInterval (-31288725505 / 1000000000000) (-31288725504 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (216559069341447 / 800000000000)) (orderedInterval (46814896414 / 1000000000000) (46814896416 / 1000000000000), orderedInterval (12567619468 / 1000000000000) (12567619470 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (70030753538151 / 160000000000)) (orderedInterval (-37175243002 / 1000000000000) (-37175238152 / 1000000000000), orderedInterval (8556719045 / 1000000000000) (8556723895 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_stateChecks1 :
    compactCertificate496.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (63191396327829 / 800000000000)) (orderedInterval (-84708134242 / 1000000000000) (-84708134241 / 1000000000000), orderedInterval (-29195643946 / 1000000000000) (-29195643945 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (169740979141713 / 800000000000)) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (460879777692621 / 800000000000)) (orderedInterval (-30583787167 / 1000000000000) (-30583734795 / 1000000000000), orderedInterval (13052820367 / 1000000000000) (13052872739 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_stateChecks2 :
    compactCertificate496.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (339481958283573 / 800000000000)) (orderedInterval (-33055799468 / 1000000000000) (-33055799467 / 1000000000000), orderedInterval (-20148382398 / 1000000000000) (-20148382397 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (581708121803529 / 800000000000)) (orderedInterval (-23703630501 / 1000000000000) (-23703615382 / 1000000000000), orderedInterval (17726627529 / 1000000000000) (17726642648 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (428483569680411 / 800000000000)) (orderedInterval (25270843410 / 1000000000000) (25270857224 / 1000000000000), orderedInterval (-23475349309 / 1000000000000) (-23475335495 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_stateChecks3 :
    compactCertificate496.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (657403985384853 / 800000000000)) (orderedInterval (-14715114525 / 1000000000000) (-14715114407 / 1000000000000), orderedInterval (23634638575 / 1000000000000) (23634638692 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (379552367928237 / 800000000000)) (orderedInterval (-27401475510 / 1000000000000) (-27401475509 / 1000000000000), orderedInterval (-24281446389 / 1000000000000) (-24281446388 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 268 12 (673522337396433 / 800000000000)) (orderedInterval (18569106564 / 1000000000000) (18569106565 / 1000000000000), orderedInterval (20270884211 / 1000000000000) (20270884212 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_stateChecks4 :
    compactCertificate496.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (629291934615477 / 800000000000)) (orderedInterval (25844422206 / 1000000000000) (25844499753 / 1000000000000), orderedInterval (-11906770419 / 1000000000000) (-11906692871 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (449092418105541 / 800000000000)) (orderedInterval (6504973273 / 1000000000000) (6504973277 / 1000000000000), orderedInterval (-33047304771 / 1000000000000) (-33047304767 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (509222937425139 / 800000000000)) (orderedInterval (13167313071 / 1000000000000) (13167313144 / 1000000000000), orderedInterval (-28763867886 / 1000000000000) (-28763867813 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_stateChecks5 :
    compactCertificate496.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (424536996065091 / 800000000000)) (orderedInterval (-17427360560 / 1000000000000) (-17427360559 / 1000000000000), orderedInterval (-29915793183 / 1000000000000) (-29915793182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (375091310938911 / 800000000000)) (orderedInterval (-36841679598 / 1000000000000) (-36841679258 / 1000000000000), orderedInterval (-654577604 / 1000000000000) (-654577264 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (108716081796189 / 160000000000)) (orderedInterval (30437746503 / 1000000000000) (30437751525 / 1000000000000), orderedInterval (-3258353130 / 1000000000000) (-3258348109 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_stateChecks6 :
    compactCertificate496.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (300714403662183 / 800000000000)) (orderedInterval (-12673666258 / 1000000000000) (-12673666166 / 1000000000000), orderedInterval (39170389534 / 1000000000000) (39170389625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (254918930305263 / 800000000000)) (orderedInterval (-37822357698 / 1000000000000) (-37822290330 / 1000000000000), orderedInterval (23878304036 / 1000000000000) (23878371404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (159516430319589 / 800000000000)) (orderedInterval (-43608417814 / 1000000000000) (-43608309796 / 1000000000000), orderedInterval (36040573959 / 1000000000000) (36040681978 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_stateChecks7 :
    compactCertificate496.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (85788466753563 / 800000000000)) (orderedInterval (71969915366 / 1000000000000) (71969915367 / 1000000000000), orderedInterval (27176797351 / 1000000000000) (27176797352 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (232932375469689 / 800000000000)) (orderedInterval (10098347743 / 1000000000000) (10098347786 / 1000000000000), orderedInterval (-45673445300 / 1000000000000) (-45673445258 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (318049244702553 / 800000000000)) (orderedInterval (23757016244 / 1000000000000) (23757020435 / 1000000000000), orderedInterval (-32231055098 / 1000000000000) (-32231050907 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_stateChecks8 :
    compactCertificate496.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (134483569680411 / 800000000000)) (orderedInterval (-42256383529 / 1000000000000) (-42256341256 / 1000000000000), orderedInterval (44863222453 / 1000000000000) (44863264726 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (546668244446331 / 800000000000)) (orderedInterval (-20731150484 / 1000000000000) (-20731147575 / 1000000000000), orderedInterval (22417298758 / 1000000000000) (22417301667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (365149052462229 / 800000000000)) (orderedInterval (-37079222832 / 1000000000000) (-37079221140 / 1000000000000), orderedInterval (4500653270 / 1000000000000) (4500654962 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_states : ∀ j,
    BesselStateValid (compactCertificate496.point j) (compactCertificate496.state j) :=
  compactCertificate496.statesValid_of_checks3 compactCertificate496_stateChecks0
    compactCertificate496_stateChecks1 compactCertificate496_stateChecks2
    compactCertificate496_stateChecks3 compactCertificate496_stateChecks4
    compactCertificate496_stateChecks5 compactCertificate496_stateChecks6
    compactCertificate496_stateChecks7 compactCertificate496_stateChecks8

theorem compactCertificate496_chunkChecks0_0 :
    compactCertificate496.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (735 / 2) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27404014723 / 1000000000000) (-27404014722 / 1000000000000), orderedInterval (-31288725505 / 1000000000000) (-31288725504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (216559069341447 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46814896414 / 1000000000000) (46814896416 / 1000000000000), orderedInterval (12567619468 / 1000000000000) (12567619470 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (70030753538151 / 160000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37175243002 / 1000000000000) (-37175238152 / 1000000000000), orderedInterval (8556719045 / 1000000000000) (8556723895 / 1000000000000)))) (orderedInterval (-12607253742 / 1000000000000) (-12607253431 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (63191396327829 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-84708134242 / 1000000000000) (-84708134241 / 1000000000000), orderedInterval (-29195643946 / 1000000000000) (-29195643945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (169740979141713 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (460879777692621 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30583787167 / 1000000000000) (-30583734795 / 1000000000000), orderedInterval (13052820367 / 1000000000000) (13052872739 / 1000000000000)))) (orderedInterval (1855543853 / 1000000000000) (1855548167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (339481958283573 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33055799468 / 1000000000000) (-33055799467 / 1000000000000), orderedInterval (-20148382398 / 1000000000000) (-20148382397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (581708121803529 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23703630501 / 1000000000000) (-23703615382 / 1000000000000), orderedInterval (17726627529 / 1000000000000) (17726642648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (428483569680411 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25270843410 / 1000000000000) (25270857224 / 1000000000000), orderedInterval (-23475349309 / 1000000000000) (-23475335495 / 1000000000000)))) (orderedInterval (1341860752 / 1000000000000) (1341861573 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_chunkChecks0_1 :
    compactCertificate496.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (657403985384853 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14715114525 / 1000000000000) (-14715114407 / 1000000000000), orderedInterval (23634638575 / 1000000000000) (23634638692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (379552367928237 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27401475510 / 1000000000000) (-27401475509 / 1000000000000), orderedInterval (-24281446389 / 1000000000000) (-24281446388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (673522337396433 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18569106564 / 1000000000000) (18569106565 / 1000000000000), orderedInterval (20270884211 / 1000000000000) (20270884212 / 1000000000000)))) (orderedInterval (3224182146 / 1000000000000) (3224182313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (629291934615477 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25844422206 / 1000000000000) (25844499753 / 1000000000000), orderedInterval (-11906770419 / 1000000000000) (-11906692871 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (449092418105541 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6504973273 / 1000000000000) (6504973277 / 1000000000000), orderedInterval (-33047304771 / 1000000000000) (-33047304767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (509222937425139 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13167313071 / 1000000000000) (13167313144 / 1000000000000), orderedInterval (-28763867886 / 1000000000000) (-28763867813 / 1000000000000)))) (orderedInterval (81921728 / 1000000000000) (81923173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (424536996065091 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17427360560 / 1000000000000) (-17427360559 / 1000000000000), orderedInterval (-29915793183 / 1000000000000) (-29915793182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (375091310938911 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36841679598 / 1000000000000) (-36841679258 / 1000000000000), orderedInterval (-654577604 / 1000000000000) (-654577264 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (108716081796189 / 160000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30437746503 / 1000000000000) (30437751525 / 1000000000000), orderedInterval (-3258353130 / 1000000000000) (-3258348109 / 1000000000000)))) (orderedInterval (2686407992 / 1000000000000) (2686408176 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_chunkChecks0_2 :
    compactCertificate496.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (300714403662183 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12673666258 / 1000000000000) (-12673666166 / 1000000000000), orderedInterval (39170389534 / 1000000000000) (39170389625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (254918930305263 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37822357698 / 1000000000000) (-37822290330 / 1000000000000), orderedInterval (23878304036 / 1000000000000) (23878371404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (159516430319589 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43608417814 / 1000000000000) (-43608309796 / 1000000000000), orderedInterval (36040573959 / 1000000000000) (36040681978 / 1000000000000)))) (orderedInterval (2747479495 / 1000000000000) (2747486932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (85788466753563 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71969915366 / 1000000000000) (71969915367 / 1000000000000), orderedInterval (27176797351 / 1000000000000) (27176797352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (232932375469689 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10098347743 / 1000000000000) (10098347786 / 1000000000000), orderedInterval (-45673445300 / 1000000000000) (-45673445258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (318049244702553 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23757016244 / 1000000000000) (23757020435 / 1000000000000), orderedInterval (-32231055098 / 1000000000000) (-32231050907 / 1000000000000)))) (orderedInterval (-3378743953 / 1000000000000) (-3378743587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (134483569680411 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42256383529 / 1000000000000) (-42256341256 / 1000000000000), orderedInterval (44863222453 / 1000000000000) (44863264726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (546668244446331 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20731150484 / 1000000000000) (-20731147575 / 1000000000000), orderedInterval (22417298758 / 1000000000000) (22417301667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (365149052462229 / 800000000000) 0 (IntervalRat.scale (735 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37079222832 / 1000000000000) (-37079221140 / 1000000000000), orderedInterval (4500653270 / 1000000000000) (4500654962 / 1000000000000)))) (orderedInterval (8389862347 / 1000000000000) (8389863258 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_chunkChecks0 :
    compactCertificate496.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate496.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate496_chunkChecks0_0
    compactCertificate496_chunkChecks0_1 compactCertificate496_chunkChecks0_2

theorem compactCertificate496_chunkChecks1_0 :
    compactCertificate496.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (735 / 2) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27404014723 / 1000000000000) (-27404014722 / 1000000000000), orderedInterval (-31288725505 / 1000000000000) (-31288725504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (216559069341447 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46814896414 / 1000000000000) (46814896416 / 1000000000000), orderedInterval (12567619468 / 1000000000000) (12567619470 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (70030753538151 / 160000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37175243002 / 1000000000000) (-37175238152 / 1000000000000), orderedInterval (8556719045 / 1000000000000) (8556723895 / 1000000000000)))) (orderedInterval (-11717473680 / 1000000000000) (-11717473311 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (63191396327829 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-84708134242 / 1000000000000) (-84708134241 / 1000000000000), orderedInterval (-29195643946 / 1000000000000) (-29195643945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (169740979141713 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (460879777692621 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30583787167 / 1000000000000) (-30583734795 / 1000000000000), orderedInterval (13052820367 / 1000000000000) (13052872739 / 1000000000000)))) (orderedInterval (-477840693 / 1000000000000) (-477834491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (339481958283573 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33055799468 / 1000000000000) (-33055799467 / 1000000000000), orderedInterval (-20148382398 / 1000000000000) (-20148382397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (581708121803529 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23703630501 / 1000000000000) (-23703615382 / 1000000000000), orderedInterval (17726627529 / 1000000000000) (17726642648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (428483569680411 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25270843410 / 1000000000000) (25270857224 / 1000000000000), orderedInterval (-23475349309 / 1000000000000) (-23475335495 / 1000000000000)))) (orderedInterval (-1908695453 / 1000000000000) (-1908694007 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_chunkChecks1_1 :
    compactCertificate496.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (657403985384853 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14715114525 / 1000000000000) (-14715114407 / 1000000000000), orderedInterval (23634638575 / 1000000000000) (23634638692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (379552367928237 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27401475510 / 1000000000000) (-27401475509 / 1000000000000), orderedInterval (-24281446389 / 1000000000000) (-24281446388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (673522337396433 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18569106564 / 1000000000000) (18569106565 / 1000000000000), orderedInterval (20270884211 / 1000000000000) (20270884212 / 1000000000000)))) (orderedInterval (-5111645233 / 1000000000000) (-5111644884 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (629291934615477 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25844422206 / 1000000000000) (25844499753 / 1000000000000), orderedInterval (-11906770419 / 1000000000000) (-11906692871 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (449092418105541 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6504973273 / 1000000000000) (6504973277 / 1000000000000), orderedInterval (-33047304771 / 1000000000000) (-33047304767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (509222937425139 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13167313071 / 1000000000000) (13167313144 / 1000000000000), orderedInterval (-28763867886 / 1000000000000) (-28763867813 / 1000000000000)))) (orderedInterval (-4061374234 / 1000000000000) (-4061371164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (424536996065091 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17427360560 / 1000000000000) (-17427360559 / 1000000000000), orderedInterval (-29915793183 / 1000000000000) (-29915793182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (375091310938911 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36841679598 / 1000000000000) (-36841679258 / 1000000000000), orderedInterval (-654577604 / 1000000000000) (-654577264 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (108716081796189 / 160000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30437746503 / 1000000000000) (30437751525 / 1000000000000), orderedInterval (-3258353130 / 1000000000000) (-3258348109 / 1000000000000)))) (orderedInterval (-605299522 / 1000000000000) (-605299208 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_chunkChecks1_2 :
    compactCertificate496.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (300714403662183 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12673666258 / 1000000000000) (-12673666166 / 1000000000000), orderedInterval (39170389534 / 1000000000000) (39170389625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (254918930305263 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37822357698 / 1000000000000) (-37822290330 / 1000000000000), orderedInterval (23878304036 / 1000000000000) (23878371404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (159516430319589 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43608417814 / 1000000000000) (-43608309796 / 1000000000000), orderedInterval (36040573959 / 1000000000000) (36040681978 / 1000000000000)))) (orderedInterval (-6941338456 / 1000000000000) (-6941333141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (85788466753563 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71969915366 / 1000000000000) (71969915367 / 1000000000000), orderedInterval (27176797351 / 1000000000000) (27176797352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (232932375469689 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10098347743 / 1000000000000) (10098347786 / 1000000000000), orderedInterval (-45673445300 / 1000000000000) (-45673445258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (318049244702553 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23757016244 / 1000000000000) (23757020435 / 1000000000000), orderedInterval (-32231055098 / 1000000000000) (-32231050907 / 1000000000000)))) (orderedInterval (3346737029 / 1000000000000) (3346737417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (134483569680411 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42256383529 / 1000000000000) (-42256341256 / 1000000000000), orderedInterval (44863222453 / 1000000000000) (44863264726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (546668244446331 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20731150484 / 1000000000000) (-20731147575 / 1000000000000), orderedInterval (22417298758 / 1000000000000) (22417301667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (365149052462229 / 800000000000) 1 (IntervalRat.scale (735 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37079222832 / 1000000000000) (-37079221140 / 1000000000000), orderedInterval (4500653270 / 1000000000000) (4500654962 / 1000000000000)))) (orderedInterval (-4318166297 / 1000000000000) (-4318165203 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_chunkChecks1 :
    compactCertificate496.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate496.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate496_chunkChecks1_0
    compactCertificate496_chunkChecks1_1 compactCertificate496_chunkChecks1_2

theorem compactCertificate496_chunkChecks2_0 :
    compactCertificate496.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (735 / 2) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27404014723 / 1000000000000) (-27404014722 / 1000000000000), orderedInterval (-31288725505 / 1000000000000) (-31288725504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (216559069341447 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46814896414 / 1000000000000) (46814896416 / 1000000000000), orderedInterval (12567619468 / 1000000000000) (12567619470 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (70030753538151 / 160000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37175243002 / 1000000000000) (-37175238152 / 1000000000000), orderedInterval (8556719045 / 1000000000000) (8556723895 / 1000000000000)))) (orderedInterval (13751584464 / 1000000000000) (13751584903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (63191396327829 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-84708134242 / 1000000000000) (-84708134241 / 1000000000000), orderedInterval (-29195643946 / 1000000000000) (-29195643945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (169740979141713 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (460879777692621 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30583787167 / 1000000000000) (-30583734795 / 1000000000000), orderedInterval (13052820367 / 1000000000000) (13052872739 / 1000000000000)))) (orderedInterval (-4971516031 / 1000000000000) (-4971506613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (339481958283573 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33055799468 / 1000000000000) (-33055799467 / 1000000000000), orderedInterval (-20148382398 / 1000000000000) (-20148382397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (581708121803529 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23703630501 / 1000000000000) (-23703615382 / 1000000000000), orderedInterval (17726627529 / 1000000000000) (17726642648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (428483569680411 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25270843410 / 1000000000000) (25270857224 / 1000000000000), orderedInterval (-23475349309 / 1000000000000) (-23475335495 / 1000000000000)))) (orderedInterval (-4154297565 / 1000000000000) (-4154294962 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_chunkChecks2_1 :
    compactCertificate496.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (657403985384853 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14715114525 / 1000000000000) (-14715114407 / 1000000000000), orderedInterval (23634638575 / 1000000000000) (23634638692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (379552367928237 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27401475510 / 1000000000000) (-27401475509 / 1000000000000), orderedInterval (-24281446389 / 1000000000000) (-24281446388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (673522337396433 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18569106564 / 1000000000000) (18569106565 / 1000000000000), orderedInterval (20270884211 / 1000000000000) (20270884212 / 1000000000000)))) (orderedInterval (-23529557747 / 1000000000000) (-23529556994 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (629291934615477 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25844422206 / 1000000000000) (25844499753 / 1000000000000), orderedInterval (-11906770419 / 1000000000000) (-11906692871 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (449092418105541 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6504973273 / 1000000000000) (6504973277 / 1000000000000), orderedInterval (-33047304771 / 1000000000000) (-33047304767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (509222937425139 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13167313071 / 1000000000000) (13167313144 / 1000000000000), orderedInterval (-28763867886 / 1000000000000) (-28763867813 / 1000000000000)))) (orderedInterval (913260474 / 1000000000000) (913267016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (424536996065091 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17427360560 / 1000000000000) (-17427360559 / 1000000000000), orderedInterval (-29915793183 / 1000000000000) (-29915793182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (375091310938911 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36841679598 / 1000000000000) (-36841679258 / 1000000000000), orderedInterval (-654577604 / 1000000000000) (-654577264 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (108716081796189 / 160000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30437746503 / 1000000000000) (30437751525 / 1000000000000), orderedInterval (-3258353130 / 1000000000000) (-3258348109 / 1000000000000)))) (orderedInterval (-5674601960 / 1000000000000) (-5674601412 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_chunkChecks2_2 :
    compactCertificate496.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (300714403662183 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12673666258 / 1000000000000) (-12673666166 / 1000000000000), orderedInterval (39170389534 / 1000000000000) (39170389625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (254918930305263 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37822357698 / 1000000000000) (-37822290330 / 1000000000000), orderedInterval (23878304036 / 1000000000000) (23878371404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (159516430319589 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43608417814 / 1000000000000) (-43608309796 / 1000000000000), orderedInterval (36040573959 / 1000000000000) (36040681978 / 1000000000000)))) (orderedInterval (-3292656545 / 1000000000000) (-3292652532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (85788466753563 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71969915366 / 1000000000000) (71969915367 / 1000000000000), orderedInterval (27176797351 / 1000000000000) (27176797352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (232932375469689 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10098347743 / 1000000000000) (10098347786 / 1000000000000), orderedInterval (-45673445300 / 1000000000000) (-45673445258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (318049244702553 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23757016244 / 1000000000000) (23757020435 / 1000000000000), orderedInterval (-32231055098 / 1000000000000) (-32231050907 / 1000000000000)))) (orderedInterval (2378619075 / 1000000000000) (2378619493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (134483569680411 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42256383529 / 1000000000000) (-42256341256 / 1000000000000), orderedInterval (44863222453 / 1000000000000) (44863264726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (546668244446331 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20731150484 / 1000000000000) (-20731147575 / 1000000000000), orderedInterval (22417298758 / 1000000000000) (22417301667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (365149052462229 / 800000000000) 2 (IntervalRat.scale (735 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37079222832 / 1000000000000) (-37079221140 / 1000000000000), orderedInterval (4500653270 / 1000000000000) (4500654962 / 1000000000000)))) (orderedInterval (-16501289326 / 1000000000000) (-16501287751 / 1000000000000))) = true
  rfl'

theorem compactCertificate496_chunkChecks2 :
    compactCertificate496.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate496.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate496_chunkChecks2_0
    compactCertificate496_chunkChecks2_1 compactCertificate496_chunkChecks2_2

theorem compactCertificate496_chunkChecks3_0 :
    compactCertificate496.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (735 / 2) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27404014723 / 1000000000000) (-27404014722 / 1000000000000), orderedInterval (-31288725505 / 1000000000000) (-31288725504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (216559069341447 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46814896414 / 1000000000000) (46814896416 / 1000000000000), orderedInterval (12567619468 / 1000000000000) (12567619470 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (70030753538151 / 160000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37175243002 / 1000000000000) (-37175238152 / 1000000000000), orderedInterval (8556719045 / 1000000000000) (8556723895 / 1000000000000)))) (orderedInterval (11469164825 / 1000000000000) (11469165346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (63191396327829 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-84708134242 / 1000000000000) (-84708134241 / 1000000000000), orderedInterval (-29195643946 / 1000000000000) (-29195643945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (169740979141713 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (460879777692621 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30583787167 / 1000000000000) (-30583734795 / 1000000000000), orderedInterval (13052820367 / 1000000000000) (13052872739 / 1000000000000)))) (orderedInterval (3282110754 / 1000000000000) (3282125331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (339481958283573 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33055799468 / 1000000000000) (-33055799467 / 1000000000000), orderedInterval (-20148382398 / 1000000000000) (-20148382397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (581708121803529 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23703630501 / 1000000000000) (-23703615382 / 1000000000000), orderedInterval (17726627529 / 1000000000000) (17726642648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (428483569680411 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25270843410 / 1000000000000) (25270857224 / 1000000000000), orderedInterval (-23475349309 / 1000000000000) (-23475335495 / 1000000000000)))) (orderedInterval (6002813869 / 1000000000000) (6002818638 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate496_chunkChecks3_1 :
    compactCertificate496.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (657403985384853 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14715114525 / 1000000000000) (-14715114407 / 1000000000000), orderedInterval (23634638575 / 1000000000000) (23634638692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (379552367928237 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27401475510 / 1000000000000) (-27401475509 / 1000000000000), orderedInterval (-24281446389 / 1000000000000) (-24281446388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (673522337396433 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18569106564 / 1000000000000) (18569106565 / 1000000000000), orderedInterval (20270884211 / 1000000000000) (20270884212 / 1000000000000)))) (orderedInterval (16241902383 / 1000000000000) (16241904036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (629291934615477 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25844422206 / 1000000000000) (25844499753 / 1000000000000), orderedInterval (-11906770419 / 1000000000000) (-11906692871 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (449092418105541 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6504973273 / 1000000000000) (6504973277 / 1000000000000), orderedInterval (-33047304771 / 1000000000000) (-33047304767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (509222937425139 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13167313071 / 1000000000000) (13167313144 / 1000000000000), orderedInterval (-28763867886 / 1000000000000) (-28763867813 / 1000000000000)))) (orderedInterval (8271550924 / 1000000000000) (8271564873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (424536996065091 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17427360560 / 1000000000000) (-17427360559 / 1000000000000), orderedInterval (-29915793183 / 1000000000000) (-29915793182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (375091310938911 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36841679598 / 1000000000000) (-36841679258 / 1000000000000), orderedInterval (-654577604 / 1000000000000) (-654577264 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (108716081796189 / 160000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30437746503 / 1000000000000) (30437751525 / 1000000000000), orderedInterval (-3258353130 / 1000000000000) (-3258348109 / 1000000000000)))) (orderedInterval (1505099410 / 1000000000000) (1505100381 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate496_chunkChecks3_2 :
    compactCertificate496.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (300714403662183 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12673666258 / 1000000000000) (-12673666166 / 1000000000000), orderedInterval (39170389534 / 1000000000000) (39170389625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (254918930305263 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37822357698 / 1000000000000) (-37822290330 / 1000000000000), orderedInterval (23878304036 / 1000000000000) (23878371404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (159516430319589 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43608417814 / 1000000000000) (-43608309796 / 1000000000000), orderedInterval (36040573959 / 1000000000000) (36040681978 / 1000000000000)))) (orderedInterval (7404548505 / 1000000000000) (7404551658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (85788466753563 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71969915366 / 1000000000000) (71969915367 / 1000000000000), orderedInterval (27176797351 / 1000000000000) (27176797352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (232932375469689 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10098347743 / 1000000000000) (10098347786 / 1000000000000), orderedInterval (-45673445300 / 1000000000000) (-45673445258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (318049244702553 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23757016244 / 1000000000000) (23757020435 / 1000000000000), orderedInterval (-32231055098 / 1000000000000) (-32231050907 / 1000000000000)))) (orderedInterval (-3636575469 / 1000000000000) (-3636575020 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (134483569680411 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42256383529 / 1000000000000) (-42256341256 / 1000000000000), orderedInterval (44863222453 / 1000000000000) (44863264726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (546668244446331 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20731150484 / 1000000000000) (-20731147575 / 1000000000000), orderedInterval (22417298758 / 1000000000000) (22417301667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (365149052462229 / 800000000000) 3 (IntervalRat.scale (735 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37079222832 / 1000000000000) (-37079221140 / 1000000000000), orderedInterval (4500653270 / 1000000000000) (4500654962 / 1000000000000)))) (orderedInterval (13368149824 / 1000000000000) (13368152308 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate496_chunkChecks3 :
    compactCertificate496.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate496.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate496_chunkChecks3_0
    compactCertificate496_chunkChecks3_1 compactCertificate496_chunkChecks3_2

theorem compactCertificate496_chunkChecks4_0 :
    compactCertificate496.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (735 / 2) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-27404014723 / 1000000000000) (-27404014722 / 1000000000000), orderedInterval (-31288725505 / 1000000000000) (-31288725504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (216559069341447 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46814896414 / 1000000000000) (46814896416 / 1000000000000), orderedInterval (12567619468 / 1000000000000) (12567619470 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (70030753538151 / 160000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37175243002 / 1000000000000) (-37175238152 / 1000000000000), orderedInterval (8556719045 / 1000000000000) (8556723895 / 1000000000000)))) (orderedInterval (-15185219526 / 1000000000000) (-15185218904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (63191396327829 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-84708134242 / 1000000000000) (-84708134241 / 1000000000000), orderedInterval (-29195643946 / 1000000000000) (-29195643945 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (169740979141713 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-33897750346 / 1000000000000) (-33897735382 / 1000000000000), orderedInterval (43107472450 / 1000000000000) (43107487414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (460879777692621 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30583787167 / 1000000000000) (-30583734795 / 1000000000000), orderedInterval (13052820367 / 1000000000000) (13052872739 / 1000000000000)))) (orderedInterval (12976344740 / 1000000000000) (12976367523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (339481958283573 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-33055799468 / 1000000000000) (-33055799467 / 1000000000000), orderedInterval (-20148382398 / 1000000000000) (-20148382397 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (581708121803529 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23703630501 / 1000000000000) (-23703615382 / 1000000000000), orderedInterval (17726627529 / 1000000000000) (17726642648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (428483569680411 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (25270843410 / 1000000000000) (25270857224 / 1000000000000), orderedInterval (-23475349309 / 1000000000000) (-23475335495 / 1000000000000)))) (orderedInterval (13927970228 / 1000000000000) (13927979121 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate496_chunkChecks4_1 :
    compactCertificate496.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (657403985384853 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14715114525 / 1000000000000) (-14715114407 / 1000000000000), orderedInterval (23634638575 / 1000000000000) (23634638692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (379552367928237 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27401475510 / 1000000000000) (-27401475509 / 1000000000000), orderedInterval (-24281446389 / 1000000000000) (-24281446388 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (673522337396433 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18569106564 / 1000000000000) (18569106565 / 1000000000000), orderedInterval (20270884211 / 1000000000000) (20270884212 / 1000000000000)))) (orderedInterval (132346098581 / 1000000000000) (132346102259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (629291934615477 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25844422206 / 1000000000000) (25844499753 / 1000000000000), orderedInterval (-11906770419 / 1000000000000) (-11906692871 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (449092418105541 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (6504973273 / 1000000000000) (6504973277 / 1000000000000), orderedInterval (-33047304771 / 1000000000000) (-33047304767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (509222937425139 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13167313071 / 1000000000000) (13167313144 / 1000000000000), orderedInterval (-28763867886 / 1000000000000) (-28763867813 / 1000000000000)))) (orderedInterval (-7089203565 / 1000000000000) (-7089173753 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (424536996065091 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17427360560 / 1000000000000) (-17427360559 / 1000000000000), orderedInterval (-29915793183 / 1000000000000) (-29915793182 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (375091310938911 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36841679598 / 1000000000000) (-36841679258 / 1000000000000), orderedInterval (-654577604 / 1000000000000) (-654577264 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (108716081796189 / 160000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (30437746503 / 1000000000000) (30437751525 / 1000000000000), orderedInterval (-3258353130 / 1000000000000) (-3258348109 / 1000000000000)))) (orderedInterval (13809939789 / 1000000000000) (13809941533 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate496_chunkChecks4_2 :
    compactCertificate496.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (300714403662183 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-12673666258 / 1000000000000) (-12673666166 / 1000000000000), orderedInterval (39170389534 / 1000000000000) (39170389625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (254918930305263 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-37822357698 / 1000000000000) (-37822290330 / 1000000000000), orderedInterval (23878304036 / 1000000000000) (23878371404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (159516430319589 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43608417814 / 1000000000000) (-43608309796 / 1000000000000), orderedInterval (36040573959 / 1000000000000) (36040681978 / 1000000000000)))) (orderedInterval (3264619292 / 1000000000000) (3264621863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (85788466753563 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (71969915366 / 1000000000000) (71969915367 / 1000000000000), orderedInterval (27176797351 / 1000000000000) (27176797352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (232932375469689 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10098347743 / 1000000000000) (10098347786 / 1000000000000), orderedInterval (-45673445300 / 1000000000000) (-45673445258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (318049244702553 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23757016244 / 1000000000000) (23757020435 / 1000000000000), orderedInterval (-32231055098 / 1000000000000) (-32231050907 / 1000000000000)))) (orderedInterval (-2573712405 / 1000000000000) (-2573711919 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (134483569680411 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42256383529 / 1000000000000) (-42256341256 / 1000000000000), orderedInterval (44863222453 / 1000000000000) (44863264726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (546668244446331 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20731150484 / 1000000000000) (-20731147575 / 1000000000000), orderedInterval (22417298758 / 1000000000000) (22417301667 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (365149052462229 / 800000000000) 4 (IntervalRat.scale (735 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37079222832 / 1000000000000) (-37079221140 / 1000000000000), orderedInterval (4500653270 / 1000000000000) (4500654962 / 1000000000000)))) (orderedInterval (36643145302 / 1000000000000) (36643149434 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate496_chunkChecks4 :
    compactCertificate496.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate496.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate496_chunkChecks4_0
    compactCertificate496_chunkChecks4_1 compactCertificate496_chunkChecks4_2

theorem compactCertificate496_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate496.chunkCheck r b = true :=
  compactCertificate496.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate496_chunkChecks0
    · exact compactCertificate496_chunkChecks1
    · exact compactCertificate496_chunkChecks2
    · exact compactCertificate496_chunkChecks3
    · exact compactCertificate496_chunkChecks4)

theorem compactCertificate496_coefficient0 :
    compactCertificate496.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate496_coefficient1 :
    compactCertificate496.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate496_coefficient2 :
    compactCertificate496.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate496_coefficient3 :
    compactCertificate496.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate496_coefficient4 :
    compactCertificate496.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate496_coefficients : ∀ r : Fin 5,
    compactCertificate496.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate496_coefficient0
  · exact compactCertificate496_coefficient1
  · exact compactCertificate496_coefficient2
  · exact compactCertificate496_coefficient3
  · exact compactCertificate496_coefficient4

theorem compactCertificate496_lower : (1 : ℚ) ≤ compactCertificate496.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate496, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate496_proves {t : ℝ} (ht : t ∈ compactCertificate496.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate496.proves compactCertificate496_states compactCertificate496_chunks
    compactCertificate496_coefficients compactCertificate496_lower ht

end Erdos232
