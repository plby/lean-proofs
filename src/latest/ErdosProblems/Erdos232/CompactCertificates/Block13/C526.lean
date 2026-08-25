/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate526 : CompactCertificate where
  left := 397
  right := 398
  center := 795 / 2
  grid := fun i =>
    match i.val with
    | 0 => 127
    | 1 => 93
    | 2 => 151
    | 3 => 27
    | 4 => 73
    | 5 => 198
    | 6 => 146
    | 7 => 250
    | 8 => 184
    | 9 => 283
    | 10 => 163
    | 11 => 290
    | 12 => 271
    | 13 => 193
    | 14 => 219
    | 15 => 183
    | 16 => 162
    | 17 => 234
    | 18 => 129
    | 19 => 110
    | 20 => 69
    | 21 => 37
    | 22 => 100
    | 23 => 137
    | 24 => 58
    | 25 => 235
    | _ => 157
  point := fun i =>
    match i.val with
    | 0 => 795 / 2
    | 1 => 234237360716259 / 800000000000
    | 2 => 75747549745347 / 160000000000
    | 3 => 68349877660713 / 800000000000
    | 4 => 183597385602261 / 800000000000
    | 5 => 498502616687937 / 800000000000
    | 6 => 367194771204681 / 800000000000
    | 7 => 629194499093613 / 800000000000
    | 8 => 463461820266567 / 800000000000
    | 9 => 711069616844841 / 800000000000
    | 10 => 410536234697889 / 800000000000
    | 11 => 728503752694101 / 800000000000
    | 12 => 680662704788169 / 800000000000
    | 13 => 485753023665177 / 800000000000
    | 14 => 550792156806783 / 800000000000
    | 15 => 459193077376527 / 800000000000
    | 16 => 405711009791067 / 800000000000
    | 17 => 117590863983633 / 160000000000
    | 18 => 325262518246851 / 800000000000
    | 19 => 275728638901611 / 800000000000
    | 20 => 172538179733433 / 800000000000
    | 21 => 92791606896711 / 800000000000
    | 22 => 251947263263133 / 800000000000
    | 23 => 344012448351741 / 800000000000
    | 24 => 145461820266567 / 800000000000
    | 25 => 591294223584807 / 800000000000
    | _ => 394957138377513 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (25694928598 / 1000000000000) (25694936551 / 1000000000000), orderedInterval (-30713423440 / 1000000000000) (-30713415487 / 1000000000000))
    | 1 => (orderedInterval (-46053800920 / 1000000000000) (-46053800907 / 1000000000000), orderedInterval (-7223188320 / 1000000000000) (-7223188307 / 1000000000000))
    | 2 => (orderedInterval (6318546012 / 1000000000000) (6318546017 / 1000000000000), orderedInterval (-36128627883 / 1000000000000) (-36128627877 / 1000000000000))
    | 3 => (orderedInterval (-85038871850 / 1000000000000) (-85038871848 / 1000000000000), orderedInterval (-14320436018 / 1000000000000) (-14320436015 / 1000000000000))
    | 4 => (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000))
    | 5 => (orderedInterval (30465642956 / 1000000000000) (30465670479 / 1000000000000), orderedInterval (-9693725632 / 1000000000000) (-9693698110 / 1000000000000))
    | 6 => (orderedInterval (33292427793 / 1000000000000) (33292427794 / 1000000000000), orderedInterval (16655188898 / 1000000000000) (16655188899 / 1000000000000))
    | 7 => (orderedInterval (27099674718 / 1000000000000) (27099733603 / 1000000000000), orderedInterval (-8680215780 / 1000000000000) (-8680156896 / 1000000000000))
    | 8 => (orderedInterval (29270512668 / 1000000000000) (29270623240 / 1000000000000), orderedInterval (-15585792591 / 1000000000000) (-15585682020 / 1000000000000))
    | 9 => (orderedInterval (-14024011762 / 1000000000000) (-14024011761 / 1000000000000), orderedInterval (-22786105478 / 1000000000000) (-22786105477 / 1000000000000))
    | 10 => (orderedInterval (-33595513889 / 1000000000000) (-33595497954 / 1000000000000), orderedInterval (10611188497 / 1000000000000) (10611204432 / 1000000000000))
    | 11 => (orderedInterval (9142889616 / 1000000000000) (9142889617 / 1000000000000), orderedInterval (24804374568 / 1000000000000) (24804374569 / 1000000000000))
    | 12 => (orderedInterval (-6555831085 / 1000000000000) (-6555831084 / 1000000000000), orderedInterval (-26552811835 / 1000000000000) (-26552811834 / 1000000000000))
    | 13 => (orderedInterval (-32280837796 / 1000000000000) (-32280835287 / 1000000000000), orderedInterval (2559135270 / 1000000000000) (2559137779 / 1000000000000))
    | 14 => (orderedInterval (-29012321275 / 1000000000000) (-29012321246 / 1000000000000), orderedInterval (-9086379992 / 1000000000000) (-9086379962 / 1000000000000))
    | 15 => (orderedInterval (4479942216 / 1000000000000) (4479942218 / 1000000000000), orderedInterval (-33004522495 / 1000000000000) (-33004522493 / 1000000000000))
    | 16 => (orderedInterval (-30080601001 / 1000000000000) (-30080512068 / 1000000000000), orderedInterval (18750629392 / 1000000000000) (18750718324 / 1000000000000))
    | 17 => (orderedInterval (16507538738 / 1000000000000) (16507538739 / 1000000000000), orderedInterval (24355096345 / 1000000000000) (24355096346 / 1000000000000))
    | 18 => (orderedInterval (-34201514736 / 1000000000000) (-34201441649 / 1000000000000), orderedInterval (19943216356 / 1000000000000) (19943289443 / 1000000000000))
    | 19 => (orderedInterval (-5544017003 / 1000000000000) (-5544016996 / 1000000000000), orderedInterval (42626776867 / 1000000000000) (42626776874 / 1000000000000))
    | 20 => (orderedInterval (16695454294 / 1000000000000) (16695454567 / 1000000000000), orderedInterval (-51740295712 / 1000000000000) (-51740295439 / 1000000000000))
    | 21 => (orderedInterval (-37765122346 / 1000000000000) (-37765122345 / 1000000000000), orderedInterval (-63574307594 / 1000000000000) (-63574307593 / 1000000000000))
    | 22 => (orderedInterval (44957667570 / 1000000000000) (44957667704 / 1000000000000), orderedInterval (422340145 / 1000000000000) (422340278 / 1000000000000))
    | 23 => (orderedInterval (-15071177521 / 1000000000000) (-15071177520 / 1000000000000), orderedInterval (-35384705157 / 1000000000000) (-35384705156 / 1000000000000))
    | 24 => (orderedInterval (23021175501 / 1000000000000) (23021175502 / 1000000000000), orderedInterval (54446037220 / 1000000000000) (54446037221 / 1000000000000))
    | 25 => (orderedInterval (-29299072429 / 1000000000000) (-29299068267 / 1000000000000), orderedInterval (1719267837 / 1000000000000) (1719271999 / 1000000000000))
    | _ => (orderedInterval (-34094797114 / 1000000000000) (-34094797109 / 1000000000000), orderedInterval (-11236703374 / 1000000000000) (-11236703369 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (10126217583 / 1000000000000) (10126220764 / 1000000000000)
      | 1 => orderedInterval (-2802146666 / 1000000000000) (-2802144661 / 1000000000000)
      | 2 => orderedInterval (-128453681 / 1000000000000) (-128449170 / 1000000000000)
      | 3 => orderedInterval (1302461992 / 1000000000000) (1302463331 / 1000000000000)
      | 4 => orderedInterval (-2787396524 / 1000000000000) (-2787396239 / 1000000000000)
      | 5 => orderedInterval (2195798820 / 1000000000000) (2195803948 / 1000000000000)
      | 6 => orderedInterval (6325868132 / 1000000000000) (6325879928 / 1000000000000)
      | 7 => orderedInterval (832426990 / 1000000000000) (832427041 / 1000000000000)
      | _ => orderedInterval (8920863733 / 1000000000000) (8920864183 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14748303841 / 1000000000000) (-14748300657 / 1000000000000)
      | 1 => orderedInterval (465597708 / 1000000000000) (465600830 / 1000000000000)
      | 2 => orderedInterval (-19248694 / 1000000000000) (-19241166 / 1000000000000)
      | 3 => orderedInterval (18146297185 / 1000000000000) (18146299036 / 1000000000000)
      | 4 => orderedInterval (1475349436 / 1000000000000) (1475349876 / 1000000000000)
      | 5 => orderedInterval (-766397226 / 1000000000000) (-766390677 / 1000000000000)
      | 6 => orderedInterval (-6267487160 / 1000000000000) (-6267475109 / 1000000000000)
      | 7 => orderedInterval (3268624819 / 1000000000000) (3268624864 / 1000000000000)
      | _ => orderedInterval (2508428067 / 1000000000000) (2508428853 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-10440578242 / 1000000000000) (-10440575045 / 1000000000000)
      | 1 => orderedInterval (5798135907 / 1000000000000) (5798140798 / 1000000000000)
      | 2 => orderedInterval (1769715787 / 1000000000000) (1769728662 / 1000000000000)
      | 3 => orderedInterval (-15177707383 / 1000000000000) (-15177704710 / 1000000000000)
      | 4 => orderedInterval (6136253904 / 1000000000000) (6136254587 / 1000000000000)
      | 5 => orderedInterval (-4352766685 / 1000000000000) (-4352758303 / 1000000000000)
      | 6 => orderedInterval (-6101349983 / 1000000000000) (-6101337636 / 1000000000000)
      | 7 => orderedInterval (-779088908 / 1000000000000) (-779088863 / 1000000000000)
      | _ => orderedInterval (-18149275595 / 1000000000000) (-18149274192 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15808454894 / 1000000000000) (15808458097 / 1000000000000)
      | 1 => orderedInterval (-2454816766 / 1000000000000) (-2454809104 / 1000000000000)
      | 2 => orderedInterval (-912211515 / 1000000000000) (-912189016 / 1000000000000)
      | 3 => orderedInterval (-89314749841 / 1000000000000) (-89314745758 / 1000000000000)
      | 4 => orderedInterval (-5817750344 / 1000000000000) (-5817749280 / 1000000000000)
      | 5 => orderedInterval (-554513440 / 1000000000000) (-554502724 / 1000000000000)
      | 6 => orderedInterval (5269389293 / 1000000000000) (5269401916 / 1000000000000)
      | 7 => orderedInterval (-3455673075 / 1000000000000) (-3455673029 / 1000000000000)
      | _ => orderedInterval (-3125279965 / 1000000000000) (-3125277430 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10724673818 / 1000000000000) (10724677036 / 1000000000000)
      | 1 => orderedInterval (-13237976137 / 1000000000000) (-13237964110 / 1000000000000)
      | 2 => orderedInterval (-9614247251 / 1000000000000) (-9614207014 / 1000000000000)
      | 3 => orderedInterval (91631096495 / 1000000000000) (91631103201 / 1000000000000)
      | 4 => orderedInterval (-12784589412 / 1000000000000) (-12784587740 / 1000000000000)
      | 5 => orderedInterval (9727686661 / 1000000000000) (9727700398 / 1000000000000)
      | 6 => orderedInterval (6183407018 / 1000000000000) (6183419956 / 1000000000000)
      | 7 => orderedInterval (1202466253 / 1000000000000) (1202466301 / 1000000000000)
      | _ => orderedInterval (43753529395 / 1000000000000) (43753534024 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (23985640379 / 1000000000000) (23985669125 / 1000000000000)
    | 1 => orderedInterval (4062860294 / 1000000000000) (4062895850 / 1000000000000)
    | 2 => orderedInterval (-41296661198 / 1000000000000) (-41296614702 / 1000000000000)
    | 3 => orderedInterval (-84557150759 / 1000000000000) (-84557086328 / 1000000000000)
    | _ => orderedInterval (127586046840 / 1000000000000) (127586142052 / 1000000000000)

theorem compactCertificate526_stateChecks0 :
    compactCertificate526.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (795 / 2)) (orderedInterval (25694928598 / 1000000000000) (25694936551 / 1000000000000), orderedInterval (-30713423440 / 1000000000000) (-30713415487 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (234237360716259 / 800000000000)) (orderedInterval (-46053800920 / 1000000000000) (-46053800907 / 1000000000000), orderedInterval (-7223188320 / 1000000000000) (-7223188307 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (75747549745347 / 160000000000)) (orderedInterval (6318546012 / 1000000000000) (6318546017 / 1000000000000), orderedInterval (-36128627883 / 1000000000000) (-36128627877 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_stateChecks1 :
    compactCertificate526.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (68349877660713 / 800000000000)) (orderedInterval (-85038871850 / 1000000000000) (-85038871848 / 1000000000000), orderedInterval (-14320436018 / 1000000000000) (-14320436015 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (183597385602261 / 800000000000)) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (498502616687937 / 800000000000)) (orderedInterval (30465642956 / 1000000000000) (30465670479 / 1000000000000), orderedInterval (-9693725632 / 1000000000000) (-9693698110 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_stateChecks2 :
    compactCertificate526.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (367194771204681 / 800000000000)) (orderedInterval (33292427793 / 1000000000000) (33292427794 / 1000000000000), orderedInterval (16655188898 / 1000000000000) (16655188899 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (629194499093613 / 800000000000)) (orderedInterval (27099674718 / 1000000000000) (27099733603 / 1000000000000), orderedInterval (-8680215780 / 1000000000000) (-8680156896 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (463461820266567 / 800000000000)) (orderedInterval (29270512668 / 1000000000000) (29270623240 / 1000000000000), orderedInterval (-15585792591 / 1000000000000) (-15585682020 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_stateChecks3 :
    compactCertificate526.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 283 12 (711069616844841 / 800000000000)) (orderedInterval (-14024011762 / 1000000000000) (-14024011761 / 1000000000000), orderedInterval (-22786105478 / 1000000000000) (-22786105477 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (410536234697889 / 800000000000)) (orderedInterval (-33595513889 / 1000000000000) (-33595497954 / 1000000000000), orderedInterval (10611188497 / 1000000000000) (10611204432 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 290 12 (728503752694101 / 800000000000)) (orderedInterval (9142889616 / 1000000000000) (9142889617 / 1000000000000), orderedInterval (24804374568 / 1000000000000) (24804374569 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_stateChecks4 :
    compactCertificate526.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 271 12 (680662704788169 / 800000000000)) (orderedInterval (-6555831085 / 1000000000000) (-6555831084 / 1000000000000), orderedInterval (-26552811835 / 1000000000000) (-26552811834 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (485753023665177 / 800000000000)) (orderedInterval (-32280837796 / 1000000000000) (-32280835287 / 1000000000000), orderedInterval (2559135270 / 1000000000000) (2559137779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (550792156806783 / 800000000000)) (orderedInterval (-29012321275 / 1000000000000) (-29012321246 / 1000000000000), orderedInterval (-9086379992 / 1000000000000) (-9086379962 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_stateChecks5 :
    compactCertificate526.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (459193077376527 / 800000000000)) (orderedInterval (4479942216 / 1000000000000) (4479942218 / 1000000000000), orderedInterval (-33004522495 / 1000000000000) (-33004522493 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (405711009791067 / 800000000000)) (orderedInterval (-30080601001 / 1000000000000) (-30080512068 / 1000000000000), orderedInterval (18750629392 / 1000000000000) (18750718324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (117590863983633 / 160000000000)) (orderedInterval (16507538738 / 1000000000000) (16507538739 / 1000000000000), orderedInterval (24355096345 / 1000000000000) (24355096346 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_stateChecks6 :
    compactCertificate526.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (325262518246851 / 800000000000)) (orderedInterval (-34201514736 / 1000000000000) (-34201441649 / 1000000000000), orderedInterval (19943216356 / 1000000000000) (19943289443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (275728638901611 / 800000000000)) (orderedInterval (-5544017003 / 1000000000000) (-5544016996 / 1000000000000), orderedInterval (42626776867 / 1000000000000) (42626776874 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (172538179733433 / 800000000000)) (orderedInterval (16695454294 / 1000000000000) (16695454567 / 1000000000000), orderedInterval (-51740295712 / 1000000000000) (-51740295439 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_stateChecks7 :
    compactCertificate526.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (92791606896711 / 800000000000)) (orderedInterval (-37765122346 / 1000000000000) (-37765122345 / 1000000000000), orderedInterval (-63574307594 / 1000000000000) (-63574307593 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (251947263263133 / 800000000000)) (orderedInterval (44957667570 / 1000000000000) (44957667704 / 1000000000000), orderedInterval (422340145 / 1000000000000) (422340278 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (344012448351741 / 800000000000)) (orderedInterval (-15071177521 / 1000000000000) (-15071177520 / 1000000000000), orderedInterval (-35384705157 / 1000000000000) (-35384705156 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_stateChecks8 :
    compactCertificate526.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (145461820266567 / 800000000000)) (orderedInterval (23021175501 / 1000000000000) (23021175502 / 1000000000000), orderedInterval (54446037220 / 1000000000000) (54446037221 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (591294223584807 / 800000000000)) (orderedInterval (-29299072429 / 1000000000000) (-29299068267 / 1000000000000), orderedInterval (1719267837 / 1000000000000) (1719271999 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (394957138377513 / 800000000000)) (orderedInterval (-34094797114 / 1000000000000) (-34094797109 / 1000000000000), orderedInterval (-11236703374 / 1000000000000) (-11236703369 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_states : ∀ j,
    BesselStateValid (compactCertificate526.point j) (compactCertificate526.state j) :=
  compactCertificate526.statesValid_of_checks3 compactCertificate526_stateChecks0
    compactCertificate526_stateChecks1 compactCertificate526_stateChecks2
    compactCertificate526_stateChecks3 compactCertificate526_stateChecks4
    compactCertificate526_stateChecks5 compactCertificate526_stateChecks6
    compactCertificate526_stateChecks7 compactCertificate526_stateChecks8

theorem compactCertificate526_chunkChecks0_0 :
    compactCertificate526.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (795 / 2) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25694928598 / 1000000000000) (25694936551 / 1000000000000), orderedInterval (-30713423440 / 1000000000000) (-30713415487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (234237360716259 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46053800920 / 1000000000000) (-46053800907 / 1000000000000), orderedInterval (-7223188320 / 1000000000000) (-7223188307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (75747549745347 / 160000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (6318546012 / 1000000000000) (6318546017 / 1000000000000), orderedInterval (-36128627883 / 1000000000000) (-36128627877 / 1000000000000)))) (orderedInterval (10126217583 / 1000000000000) (10126220764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (68349877660713 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85038871850 / 1000000000000) (-85038871848 / 1000000000000), orderedInterval (-14320436018 / 1000000000000) (-14320436015 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (183597385602261 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (498502616687937 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30465642956 / 1000000000000) (30465670479 / 1000000000000), orderedInterval (-9693725632 / 1000000000000) (-9693698110 / 1000000000000)))) (orderedInterval (-2802146666 / 1000000000000) (-2802144661 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (367194771204681 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33292427793 / 1000000000000) (33292427794 / 1000000000000), orderedInterval (16655188898 / 1000000000000) (16655188899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (629194499093613 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27099674718 / 1000000000000) (27099733603 / 1000000000000), orderedInterval (-8680215780 / 1000000000000) (-8680156896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (463461820266567 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29270512668 / 1000000000000) (29270623240 / 1000000000000), orderedInterval (-15585792591 / 1000000000000) (-15585682020 / 1000000000000)))) (orderedInterval (-128453681 / 1000000000000) (-128449170 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_chunkChecks0_1 :
    compactCertificate526.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (711069616844841 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14024011762 / 1000000000000) (-14024011761 / 1000000000000), orderedInterval (-22786105478 / 1000000000000) (-22786105477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (410536234697889 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33595513889 / 1000000000000) (-33595497954 / 1000000000000), orderedInterval (10611188497 / 1000000000000) (10611204432 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (728503752694101 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9142889616 / 1000000000000) (9142889617 / 1000000000000), orderedInterval (24804374568 / 1000000000000) (24804374569 / 1000000000000)))) (orderedInterval (1302461992 / 1000000000000) (1302463331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (680662704788169 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6555831085 / 1000000000000) (-6555831084 / 1000000000000), orderedInterval (-26552811835 / 1000000000000) (-26552811834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (485753023665177 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32280837796 / 1000000000000) (-32280835287 / 1000000000000), orderedInterval (2559135270 / 1000000000000) (2559137779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (550792156806783 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29012321275 / 1000000000000) (-29012321246 / 1000000000000), orderedInterval (-9086379992 / 1000000000000) (-9086379962 / 1000000000000)))) (orderedInterval (-2787396524 / 1000000000000) (-2787396239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (459193077376527 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4479942216 / 1000000000000) (4479942218 / 1000000000000), orderedInterval (-33004522495 / 1000000000000) (-33004522493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (405711009791067 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30080601001 / 1000000000000) (-30080512068 / 1000000000000), orderedInterval (18750629392 / 1000000000000) (18750718324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (117590863983633 / 160000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16507538738 / 1000000000000) (16507538739 / 1000000000000), orderedInterval (24355096345 / 1000000000000) (24355096346 / 1000000000000)))) (orderedInterval (2195798820 / 1000000000000) (2195803948 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_chunkChecks0_2 :
    compactCertificate526.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (325262518246851 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34201514736 / 1000000000000) (-34201441649 / 1000000000000), orderedInterval (19943216356 / 1000000000000) (19943289443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (275728638901611 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5544017003 / 1000000000000) (-5544016996 / 1000000000000), orderedInterval (42626776867 / 1000000000000) (42626776874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (172538179733433 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16695454294 / 1000000000000) (16695454567 / 1000000000000), orderedInterval (-51740295712 / 1000000000000) (-51740295439 / 1000000000000)))) (orderedInterval (6325868132 / 1000000000000) (6325879928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (92791606896711 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-37765122346 / 1000000000000) (-37765122345 / 1000000000000), orderedInterval (-63574307594 / 1000000000000) (-63574307593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (251947263263133 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44957667570 / 1000000000000) (44957667704 / 1000000000000), orderedInterval (422340145 / 1000000000000) (422340278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (344012448351741 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15071177521 / 1000000000000) (-15071177520 / 1000000000000), orderedInterval (-35384705157 / 1000000000000) (-35384705156 / 1000000000000)))) (orderedInterval (832426990 / 1000000000000) (832427041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (145461820266567 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23021175501 / 1000000000000) (23021175502 / 1000000000000), orderedInterval (54446037220 / 1000000000000) (54446037221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (591294223584807 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29299072429 / 1000000000000) (-29299068267 / 1000000000000), orderedInterval (1719267837 / 1000000000000) (1719271999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (394957138377513 / 800000000000) 0 (IntervalRat.scale (795 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34094797114 / 1000000000000) (-34094797109 / 1000000000000), orderedInterval (-11236703374 / 1000000000000) (-11236703369 / 1000000000000)))) (orderedInterval (8920863733 / 1000000000000) (8920864183 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_chunkChecks0 :
    compactCertificate526.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate526.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate526_chunkChecks0_0
    compactCertificate526_chunkChecks0_1 compactCertificate526_chunkChecks0_2

theorem compactCertificate526_chunkChecks1_0 :
    compactCertificate526.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (795 / 2) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25694928598 / 1000000000000) (25694936551 / 1000000000000), orderedInterval (-30713423440 / 1000000000000) (-30713415487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (234237360716259 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46053800920 / 1000000000000) (-46053800907 / 1000000000000), orderedInterval (-7223188320 / 1000000000000) (-7223188307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (75747549745347 / 160000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (6318546012 / 1000000000000) (6318546017 / 1000000000000), orderedInterval (-36128627883 / 1000000000000) (-36128627877 / 1000000000000)))) (orderedInterval (-14748303841 / 1000000000000) (-14748300657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (68349877660713 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85038871850 / 1000000000000) (-85038871848 / 1000000000000), orderedInterval (-14320436018 / 1000000000000) (-14320436015 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (183597385602261 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (498502616687937 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30465642956 / 1000000000000) (30465670479 / 1000000000000), orderedInterval (-9693725632 / 1000000000000) (-9693698110 / 1000000000000)))) (orderedInterval (465597708 / 1000000000000) (465600830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (367194771204681 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33292427793 / 1000000000000) (33292427794 / 1000000000000), orderedInterval (16655188898 / 1000000000000) (16655188899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (629194499093613 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27099674718 / 1000000000000) (27099733603 / 1000000000000), orderedInterval (-8680215780 / 1000000000000) (-8680156896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (463461820266567 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29270512668 / 1000000000000) (29270623240 / 1000000000000), orderedInterval (-15585792591 / 1000000000000) (-15585682020 / 1000000000000)))) (orderedInterval (-19248694 / 1000000000000) (-19241166 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_chunkChecks1_1 :
    compactCertificate526.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (711069616844841 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14024011762 / 1000000000000) (-14024011761 / 1000000000000), orderedInterval (-22786105478 / 1000000000000) (-22786105477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (410536234697889 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33595513889 / 1000000000000) (-33595497954 / 1000000000000), orderedInterval (10611188497 / 1000000000000) (10611204432 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (728503752694101 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9142889616 / 1000000000000) (9142889617 / 1000000000000), orderedInterval (24804374568 / 1000000000000) (24804374569 / 1000000000000)))) (orderedInterval (18146297185 / 1000000000000) (18146299036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (680662704788169 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6555831085 / 1000000000000) (-6555831084 / 1000000000000), orderedInterval (-26552811835 / 1000000000000) (-26552811834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (485753023665177 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32280837796 / 1000000000000) (-32280835287 / 1000000000000), orderedInterval (2559135270 / 1000000000000) (2559137779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (550792156806783 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29012321275 / 1000000000000) (-29012321246 / 1000000000000), orderedInterval (-9086379992 / 1000000000000) (-9086379962 / 1000000000000)))) (orderedInterval (1475349436 / 1000000000000) (1475349876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (459193077376527 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4479942216 / 1000000000000) (4479942218 / 1000000000000), orderedInterval (-33004522495 / 1000000000000) (-33004522493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (405711009791067 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30080601001 / 1000000000000) (-30080512068 / 1000000000000), orderedInterval (18750629392 / 1000000000000) (18750718324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (117590863983633 / 160000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16507538738 / 1000000000000) (16507538739 / 1000000000000), orderedInterval (24355096345 / 1000000000000) (24355096346 / 1000000000000)))) (orderedInterval (-766397226 / 1000000000000) (-766390677 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_chunkChecks1_2 :
    compactCertificate526.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (325262518246851 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34201514736 / 1000000000000) (-34201441649 / 1000000000000), orderedInterval (19943216356 / 1000000000000) (19943289443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (275728638901611 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5544017003 / 1000000000000) (-5544016996 / 1000000000000), orderedInterval (42626776867 / 1000000000000) (42626776874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (172538179733433 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16695454294 / 1000000000000) (16695454567 / 1000000000000), orderedInterval (-51740295712 / 1000000000000) (-51740295439 / 1000000000000)))) (orderedInterval (-6267487160 / 1000000000000) (-6267475109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (92791606896711 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-37765122346 / 1000000000000) (-37765122345 / 1000000000000), orderedInterval (-63574307594 / 1000000000000) (-63574307593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (251947263263133 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44957667570 / 1000000000000) (44957667704 / 1000000000000), orderedInterval (422340145 / 1000000000000) (422340278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (344012448351741 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15071177521 / 1000000000000) (-15071177520 / 1000000000000), orderedInterval (-35384705157 / 1000000000000) (-35384705156 / 1000000000000)))) (orderedInterval (3268624819 / 1000000000000) (3268624864 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (145461820266567 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23021175501 / 1000000000000) (23021175502 / 1000000000000), orderedInterval (54446037220 / 1000000000000) (54446037221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (591294223584807 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29299072429 / 1000000000000) (-29299068267 / 1000000000000), orderedInterval (1719267837 / 1000000000000) (1719271999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (394957138377513 / 800000000000) 1 (IntervalRat.scale (795 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34094797114 / 1000000000000) (-34094797109 / 1000000000000), orderedInterval (-11236703374 / 1000000000000) (-11236703369 / 1000000000000)))) (orderedInterval (2508428067 / 1000000000000) (2508428853 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_chunkChecks1 :
    compactCertificate526.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate526.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate526_chunkChecks1_0
    compactCertificate526_chunkChecks1_1 compactCertificate526_chunkChecks1_2

theorem compactCertificate526_chunkChecks2_0 :
    compactCertificate526.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (795 / 2) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25694928598 / 1000000000000) (25694936551 / 1000000000000), orderedInterval (-30713423440 / 1000000000000) (-30713415487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (234237360716259 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46053800920 / 1000000000000) (-46053800907 / 1000000000000), orderedInterval (-7223188320 / 1000000000000) (-7223188307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (75747549745347 / 160000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (6318546012 / 1000000000000) (6318546017 / 1000000000000), orderedInterval (-36128627883 / 1000000000000) (-36128627877 / 1000000000000)))) (orderedInterval (-10440578242 / 1000000000000) (-10440575045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (68349877660713 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85038871850 / 1000000000000) (-85038871848 / 1000000000000), orderedInterval (-14320436018 / 1000000000000) (-14320436015 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (183597385602261 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (498502616687937 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30465642956 / 1000000000000) (30465670479 / 1000000000000), orderedInterval (-9693725632 / 1000000000000) (-9693698110 / 1000000000000)))) (orderedInterval (5798135907 / 1000000000000) (5798140798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (367194771204681 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33292427793 / 1000000000000) (33292427794 / 1000000000000), orderedInterval (16655188898 / 1000000000000) (16655188899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (629194499093613 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27099674718 / 1000000000000) (27099733603 / 1000000000000), orderedInterval (-8680215780 / 1000000000000) (-8680156896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (463461820266567 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29270512668 / 1000000000000) (29270623240 / 1000000000000), orderedInterval (-15585792591 / 1000000000000) (-15585682020 / 1000000000000)))) (orderedInterval (1769715787 / 1000000000000) (1769728662 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_chunkChecks2_1 :
    compactCertificate526.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (711069616844841 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14024011762 / 1000000000000) (-14024011761 / 1000000000000), orderedInterval (-22786105478 / 1000000000000) (-22786105477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (410536234697889 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33595513889 / 1000000000000) (-33595497954 / 1000000000000), orderedInterval (10611188497 / 1000000000000) (10611204432 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (728503752694101 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9142889616 / 1000000000000) (9142889617 / 1000000000000), orderedInterval (24804374568 / 1000000000000) (24804374569 / 1000000000000)))) (orderedInterval (-15177707383 / 1000000000000) (-15177704710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (680662704788169 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6555831085 / 1000000000000) (-6555831084 / 1000000000000), orderedInterval (-26552811835 / 1000000000000) (-26552811834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (485753023665177 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32280837796 / 1000000000000) (-32280835287 / 1000000000000), orderedInterval (2559135270 / 1000000000000) (2559137779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (550792156806783 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29012321275 / 1000000000000) (-29012321246 / 1000000000000), orderedInterval (-9086379992 / 1000000000000) (-9086379962 / 1000000000000)))) (orderedInterval (6136253904 / 1000000000000) (6136254587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (459193077376527 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4479942216 / 1000000000000) (4479942218 / 1000000000000), orderedInterval (-33004522495 / 1000000000000) (-33004522493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (405711009791067 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30080601001 / 1000000000000) (-30080512068 / 1000000000000), orderedInterval (18750629392 / 1000000000000) (18750718324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (117590863983633 / 160000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16507538738 / 1000000000000) (16507538739 / 1000000000000), orderedInterval (24355096345 / 1000000000000) (24355096346 / 1000000000000)))) (orderedInterval (-4352766685 / 1000000000000) (-4352758303 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_chunkChecks2_2 :
    compactCertificate526.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (325262518246851 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34201514736 / 1000000000000) (-34201441649 / 1000000000000), orderedInterval (19943216356 / 1000000000000) (19943289443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (275728638901611 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5544017003 / 1000000000000) (-5544016996 / 1000000000000), orderedInterval (42626776867 / 1000000000000) (42626776874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (172538179733433 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16695454294 / 1000000000000) (16695454567 / 1000000000000), orderedInterval (-51740295712 / 1000000000000) (-51740295439 / 1000000000000)))) (orderedInterval (-6101349983 / 1000000000000) (-6101337636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (92791606896711 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-37765122346 / 1000000000000) (-37765122345 / 1000000000000), orderedInterval (-63574307594 / 1000000000000) (-63574307593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (251947263263133 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44957667570 / 1000000000000) (44957667704 / 1000000000000), orderedInterval (422340145 / 1000000000000) (422340278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (344012448351741 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15071177521 / 1000000000000) (-15071177520 / 1000000000000), orderedInterval (-35384705157 / 1000000000000) (-35384705156 / 1000000000000)))) (orderedInterval (-779088908 / 1000000000000) (-779088863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (145461820266567 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23021175501 / 1000000000000) (23021175502 / 1000000000000), orderedInterval (54446037220 / 1000000000000) (54446037221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (591294223584807 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29299072429 / 1000000000000) (-29299068267 / 1000000000000), orderedInterval (1719267837 / 1000000000000) (1719271999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (394957138377513 / 800000000000) 2 (IntervalRat.scale (795 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34094797114 / 1000000000000) (-34094797109 / 1000000000000), orderedInterval (-11236703374 / 1000000000000) (-11236703369 / 1000000000000)))) (orderedInterval (-18149275595 / 1000000000000) (-18149274192 / 1000000000000))) = true
  rfl'

theorem compactCertificate526_chunkChecks2 :
    compactCertificate526.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate526.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate526_chunkChecks2_0
    compactCertificate526_chunkChecks2_1 compactCertificate526_chunkChecks2_2

theorem compactCertificate526_chunkChecks3_0 :
    compactCertificate526.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (795 / 2) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25694928598 / 1000000000000) (25694936551 / 1000000000000), orderedInterval (-30713423440 / 1000000000000) (-30713415487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (234237360716259 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46053800920 / 1000000000000) (-46053800907 / 1000000000000), orderedInterval (-7223188320 / 1000000000000) (-7223188307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (75747549745347 / 160000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (6318546012 / 1000000000000) (6318546017 / 1000000000000), orderedInterval (-36128627883 / 1000000000000) (-36128627877 / 1000000000000)))) (orderedInterval (15808454894 / 1000000000000) (15808458097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (68349877660713 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85038871850 / 1000000000000) (-85038871848 / 1000000000000), orderedInterval (-14320436018 / 1000000000000) (-14320436015 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (183597385602261 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (498502616687937 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30465642956 / 1000000000000) (30465670479 / 1000000000000), orderedInterval (-9693725632 / 1000000000000) (-9693698110 / 1000000000000)))) (orderedInterval (-2454816766 / 1000000000000) (-2454809104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (367194771204681 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33292427793 / 1000000000000) (33292427794 / 1000000000000), orderedInterval (16655188898 / 1000000000000) (16655188899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (629194499093613 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27099674718 / 1000000000000) (27099733603 / 1000000000000), orderedInterval (-8680215780 / 1000000000000) (-8680156896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (463461820266567 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29270512668 / 1000000000000) (29270623240 / 1000000000000), orderedInterval (-15585792591 / 1000000000000) (-15585682020 / 1000000000000)))) (orderedInterval (-912211515 / 1000000000000) (-912189016 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate526_chunkChecks3_1 :
    compactCertificate526.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (711069616844841 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14024011762 / 1000000000000) (-14024011761 / 1000000000000), orderedInterval (-22786105478 / 1000000000000) (-22786105477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (410536234697889 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33595513889 / 1000000000000) (-33595497954 / 1000000000000), orderedInterval (10611188497 / 1000000000000) (10611204432 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (728503752694101 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9142889616 / 1000000000000) (9142889617 / 1000000000000), orderedInterval (24804374568 / 1000000000000) (24804374569 / 1000000000000)))) (orderedInterval (-89314749841 / 1000000000000) (-89314745758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (680662704788169 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6555831085 / 1000000000000) (-6555831084 / 1000000000000), orderedInterval (-26552811835 / 1000000000000) (-26552811834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (485753023665177 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32280837796 / 1000000000000) (-32280835287 / 1000000000000), orderedInterval (2559135270 / 1000000000000) (2559137779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (550792156806783 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29012321275 / 1000000000000) (-29012321246 / 1000000000000), orderedInterval (-9086379992 / 1000000000000) (-9086379962 / 1000000000000)))) (orderedInterval (-5817750344 / 1000000000000) (-5817749280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (459193077376527 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4479942216 / 1000000000000) (4479942218 / 1000000000000), orderedInterval (-33004522495 / 1000000000000) (-33004522493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (405711009791067 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30080601001 / 1000000000000) (-30080512068 / 1000000000000), orderedInterval (18750629392 / 1000000000000) (18750718324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (117590863983633 / 160000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16507538738 / 1000000000000) (16507538739 / 1000000000000), orderedInterval (24355096345 / 1000000000000) (24355096346 / 1000000000000)))) (orderedInterval (-554513440 / 1000000000000) (-554502724 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate526_chunkChecks3_2 :
    compactCertificate526.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (325262518246851 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34201514736 / 1000000000000) (-34201441649 / 1000000000000), orderedInterval (19943216356 / 1000000000000) (19943289443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (275728638901611 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5544017003 / 1000000000000) (-5544016996 / 1000000000000), orderedInterval (42626776867 / 1000000000000) (42626776874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (172538179733433 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16695454294 / 1000000000000) (16695454567 / 1000000000000), orderedInterval (-51740295712 / 1000000000000) (-51740295439 / 1000000000000)))) (orderedInterval (5269389293 / 1000000000000) (5269401916 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (92791606896711 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-37765122346 / 1000000000000) (-37765122345 / 1000000000000), orderedInterval (-63574307594 / 1000000000000) (-63574307593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (251947263263133 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44957667570 / 1000000000000) (44957667704 / 1000000000000), orderedInterval (422340145 / 1000000000000) (422340278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (344012448351741 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15071177521 / 1000000000000) (-15071177520 / 1000000000000), orderedInterval (-35384705157 / 1000000000000) (-35384705156 / 1000000000000)))) (orderedInterval (-3455673075 / 1000000000000) (-3455673029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (145461820266567 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23021175501 / 1000000000000) (23021175502 / 1000000000000), orderedInterval (54446037220 / 1000000000000) (54446037221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (591294223584807 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29299072429 / 1000000000000) (-29299068267 / 1000000000000), orderedInterval (1719267837 / 1000000000000) (1719271999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (394957138377513 / 800000000000) 3 (IntervalRat.scale (795 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34094797114 / 1000000000000) (-34094797109 / 1000000000000), orderedInterval (-11236703374 / 1000000000000) (-11236703369 / 1000000000000)))) (orderedInterval (-3125279965 / 1000000000000) (-3125277430 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate526_chunkChecks3 :
    compactCertificate526.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate526.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate526_chunkChecks3_0
    compactCertificate526_chunkChecks3_1 compactCertificate526_chunkChecks3_2

theorem compactCertificate526_chunkChecks4_0 :
    compactCertificate526.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (795 / 2) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25694928598 / 1000000000000) (25694936551 / 1000000000000), orderedInterval (-30713423440 / 1000000000000) (-30713415487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (234237360716259 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46053800920 / 1000000000000) (-46053800907 / 1000000000000), orderedInterval (-7223188320 / 1000000000000) (-7223188307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (75747549745347 / 160000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (6318546012 / 1000000000000) (6318546017 / 1000000000000), orderedInterval (-36128627883 / 1000000000000) (-36128627877 / 1000000000000)))) (orderedInterval (10724673818 / 1000000000000) (10724677036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (68349877660713 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-85038871850 / 1000000000000) (-85038871848 / 1000000000000), orderedInterval (-14320436018 / 1000000000000) (-14320436015 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (183597385602261 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42697616589 / 1000000000000) (-42697616588 / 1000000000000), orderedInterval (-30743534348 / 1000000000000) (-30743534347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (498502616687937 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30465642956 / 1000000000000) (30465670479 / 1000000000000), orderedInterval (-9693725632 / 1000000000000) (-9693698110 / 1000000000000)))) (orderedInterval (-13237976137 / 1000000000000) (-13237964110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (367194771204681 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33292427793 / 1000000000000) (33292427794 / 1000000000000), orderedInterval (16655188898 / 1000000000000) (16655188899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (629194499093613 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27099674718 / 1000000000000) (27099733603 / 1000000000000), orderedInterval (-8680215780 / 1000000000000) (-8680156896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (463461820266567 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29270512668 / 1000000000000) (29270623240 / 1000000000000), orderedInterval (-15585792591 / 1000000000000) (-15585682020 / 1000000000000)))) (orderedInterval (-9614247251 / 1000000000000) (-9614207014 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate526_chunkChecks4_1 :
    compactCertificate526.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (711069616844841 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14024011762 / 1000000000000) (-14024011761 / 1000000000000), orderedInterval (-22786105478 / 1000000000000) (-22786105477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (410536234697889 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33595513889 / 1000000000000) (-33595497954 / 1000000000000), orderedInterval (10611188497 / 1000000000000) (10611204432 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (728503752694101 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9142889616 / 1000000000000) (9142889617 / 1000000000000), orderedInterval (24804374568 / 1000000000000) (24804374569 / 1000000000000)))) (orderedInterval (91631096495 / 1000000000000) (91631103201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (680662704788169 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-6555831085 / 1000000000000) (-6555831084 / 1000000000000), orderedInterval (-26552811835 / 1000000000000) (-26552811834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (485753023665177 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32280837796 / 1000000000000) (-32280835287 / 1000000000000), orderedInterval (2559135270 / 1000000000000) (2559137779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (550792156806783 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29012321275 / 1000000000000) (-29012321246 / 1000000000000), orderedInterval (-9086379992 / 1000000000000) (-9086379962 / 1000000000000)))) (orderedInterval (-12784589412 / 1000000000000) (-12784587740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (459193077376527 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (4479942216 / 1000000000000) (4479942218 / 1000000000000), orderedInterval (-33004522495 / 1000000000000) (-33004522493 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (405711009791067 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30080601001 / 1000000000000) (-30080512068 / 1000000000000), orderedInterval (18750629392 / 1000000000000) (18750718324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (117590863983633 / 160000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16507538738 / 1000000000000) (16507538739 / 1000000000000), orderedInterval (24355096345 / 1000000000000) (24355096346 / 1000000000000)))) (orderedInterval (9727686661 / 1000000000000) (9727700398 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate526_chunkChecks4_2 :
    compactCertificate526.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (325262518246851 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34201514736 / 1000000000000) (-34201441649 / 1000000000000), orderedInterval (19943216356 / 1000000000000) (19943289443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (275728638901611 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-5544017003 / 1000000000000) (-5544016996 / 1000000000000), orderedInterval (42626776867 / 1000000000000) (42626776874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (172538179733433 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16695454294 / 1000000000000) (16695454567 / 1000000000000), orderedInterval (-51740295712 / 1000000000000) (-51740295439 / 1000000000000)))) (orderedInterval (6183407018 / 1000000000000) (6183419956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (92791606896711 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-37765122346 / 1000000000000) (-37765122345 / 1000000000000), orderedInterval (-63574307594 / 1000000000000) (-63574307593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (251947263263133 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44957667570 / 1000000000000) (44957667704 / 1000000000000), orderedInterval (422340145 / 1000000000000) (422340278 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (344012448351741 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15071177521 / 1000000000000) (-15071177520 / 1000000000000), orderedInterval (-35384705157 / 1000000000000) (-35384705156 / 1000000000000)))) (orderedInterval (1202466253 / 1000000000000) (1202466301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (145461820266567 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (23021175501 / 1000000000000) (23021175502 / 1000000000000), orderedInterval (54446037220 / 1000000000000) (54446037221 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (591294223584807 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29299072429 / 1000000000000) (-29299068267 / 1000000000000), orderedInterval (1719267837 / 1000000000000) (1719271999 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (394957138377513 / 800000000000) 4 (IntervalRat.scale (795 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-34094797114 / 1000000000000) (-34094797109 / 1000000000000), orderedInterval (-11236703374 / 1000000000000) (-11236703369 / 1000000000000)))) (orderedInterval (43753529395 / 1000000000000) (43753534024 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate526_chunkChecks4 :
    compactCertificate526.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate526.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate526_chunkChecks4_0
    compactCertificate526_chunkChecks4_1 compactCertificate526_chunkChecks4_2

theorem compactCertificate526_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate526.chunkCheck r b = true :=
  compactCertificate526.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate526_chunkChecks0
    · exact compactCertificate526_chunkChecks1
    · exact compactCertificate526_chunkChecks2
    · exact compactCertificate526_chunkChecks3
    · exact compactCertificate526_chunkChecks4)

theorem compactCertificate526_coefficient0 :
    compactCertificate526.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate526_coefficient1 :
    compactCertificate526.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate526_coefficient2 :
    compactCertificate526.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate526_coefficient3 :
    compactCertificate526.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate526_coefficient4 :
    compactCertificate526.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate526_coefficients : ∀ r : Fin 5,
    compactCertificate526.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate526_coefficient0
  · exact compactCertificate526_coefficient1
  · exact compactCertificate526_coefficient2
  · exact compactCertificate526_coefficient3
  · exact compactCertificate526_coefficient4

theorem compactCertificate526_lower : (1 : ℚ) ≤ compactCertificate526.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate526, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate526_proves {t : ℝ} (ht : t ∈ compactCertificate526.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate526.proves compactCertificate526_states compactCertificate526_chunks
    compactCertificate526_coefficients compactCertificate526_lower ht

end Erdos232
