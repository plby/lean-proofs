/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate346 : CompactCertificate where
  left := 217
  right := 218
  center := 435 / 2
  grid := fun i =>
    match i.val with
    | 0 => 69
    | 1 => 51
    | 2 => 82
    | 3 => 15
    | 4 => 40
    | 5 => 109
    | 6 => 80
    | 7 => 137
    | 8 => 101
    | 9 => 155
    | 10 => 89
    | 11 => 159
    | 12 => 148
    | 13 => 106
    | 14 => 120
    | 15 => 100
    | 16 => 88
    | 17 => 128
    | 18 => 71
    | 19 => 60
    | 20 => 38
    | 21 => 20
    | 22 => 55
    | 23 => 75
    | 24 => 32
    | 25 => 129
    | _ => 86
  point := fun i =>
    match i.val with
    | 0 => 435 / 2
    | 1 => 128167612467387 / 800000000000
    | 2 => 41446772502171 / 160000000000
    | 3 => 37398989663409 / 800000000000
    | 4 => 100458946838973 / 800000000000
    | 5 => 272765582716041 / 800000000000
    | 6 => 200917893678033 / 800000000000
    | 7 => 344276235353109 / 800000000000
    | 8 => 253592316749631 / 800000000000
    | 9 => 389075828084913 / 800000000000
    | 10 => 224633034079977 / 800000000000
    | 11 => 398615260908093 / 800000000000
    | 12 => 372438083752017 / 800000000000
    | 13 => 265789390307361 / 800000000000
    | 14 => 301376840516919 / 800000000000
    | 15 => 251256589507911 / 800000000000
    | 16 => 221992816678131 / 800000000000
    | 17 => 64342170858969 / 160000000000
    | 18 => 177973830738843 / 800000000000
    | 19 => 150870387323523 / 800000000000
    | 20 => 94407683250369 / 800000000000
    | 21 => 50772766037823 / 800000000000
    | 22 => 137857936502469 / 800000000000
    | 23 => 188233226456613 / 800000000000
    | 24 => 79592316749631 / 800000000000
    | 25 => 323538348753951 / 800000000000
    | _ => 216108622885809 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-54017164906 / 1000000000000) (-54017164872 / 1000000000000), orderedInterval (-2896695805 / 1000000000000) (-2896695771 / 1000000000000))
    | 1 => (orderedInterval (-44013632252 / 1000000000000) (-44013632251 / 1000000000000), orderedInterval (-44989912240 / 1000000000000) (-44989912239 / 1000000000000))
    | 2 => (orderedInterval (39589204061 / 1000000000000) (39589310180 / 1000000000000), orderedInterval (-29914010212 / 1000000000000) (-29913904093 / 1000000000000))
    | 3 => (orderedInterval (-46254731921 / 1000000000000) (-46254731920 / 1000000000000), orderedInterval (-106645139724 / 1000000000000) (-106645139723 / 1000000000000))
    | 4 => (orderedInterval (45562486177 / 1000000000000) (45562486178 / 1000000000000), orderedInterval (54533831316 / 1000000000000) (54533831317 / 1000000000000))
    | 5 => (orderedInterval (27558061971 / 1000000000000) (27558071998 / 1000000000000), orderedInterval (-33322680602 / 1000000000000) (-33322670575 / 1000000000000))
    | 6 => (orderedInterval (28629583588 / 1000000000000) (28629583589 / 1000000000000), orderedInterval (41357905936 / 1000000000000) (41357905937 / 1000000000000))
    | 7 => (orderedInterval (-25712342297 / 1000000000000) (-25712342296 / 1000000000000), orderedInterval (-28574299556 / 1000000000000) (-28574299555 / 1000000000000))
    | 8 => (orderedInterval (-20477043574 / 1000000000000) (-20477043573 / 1000000000000), orderedInterval (-39830180194 / 1000000000000) (-39830180193 / 1000000000000))
    | 9 => (orderedInterval (-6586346156 / 1000000000000) (-6586346155 / 1000000000000), orderedInterval (-35568631415 / 1000000000000) (-35568631414 / 1000000000000))
    | 10 => (orderedInterval (-43787776083 / 1000000000000) (-43787762830 / 1000000000000), orderedInterval (18782602869 / 1000000000000) (18782616123 / 1000000000000))
    | 11 => (orderedInterval (15836892875 / 1000000000000) (15836893161 / 1000000000000), orderedInterval (-32060483282 / 1000000000000) (-32060482995 / 1000000000000))
    | 12 => (orderedInterval (36287141836 / 1000000000000) (36287141864 / 1000000000000), orderedInterval (7081912167 / 1000000000000) (7081912196 / 1000000000000))
    | 13 => (orderedInterval (566355139 / 1000000000000) (566355140 / 1000000000000), orderedInterval (43769508587 / 1000000000000) (43769508589 / 1000000000000))
    | 14 => (orderedInterval (20247238207 / 1000000000000) (20247238208 / 1000000000000), orderedInterval (35749475516 / 1000000000000) (35749475517 / 1000000000000))
    | 15 => (orderedInterval (28882376303 / 1000000000000) (28882376304 / 1000000000000), orderedInterval (34491009211 / 1000000000000) (34491009212 / 1000000000000))
    | 16 => (orderedInterval (46467190205 / 1000000000000) (46467192707 / 1000000000000), orderedInterval (-11702522064 / 1000000000000) (-11702519562 / 1000000000000))
    | 17 => (orderedInterval (28536490474 / 1000000000000) (28536490475 / 1000000000000), orderedInterval (27690937354 / 1000000000000) (27690937355 / 1000000000000))
    | 18 => (orderedInterval (-10577645576 / 1000000000000) (-10577645575 / 1000000000000), orderedInterval (-52414316311 / 1000000000000) (-52414316310 / 1000000000000))
    | 19 => (orderedInterval (44675260093 / 1000000000000) (44675260094 / 1000000000000), orderedInterval (37027705242 / 1000000000000) (37027705243 / 1000000000000))
    | 20 => (orderedInterval (-40654460558 / 1000000000000) (-40654449768 / 1000000000000), orderedInterval (61343131568 / 1000000000000) (61343142358 / 1000000000000))
    | 21 => (orderedInterval (98978785879 / 1000000000000) (98978785881 / 1000000000000), orderedInterval (14510432936 / 1000000000000) (14510432938 / 1000000000000))
    | 22 => (orderedInterval (-19090692296 / 1000000000000) (-19090692295 / 1000000000000), orderedInterval (-57649984717 / 1000000000000) (-57649984716 / 1000000000000))
    | 23 => (orderedInterval (-22950156851 / 1000000000000) (-22950156850 / 1000000000000), orderedInterval (-46630538477 / 1000000000000) (-46630538476 / 1000000000000))
    | 24 => (orderedInterval (-20288071989 / 1000000000000) (-20288071708 / 1000000000000), orderedInterval (77479414156 / 1000000000000) (77479414437 / 1000000000000))
    | 25 => (orderedInterval (2277202138 / 1000000000000) (2277202140 / 1000000000000), orderedInterval (-39612904182 / 1000000000000) (-39612904180 / 1000000000000))
    | _ => (orderedInterval (32867673518 / 1000000000000) (32867673519 / 1000000000000), orderedInterval (35665657055 / 1000000000000) (35665657056 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-19497495238 / 1000000000000) (-19497488981 / 1000000000000)
      | 1 => orderedInterval (206303511 / 1000000000000) (206304250 / 1000000000000)
      | 2 => orderedInterval (298181763 / 1000000000000) (298181776 / 1000000000000)
      | 3 => orderedInterval (177307900 / 1000000000000) (177309009 / 1000000000000)
      | 4 => orderedInterval (-704001429 / 1000000000000) (-704001401 / 1000000000000)
      | 5 => orderedInterval (-1594992013 / 1000000000000) (-1594991849 / 1000000000000)
      | 6 => orderedInterval (-2160849182 / 1000000000000) (-2160848776 / 1000000000000)
      | 7 => orderedInterval (364327114 / 1000000000000) (364327141 / 1000000000000)
      | _ => orderedInterval (-6474518917 / 1000000000000) (-6474518854 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-3547609404 / 1000000000000) (-3547601956 / 1000000000000)
      | 1 => orderedInterval (5111789528 / 1000000000000) (5111790675 / 1000000000000)
      | 2 => orderedInterval (340885883 / 1000000000000) (340885905 / 1000000000000)
      | 3 => orderedInterval (5487864374 / 1000000000000) (5487865915 / 1000000000000)
      | 4 => orderedInterval (5735373789 / 1000000000000) (5735373833 / 1000000000000)
      | 5 => orderedInterval (2740420140 / 1000000000000) (2740420353 / 1000000000000)
      | 6 => orderedInterval (7838413518 / 1000000000000) (7838413759 / 1000000000000)
      | 7 => orderedInterval (4824088604 / 1000000000000) (4824088628 / 1000000000000)
      | _ => orderedInterval (-2101818258 / 1000000000000) (-2101818172 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (18354010998 / 1000000000000) (18354019899 / 1000000000000)
      | 1 => orderedInterval (4213119618 / 1000000000000) (4213121417 / 1000000000000)
      | 2 => orderedInterval (-2055134441 / 1000000000000) (-2055134402 / 1000000000000)
      | 3 => orderedInterval (-12284899443 / 1000000000000) (-12284897202 / 1000000000000)
      | 4 => orderedInterval (3157385037 / 1000000000000) (3157385109 / 1000000000000)
      | 5 => orderedInterval (1122621874 / 1000000000000) (1122622153 / 1000000000000)
      | 6 => orderedInterval (485212257 / 1000000000000) (485212410 / 1000000000000)
      | 7 => orderedInterval (-2196828057 / 1000000000000) (-2196828033 / 1000000000000)
      | _ => orderedInterval (10188963194 / 1000000000000) (10188963321 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (4196786596 / 1000000000000) (4196797194 / 1000000000000)
      | 1 => orderedInterval (-9539665359 / 1000000000000) (-9539662543 / 1000000000000)
      | 2 => orderedInterval (-3837398991 / 1000000000000) (-3837398921 / 1000000000000)
      | 3 => orderedInterval (-18802766556 / 1000000000000) (-18802763102 / 1000000000000)
      | 4 => orderedInterval (-12572801532 / 1000000000000) (-12572801407 / 1000000000000)
      | 5 => orderedInterval (-7076280571 / 1000000000000) (-7076280203 / 1000000000000)
      | 6 => orderedInterval (-7922927381 / 1000000000000) (-7922927277 / 1000000000000)
      | 7 => orderedInterval (-5157997899 / 1000000000000) (-5157997875 / 1000000000000)
      | _ => orderedInterval (-8000895942 / 1000000000000) (-8000895747 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16895100155 / 1000000000000) (-16895087489 / 1000000000000)
      | 1 => orderedInterval (-11557142186 / 1000000000000) (-11557137761 / 1000000000000)
      | 2 => orderedInterval (9957092266 / 1000000000000) (9957092394 / 1000000000000)
      | 3 => orderedInterval (82427339522 / 1000000000000) (82427345261 / 1000000000000)
      | 4 => orderedInterval (-14265562908 / 1000000000000) (-14265562691 / 1000000000000)
      | 5 => orderedInterval (3008171354 / 1000000000000) (3008171847 / 1000000000000)
      | 6 => orderedInterval (380096604 / 1000000000000) (380096682 / 1000000000000)
      | 7 => orderedInterval (2613713548 / 1000000000000) (2613713574 / 1000000000000)
      | _ => orderedInterval (-16821629120 / 1000000000000) (-16821628808 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-29385736491 / 1000000000000) (-29385727685 / 1000000000000)
    | 1 => orderedInterval (26429408174 / 1000000000000) (26429418940 / 1000000000000)
    | 2 => orderedInterval (20984451037 / 1000000000000) (20984464672 / 1000000000000)
    | 3 => orderedInterval (-68713947635 / 1000000000000) (-68713929881 / 1000000000000)
    | _ => orderedInterval (38846978925 / 1000000000000) (38847003009 / 1000000000000)

theorem compactCertificate346_stateChecks0 :
    compactCertificate346.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (435 / 2)) (orderedInterval (-54017164906 / 1000000000000) (-54017164872 / 1000000000000), orderedInterval (-2896695805 / 1000000000000) (-2896695771 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (128167612467387 / 800000000000)) (orderedInterval (-44013632252 / 1000000000000) (-44013632251 / 1000000000000), orderedInterval (-44989912240 / 1000000000000) (-44989912239 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (41446772502171 / 160000000000)) (orderedInterval (39589204061 / 1000000000000) (39589310180 / 1000000000000), orderedInterval (-29914010212 / 1000000000000) (-29913904093 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_stateChecks1 :
    compactCertificate346.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (37398989663409 / 800000000000)) (orderedInterval (-46254731921 / 1000000000000) (-46254731920 / 1000000000000), orderedInterval (-106645139724 / 1000000000000) (-106645139723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (100458946838973 / 800000000000)) (orderedInterval (45562486177 / 1000000000000) (45562486178 / 1000000000000), orderedInterval (54533831316 / 1000000000000) (54533831317 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (272765582716041 / 800000000000)) (orderedInterval (27558061971 / 1000000000000) (27558071998 / 1000000000000), orderedInterval (-33322680602 / 1000000000000) (-33322670575 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_stateChecks2 :
    compactCertificate346.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (200917893678033 / 800000000000)) (orderedInterval (28629583588 / 1000000000000) (28629583589 / 1000000000000), orderedInterval (41357905936 / 1000000000000) (41357905937 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (344276235353109 / 800000000000)) (orderedInterval (-25712342297 / 1000000000000) (-25712342296 / 1000000000000), orderedInterval (-28574299556 / 1000000000000) (-28574299555 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (253592316749631 / 800000000000)) (orderedInterval (-20477043574 / 1000000000000) (-20477043573 / 1000000000000), orderedInterval (-39830180194 / 1000000000000) (-39830180193 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_stateChecks3 :
    compactCertificate346.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (389075828084913 / 800000000000)) (orderedInterval (-6586346156 / 1000000000000) (-6586346155 / 1000000000000), orderedInterval (-35568631415 / 1000000000000) (-35568631414 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (224633034079977 / 800000000000)) (orderedInterval (-43787776083 / 1000000000000) (-43787762830 / 1000000000000), orderedInterval (18782602869 / 1000000000000) (18782616123 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (398615260908093 / 800000000000)) (orderedInterval (15836892875 / 1000000000000) (15836893161 / 1000000000000), orderedInterval (-32060483282 / 1000000000000) (-32060482995 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_stateChecks4 :
    compactCertificate346.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (372438083752017 / 800000000000)) (orderedInterval (36287141836 / 1000000000000) (36287141864 / 1000000000000), orderedInterval (7081912167 / 1000000000000) (7081912196 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (265789390307361 / 800000000000)) (orderedInterval (566355139 / 1000000000000) (566355140 / 1000000000000), orderedInterval (43769508587 / 1000000000000) (43769508589 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (301376840516919 / 800000000000)) (orderedInterval (20247238207 / 1000000000000) (20247238208 / 1000000000000), orderedInterval (35749475516 / 1000000000000) (35749475517 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_stateChecks5 :
    compactCertificate346.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (251256589507911 / 800000000000)) (orderedInterval (28882376303 / 1000000000000) (28882376304 / 1000000000000), orderedInterval (34491009211 / 1000000000000) (34491009212 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (221992816678131 / 800000000000)) (orderedInterval (46467190205 / 1000000000000) (46467192707 / 1000000000000), orderedInterval (-11702522064 / 1000000000000) (-11702519562 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (64342170858969 / 160000000000)) (orderedInterval (28536490474 / 1000000000000) (28536490475 / 1000000000000), orderedInterval (27690937354 / 1000000000000) (27690937355 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_stateChecks6 :
    compactCertificate346.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (177973830738843 / 800000000000)) (orderedInterval (-10577645576 / 1000000000000) (-10577645575 / 1000000000000), orderedInterval (-52414316311 / 1000000000000) (-52414316310 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (150870387323523 / 800000000000)) (orderedInterval (44675260093 / 1000000000000) (44675260094 / 1000000000000), orderedInterval (37027705242 / 1000000000000) (37027705243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (94407683250369 / 800000000000)) (orderedInterval (-40654460558 / 1000000000000) (-40654449768 / 1000000000000), orderedInterval (61343131568 / 1000000000000) (61343142358 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_stateChecks7 :
    compactCertificate346.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (50772766037823 / 800000000000)) (orderedInterval (98978785879 / 1000000000000) (98978785881 / 1000000000000), orderedInterval (14510432936 / 1000000000000) (14510432938 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (137857936502469 / 800000000000)) (orderedInterval (-19090692296 / 1000000000000) (-19090692295 / 1000000000000), orderedInterval (-57649984717 / 1000000000000) (-57649984716 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (188233226456613 / 800000000000)) (orderedInterval (-22950156851 / 1000000000000) (-22950156850 / 1000000000000), orderedInterval (-46630538477 / 1000000000000) (-46630538476 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_stateChecks8 :
    compactCertificate346.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (79592316749631 / 800000000000)) (orderedInterval (-20288071989 / 1000000000000) (-20288071708 / 1000000000000), orderedInterval (77479414156 / 1000000000000) (77479414437 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (323538348753951 / 800000000000)) (orderedInterval (2277202138 / 1000000000000) (2277202140 / 1000000000000), orderedInterval (-39612904182 / 1000000000000) (-39612904180 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (216108622885809 / 800000000000)) (orderedInterval (32867673518 / 1000000000000) (32867673519 / 1000000000000), orderedInterval (35665657055 / 1000000000000) (35665657056 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_states : ∀ j,
    BesselStateValid (compactCertificate346.point j) (compactCertificate346.state j) :=
  compactCertificate346.statesValid_of_checks3 compactCertificate346_stateChecks0
    compactCertificate346_stateChecks1 compactCertificate346_stateChecks2
    compactCertificate346_stateChecks3 compactCertificate346_stateChecks4
    compactCertificate346_stateChecks5 compactCertificate346_stateChecks6
    compactCertificate346_stateChecks7 compactCertificate346_stateChecks8

theorem compactCertificate346_chunkChecks0_0 :
    compactCertificate346.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (435 / 2) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54017164906 / 1000000000000) (-54017164872 / 1000000000000), orderedInterval (-2896695805 / 1000000000000) (-2896695771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (128167612467387 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44013632252 / 1000000000000) (-44013632251 / 1000000000000), orderedInterval (-44989912240 / 1000000000000) (-44989912239 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (41446772502171 / 160000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39589204061 / 1000000000000) (39589310180 / 1000000000000), orderedInterval (-29914010212 / 1000000000000) (-29913904093 / 1000000000000)))) (orderedInterval (-19497495238 / 1000000000000) (-19497488981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (37398989663409 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-46254731921 / 1000000000000) (-46254731920 / 1000000000000), orderedInterval (-106645139724 / 1000000000000) (-106645139723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (100458946838973 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (45562486177 / 1000000000000) (45562486178 / 1000000000000), orderedInterval (54533831316 / 1000000000000) (54533831317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (272765582716041 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27558061971 / 1000000000000) (27558071998 / 1000000000000), orderedInterval (-33322680602 / 1000000000000) (-33322670575 / 1000000000000)))) (orderedInterval (206303511 / 1000000000000) (206304250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (200917893678033 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28629583588 / 1000000000000) (28629583589 / 1000000000000), orderedInterval (41357905936 / 1000000000000) (41357905937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (344276235353109 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25712342297 / 1000000000000) (-25712342296 / 1000000000000), orderedInterval (-28574299556 / 1000000000000) (-28574299555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (253592316749631 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20477043574 / 1000000000000) (-20477043573 / 1000000000000), orderedInterval (-39830180194 / 1000000000000) (-39830180193 / 1000000000000)))) (orderedInterval (298181763 / 1000000000000) (298181776 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_chunkChecks0_1 :
    compactCertificate346.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (389075828084913 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6586346156 / 1000000000000) (-6586346155 / 1000000000000), orderedInterval (-35568631415 / 1000000000000) (-35568631414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (224633034079977 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-43787776083 / 1000000000000) (-43787762830 / 1000000000000), orderedInterval (18782602869 / 1000000000000) (18782616123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (398615260908093 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15836892875 / 1000000000000) (15836893161 / 1000000000000), orderedInterval (-32060483282 / 1000000000000) (-32060482995 / 1000000000000)))) (orderedInterval (177307900 / 1000000000000) (177309009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (372438083752017 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36287141836 / 1000000000000) (36287141864 / 1000000000000), orderedInterval (7081912167 / 1000000000000) (7081912196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (265789390307361 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (566355139 / 1000000000000) (566355140 / 1000000000000), orderedInterval (43769508587 / 1000000000000) (43769508589 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (301376840516919 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20247238207 / 1000000000000) (20247238208 / 1000000000000), orderedInterval (35749475516 / 1000000000000) (35749475517 / 1000000000000)))) (orderedInterval (-704001429 / 1000000000000) (-704001401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (251256589507911 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28882376303 / 1000000000000) (28882376304 / 1000000000000), orderedInterval (34491009211 / 1000000000000) (34491009212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (221992816678131 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46467190205 / 1000000000000) (46467192707 / 1000000000000), orderedInterval (-11702522064 / 1000000000000) (-11702519562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (64342170858969 / 160000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28536490474 / 1000000000000) (28536490475 / 1000000000000), orderedInterval (27690937354 / 1000000000000) (27690937355 / 1000000000000)))) (orderedInterval (-1594992013 / 1000000000000) (-1594991849 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_chunkChecks0_2 :
    compactCertificate346.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (177973830738843 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10577645576 / 1000000000000) (-10577645575 / 1000000000000), orderedInterval (-52414316311 / 1000000000000) (-52414316310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (150870387323523 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44675260093 / 1000000000000) (44675260094 / 1000000000000), orderedInterval (37027705242 / 1000000000000) (37027705243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (94407683250369 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40654460558 / 1000000000000) (-40654449768 / 1000000000000), orderedInterval (61343131568 / 1000000000000) (61343142358 / 1000000000000)))) (orderedInterval (-2160849182 / 1000000000000) (-2160848776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (50772766037823 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (98978785879 / 1000000000000) (98978785881 / 1000000000000), orderedInterval (14510432936 / 1000000000000) (14510432938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (137857936502469 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19090692296 / 1000000000000) (-19090692295 / 1000000000000), orderedInterval (-57649984717 / 1000000000000) (-57649984716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (188233226456613 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22950156851 / 1000000000000) (-22950156850 / 1000000000000), orderedInterval (-46630538477 / 1000000000000) (-46630538476 / 1000000000000)))) (orderedInterval (364327114 / 1000000000000) (364327141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (79592316749631 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20288071989 / 1000000000000) (-20288071708 / 1000000000000), orderedInterval (77479414156 / 1000000000000) (77479414437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (323538348753951 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2277202138 / 1000000000000) (2277202140 / 1000000000000), orderedInterval (-39612904182 / 1000000000000) (-39612904180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (216108622885809 / 800000000000) 0 (IntervalRat.scale (435 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32867673518 / 1000000000000) (32867673519 / 1000000000000), orderedInterval (35665657055 / 1000000000000) (35665657056 / 1000000000000)))) (orderedInterval (-6474518917 / 1000000000000) (-6474518854 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_chunkChecks0 :
    compactCertificate346.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate346.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate346_chunkChecks0_0
    compactCertificate346_chunkChecks0_1 compactCertificate346_chunkChecks0_2

theorem compactCertificate346_chunkChecks1_0 :
    compactCertificate346.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (435 / 2) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54017164906 / 1000000000000) (-54017164872 / 1000000000000), orderedInterval (-2896695805 / 1000000000000) (-2896695771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (128167612467387 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44013632252 / 1000000000000) (-44013632251 / 1000000000000), orderedInterval (-44989912240 / 1000000000000) (-44989912239 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (41446772502171 / 160000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39589204061 / 1000000000000) (39589310180 / 1000000000000), orderedInterval (-29914010212 / 1000000000000) (-29913904093 / 1000000000000)))) (orderedInterval (-3547609404 / 1000000000000) (-3547601956 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (37398989663409 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-46254731921 / 1000000000000) (-46254731920 / 1000000000000), orderedInterval (-106645139724 / 1000000000000) (-106645139723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (100458946838973 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (45562486177 / 1000000000000) (45562486178 / 1000000000000), orderedInterval (54533831316 / 1000000000000) (54533831317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (272765582716041 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27558061971 / 1000000000000) (27558071998 / 1000000000000), orderedInterval (-33322680602 / 1000000000000) (-33322670575 / 1000000000000)))) (orderedInterval (5111789528 / 1000000000000) (5111790675 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (200917893678033 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28629583588 / 1000000000000) (28629583589 / 1000000000000), orderedInterval (41357905936 / 1000000000000) (41357905937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (344276235353109 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25712342297 / 1000000000000) (-25712342296 / 1000000000000), orderedInterval (-28574299556 / 1000000000000) (-28574299555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (253592316749631 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20477043574 / 1000000000000) (-20477043573 / 1000000000000), orderedInterval (-39830180194 / 1000000000000) (-39830180193 / 1000000000000)))) (orderedInterval (340885883 / 1000000000000) (340885905 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_chunkChecks1_1 :
    compactCertificate346.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (389075828084913 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6586346156 / 1000000000000) (-6586346155 / 1000000000000), orderedInterval (-35568631415 / 1000000000000) (-35568631414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (224633034079977 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-43787776083 / 1000000000000) (-43787762830 / 1000000000000), orderedInterval (18782602869 / 1000000000000) (18782616123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (398615260908093 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15836892875 / 1000000000000) (15836893161 / 1000000000000), orderedInterval (-32060483282 / 1000000000000) (-32060482995 / 1000000000000)))) (orderedInterval (5487864374 / 1000000000000) (5487865915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (372438083752017 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36287141836 / 1000000000000) (36287141864 / 1000000000000), orderedInterval (7081912167 / 1000000000000) (7081912196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (265789390307361 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (566355139 / 1000000000000) (566355140 / 1000000000000), orderedInterval (43769508587 / 1000000000000) (43769508589 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (301376840516919 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20247238207 / 1000000000000) (20247238208 / 1000000000000), orderedInterval (35749475516 / 1000000000000) (35749475517 / 1000000000000)))) (orderedInterval (5735373789 / 1000000000000) (5735373833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (251256589507911 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28882376303 / 1000000000000) (28882376304 / 1000000000000), orderedInterval (34491009211 / 1000000000000) (34491009212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (221992816678131 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46467190205 / 1000000000000) (46467192707 / 1000000000000), orderedInterval (-11702522064 / 1000000000000) (-11702519562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (64342170858969 / 160000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28536490474 / 1000000000000) (28536490475 / 1000000000000), orderedInterval (27690937354 / 1000000000000) (27690937355 / 1000000000000)))) (orderedInterval (2740420140 / 1000000000000) (2740420353 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_chunkChecks1_2 :
    compactCertificate346.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (177973830738843 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10577645576 / 1000000000000) (-10577645575 / 1000000000000), orderedInterval (-52414316311 / 1000000000000) (-52414316310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (150870387323523 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44675260093 / 1000000000000) (44675260094 / 1000000000000), orderedInterval (37027705242 / 1000000000000) (37027705243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (94407683250369 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40654460558 / 1000000000000) (-40654449768 / 1000000000000), orderedInterval (61343131568 / 1000000000000) (61343142358 / 1000000000000)))) (orderedInterval (7838413518 / 1000000000000) (7838413759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (50772766037823 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (98978785879 / 1000000000000) (98978785881 / 1000000000000), orderedInterval (14510432936 / 1000000000000) (14510432938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (137857936502469 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19090692296 / 1000000000000) (-19090692295 / 1000000000000), orderedInterval (-57649984717 / 1000000000000) (-57649984716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (188233226456613 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22950156851 / 1000000000000) (-22950156850 / 1000000000000), orderedInterval (-46630538477 / 1000000000000) (-46630538476 / 1000000000000)))) (orderedInterval (4824088604 / 1000000000000) (4824088628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (79592316749631 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20288071989 / 1000000000000) (-20288071708 / 1000000000000), orderedInterval (77479414156 / 1000000000000) (77479414437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (323538348753951 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2277202138 / 1000000000000) (2277202140 / 1000000000000), orderedInterval (-39612904182 / 1000000000000) (-39612904180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (216108622885809 / 800000000000) 1 (IntervalRat.scale (435 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32867673518 / 1000000000000) (32867673519 / 1000000000000), orderedInterval (35665657055 / 1000000000000) (35665657056 / 1000000000000)))) (orderedInterval (-2101818258 / 1000000000000) (-2101818172 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_chunkChecks1 :
    compactCertificate346.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate346.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate346_chunkChecks1_0
    compactCertificate346_chunkChecks1_1 compactCertificate346_chunkChecks1_2

theorem compactCertificate346_chunkChecks2_0 :
    compactCertificate346.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (435 / 2) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54017164906 / 1000000000000) (-54017164872 / 1000000000000), orderedInterval (-2896695805 / 1000000000000) (-2896695771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (128167612467387 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44013632252 / 1000000000000) (-44013632251 / 1000000000000), orderedInterval (-44989912240 / 1000000000000) (-44989912239 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (41446772502171 / 160000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39589204061 / 1000000000000) (39589310180 / 1000000000000), orderedInterval (-29914010212 / 1000000000000) (-29913904093 / 1000000000000)))) (orderedInterval (18354010998 / 1000000000000) (18354019899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (37398989663409 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-46254731921 / 1000000000000) (-46254731920 / 1000000000000), orderedInterval (-106645139724 / 1000000000000) (-106645139723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (100458946838973 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (45562486177 / 1000000000000) (45562486178 / 1000000000000), orderedInterval (54533831316 / 1000000000000) (54533831317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (272765582716041 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27558061971 / 1000000000000) (27558071998 / 1000000000000), orderedInterval (-33322680602 / 1000000000000) (-33322670575 / 1000000000000)))) (orderedInterval (4213119618 / 1000000000000) (4213121417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (200917893678033 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28629583588 / 1000000000000) (28629583589 / 1000000000000), orderedInterval (41357905936 / 1000000000000) (41357905937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (344276235353109 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25712342297 / 1000000000000) (-25712342296 / 1000000000000), orderedInterval (-28574299556 / 1000000000000) (-28574299555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (253592316749631 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20477043574 / 1000000000000) (-20477043573 / 1000000000000), orderedInterval (-39830180194 / 1000000000000) (-39830180193 / 1000000000000)))) (orderedInterval (-2055134441 / 1000000000000) (-2055134402 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_chunkChecks2_1 :
    compactCertificate346.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (389075828084913 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6586346156 / 1000000000000) (-6586346155 / 1000000000000), orderedInterval (-35568631415 / 1000000000000) (-35568631414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (224633034079977 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-43787776083 / 1000000000000) (-43787762830 / 1000000000000), orderedInterval (18782602869 / 1000000000000) (18782616123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (398615260908093 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15836892875 / 1000000000000) (15836893161 / 1000000000000), orderedInterval (-32060483282 / 1000000000000) (-32060482995 / 1000000000000)))) (orderedInterval (-12284899443 / 1000000000000) (-12284897202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (372438083752017 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36287141836 / 1000000000000) (36287141864 / 1000000000000), orderedInterval (7081912167 / 1000000000000) (7081912196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (265789390307361 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (566355139 / 1000000000000) (566355140 / 1000000000000), orderedInterval (43769508587 / 1000000000000) (43769508589 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (301376840516919 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20247238207 / 1000000000000) (20247238208 / 1000000000000), orderedInterval (35749475516 / 1000000000000) (35749475517 / 1000000000000)))) (orderedInterval (3157385037 / 1000000000000) (3157385109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (251256589507911 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28882376303 / 1000000000000) (28882376304 / 1000000000000), orderedInterval (34491009211 / 1000000000000) (34491009212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (221992816678131 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46467190205 / 1000000000000) (46467192707 / 1000000000000), orderedInterval (-11702522064 / 1000000000000) (-11702519562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (64342170858969 / 160000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28536490474 / 1000000000000) (28536490475 / 1000000000000), orderedInterval (27690937354 / 1000000000000) (27690937355 / 1000000000000)))) (orderedInterval (1122621874 / 1000000000000) (1122622153 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_chunkChecks2_2 :
    compactCertificate346.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (177973830738843 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10577645576 / 1000000000000) (-10577645575 / 1000000000000), orderedInterval (-52414316311 / 1000000000000) (-52414316310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (150870387323523 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44675260093 / 1000000000000) (44675260094 / 1000000000000), orderedInterval (37027705242 / 1000000000000) (37027705243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (94407683250369 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40654460558 / 1000000000000) (-40654449768 / 1000000000000), orderedInterval (61343131568 / 1000000000000) (61343142358 / 1000000000000)))) (orderedInterval (485212257 / 1000000000000) (485212410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (50772766037823 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (98978785879 / 1000000000000) (98978785881 / 1000000000000), orderedInterval (14510432936 / 1000000000000) (14510432938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (137857936502469 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19090692296 / 1000000000000) (-19090692295 / 1000000000000), orderedInterval (-57649984717 / 1000000000000) (-57649984716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (188233226456613 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22950156851 / 1000000000000) (-22950156850 / 1000000000000), orderedInterval (-46630538477 / 1000000000000) (-46630538476 / 1000000000000)))) (orderedInterval (-2196828057 / 1000000000000) (-2196828033 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (79592316749631 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20288071989 / 1000000000000) (-20288071708 / 1000000000000), orderedInterval (77479414156 / 1000000000000) (77479414437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (323538348753951 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2277202138 / 1000000000000) (2277202140 / 1000000000000), orderedInterval (-39612904182 / 1000000000000) (-39612904180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (216108622885809 / 800000000000) 2 (IntervalRat.scale (435 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32867673518 / 1000000000000) (32867673519 / 1000000000000), orderedInterval (35665657055 / 1000000000000) (35665657056 / 1000000000000)))) (orderedInterval (10188963194 / 1000000000000) (10188963321 / 1000000000000))) = true
  rfl'

theorem compactCertificate346_chunkChecks2 :
    compactCertificate346.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate346.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate346_chunkChecks2_0
    compactCertificate346_chunkChecks2_1 compactCertificate346_chunkChecks2_2

theorem compactCertificate346_chunkChecks3_0 :
    compactCertificate346.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (435 / 2) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54017164906 / 1000000000000) (-54017164872 / 1000000000000), orderedInterval (-2896695805 / 1000000000000) (-2896695771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (128167612467387 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44013632252 / 1000000000000) (-44013632251 / 1000000000000), orderedInterval (-44989912240 / 1000000000000) (-44989912239 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (41446772502171 / 160000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39589204061 / 1000000000000) (39589310180 / 1000000000000), orderedInterval (-29914010212 / 1000000000000) (-29913904093 / 1000000000000)))) (orderedInterval (4196786596 / 1000000000000) (4196797194 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (37398989663409 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-46254731921 / 1000000000000) (-46254731920 / 1000000000000), orderedInterval (-106645139724 / 1000000000000) (-106645139723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (100458946838973 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (45562486177 / 1000000000000) (45562486178 / 1000000000000), orderedInterval (54533831316 / 1000000000000) (54533831317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (272765582716041 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27558061971 / 1000000000000) (27558071998 / 1000000000000), orderedInterval (-33322680602 / 1000000000000) (-33322670575 / 1000000000000)))) (orderedInterval (-9539665359 / 1000000000000) (-9539662543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (200917893678033 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28629583588 / 1000000000000) (28629583589 / 1000000000000), orderedInterval (41357905936 / 1000000000000) (41357905937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (344276235353109 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25712342297 / 1000000000000) (-25712342296 / 1000000000000), orderedInterval (-28574299556 / 1000000000000) (-28574299555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (253592316749631 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20477043574 / 1000000000000) (-20477043573 / 1000000000000), orderedInterval (-39830180194 / 1000000000000) (-39830180193 / 1000000000000)))) (orderedInterval (-3837398991 / 1000000000000) (-3837398921 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate346_chunkChecks3_1 :
    compactCertificate346.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (389075828084913 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6586346156 / 1000000000000) (-6586346155 / 1000000000000), orderedInterval (-35568631415 / 1000000000000) (-35568631414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (224633034079977 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-43787776083 / 1000000000000) (-43787762830 / 1000000000000), orderedInterval (18782602869 / 1000000000000) (18782616123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (398615260908093 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15836892875 / 1000000000000) (15836893161 / 1000000000000), orderedInterval (-32060483282 / 1000000000000) (-32060482995 / 1000000000000)))) (orderedInterval (-18802766556 / 1000000000000) (-18802763102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (372438083752017 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36287141836 / 1000000000000) (36287141864 / 1000000000000), orderedInterval (7081912167 / 1000000000000) (7081912196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (265789390307361 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (566355139 / 1000000000000) (566355140 / 1000000000000), orderedInterval (43769508587 / 1000000000000) (43769508589 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (301376840516919 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20247238207 / 1000000000000) (20247238208 / 1000000000000), orderedInterval (35749475516 / 1000000000000) (35749475517 / 1000000000000)))) (orderedInterval (-12572801532 / 1000000000000) (-12572801407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (251256589507911 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28882376303 / 1000000000000) (28882376304 / 1000000000000), orderedInterval (34491009211 / 1000000000000) (34491009212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (221992816678131 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46467190205 / 1000000000000) (46467192707 / 1000000000000), orderedInterval (-11702522064 / 1000000000000) (-11702519562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (64342170858969 / 160000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28536490474 / 1000000000000) (28536490475 / 1000000000000), orderedInterval (27690937354 / 1000000000000) (27690937355 / 1000000000000)))) (orderedInterval (-7076280571 / 1000000000000) (-7076280203 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate346_chunkChecks3_2 :
    compactCertificate346.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (177973830738843 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10577645576 / 1000000000000) (-10577645575 / 1000000000000), orderedInterval (-52414316311 / 1000000000000) (-52414316310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (150870387323523 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44675260093 / 1000000000000) (44675260094 / 1000000000000), orderedInterval (37027705242 / 1000000000000) (37027705243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (94407683250369 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40654460558 / 1000000000000) (-40654449768 / 1000000000000), orderedInterval (61343131568 / 1000000000000) (61343142358 / 1000000000000)))) (orderedInterval (-7922927381 / 1000000000000) (-7922927277 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (50772766037823 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (98978785879 / 1000000000000) (98978785881 / 1000000000000), orderedInterval (14510432936 / 1000000000000) (14510432938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (137857936502469 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19090692296 / 1000000000000) (-19090692295 / 1000000000000), orderedInterval (-57649984717 / 1000000000000) (-57649984716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (188233226456613 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22950156851 / 1000000000000) (-22950156850 / 1000000000000), orderedInterval (-46630538477 / 1000000000000) (-46630538476 / 1000000000000)))) (orderedInterval (-5157997899 / 1000000000000) (-5157997875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (79592316749631 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20288071989 / 1000000000000) (-20288071708 / 1000000000000), orderedInterval (77479414156 / 1000000000000) (77479414437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (323538348753951 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2277202138 / 1000000000000) (2277202140 / 1000000000000), orderedInterval (-39612904182 / 1000000000000) (-39612904180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (216108622885809 / 800000000000) 3 (IntervalRat.scale (435 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32867673518 / 1000000000000) (32867673519 / 1000000000000), orderedInterval (35665657055 / 1000000000000) (35665657056 / 1000000000000)))) (orderedInterval (-8000895942 / 1000000000000) (-8000895747 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate346_chunkChecks3 :
    compactCertificate346.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate346.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate346_chunkChecks3_0
    compactCertificate346_chunkChecks3_1 compactCertificate346_chunkChecks3_2

theorem compactCertificate346_chunkChecks4_0 :
    compactCertificate346.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (435 / 2) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-54017164906 / 1000000000000) (-54017164872 / 1000000000000), orderedInterval (-2896695805 / 1000000000000) (-2896695771 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (128167612467387 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44013632252 / 1000000000000) (-44013632251 / 1000000000000), orderedInterval (-44989912240 / 1000000000000) (-44989912239 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (41446772502171 / 160000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (39589204061 / 1000000000000) (39589310180 / 1000000000000), orderedInterval (-29914010212 / 1000000000000) (-29913904093 / 1000000000000)))) (orderedInterval (-16895100155 / 1000000000000) (-16895087489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (37398989663409 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-46254731921 / 1000000000000) (-46254731920 / 1000000000000), orderedInterval (-106645139724 / 1000000000000) (-106645139723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (100458946838973 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (45562486177 / 1000000000000) (45562486178 / 1000000000000), orderedInterval (54533831316 / 1000000000000) (54533831317 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (272765582716041 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27558061971 / 1000000000000) (27558071998 / 1000000000000), orderedInterval (-33322680602 / 1000000000000) (-33322670575 / 1000000000000)))) (orderedInterval (-11557142186 / 1000000000000) (-11557137761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (200917893678033 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28629583588 / 1000000000000) (28629583589 / 1000000000000), orderedInterval (41357905936 / 1000000000000) (41357905937 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (344276235353109 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25712342297 / 1000000000000) (-25712342296 / 1000000000000), orderedInterval (-28574299556 / 1000000000000) (-28574299555 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (253592316749631 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20477043574 / 1000000000000) (-20477043573 / 1000000000000), orderedInterval (-39830180194 / 1000000000000) (-39830180193 / 1000000000000)))) (orderedInterval (9957092266 / 1000000000000) (9957092394 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate346_chunkChecks4_1 :
    compactCertificate346.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (389075828084913 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6586346156 / 1000000000000) (-6586346155 / 1000000000000), orderedInterval (-35568631415 / 1000000000000) (-35568631414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (224633034079977 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-43787776083 / 1000000000000) (-43787762830 / 1000000000000), orderedInterval (18782602869 / 1000000000000) (18782616123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (398615260908093 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15836892875 / 1000000000000) (15836893161 / 1000000000000), orderedInterval (-32060483282 / 1000000000000) (-32060482995 / 1000000000000)))) (orderedInterval (82427339522 / 1000000000000) (82427345261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (372438083752017 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36287141836 / 1000000000000) (36287141864 / 1000000000000), orderedInterval (7081912167 / 1000000000000) (7081912196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (265789390307361 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (566355139 / 1000000000000) (566355140 / 1000000000000), orderedInterval (43769508587 / 1000000000000) (43769508589 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (301376840516919 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (20247238207 / 1000000000000) (20247238208 / 1000000000000), orderedInterval (35749475516 / 1000000000000) (35749475517 / 1000000000000)))) (orderedInterval (-14265562908 / 1000000000000) (-14265562691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (251256589507911 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28882376303 / 1000000000000) (28882376304 / 1000000000000), orderedInterval (34491009211 / 1000000000000) (34491009212 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (221992816678131 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (46467190205 / 1000000000000) (46467192707 / 1000000000000), orderedInterval (-11702522064 / 1000000000000) (-11702519562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (64342170858969 / 160000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (28536490474 / 1000000000000) (28536490475 / 1000000000000), orderedInterval (27690937354 / 1000000000000) (27690937355 / 1000000000000)))) (orderedInterval (3008171354 / 1000000000000) (3008171847 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate346_chunkChecks4_2 :
    compactCertificate346.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (177973830738843 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-10577645576 / 1000000000000) (-10577645575 / 1000000000000), orderedInterval (-52414316311 / 1000000000000) (-52414316310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (150870387323523 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (44675260093 / 1000000000000) (44675260094 / 1000000000000), orderedInterval (37027705242 / 1000000000000) (37027705243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (94407683250369 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-40654460558 / 1000000000000) (-40654449768 / 1000000000000), orderedInterval (61343131568 / 1000000000000) (61343142358 / 1000000000000)))) (orderedInterval (380096604 / 1000000000000) (380096682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (50772766037823 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (98978785879 / 1000000000000) (98978785881 / 1000000000000), orderedInterval (14510432936 / 1000000000000) (14510432938 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (137857936502469 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-19090692296 / 1000000000000) (-19090692295 / 1000000000000), orderedInterval (-57649984717 / 1000000000000) (-57649984716 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (188233226456613 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-22950156851 / 1000000000000) (-22950156850 / 1000000000000), orderedInterval (-46630538477 / 1000000000000) (-46630538476 / 1000000000000)))) (orderedInterval (2613713548 / 1000000000000) (2613713574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (79592316749631 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20288071989 / 1000000000000) (-20288071708 / 1000000000000), orderedInterval (77479414156 / 1000000000000) (77479414437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (323538348753951 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2277202138 / 1000000000000) (2277202140 / 1000000000000), orderedInterval (-39612904182 / 1000000000000) (-39612904180 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (216108622885809 / 800000000000) 4 (IntervalRat.scale (435 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32867673518 / 1000000000000) (32867673519 / 1000000000000), orderedInterval (35665657055 / 1000000000000) (35665657056 / 1000000000000)))) (orderedInterval (-16821629120 / 1000000000000) (-16821628808 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate346_chunkChecks4 :
    compactCertificate346.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate346.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate346_chunkChecks4_0
    compactCertificate346_chunkChecks4_1 compactCertificate346_chunkChecks4_2

theorem compactCertificate346_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate346.chunkCheck r b = true :=
  compactCertificate346.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate346_chunkChecks0
    · exact compactCertificate346_chunkChecks1
    · exact compactCertificate346_chunkChecks2
    · exact compactCertificate346_chunkChecks3
    · exact compactCertificate346_chunkChecks4)

theorem compactCertificate346_coefficient0 :
    compactCertificate346.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate346_coefficient1 :
    compactCertificate346.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate346_coefficient2 :
    compactCertificate346.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate346_coefficient3 :
    compactCertificate346.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate346_coefficient4 :
    compactCertificate346.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate346_coefficients : ∀ r : Fin 5,
    compactCertificate346.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate346_coefficient0
  · exact compactCertificate346_coefficient1
  · exact compactCertificate346_coefficient2
  · exact compactCertificate346_coefficient3
  · exact compactCertificate346_coefficient4

theorem compactCertificate346_lower : (1 : ℚ) ≤ compactCertificate346.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate346, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate346_proves {t : ℝ} (ht : t ∈ compactCertificate346.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate346.proves compactCertificate346_states compactCertificate346_chunks
    compactCertificate346_coefficients compactCertificate346_lower ht

end Erdos232
