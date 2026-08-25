/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate318 : CompactCertificate where
  left := 191
  right := 383 / 2
  center := 765 / 4
  grid := fun i =>
    match i.val with
    | 0 => 61
    | 1 => 45
    | 2 => 73
    | 3 => 13
    | 4 => 35
    | 5 => 95
    | 6 => 70
    | 7 => 121
    | 8 => 89
    | 9 => 136
    | 10 => 79
    | 11 => 140
    | 12 => 130
    | 13 => 93
    | 14 => 105
    | 15 => 88
    | 16 => 78
    | 17 => 113
    | 18 => 62
    | 19 => 53
    | 20 => 33
    | 21 => 18
    | 22 => 48
    | 23 => 66
    | 24 => 28
    | 25 => 113
    | _ => 76
  point := fun i =>
    match i.val with
    | 0 => 765 / 4
    | 1 => 225398215028853 / 1600000000000
    | 2 => 72889151641749 / 320000000000
    | 3 => 65770636994271 / 1600000000000
    | 4 => 176669182371987 / 1600000000000
    | 5 => 479691197190279 / 1600000000000
    | 6 => 353338364744127 / 1600000000000
    | 7 => 605451310448571 / 1600000000000
    | 8 => 445972694973489 / 1600000000000
    | 9 => 684236801114847 / 1600000000000
    | 10 => 395044301313063 / 1600000000000
    | 11 => 701013045045267 / 1600000000000
    | 12 => 654977319701823 / 1600000000000
    | 13 => 467422720885359 / 1600000000000
    | 14 => 530007547115961 / 1600000000000
    | 15 => 441865036720809 / 1600000000000
    | 16 => 390401160364989 / 1600000000000
    | 17 => 113153472889911 / 320000000000
    | 18 => 312988460954517 / 1600000000000
    | 19 => 265323784603437 / 1600000000000
    | 20 => 166027305026511 / 1600000000000
    | 21 => 89290036825137 / 1600000000000
    | 22 => 242439819366411 / 1600000000000
    | 23 => 331030846527147 / 1600000000000
    | 24 => 139972694973489 / 1600000000000
    | 25 => 568981234015569 / 1600000000000
    | _ => 380053095419871 / 1600000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-22339522954 / 1000000000000) (-22339522953 / 1000000000000), orderedInterval (-53136375435 / 1000000000000) (-53136375434 / 1000000000000))
    | 1 => (orderedInterval (-19011799360 / 1000000000000) (-19011799359 / 1000000000000), orderedInterval (-64412374419 / 1000000000000) (-64412374418 / 1000000000000))
    | 2 => (orderedInterval (36909138019 / 1000000000000) (36909175255 / 1000000000000), orderedInterval (-37931007961 / 1000000000000) (-37930970725 / 1000000000000))
    | 3 => (orderedInterval (-107838826226 / 1000000000000) (-107838826225 / 1000000000000), orderedInterval (-60795182092 / 1000000000000) (-60795182091 / 1000000000000))
    | 4 => (orderedInterval (-71979172717 / 1000000000000) (-71979172716 / 1000000000000), orderedInterval (-23850140946 / 1000000000000) (-23850140945 / 1000000000000))
    | 5 => (orderedInterval (-38798358715 / 1000000000000) (-38798292306 / 1000000000000), orderedInterval (24926702623 / 1000000000000) (24926769031 / 1000000000000))
    | 6 => (orderedInterval (53173262972 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984141 / 1000000000000) (-7560983628 / 1000000000000))
    | 7 => (orderedInterval (33137175566 / 1000000000000) (33137258465 / 1000000000000), orderedInterval (-24215955290 / 1000000000000) (-24215872391 / 1000000000000))
    | 8 => (orderedInterval (4003152557 / 1000000000000) (4003152563 / 1000000000000), orderedInterval (-47630242296 / 1000000000000) (-47630242290 / 1000000000000))
    | 9 => (orderedInterval (35622556413 / 1000000000000) (35622556415 / 1000000000000), orderedInterval (14780173865 / 1000000000000) (14780173867 / 1000000000000))
    | 10 => (orderedInterval (24265838652 / 1000000000000) (24265840799 / 1000000000000), orderedInterval (-44654025716 / 1000000000000) (-44654023570 / 1000000000000))
    | 11 => (orderedInterval (-29970507252 / 1000000000000) (-29970460504 / 1000000000000), orderedInterval (23588326934 / 1000000000000) (23588373681 / 1000000000000))
    | 12 => (orderedInterval (38879736362 / 1000000000000) (38879738595 / 1000000000000), orderedInterval (-6644496209 / 1000000000000) (-6644493975 / 1000000000000))
    | 13 => (orderedInterval (-32026121457 / 1000000000000) (-32026121456 / 1000000000000), orderedInterval (-33908308102 / 1000000000000) (-33908308101 / 1000000000000))
    | 14 => (orderedInterval (-36139330651 / 1000000000000) (-36139231060 / 1000000000000), orderedInterval (24869717243 / 1000000000000) (24869816834 / 1000000000000))
    | 15 => (orderedInterval (22614590923 / 1000000000000) (22614590924 / 1000000000000), orderedInterval (42312240669 / 1000000000000) (42312240670 / 1000000000000))
    | 16 => (orderedInterval (-13063131583 / 1000000000000) (-13063131475 / 1000000000000), orderedInterval (49407422862 / 1000000000000) (49407422970 / 1000000000000))
    | 17 => (orderedInterval (24318415704 / 1000000000000) (24318419761 / 1000000000000), orderedInterval (-34804879041 / 1000000000000) (-34804874984 / 1000000000000))
    | 18 => (orderedInterval (56967187602 / 1000000000000) (56967187742 / 1000000000000), orderedInterval (-3168075205 / 1000000000000) (-3168075064 / 1000000000000))
    | 19 => (orderedInterval (-6653977864 / 1000000000000) (-6653977862 / 1000000000000), orderedInterval (-61581828298 / 1000000000000) (-61581828297 / 1000000000000))
    | 20 => (orderedInterval (-60304302328 / 1000000000000) (-60304302327 / 1000000000000), orderedInterval (-49694058561 / 1000000000000) (-49694058560 / 1000000000000))
    | 21 => (orderedInterval (4352564878 / 1000000000000) (4352564883 / 1000000000000), orderedInterval (106681132277 / 1000000000000) (106681132282 / 1000000000000))
    | 22 => (orderedInterval (64710008125 / 1000000000000) (64710008145 / 1000000000000), orderedInterval (3529822230 / 1000000000000) (3529822250 / 1000000000000))
    | 23 => (orderedInterval (18182520071 / 1000000000000) (18182520072 / 1000000000000), orderedInterval (52362474170 / 1000000000000) (52362474171 / 1000000000000))
    | 24 => (orderedInterval (25397514814 / 1000000000000) (25397514815 / 1000000000000), orderedInterval (81292786341 / 1000000000000) (81292786342 / 1000000000000))
    | 25 => (orderedInterval (-41683194218 / 1000000000000) (-41683194201 / 1000000000000), orderedInterval (-7201707348 / 1000000000000) (-7201707331 / 1000000000000))
    | _ => (orderedInterval (-22190570435 / 1000000000000) (-22190569233 / 1000000000000), orderedInterval (46819695314 / 1000000000000) (46819696516 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-6865887658 / 1000000000000) (-6865885459 / 1000000000000)
      | 1 => orderedInterval (1300046195 / 1000000000000) (1300050940 / 1000000000000)
      | 2 => orderedInterval (-925337340 / 1000000000000) (-925334771 / 1000000000000)
      | 3 => orderedInterval (-8792283438 / 1000000000000) (-8792276557 / 1000000000000)
      | 4 => orderedInterval (-3547495783 / 1000000000000) (-3547495215 / 1000000000000)
      | 5 => orderedInterval (1631352929 / 1000000000000) (1631353058 / 1000000000000)
      | 6 => orderedInterval (-10695230837 / 1000000000000) (-10695230766 / 1000000000000)
      | 7 => orderedInterval (-2941925448 / 1000000000000) (-2941925424 / 1000000000000)
      | _ => orderedInterval (7709730039 / 1000000000000) (7709730320 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-24154469962 / 1000000000000) (-24154467344 / 1000000000000)
      | 1 => orderedInterval (-3138868187 / 1000000000000) (-3138860760 / 1000000000000)
      | 2 => orderedInterval (-199842483 / 1000000000000) (-199837404 / 1000000000000)
      | 3 => orderedInterval (-2461877147 / 1000000000000) (-2461861559 / 1000000000000)
      | 4 => orderedInterval (-4859192664 / 1000000000000) (-4859191667 / 1000000000000)
      | 5 => orderedInterval (-4549377971 / 1000000000000) (-4549377744 / 1000000000000)
      | 6 => orderedInterval (2662545146 / 1000000000000) (2662545214 / 1000000000000)
      | 7 => orderedInterval (-4979517702 / 1000000000000) (-4979517681 / 1000000000000)
      | _ => orderedInterval (-9596310706 / 1000000000000) (-9596310348 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (6004776296 / 1000000000000) (6004779427 / 1000000000000)
      | 1 => orderedInterval (-5939590080 / 1000000000000) (-5939578403 / 1000000000000)
      | 2 => orderedInterval (3796848664 / 1000000000000) (3796858735 / 1000000000000)
      | 3 => orderedInterval (51024649829 / 1000000000000) (51024685391 / 1000000000000)
      | 4 => orderedInterval (9758973579 / 1000000000000) (9758975343 / 1000000000000)
      | 5 => orderedInterval (-3866064130 / 1000000000000) (-3866063724 / 1000000000000)
      | 6 => orderedInterval (9810299507 / 1000000000000) (9810299574 / 1000000000000)
      | 7 => orderedInterval (2585200007 / 1000000000000) (2585200029 / 1000000000000)
      | _ => orderedInterval (-18135770010 / 1000000000000) (-18135769546 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (25029552781 / 1000000000000) (25029556509 / 1000000000000)
      | 1 => orderedInterval (7018414979 / 1000000000000) (7018433280 / 1000000000000)
      | 2 => orderedInterval (-2241858773 / 1000000000000) (-2241838854 / 1000000000000)
      | 3 => orderedInterval (-4101600833 / 1000000000000) (-4101519668 / 1000000000000)
      | 4 => orderedInterval (10855046013 / 1000000000000) (10855049141 / 1000000000000)
      | 5 => orderedInterval (10052995752 / 1000000000000) (10052996484 / 1000000000000)
      | 6 => orderedInterval (-2607003154 / 1000000000000) (-2607003088 / 1000000000000)
      | 7 => orderedInterval (5155661262 / 1000000000000) (5155661284 / 1000000000000)
      | _ => orderedInterval (13109177884 / 1000000000000) (13109178497 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-4810424698 / 1000000000000) (-4810420239 / 1000000000000)
      | 1 => orderedInterval (16293294854 / 1000000000000) (16293323637 / 1000000000000)
      | 2 => orderedInterval (-15204515447 / 1000000000000) (-15204475940 / 1000000000000)
      | 3 => orderedInterval (-270552533554 / 1000000000000) (-270552347587 / 1000000000000)
      | 4 => orderedInterval (-29688782307 / 1000000000000) (-29688776712 / 1000000000000)
      | 5 => orderedInterval (10287077664 / 1000000000000) (10287078998 / 1000000000000)
      | 6 => orderedInterval (-9899395962 / 1000000000000) (-9899395896 / 1000000000000)
      | 7 => orderedInterval (-2541386530 / 1000000000000) (-2541386506 / 1000000000000)
      | _ => orderedInterval (50336670605 / 1000000000000) (50336671436 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-23127031341 / 1000000000000) (-23127013874 / 1000000000000)
    | 1 => orderedInterval (-51276911676 / 1000000000000) (-51276879293 / 1000000000000)
    | 2 => orderedInterval (55039323662 / 1000000000000) (55039386826 / 1000000000000)
    | 3 => orderedInterval (62270385911 / 1000000000000) (62270513585 / 1000000000000)
    | _ => orderedInterval (-255779995375 / 1000000000000) (-255779728809 / 1000000000000)

theorem compactCertificate318_stateChecks0 :
    compactCertificate318.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (765 / 4)) (orderedInterval (-22339522954 / 1000000000000) (-22339522953 / 1000000000000), orderedInterval (-53136375435 / 1000000000000) (-53136375434 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (225398215028853 / 1600000000000)) (orderedInterval (-19011799360 / 1000000000000) (-19011799359 / 1000000000000), orderedInterval (-64412374419 / 1000000000000) (-64412374418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (72889151641749 / 320000000000)) (orderedInterval (36909138019 / 1000000000000) (36909175255 / 1000000000000), orderedInterval (-37931007961 / 1000000000000) (-37930970725 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_stateChecks1 :
    compactCertificate318.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (65770636994271 / 1600000000000)) (orderedInterval (-107838826226 / 1000000000000) (-107838826225 / 1000000000000), orderedInterval (-60795182092 / 1000000000000) (-60795182091 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (176669182371987 / 1600000000000)) (orderedInterval (-71979172717 / 1000000000000) (-71979172716 / 1000000000000), orderedInterval (-23850140946 / 1000000000000) (-23850140945 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (479691197190279 / 1600000000000)) (orderedInterval (-38798358715 / 1000000000000) (-38798292306 / 1000000000000), orderedInterval (24926702623 / 1000000000000) (24926769031 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_stateChecks2 :
    compactCertificate318.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (353338364744127 / 1600000000000)) (orderedInterval (53173262972 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984141 / 1000000000000) (-7560983628 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (605451310448571 / 1600000000000)) (orderedInterval (33137175566 / 1000000000000) (33137258465 / 1000000000000), orderedInterval (-24215955290 / 1000000000000) (-24215872391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (445972694973489 / 1600000000000)) (orderedInterval (4003152557 / 1000000000000) (4003152563 / 1000000000000), orderedInterval (-47630242296 / 1000000000000) (-47630242290 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_stateChecks3 :
    compactCertificate318.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (684236801114847 / 1600000000000)) (orderedInterval (35622556413 / 1000000000000) (35622556415 / 1000000000000), orderedInterval (14780173865 / 1000000000000) (14780173867 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (395044301313063 / 1600000000000)) (orderedInterval (24265838652 / 1000000000000) (24265840799 / 1000000000000), orderedInterval (-44654025716 / 1000000000000) (-44654023570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (701013045045267 / 1600000000000)) (orderedInterval (-29970507252 / 1000000000000) (-29970460504 / 1000000000000), orderedInterval (23588326934 / 1000000000000) (23588373681 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_stateChecks4 :
    compactCertificate318.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (654977319701823 / 1600000000000)) (orderedInterval (38879736362 / 1000000000000) (38879738595 / 1000000000000), orderedInterval (-6644496209 / 1000000000000) (-6644493975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (467422720885359 / 1600000000000)) (orderedInterval (-32026121457 / 1000000000000) (-32026121456 / 1000000000000), orderedInterval (-33908308102 / 1000000000000) (-33908308101 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (530007547115961 / 1600000000000)) (orderedInterval (-36139330651 / 1000000000000) (-36139231060 / 1000000000000), orderedInterval (24869717243 / 1000000000000) (24869816834 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_stateChecks5 :
    compactCertificate318.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (441865036720809 / 1600000000000)) (orderedInterval (22614590923 / 1000000000000) (22614590924 / 1000000000000), orderedInterval (42312240669 / 1000000000000) (42312240670 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (390401160364989 / 1600000000000)) (orderedInterval (-13063131583 / 1000000000000) (-13063131475 / 1000000000000), orderedInterval (49407422862 / 1000000000000) (49407422970 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (113153472889911 / 320000000000)) (orderedInterval (24318415704 / 1000000000000) (24318419761 / 1000000000000), orderedInterval (-34804879041 / 1000000000000) (-34804874984 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_stateChecks6 :
    compactCertificate318.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (312988460954517 / 1600000000000)) (orderedInterval (56967187602 / 1000000000000) (56967187742 / 1000000000000), orderedInterval (-3168075205 / 1000000000000) (-3168075064 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (265323784603437 / 1600000000000)) (orderedInterval (-6653977864 / 1000000000000) (-6653977862 / 1000000000000), orderedInterval (-61581828298 / 1000000000000) (-61581828297 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (166027305026511 / 1600000000000)) (orderedInterval (-60304302328 / 1000000000000) (-60304302327 / 1000000000000), orderedInterval (-49694058561 / 1000000000000) (-49694058560 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_stateChecks7 :
    compactCertificate318.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (89290036825137 / 1600000000000)) (orderedInterval (4352564878 / 1000000000000) (4352564883 / 1000000000000), orderedInterval (106681132277 / 1000000000000) (106681132282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (242439819366411 / 1600000000000)) (orderedInterval (64710008125 / 1000000000000) (64710008145 / 1000000000000), orderedInterval (3529822230 / 1000000000000) (3529822250 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (331030846527147 / 1600000000000)) (orderedInterval (18182520071 / 1000000000000) (18182520072 / 1000000000000), orderedInterval (52362474170 / 1000000000000) (52362474171 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_stateChecks8 :
    compactCertificate318.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (139972694973489 / 1600000000000)) (orderedInterval (25397514814 / 1000000000000) (25397514815 / 1000000000000), orderedInterval (81292786341 / 1000000000000) (81292786342 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (568981234015569 / 1600000000000)) (orderedInterval (-41683194218 / 1000000000000) (-41683194201 / 1000000000000), orderedInterval (-7201707348 / 1000000000000) (-7201707331 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (380053095419871 / 1600000000000)) (orderedInterval (-22190570435 / 1000000000000) (-22190569233 / 1000000000000), orderedInterval (46819695314 / 1000000000000) (46819696516 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_states : ∀ j,
    BesselStateValid (compactCertificate318.point j) (compactCertificate318.state j) :=
  compactCertificate318.statesValid_of_checks3 compactCertificate318_stateChecks0
    compactCertificate318_stateChecks1 compactCertificate318_stateChecks2
    compactCertificate318_stateChecks3 compactCertificate318_stateChecks4
    compactCertificate318_stateChecks5 compactCertificate318_stateChecks6
    compactCertificate318_stateChecks7 compactCertificate318_stateChecks8

theorem compactCertificate318_chunkChecks0_0 :
    compactCertificate318.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (765 / 4) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-22339522954 / 1000000000000) (-22339522953 / 1000000000000), orderedInterval (-53136375435 / 1000000000000) (-53136375434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (225398215028853 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19011799360 / 1000000000000) (-19011799359 / 1000000000000), orderedInterval (-64412374419 / 1000000000000) (-64412374418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (72889151641749 / 320000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36909138019 / 1000000000000) (36909175255 / 1000000000000), orderedInterval (-37931007961 / 1000000000000) (-37930970725 / 1000000000000)))) (orderedInterval (-6865887658 / 1000000000000) (-6865885459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (65770636994271 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107838826226 / 1000000000000) (-107838826225 / 1000000000000), orderedInterval (-60795182092 / 1000000000000) (-60795182091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (176669182371987 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71979172717 / 1000000000000) (-71979172716 / 1000000000000), orderedInterval (-23850140946 / 1000000000000) (-23850140945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (479691197190279 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-38798358715 / 1000000000000) (-38798292306 / 1000000000000), orderedInterval (24926702623 / 1000000000000) (24926769031 / 1000000000000)))) (orderedInterval (1300046195 / 1000000000000) (1300050940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (353338364744127 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53173262972 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984141 / 1000000000000) (-7560983628 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (605451310448571 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33137175566 / 1000000000000) (33137258465 / 1000000000000), orderedInterval (-24215955290 / 1000000000000) (-24215872391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (445972694973489 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4003152557 / 1000000000000) (4003152563 / 1000000000000), orderedInterval (-47630242296 / 1000000000000) (-47630242290 / 1000000000000)))) (orderedInterval (-925337340 / 1000000000000) (-925334771 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_chunkChecks0_1 :
    compactCertificate318.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (684236801114847 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35622556413 / 1000000000000) (35622556415 / 1000000000000), orderedInterval (14780173865 / 1000000000000) (14780173867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (395044301313063 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24265838652 / 1000000000000) (24265840799 / 1000000000000), orderedInterval (-44654025716 / 1000000000000) (-44654023570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (701013045045267 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29970507252 / 1000000000000) (-29970460504 / 1000000000000), orderedInterval (23588326934 / 1000000000000) (23588373681 / 1000000000000)))) (orderedInterval (-8792283438 / 1000000000000) (-8792276557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (654977319701823 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38879736362 / 1000000000000) (38879738595 / 1000000000000), orderedInterval (-6644496209 / 1000000000000) (-6644493975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (467422720885359 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32026121457 / 1000000000000) (-32026121456 / 1000000000000), orderedInterval (-33908308102 / 1000000000000) (-33908308101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (530007547115961 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36139330651 / 1000000000000) (-36139231060 / 1000000000000), orderedInterval (24869717243 / 1000000000000) (24869816834 / 1000000000000)))) (orderedInterval (-3547495783 / 1000000000000) (-3547495215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (441865036720809 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22614590923 / 1000000000000) (22614590924 / 1000000000000), orderedInterval (42312240669 / 1000000000000) (42312240670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (390401160364989 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13063131583 / 1000000000000) (-13063131475 / 1000000000000), orderedInterval (49407422862 / 1000000000000) (49407422970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (113153472889911 / 320000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24318415704 / 1000000000000) (24318419761 / 1000000000000), orderedInterval (-34804879041 / 1000000000000) (-34804874984 / 1000000000000)))) (orderedInterval (1631352929 / 1000000000000) (1631353058 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_chunkChecks0_2 :
    compactCertificate318.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (312988460954517 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56967187602 / 1000000000000) (56967187742 / 1000000000000), orderedInterval (-3168075205 / 1000000000000) (-3168075064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (265323784603437 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6653977864 / 1000000000000) (-6653977862 / 1000000000000), orderedInterval (-61581828298 / 1000000000000) (-61581828297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (166027305026511 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60304302328 / 1000000000000) (-60304302327 / 1000000000000), orderedInterval (-49694058561 / 1000000000000) (-49694058560 / 1000000000000)))) (orderedInterval (-10695230837 / 1000000000000) (-10695230766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (89290036825137 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4352564878 / 1000000000000) (4352564883 / 1000000000000), orderedInterval (106681132277 / 1000000000000) (106681132282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (242439819366411 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (64710008125 / 1000000000000) (64710008145 / 1000000000000), orderedInterval (3529822230 / 1000000000000) (3529822250 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (331030846527147 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18182520071 / 1000000000000) (18182520072 / 1000000000000), orderedInterval (52362474170 / 1000000000000) (52362474171 / 1000000000000)))) (orderedInterval (-2941925448 / 1000000000000) (-2941925424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (139972694973489 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25397514814 / 1000000000000) (25397514815 / 1000000000000), orderedInterval (81292786341 / 1000000000000) (81292786342 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (568981234015569 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-41683194218 / 1000000000000) (-41683194201 / 1000000000000), orderedInterval (-7201707348 / 1000000000000) (-7201707331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (380053095419871 / 1600000000000) 0 (IntervalRat.scale (765 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22190570435 / 1000000000000) (-22190569233 / 1000000000000), orderedInterval (46819695314 / 1000000000000) (46819696516 / 1000000000000)))) (orderedInterval (7709730039 / 1000000000000) (7709730320 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_chunkChecks0 :
    compactCertificate318.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate318.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate318_chunkChecks0_0
    compactCertificate318_chunkChecks0_1 compactCertificate318_chunkChecks0_2

theorem compactCertificate318_chunkChecks1_0 :
    compactCertificate318.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (765 / 4) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-22339522954 / 1000000000000) (-22339522953 / 1000000000000), orderedInterval (-53136375435 / 1000000000000) (-53136375434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (225398215028853 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19011799360 / 1000000000000) (-19011799359 / 1000000000000), orderedInterval (-64412374419 / 1000000000000) (-64412374418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (72889151641749 / 320000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36909138019 / 1000000000000) (36909175255 / 1000000000000), orderedInterval (-37931007961 / 1000000000000) (-37930970725 / 1000000000000)))) (orderedInterval (-24154469962 / 1000000000000) (-24154467344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (65770636994271 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107838826226 / 1000000000000) (-107838826225 / 1000000000000), orderedInterval (-60795182092 / 1000000000000) (-60795182091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (176669182371987 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71979172717 / 1000000000000) (-71979172716 / 1000000000000), orderedInterval (-23850140946 / 1000000000000) (-23850140945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (479691197190279 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-38798358715 / 1000000000000) (-38798292306 / 1000000000000), orderedInterval (24926702623 / 1000000000000) (24926769031 / 1000000000000)))) (orderedInterval (-3138868187 / 1000000000000) (-3138860760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (353338364744127 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53173262972 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984141 / 1000000000000) (-7560983628 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (605451310448571 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33137175566 / 1000000000000) (33137258465 / 1000000000000), orderedInterval (-24215955290 / 1000000000000) (-24215872391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (445972694973489 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4003152557 / 1000000000000) (4003152563 / 1000000000000), orderedInterval (-47630242296 / 1000000000000) (-47630242290 / 1000000000000)))) (orderedInterval (-199842483 / 1000000000000) (-199837404 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_chunkChecks1_1 :
    compactCertificate318.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (684236801114847 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35622556413 / 1000000000000) (35622556415 / 1000000000000), orderedInterval (14780173865 / 1000000000000) (14780173867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (395044301313063 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24265838652 / 1000000000000) (24265840799 / 1000000000000), orderedInterval (-44654025716 / 1000000000000) (-44654023570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (701013045045267 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29970507252 / 1000000000000) (-29970460504 / 1000000000000), orderedInterval (23588326934 / 1000000000000) (23588373681 / 1000000000000)))) (orderedInterval (-2461877147 / 1000000000000) (-2461861559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (654977319701823 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38879736362 / 1000000000000) (38879738595 / 1000000000000), orderedInterval (-6644496209 / 1000000000000) (-6644493975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (467422720885359 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32026121457 / 1000000000000) (-32026121456 / 1000000000000), orderedInterval (-33908308102 / 1000000000000) (-33908308101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (530007547115961 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36139330651 / 1000000000000) (-36139231060 / 1000000000000), orderedInterval (24869717243 / 1000000000000) (24869816834 / 1000000000000)))) (orderedInterval (-4859192664 / 1000000000000) (-4859191667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (441865036720809 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22614590923 / 1000000000000) (22614590924 / 1000000000000), orderedInterval (42312240669 / 1000000000000) (42312240670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (390401160364989 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13063131583 / 1000000000000) (-13063131475 / 1000000000000), orderedInterval (49407422862 / 1000000000000) (49407422970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (113153472889911 / 320000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24318415704 / 1000000000000) (24318419761 / 1000000000000), orderedInterval (-34804879041 / 1000000000000) (-34804874984 / 1000000000000)))) (orderedInterval (-4549377971 / 1000000000000) (-4549377744 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_chunkChecks1_2 :
    compactCertificate318.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (312988460954517 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56967187602 / 1000000000000) (56967187742 / 1000000000000), orderedInterval (-3168075205 / 1000000000000) (-3168075064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (265323784603437 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6653977864 / 1000000000000) (-6653977862 / 1000000000000), orderedInterval (-61581828298 / 1000000000000) (-61581828297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (166027305026511 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60304302328 / 1000000000000) (-60304302327 / 1000000000000), orderedInterval (-49694058561 / 1000000000000) (-49694058560 / 1000000000000)))) (orderedInterval (2662545146 / 1000000000000) (2662545214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (89290036825137 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4352564878 / 1000000000000) (4352564883 / 1000000000000), orderedInterval (106681132277 / 1000000000000) (106681132282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (242439819366411 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (64710008125 / 1000000000000) (64710008145 / 1000000000000), orderedInterval (3529822230 / 1000000000000) (3529822250 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (331030846527147 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18182520071 / 1000000000000) (18182520072 / 1000000000000), orderedInterval (52362474170 / 1000000000000) (52362474171 / 1000000000000)))) (orderedInterval (-4979517702 / 1000000000000) (-4979517681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (139972694973489 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25397514814 / 1000000000000) (25397514815 / 1000000000000), orderedInterval (81292786341 / 1000000000000) (81292786342 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (568981234015569 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-41683194218 / 1000000000000) (-41683194201 / 1000000000000), orderedInterval (-7201707348 / 1000000000000) (-7201707331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (380053095419871 / 1600000000000) 1 (IntervalRat.scale (765 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22190570435 / 1000000000000) (-22190569233 / 1000000000000), orderedInterval (46819695314 / 1000000000000) (46819696516 / 1000000000000)))) (orderedInterval (-9596310706 / 1000000000000) (-9596310348 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_chunkChecks1 :
    compactCertificate318.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate318.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate318_chunkChecks1_0
    compactCertificate318_chunkChecks1_1 compactCertificate318_chunkChecks1_2

theorem compactCertificate318_chunkChecks2_0 :
    compactCertificate318.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (765 / 4) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-22339522954 / 1000000000000) (-22339522953 / 1000000000000), orderedInterval (-53136375435 / 1000000000000) (-53136375434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (225398215028853 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19011799360 / 1000000000000) (-19011799359 / 1000000000000), orderedInterval (-64412374419 / 1000000000000) (-64412374418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (72889151641749 / 320000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36909138019 / 1000000000000) (36909175255 / 1000000000000), orderedInterval (-37931007961 / 1000000000000) (-37930970725 / 1000000000000)))) (orderedInterval (6004776296 / 1000000000000) (6004779427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (65770636994271 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107838826226 / 1000000000000) (-107838826225 / 1000000000000), orderedInterval (-60795182092 / 1000000000000) (-60795182091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (176669182371987 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71979172717 / 1000000000000) (-71979172716 / 1000000000000), orderedInterval (-23850140946 / 1000000000000) (-23850140945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (479691197190279 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-38798358715 / 1000000000000) (-38798292306 / 1000000000000), orderedInterval (24926702623 / 1000000000000) (24926769031 / 1000000000000)))) (orderedInterval (-5939590080 / 1000000000000) (-5939578403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (353338364744127 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53173262972 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984141 / 1000000000000) (-7560983628 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (605451310448571 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33137175566 / 1000000000000) (33137258465 / 1000000000000), orderedInterval (-24215955290 / 1000000000000) (-24215872391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (445972694973489 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4003152557 / 1000000000000) (4003152563 / 1000000000000), orderedInterval (-47630242296 / 1000000000000) (-47630242290 / 1000000000000)))) (orderedInterval (3796848664 / 1000000000000) (3796858735 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_chunkChecks2_1 :
    compactCertificate318.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (684236801114847 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35622556413 / 1000000000000) (35622556415 / 1000000000000), orderedInterval (14780173865 / 1000000000000) (14780173867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (395044301313063 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24265838652 / 1000000000000) (24265840799 / 1000000000000), orderedInterval (-44654025716 / 1000000000000) (-44654023570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (701013045045267 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29970507252 / 1000000000000) (-29970460504 / 1000000000000), orderedInterval (23588326934 / 1000000000000) (23588373681 / 1000000000000)))) (orderedInterval (51024649829 / 1000000000000) (51024685391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (654977319701823 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38879736362 / 1000000000000) (38879738595 / 1000000000000), orderedInterval (-6644496209 / 1000000000000) (-6644493975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (467422720885359 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32026121457 / 1000000000000) (-32026121456 / 1000000000000), orderedInterval (-33908308102 / 1000000000000) (-33908308101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (530007547115961 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36139330651 / 1000000000000) (-36139231060 / 1000000000000), orderedInterval (24869717243 / 1000000000000) (24869816834 / 1000000000000)))) (orderedInterval (9758973579 / 1000000000000) (9758975343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (441865036720809 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22614590923 / 1000000000000) (22614590924 / 1000000000000), orderedInterval (42312240669 / 1000000000000) (42312240670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (390401160364989 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13063131583 / 1000000000000) (-13063131475 / 1000000000000), orderedInterval (49407422862 / 1000000000000) (49407422970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (113153472889911 / 320000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24318415704 / 1000000000000) (24318419761 / 1000000000000), orderedInterval (-34804879041 / 1000000000000) (-34804874984 / 1000000000000)))) (orderedInterval (-3866064130 / 1000000000000) (-3866063724 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_chunkChecks2_2 :
    compactCertificate318.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (312988460954517 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56967187602 / 1000000000000) (56967187742 / 1000000000000), orderedInterval (-3168075205 / 1000000000000) (-3168075064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (265323784603437 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6653977864 / 1000000000000) (-6653977862 / 1000000000000), orderedInterval (-61581828298 / 1000000000000) (-61581828297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (166027305026511 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60304302328 / 1000000000000) (-60304302327 / 1000000000000), orderedInterval (-49694058561 / 1000000000000) (-49694058560 / 1000000000000)))) (orderedInterval (9810299507 / 1000000000000) (9810299574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (89290036825137 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4352564878 / 1000000000000) (4352564883 / 1000000000000), orderedInterval (106681132277 / 1000000000000) (106681132282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (242439819366411 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (64710008125 / 1000000000000) (64710008145 / 1000000000000), orderedInterval (3529822230 / 1000000000000) (3529822250 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (331030846527147 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18182520071 / 1000000000000) (18182520072 / 1000000000000), orderedInterval (52362474170 / 1000000000000) (52362474171 / 1000000000000)))) (orderedInterval (2585200007 / 1000000000000) (2585200029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (139972694973489 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25397514814 / 1000000000000) (25397514815 / 1000000000000), orderedInterval (81292786341 / 1000000000000) (81292786342 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (568981234015569 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-41683194218 / 1000000000000) (-41683194201 / 1000000000000), orderedInterval (-7201707348 / 1000000000000) (-7201707331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (380053095419871 / 1600000000000) 2 (IntervalRat.scale (765 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22190570435 / 1000000000000) (-22190569233 / 1000000000000), orderedInterval (46819695314 / 1000000000000) (46819696516 / 1000000000000)))) (orderedInterval (-18135770010 / 1000000000000) (-18135769546 / 1000000000000))) = true
  rfl'

theorem compactCertificate318_chunkChecks2 :
    compactCertificate318.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate318.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate318_chunkChecks2_0
    compactCertificate318_chunkChecks2_1 compactCertificate318_chunkChecks2_2

theorem compactCertificate318_chunkChecks3_0 :
    compactCertificate318.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (765 / 4) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-22339522954 / 1000000000000) (-22339522953 / 1000000000000), orderedInterval (-53136375435 / 1000000000000) (-53136375434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (225398215028853 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19011799360 / 1000000000000) (-19011799359 / 1000000000000), orderedInterval (-64412374419 / 1000000000000) (-64412374418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (72889151641749 / 320000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36909138019 / 1000000000000) (36909175255 / 1000000000000), orderedInterval (-37931007961 / 1000000000000) (-37930970725 / 1000000000000)))) (orderedInterval (25029552781 / 1000000000000) (25029556509 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (65770636994271 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107838826226 / 1000000000000) (-107838826225 / 1000000000000), orderedInterval (-60795182092 / 1000000000000) (-60795182091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (176669182371987 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71979172717 / 1000000000000) (-71979172716 / 1000000000000), orderedInterval (-23850140946 / 1000000000000) (-23850140945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (479691197190279 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-38798358715 / 1000000000000) (-38798292306 / 1000000000000), orderedInterval (24926702623 / 1000000000000) (24926769031 / 1000000000000)))) (orderedInterval (7018414979 / 1000000000000) (7018433280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (353338364744127 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53173262972 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984141 / 1000000000000) (-7560983628 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (605451310448571 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33137175566 / 1000000000000) (33137258465 / 1000000000000), orderedInterval (-24215955290 / 1000000000000) (-24215872391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (445972694973489 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4003152557 / 1000000000000) (4003152563 / 1000000000000), orderedInterval (-47630242296 / 1000000000000) (-47630242290 / 1000000000000)))) (orderedInterval (-2241858773 / 1000000000000) (-2241838854 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate318_chunkChecks3_1 :
    compactCertificate318.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (684236801114847 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35622556413 / 1000000000000) (35622556415 / 1000000000000), orderedInterval (14780173865 / 1000000000000) (14780173867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (395044301313063 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24265838652 / 1000000000000) (24265840799 / 1000000000000), orderedInterval (-44654025716 / 1000000000000) (-44654023570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (701013045045267 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29970507252 / 1000000000000) (-29970460504 / 1000000000000), orderedInterval (23588326934 / 1000000000000) (23588373681 / 1000000000000)))) (orderedInterval (-4101600833 / 1000000000000) (-4101519668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (654977319701823 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38879736362 / 1000000000000) (38879738595 / 1000000000000), orderedInterval (-6644496209 / 1000000000000) (-6644493975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (467422720885359 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32026121457 / 1000000000000) (-32026121456 / 1000000000000), orderedInterval (-33908308102 / 1000000000000) (-33908308101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (530007547115961 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36139330651 / 1000000000000) (-36139231060 / 1000000000000), orderedInterval (24869717243 / 1000000000000) (24869816834 / 1000000000000)))) (orderedInterval (10855046013 / 1000000000000) (10855049141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (441865036720809 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22614590923 / 1000000000000) (22614590924 / 1000000000000), orderedInterval (42312240669 / 1000000000000) (42312240670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (390401160364989 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13063131583 / 1000000000000) (-13063131475 / 1000000000000), orderedInterval (49407422862 / 1000000000000) (49407422970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (113153472889911 / 320000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24318415704 / 1000000000000) (24318419761 / 1000000000000), orderedInterval (-34804879041 / 1000000000000) (-34804874984 / 1000000000000)))) (orderedInterval (10052995752 / 1000000000000) (10052996484 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate318_chunkChecks3_2 :
    compactCertificate318.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (312988460954517 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56967187602 / 1000000000000) (56967187742 / 1000000000000), orderedInterval (-3168075205 / 1000000000000) (-3168075064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (265323784603437 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6653977864 / 1000000000000) (-6653977862 / 1000000000000), orderedInterval (-61581828298 / 1000000000000) (-61581828297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (166027305026511 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60304302328 / 1000000000000) (-60304302327 / 1000000000000), orderedInterval (-49694058561 / 1000000000000) (-49694058560 / 1000000000000)))) (orderedInterval (-2607003154 / 1000000000000) (-2607003088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (89290036825137 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4352564878 / 1000000000000) (4352564883 / 1000000000000), orderedInterval (106681132277 / 1000000000000) (106681132282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (242439819366411 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (64710008125 / 1000000000000) (64710008145 / 1000000000000), orderedInterval (3529822230 / 1000000000000) (3529822250 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (331030846527147 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18182520071 / 1000000000000) (18182520072 / 1000000000000), orderedInterval (52362474170 / 1000000000000) (52362474171 / 1000000000000)))) (orderedInterval (5155661262 / 1000000000000) (5155661284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (139972694973489 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25397514814 / 1000000000000) (25397514815 / 1000000000000), orderedInterval (81292786341 / 1000000000000) (81292786342 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (568981234015569 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-41683194218 / 1000000000000) (-41683194201 / 1000000000000), orderedInterval (-7201707348 / 1000000000000) (-7201707331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (380053095419871 / 1600000000000) 3 (IntervalRat.scale (765 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22190570435 / 1000000000000) (-22190569233 / 1000000000000), orderedInterval (46819695314 / 1000000000000) (46819696516 / 1000000000000)))) (orderedInterval (13109177884 / 1000000000000) (13109178497 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate318_chunkChecks3 :
    compactCertificate318.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate318.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate318_chunkChecks3_0
    compactCertificate318_chunkChecks3_1 compactCertificate318_chunkChecks3_2

theorem compactCertificate318_chunkChecks4_0 :
    compactCertificate318.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (765 / 4) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-22339522954 / 1000000000000) (-22339522953 / 1000000000000), orderedInterval (-53136375435 / 1000000000000) (-53136375434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (225398215028853 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19011799360 / 1000000000000) (-19011799359 / 1000000000000), orderedInterval (-64412374419 / 1000000000000) (-64412374418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (72889151641749 / 320000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36909138019 / 1000000000000) (36909175255 / 1000000000000), orderedInterval (-37931007961 / 1000000000000) (-37930970725 / 1000000000000)))) (orderedInterval (-4810424698 / 1000000000000) (-4810420239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (65770636994271 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-107838826226 / 1000000000000) (-107838826225 / 1000000000000), orderedInterval (-60795182092 / 1000000000000) (-60795182091 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (176669182371987 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71979172717 / 1000000000000) (-71979172716 / 1000000000000), orderedInterval (-23850140946 / 1000000000000) (-23850140945 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (479691197190279 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-38798358715 / 1000000000000) (-38798292306 / 1000000000000), orderedInterval (24926702623 / 1000000000000) (24926769031 / 1000000000000)))) (orderedInterval (16293294854 / 1000000000000) (16293323637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (353338364744127 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (53173262972 / 1000000000000) (53173263485 / 1000000000000), orderedInterval (-7560984141 / 1000000000000) (-7560983628 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (605451310448571 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (33137175566 / 1000000000000) (33137258465 / 1000000000000), orderedInterval (-24215955290 / 1000000000000) (-24215872391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (445972694973489 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (4003152557 / 1000000000000) (4003152563 / 1000000000000), orderedInterval (-47630242296 / 1000000000000) (-47630242290 / 1000000000000)))) (orderedInterval (-15204515447 / 1000000000000) (-15204475940 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate318_chunkChecks4_1 :
    compactCertificate318.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (684236801114847 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (35622556413 / 1000000000000) (35622556415 / 1000000000000), orderedInterval (14780173865 / 1000000000000) (14780173867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (395044301313063 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (24265838652 / 1000000000000) (24265840799 / 1000000000000), orderedInterval (-44654025716 / 1000000000000) (-44654023570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (701013045045267 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-29970507252 / 1000000000000) (-29970460504 / 1000000000000), orderedInterval (23588326934 / 1000000000000) (23588373681 / 1000000000000)))) (orderedInterval (-270552533554 / 1000000000000) (-270552347587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (654977319701823 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38879736362 / 1000000000000) (38879738595 / 1000000000000), orderedInterval (-6644496209 / 1000000000000) (-6644493975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (467422720885359 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32026121457 / 1000000000000) (-32026121456 / 1000000000000), orderedInterval (-33908308102 / 1000000000000) (-33908308101 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (530007547115961 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36139330651 / 1000000000000) (-36139231060 / 1000000000000), orderedInterval (24869717243 / 1000000000000) (24869816834 / 1000000000000)))) (orderedInterval (-29688782307 / 1000000000000) (-29688776712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (441865036720809 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (22614590923 / 1000000000000) (22614590924 / 1000000000000), orderedInterval (42312240669 / 1000000000000) (42312240670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (390401160364989 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-13063131583 / 1000000000000) (-13063131475 / 1000000000000), orderedInterval (49407422862 / 1000000000000) (49407422970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (113153472889911 / 320000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24318415704 / 1000000000000) (24318419761 / 1000000000000), orderedInterval (-34804879041 / 1000000000000) (-34804874984 / 1000000000000)))) (orderedInterval (10287077664 / 1000000000000) (10287078998 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate318_chunkChecks4_2 :
    compactCertificate318.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (312988460954517 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (56967187602 / 1000000000000) (56967187742 / 1000000000000), orderedInterval (-3168075205 / 1000000000000) (-3168075064 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (265323784603437 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6653977864 / 1000000000000) (-6653977862 / 1000000000000), orderedInterval (-61581828298 / 1000000000000) (-61581828297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (166027305026511 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60304302328 / 1000000000000) (-60304302327 / 1000000000000), orderedInterval (-49694058561 / 1000000000000) (-49694058560 / 1000000000000)))) (orderedInterval (-9899395962 / 1000000000000) (-9899395896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (89290036825137 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (4352564878 / 1000000000000) (4352564883 / 1000000000000), orderedInterval (106681132277 / 1000000000000) (106681132282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (242439819366411 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (64710008125 / 1000000000000) (64710008145 / 1000000000000), orderedInterval (3529822230 / 1000000000000) (3529822250 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (331030846527147 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18182520071 / 1000000000000) (18182520072 / 1000000000000), orderedInterval (52362474170 / 1000000000000) (52362474171 / 1000000000000)))) (orderedInterval (-2541386530 / 1000000000000) (-2541386506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (139972694973489 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25397514814 / 1000000000000) (25397514815 / 1000000000000), orderedInterval (81292786341 / 1000000000000) (81292786342 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (568981234015569 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-41683194218 / 1000000000000) (-41683194201 / 1000000000000), orderedInterval (-7201707348 / 1000000000000) (-7201707331 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (380053095419871 / 1600000000000) 4 (IntervalRat.scale (765 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-22190570435 / 1000000000000) (-22190569233 / 1000000000000), orderedInterval (46819695314 / 1000000000000) (46819696516 / 1000000000000)))) (orderedInterval (50336670605 / 1000000000000) (50336671436 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate318_chunkChecks4 :
    compactCertificate318.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate318.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate318_chunkChecks4_0
    compactCertificate318_chunkChecks4_1 compactCertificate318_chunkChecks4_2

theorem compactCertificate318_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate318.chunkCheck r b = true :=
  compactCertificate318.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate318_chunkChecks0
    · exact compactCertificate318_chunkChecks1
    · exact compactCertificate318_chunkChecks2
    · exact compactCertificate318_chunkChecks3
    · exact compactCertificate318_chunkChecks4)

theorem compactCertificate318_coefficient0 :
    compactCertificate318.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate318_coefficient1 :
    compactCertificate318.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate318_coefficient2 :
    compactCertificate318.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate318_coefficient3 :
    compactCertificate318.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate318_coefficient4 :
    compactCertificate318.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate318_coefficients : ∀ r : Fin 5,
    compactCertificate318.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate318_coefficient0
  · exact compactCertificate318_coefficient1
  · exact compactCertificate318_coefficient2
  · exact compactCertificate318_coefficient3
  · exact compactCertificate318_coefficient4

theorem compactCertificate318_lower : (1 : ℚ) ≤ compactCertificate318.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate318, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate318_proves {t : ℝ} (ht : t ∈ compactCertificate318.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate318.proves compactCertificate318_states compactCertificate318_chunks
    compactCertificate318_coefficients compactCertificate318_lower ht

end Erdos232
