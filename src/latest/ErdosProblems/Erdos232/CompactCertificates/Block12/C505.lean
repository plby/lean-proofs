/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate505 : CompactCertificate where
  left := 376
  right := 377
  center := 753 / 2
  grid := fun i =>
    match i.val with
    | 0 => 120
    | 1 => 88
    | 2 => 143
    | 3 => 26
    | 4 => 69
    | 5 => 188
    | 6 => 138
    | 7 => 237
    | 8 => 175
    | 9 => 268
    | 10 => 155
    | 11 => 275
    | 12 => 257
    | 13 => 183
    | 14 => 208
    | 15 => 173
    | 16 => 153
    | 17 => 222
    | 18 => 123
    | 19 => 104
    | 20 => 65
    | 21 => 35
    | 22 => 95
    | 23 => 130
    | 24 => 55
    | 25 => 223
    | _ => 149
  point := fun i =>
    match i.val with
    | 0 => 753 / 2
    | 1 => 1109312783769453 / 4000000000000
    | 2 => 358728962001549 / 800000000000
    | 3 => 323694703638471 / 4000000000000
    | 4 => 869489505399387 / 4000000000000
    | 5 => 2360833146956079 / 4000000000000
    | 6 => 1738979010799527 / 4000000000000
    | 7 => 2979770174952771 / 4000000000000
    | 8 => 2194885224281289 / 4000000000000
    | 9 => 3367518374114247 / 4000000000000
    | 10 => 1944237639795663 / 4000000000000
    | 11 => 3450083809928667 / 4000000000000
    | 12 => 3223515828336423 / 4000000000000
    | 13 => 2300452998867159 / 4000000000000
    | 14 => 2608468516198161 / 4000000000000
    | 15 => 2174669102292609 / 4000000000000
    | 16 => 1921386102972789 / 4000000000000
    | 17 => 556892582262111 / 800000000000
    | 18 => 1540394190187917 / 4000000000000
    | 19 => 1305809214420837 / 4000000000000
    | 20 => 817114775718711 / 4000000000000
    | 21 => 439447043982537 / 4000000000000
    | 22 => 1193184209038611 / 4000000000000
    | 23 => 1629191028986547 / 4000000000000
    | 24 => 688885224281289 / 4000000000000
    | 25 => 2800280190939369 / 4000000000000
    | _ => 1870457391184071 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (11913933008 / 1000000000000) (11913933009 / 1000000000000), orderedInterval (39340862518 / 1000000000000) (39340862519 / 1000000000000))
    | 1 => (orderedInterval (47750073061 / 1000000000000) (47750073419 / 1000000000000), orderedInterval (-4019705336 / 1000000000000) (-4019704978 / 1000000000000))
    | 2 => (orderedInterval (1936895363 / 1000000000000) (1936895364 / 1000000000000), orderedInterval (-37631569516 / 1000000000000) (-37631569515 / 1000000000000))
    | 3 => (orderedInterval (2316492148 / 1000000000000) (2316492154 / 1000000000000), orderedInterval (88651915395 / 1000000000000) (88651915400 / 1000000000000))
    | 4 => (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000))
    | 5 => (orderedInterval (12000428540 / 1000000000000) (12000428541 / 1000000000000), orderedInterval (30561483563 / 1000000000000) (30561483564 / 1000000000000))
    | 6 => (orderedInterval (34952236289 / 1000000000000) (34952268306 / 1000000000000), orderedInterval (-15618800574 / 1000000000000) (-15618768557 / 1000000000000))
    | 7 => (orderedInterval (-26920220508 / 1000000000000) (-26920220497 / 1000000000000), orderedInterval (-11378890889 / 1000000000000) (-11378890878 / 1000000000000))
    | 8 => (orderedInterval (9158722276 / 1000000000000) (9158722289 / 1000000000000), orderedInterval (-32815448887 / 1000000000000) (-32815448873 / 1000000000000))
    | 9 => (orderedInterval (18091206793 / 1000000000000) (18091206794 / 1000000000000), orderedInterval (20699081152 / 1000000000000) (20699081153 / 1000000000000))
    | 10 => (orderedInterval (3696212884 / 1000000000000) (3696212886 / 1000000000000), orderedInterval (-36005132858 / 1000000000000) (-36005132856 / 1000000000000))
    | 11 => (orderedInterval (16044712242 / 1000000000000) (16044712487 / 1000000000000), orderedInterval (-21933242273 / 1000000000000) (-21933242028 / 1000000000000))
    | 12 => (orderedInterval (18640697299 / 1000000000000) (18640698422 / 1000000000000), orderedInterval (-21047104277 / 1000000000000) (-21047103154 / 1000000000000))
    | 13 => (orderedInterval (-27759905284 / 1000000000000) (-27759905283 / 1000000000000), orderedInterval (-18315284913 / 1000000000000) (-18315284912 / 1000000000000))
    | 14 => (orderedInterval (-16302897394 / 1000000000000) (-16302897060 / 1000000000000), orderedInterval (26666786318 / 1000000000000) (26666786653 / 1000000000000))
    | 15 => (orderedInterval (-27971624253 / 1000000000000) (-27971624252 / 1000000000000), orderedInterval (-19686230888 / 1000000000000) (-19686230887 / 1000000000000))
    | 16 => (orderedInterval (-16422036692 / 1000000000000) (-16422036691 / 1000000000000), orderedInterval (-32473697571 / 1000000000000) (-32473697570 / 1000000000000))
    | 17 => (orderedInterval (-15356323223 / 1000000000000) (-15356323022 / 1000000000000), orderedInterval (26063188563 / 1000000000000) (26063188764 / 1000000000000))
    | 18 => (orderedInterval (20634113755 / 1000000000000) (20634115182 / 1000000000000), orderedInterval (-35060613520 / 1000000000000) (-35060612093 / 1000000000000))
    | 19 => (orderedInterval (21622779502 / 1000000000000) (21622779503 / 1000000000000), orderedInterval (38471068093 / 1000000000000) (38471068094 / 1000000000000))
    | 20 => (orderedInterval (-42304937197 / 1000000000000) (-42304937196 / 1000000000000), orderedInterval (-36320601588 / 1000000000000) (-36320601587 / 1000000000000))
    | 21 => (orderedInterval (-48471319082 / 1000000000000) (-48471319081 / 1000000000000), orderedInterval (-58475888558 / 1000000000000) (-58475888557 / 1000000000000))
    | 22 => (orderedInterval (-27206753806 / 1000000000000) (-27206753805 / 1000000000000), orderedInterval (-37290453999 / 1000000000000) (-37290453998 / 1000000000000))
    | 23 => (orderedInterval (-12593825973 / 1000000000000) (-12593825888 / 1000000000000), orderedInterval (37491176722 / 1000000000000) (37491176808 / 1000000000000))
    | 24 => (orderedInterval (-13172130677 / 1000000000000) (-13172130676 / 1000000000000), orderedInterval (-59316881707 / 1000000000000) (-59316881706 / 1000000000000))
    | 25 => (orderedInterval (-8336755243 / 1000000000000) (-8336755242 / 1000000000000), orderedInterval (-28974462051 / 1000000000000) (-28974462050 / 1000000000000))
    | _ => (orderedInterval (-10980514222 / 1000000000000) (-10980514221 / 1000000000000), orderedInterval (-35213952428 / 1000000000000) (-35213952427 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5280863234 / 1000000000000) (5280863264 / 1000000000000)
      | 1 => orderedInterval (-2820990987 / 1000000000000) (-2820990942 / 1000000000000)
      | 2 => orderedInterval (1051675544 / 1000000000000) (1051675567 / 1000000000000)
      | 3 => orderedInterval (-659879750 / 1000000000000) (-659879565 / 1000000000000)
      | 4 => orderedInterval (-2879076308 / 1000000000000) (-2879076241 / 1000000000000)
      | 5 => orderedInterval (223588953 / 1000000000000) (223588995 / 1000000000000)
      | 6 => orderedInterval (-5900336176 / 1000000000000) (-5900335853 / 1000000000000)
      | 7 => orderedInterval (2477441009 / 1000000000000) (2477441061 / 1000000000000)
      | _ => orderedInterval (2659456463 / 1000000000000) (2659456567 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12935710904 / 1000000000000) (12935710937 / 1000000000000)
      | 1 => orderedInterval (-3818116721 / 1000000000000) (-3818116669 / 1000000000000)
      | 2 => orderedInterval (-461433151 / 1000000000000) (-461433113 / 1000000000000)
      | 3 => orderedInterval (-18811035490 / 1000000000000) (-18811035100 / 1000000000000)
      | 4 => orderedInterval (-2066034080 / 1000000000000) (-2066033960 / 1000000000000)
      | 5 => orderedInterval (3276488816 / 1000000000000) (3276488878 / 1000000000000)
      | 6 => orderedInterval (3204389255 / 1000000000000) (3204389576 / 1000000000000)
      | 7 => orderedInterval (-2122966350 / 1000000000000) (-2122966301 / 1000000000000)
      | _ => orderedInterval (12428006310 / 1000000000000) (12428006457 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-5159258354 / 1000000000000) (-5159258318 / 1000000000000)
      | 1 => orderedInterval (2755332467 / 1000000000000) (2755332538 / 1000000000000)
      | 2 => orderedInterval (-3719549245 / 1000000000000) (-3719549177 / 1000000000000)
      | 3 => orderedInterval (3696145298 / 1000000000000) (3696146145 / 1000000000000)
      | 4 => orderedInterval (7424895482 / 1000000000000) (7424895701 / 1000000000000)
      | 5 => orderedInterval (479205427 / 1000000000000) (479205523 / 1000000000000)
      | 6 => orderedInterval (4768691630 / 1000000000000) (4768691953 / 1000000000000)
      | 7 => orderedInterval (-1587557753 / 1000000000000) (-1587557704 / 1000000000000)
      | _ => orderedInterval (-5540760696 / 1000000000000) (-5540760479 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-11833920001 / 1000000000000) (-11833919959 / 1000000000000)
      | 1 => orderedInterval (8440272038 / 1000000000000) (8440272145 / 1000000000000)
      | 2 => orderedInterval (-253554463 / 1000000000000) (-253554340 / 1000000000000)
      | 3 => orderedInterval (84338111213 / 1000000000000) (84338113087 / 1000000000000)
      | 4 => orderedInterval (3128394553 / 1000000000000) (3128394966 / 1000000000000)
      | 5 => orderedInterval (-7393766202 / 1000000000000) (-7393766049 / 1000000000000)
      | 6 => orderedInterval (-4403199469 / 1000000000000) (-4403199142 / 1000000000000)
      | 7 => orderedInterval (3194265171 / 1000000000000) (3194265222 / 1000000000000)
      | _ => orderedInterval (-27772113883 / 1000000000000) (-27772113548 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (5144767141 / 1000000000000) (5144767189 / 1000000000000)
      | 1 => orderedInterval (-5412594755 / 1000000000000) (-5412594590 / 1000000000000)
      | 2 => orderedInterval (13725659586 / 1000000000000) (13725659813 / 1000000000000)
      | 3 => orderedInterval (-17229452584 / 1000000000000) (-17229448392 / 1000000000000)
      | 4 => orderedInterval (-20629732082 / 1000000000000) (-20629731285 / 1000000000000)
      | 5 => orderedInterval (-3469918791 / 1000000000000) (-3469918541 / 1000000000000)
      | 6 => orderedInterval (-4398793956 / 1000000000000) (-4398793625 / 1000000000000)
      | 7 => orderedInterval (1554608119 / 1000000000000) (1554608171 / 1000000000000)
      | _ => orderedInterval (13158576084 / 1000000000000) (13158576621 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-567258018 / 1000000000000) (-567257147 / 1000000000000)
    | 1 => orderedInterval (4565009493 / 1000000000000) (4565010705 / 1000000000000)
    | 2 => orderedInterval (3117144256 / 1000000000000) (3117146182 / 1000000000000)
    | 3 => orderedInterval (47444488957 / 1000000000000) (47444492382 / 1000000000000)
    | _ => orderedInterval (-17556881238 / 1000000000000) (-17556874639 / 1000000000000)

theorem compactCertificate505_stateChecks0 :
    compactCertificate505.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (753 / 2)) (orderedInterval (11913933008 / 1000000000000) (11913933009 / 1000000000000), orderedInterval (39340862518 / 1000000000000) (39340862519 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1109312783769453 / 4000000000000)) (orderedInterval (47750073061 / 1000000000000) (47750073419 / 1000000000000), orderedInterval (-4019705336 / 1000000000000) (-4019704978 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (358728962001549 / 800000000000)) (orderedInterval (1936895363 / 1000000000000) (1936895364 / 1000000000000), orderedInterval (-37631569516 / 1000000000000) (-37631569515 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_stateChecks1 :
    compactCertificate505.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (323694703638471 / 4000000000000)) (orderedInterval (2316492148 / 1000000000000) (2316492154 / 1000000000000), orderedInterval (88651915395 / 1000000000000) (88651915400 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (869489505399387 / 4000000000000)) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2360833146956079 / 4000000000000)) (orderedInterval (12000428540 / 1000000000000) (12000428541 / 1000000000000), orderedInterval (30561483563 / 1000000000000) (30561483564 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_stateChecks2 :
    compactCertificate505.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1738979010799527 / 4000000000000)) (orderedInterval (34952236289 / 1000000000000) (34952268306 / 1000000000000), orderedInterval (-15618800574 / 1000000000000) (-15618768557 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2979770174952771 / 4000000000000)) (orderedInterval (-26920220508 / 1000000000000) (-26920220497 / 1000000000000), orderedInterval (-11378890889 / 1000000000000) (-11378890878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2194885224281289 / 4000000000000)) (orderedInterval (9158722276 / 1000000000000) (9158722289 / 1000000000000), orderedInterval (-32815448887 / 1000000000000) (-32815448873 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_stateChecks3 :
    compactCertificate505.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 268 12 (3367518374114247 / 4000000000000)) (orderedInterval (18091206793 / 1000000000000) (18091206794 / 1000000000000), orderedInterval (20699081152 / 1000000000000) (20699081153 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1944237639795663 / 4000000000000)) (orderedInterval (3696212884 / 1000000000000) (3696212886 / 1000000000000), orderedInterval (-36005132858 / 1000000000000) (-36005132856 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 275 12 (3450083809928667 / 4000000000000)) (orderedInterval (16044712242 / 1000000000000) (16044712487 / 1000000000000), orderedInterval (-21933242273 / 1000000000000) (-21933242028 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_stateChecks4 :
    compactCertificate505.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (3223515828336423 / 4000000000000)) (orderedInterval (18640697299 / 1000000000000) (18640698422 / 1000000000000), orderedInterval (-21047104277 / 1000000000000) (-21047103154 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2300452998867159 / 4000000000000)) (orderedInterval (-27759905284 / 1000000000000) (-27759905283 / 1000000000000), orderedInterval (-18315284913 / 1000000000000) (-18315284912 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2608468516198161 / 4000000000000)) (orderedInterval (-16302897394 / 1000000000000) (-16302897060 / 1000000000000), orderedInterval (26666786318 / 1000000000000) (26666786653 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_stateChecks5 :
    compactCertificate505.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2174669102292609 / 4000000000000)) (orderedInterval (-27971624253 / 1000000000000) (-27971624252 / 1000000000000), orderedInterval (-19686230888 / 1000000000000) (-19686230887 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1921386102972789 / 4000000000000)) (orderedInterval (-16422036692 / 1000000000000) (-16422036691 / 1000000000000), orderedInterval (-32473697571 / 1000000000000) (-32473697570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (556892582262111 / 800000000000)) (orderedInterval (-15356323223 / 1000000000000) (-15356323022 / 1000000000000), orderedInterval (26063188563 / 1000000000000) (26063188764 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_stateChecks6 :
    compactCertificate505.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1540394190187917 / 4000000000000)) (orderedInterval (20634113755 / 1000000000000) (20634115182 / 1000000000000), orderedInterval (-35060613520 / 1000000000000) (-35060612093 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1305809214420837 / 4000000000000)) (orderedInterval (21622779502 / 1000000000000) (21622779503 / 1000000000000), orderedInterval (38471068093 / 1000000000000) (38471068094 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (817114775718711 / 4000000000000)) (orderedInterval (-42304937197 / 1000000000000) (-42304937196 / 1000000000000), orderedInterval (-36320601588 / 1000000000000) (-36320601587 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_stateChecks7 :
    compactCertificate505.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (439447043982537 / 4000000000000)) (orderedInterval (-48471319082 / 1000000000000) (-48471319081 / 1000000000000), orderedInterval (-58475888558 / 1000000000000) (-58475888557 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1193184209038611 / 4000000000000)) (orderedInterval (-27206753806 / 1000000000000) (-27206753805 / 1000000000000), orderedInterval (-37290453999 / 1000000000000) (-37290453998 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1629191028986547 / 4000000000000)) (orderedInterval (-12593825973 / 1000000000000) (-12593825888 / 1000000000000), orderedInterval (37491176722 / 1000000000000) (37491176808 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_stateChecks8 :
    compactCertificate505.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (688885224281289 / 4000000000000)) (orderedInterval (-13172130677 / 1000000000000) (-13172130676 / 1000000000000), orderedInterval (-59316881707 / 1000000000000) (-59316881706 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2800280190939369 / 4000000000000)) (orderedInterval (-8336755243 / 1000000000000) (-8336755242 / 1000000000000), orderedInterval (-28974462051 / 1000000000000) (-28974462050 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1870457391184071 / 4000000000000)) (orderedInterval (-10980514222 / 1000000000000) (-10980514221 / 1000000000000), orderedInterval (-35213952428 / 1000000000000) (-35213952427 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_states : ∀ j,
    BesselStateValid (compactCertificate505.point j) (compactCertificate505.state j) :=
  compactCertificate505.statesValid_of_checks3 compactCertificate505_stateChecks0
    compactCertificate505_stateChecks1 compactCertificate505_stateChecks2
    compactCertificate505_stateChecks3 compactCertificate505_stateChecks4
    compactCertificate505_stateChecks5 compactCertificate505_stateChecks6
    compactCertificate505_stateChecks7 compactCertificate505_stateChecks8

theorem compactCertificate505_chunkChecks0_0 :
    compactCertificate505.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (753 / 2) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11913933008 / 1000000000000) (11913933009 / 1000000000000), orderedInterval (39340862518 / 1000000000000) (39340862519 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1109312783769453 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (47750073061 / 1000000000000) (47750073419 / 1000000000000), orderedInterval (-4019705336 / 1000000000000) (-4019704978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (358728962001549 / 800000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1936895363 / 1000000000000) (1936895364 / 1000000000000), orderedInterval (-37631569516 / 1000000000000) (-37631569515 / 1000000000000)))) (orderedInterval (5280863234 / 1000000000000) (5280863264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (323694703638471 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (2316492148 / 1000000000000) (2316492154 / 1000000000000), orderedInterval (88651915395 / 1000000000000) (88651915400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (869489505399387 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2360833146956079 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12000428540 / 1000000000000) (12000428541 / 1000000000000), orderedInterval (30561483563 / 1000000000000) (30561483564 / 1000000000000)))) (orderedInterval (-2820990987 / 1000000000000) (-2820990942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1738979010799527 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34952236289 / 1000000000000) (34952268306 / 1000000000000), orderedInterval (-15618800574 / 1000000000000) (-15618768557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2979770174952771 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26920220508 / 1000000000000) (-26920220497 / 1000000000000), orderedInterval (-11378890889 / 1000000000000) (-11378890878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2194885224281289 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (9158722276 / 1000000000000) (9158722289 / 1000000000000), orderedInterval (-32815448887 / 1000000000000) (-32815448873 / 1000000000000)))) (orderedInterval (1051675544 / 1000000000000) (1051675567 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_chunkChecks0_1 :
    compactCertificate505.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3367518374114247 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18091206793 / 1000000000000) (18091206794 / 1000000000000), orderedInterval (20699081152 / 1000000000000) (20699081153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1944237639795663 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3696212884 / 1000000000000) (3696212886 / 1000000000000), orderedInterval (-36005132858 / 1000000000000) (-36005132856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3450083809928667 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16044712242 / 1000000000000) (16044712487 / 1000000000000), orderedInterval (-21933242273 / 1000000000000) (-21933242028 / 1000000000000)))) (orderedInterval (-659879750 / 1000000000000) (-659879565 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3223515828336423 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18640697299 / 1000000000000) (18640698422 / 1000000000000), orderedInterval (-21047104277 / 1000000000000) (-21047103154 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2300452998867159 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27759905284 / 1000000000000) (-27759905283 / 1000000000000), orderedInterval (-18315284913 / 1000000000000) (-18315284912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2608468516198161 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16302897394 / 1000000000000) (-16302897060 / 1000000000000), orderedInterval (26666786318 / 1000000000000) (26666786653 / 1000000000000)))) (orderedInterval (-2879076308 / 1000000000000) (-2879076241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2174669102292609 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27971624253 / 1000000000000) (-27971624252 / 1000000000000), orderedInterval (-19686230888 / 1000000000000) (-19686230887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1921386102972789 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-16422036692 / 1000000000000) (-16422036691 / 1000000000000), orderedInterval (-32473697571 / 1000000000000) (-32473697570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (556892582262111 / 800000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-15356323223 / 1000000000000) (-15356323022 / 1000000000000), orderedInterval (26063188563 / 1000000000000) (26063188764 / 1000000000000)))) (orderedInterval (223588953 / 1000000000000) (223588995 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_chunkChecks0_2 :
    compactCertificate505.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1540394190187917 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20634113755 / 1000000000000) (20634115182 / 1000000000000), orderedInterval (-35060613520 / 1000000000000) (-35060612093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1305809214420837 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21622779502 / 1000000000000) (21622779503 / 1000000000000), orderedInterval (38471068093 / 1000000000000) (38471068094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (817114775718711 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-42304937197 / 1000000000000) (-42304937196 / 1000000000000), orderedInterval (-36320601588 / 1000000000000) (-36320601587 / 1000000000000)))) (orderedInterval (-5900336176 / 1000000000000) (-5900335853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (439447043982537 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48471319082 / 1000000000000) (-48471319081 / 1000000000000), orderedInterval (-58475888558 / 1000000000000) (-58475888557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1193184209038611 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-27206753806 / 1000000000000) (-27206753805 / 1000000000000), orderedInterval (-37290453999 / 1000000000000) (-37290453998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1629191028986547 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-12593825973 / 1000000000000) (-12593825888 / 1000000000000), orderedInterval (37491176722 / 1000000000000) (37491176808 / 1000000000000)))) (orderedInterval (2477441009 / 1000000000000) (2477441061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (688885224281289 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13172130677 / 1000000000000) (-13172130676 / 1000000000000), orderedInterval (-59316881707 / 1000000000000) (-59316881706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2800280190939369 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8336755243 / 1000000000000) (-8336755242 / 1000000000000), orderedInterval (-28974462051 / 1000000000000) (-28974462050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1870457391184071 / 4000000000000) 0 (IntervalRat.scale (753 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10980514222 / 1000000000000) (-10980514221 / 1000000000000), orderedInterval (-35213952428 / 1000000000000) (-35213952427 / 1000000000000)))) (orderedInterval (2659456463 / 1000000000000) (2659456567 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_chunkChecks0 :
    compactCertificate505.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate505.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate505_chunkChecks0_0
    compactCertificate505_chunkChecks0_1 compactCertificate505_chunkChecks0_2

theorem compactCertificate505_chunkChecks1_0 :
    compactCertificate505.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (753 / 2) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11913933008 / 1000000000000) (11913933009 / 1000000000000), orderedInterval (39340862518 / 1000000000000) (39340862519 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1109312783769453 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (47750073061 / 1000000000000) (47750073419 / 1000000000000), orderedInterval (-4019705336 / 1000000000000) (-4019704978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (358728962001549 / 800000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1936895363 / 1000000000000) (1936895364 / 1000000000000), orderedInterval (-37631569516 / 1000000000000) (-37631569515 / 1000000000000)))) (orderedInterval (12935710904 / 1000000000000) (12935710937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (323694703638471 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (2316492148 / 1000000000000) (2316492154 / 1000000000000), orderedInterval (88651915395 / 1000000000000) (88651915400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (869489505399387 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2360833146956079 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12000428540 / 1000000000000) (12000428541 / 1000000000000), orderedInterval (30561483563 / 1000000000000) (30561483564 / 1000000000000)))) (orderedInterval (-3818116721 / 1000000000000) (-3818116669 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1738979010799527 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34952236289 / 1000000000000) (34952268306 / 1000000000000), orderedInterval (-15618800574 / 1000000000000) (-15618768557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2979770174952771 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26920220508 / 1000000000000) (-26920220497 / 1000000000000), orderedInterval (-11378890889 / 1000000000000) (-11378890878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2194885224281289 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (9158722276 / 1000000000000) (9158722289 / 1000000000000), orderedInterval (-32815448887 / 1000000000000) (-32815448873 / 1000000000000)))) (orderedInterval (-461433151 / 1000000000000) (-461433113 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_chunkChecks1_1 :
    compactCertificate505.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3367518374114247 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18091206793 / 1000000000000) (18091206794 / 1000000000000), orderedInterval (20699081152 / 1000000000000) (20699081153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1944237639795663 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3696212884 / 1000000000000) (3696212886 / 1000000000000), orderedInterval (-36005132858 / 1000000000000) (-36005132856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3450083809928667 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16044712242 / 1000000000000) (16044712487 / 1000000000000), orderedInterval (-21933242273 / 1000000000000) (-21933242028 / 1000000000000)))) (orderedInterval (-18811035490 / 1000000000000) (-18811035100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3223515828336423 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18640697299 / 1000000000000) (18640698422 / 1000000000000), orderedInterval (-21047104277 / 1000000000000) (-21047103154 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2300452998867159 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27759905284 / 1000000000000) (-27759905283 / 1000000000000), orderedInterval (-18315284913 / 1000000000000) (-18315284912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2608468516198161 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16302897394 / 1000000000000) (-16302897060 / 1000000000000), orderedInterval (26666786318 / 1000000000000) (26666786653 / 1000000000000)))) (orderedInterval (-2066034080 / 1000000000000) (-2066033960 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2174669102292609 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27971624253 / 1000000000000) (-27971624252 / 1000000000000), orderedInterval (-19686230888 / 1000000000000) (-19686230887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1921386102972789 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-16422036692 / 1000000000000) (-16422036691 / 1000000000000), orderedInterval (-32473697571 / 1000000000000) (-32473697570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (556892582262111 / 800000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-15356323223 / 1000000000000) (-15356323022 / 1000000000000), orderedInterval (26063188563 / 1000000000000) (26063188764 / 1000000000000)))) (orderedInterval (3276488816 / 1000000000000) (3276488878 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_chunkChecks1_2 :
    compactCertificate505.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1540394190187917 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20634113755 / 1000000000000) (20634115182 / 1000000000000), orderedInterval (-35060613520 / 1000000000000) (-35060612093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1305809214420837 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21622779502 / 1000000000000) (21622779503 / 1000000000000), orderedInterval (38471068093 / 1000000000000) (38471068094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (817114775718711 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-42304937197 / 1000000000000) (-42304937196 / 1000000000000), orderedInterval (-36320601588 / 1000000000000) (-36320601587 / 1000000000000)))) (orderedInterval (3204389255 / 1000000000000) (3204389576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (439447043982537 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48471319082 / 1000000000000) (-48471319081 / 1000000000000), orderedInterval (-58475888558 / 1000000000000) (-58475888557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1193184209038611 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-27206753806 / 1000000000000) (-27206753805 / 1000000000000), orderedInterval (-37290453999 / 1000000000000) (-37290453998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1629191028986547 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-12593825973 / 1000000000000) (-12593825888 / 1000000000000), orderedInterval (37491176722 / 1000000000000) (37491176808 / 1000000000000)))) (orderedInterval (-2122966350 / 1000000000000) (-2122966301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (688885224281289 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13172130677 / 1000000000000) (-13172130676 / 1000000000000), orderedInterval (-59316881707 / 1000000000000) (-59316881706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2800280190939369 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8336755243 / 1000000000000) (-8336755242 / 1000000000000), orderedInterval (-28974462051 / 1000000000000) (-28974462050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1870457391184071 / 4000000000000) 1 (IntervalRat.scale (753 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10980514222 / 1000000000000) (-10980514221 / 1000000000000), orderedInterval (-35213952428 / 1000000000000) (-35213952427 / 1000000000000)))) (orderedInterval (12428006310 / 1000000000000) (12428006457 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_chunkChecks1 :
    compactCertificate505.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate505.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate505_chunkChecks1_0
    compactCertificate505_chunkChecks1_1 compactCertificate505_chunkChecks1_2

theorem compactCertificate505_chunkChecks2_0 :
    compactCertificate505.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (753 / 2) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11913933008 / 1000000000000) (11913933009 / 1000000000000), orderedInterval (39340862518 / 1000000000000) (39340862519 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1109312783769453 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (47750073061 / 1000000000000) (47750073419 / 1000000000000), orderedInterval (-4019705336 / 1000000000000) (-4019704978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (358728962001549 / 800000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1936895363 / 1000000000000) (1936895364 / 1000000000000), orderedInterval (-37631569516 / 1000000000000) (-37631569515 / 1000000000000)))) (orderedInterval (-5159258354 / 1000000000000) (-5159258318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (323694703638471 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (2316492148 / 1000000000000) (2316492154 / 1000000000000), orderedInterval (88651915395 / 1000000000000) (88651915400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (869489505399387 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2360833146956079 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12000428540 / 1000000000000) (12000428541 / 1000000000000), orderedInterval (30561483563 / 1000000000000) (30561483564 / 1000000000000)))) (orderedInterval (2755332467 / 1000000000000) (2755332538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1738979010799527 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34952236289 / 1000000000000) (34952268306 / 1000000000000), orderedInterval (-15618800574 / 1000000000000) (-15618768557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2979770174952771 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26920220508 / 1000000000000) (-26920220497 / 1000000000000), orderedInterval (-11378890889 / 1000000000000) (-11378890878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2194885224281289 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (9158722276 / 1000000000000) (9158722289 / 1000000000000), orderedInterval (-32815448887 / 1000000000000) (-32815448873 / 1000000000000)))) (orderedInterval (-3719549245 / 1000000000000) (-3719549177 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_chunkChecks2_1 :
    compactCertificate505.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3367518374114247 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18091206793 / 1000000000000) (18091206794 / 1000000000000), orderedInterval (20699081152 / 1000000000000) (20699081153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1944237639795663 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3696212884 / 1000000000000) (3696212886 / 1000000000000), orderedInterval (-36005132858 / 1000000000000) (-36005132856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3450083809928667 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16044712242 / 1000000000000) (16044712487 / 1000000000000), orderedInterval (-21933242273 / 1000000000000) (-21933242028 / 1000000000000)))) (orderedInterval (3696145298 / 1000000000000) (3696146145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3223515828336423 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18640697299 / 1000000000000) (18640698422 / 1000000000000), orderedInterval (-21047104277 / 1000000000000) (-21047103154 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2300452998867159 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27759905284 / 1000000000000) (-27759905283 / 1000000000000), orderedInterval (-18315284913 / 1000000000000) (-18315284912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2608468516198161 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16302897394 / 1000000000000) (-16302897060 / 1000000000000), orderedInterval (26666786318 / 1000000000000) (26666786653 / 1000000000000)))) (orderedInterval (7424895482 / 1000000000000) (7424895701 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2174669102292609 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27971624253 / 1000000000000) (-27971624252 / 1000000000000), orderedInterval (-19686230888 / 1000000000000) (-19686230887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1921386102972789 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-16422036692 / 1000000000000) (-16422036691 / 1000000000000), orderedInterval (-32473697571 / 1000000000000) (-32473697570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (556892582262111 / 800000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-15356323223 / 1000000000000) (-15356323022 / 1000000000000), orderedInterval (26063188563 / 1000000000000) (26063188764 / 1000000000000)))) (orderedInterval (479205427 / 1000000000000) (479205523 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_chunkChecks2_2 :
    compactCertificate505.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1540394190187917 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20634113755 / 1000000000000) (20634115182 / 1000000000000), orderedInterval (-35060613520 / 1000000000000) (-35060612093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1305809214420837 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21622779502 / 1000000000000) (21622779503 / 1000000000000), orderedInterval (38471068093 / 1000000000000) (38471068094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (817114775718711 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-42304937197 / 1000000000000) (-42304937196 / 1000000000000), orderedInterval (-36320601588 / 1000000000000) (-36320601587 / 1000000000000)))) (orderedInterval (4768691630 / 1000000000000) (4768691953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (439447043982537 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48471319082 / 1000000000000) (-48471319081 / 1000000000000), orderedInterval (-58475888558 / 1000000000000) (-58475888557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1193184209038611 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-27206753806 / 1000000000000) (-27206753805 / 1000000000000), orderedInterval (-37290453999 / 1000000000000) (-37290453998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1629191028986547 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-12593825973 / 1000000000000) (-12593825888 / 1000000000000), orderedInterval (37491176722 / 1000000000000) (37491176808 / 1000000000000)))) (orderedInterval (-1587557753 / 1000000000000) (-1587557704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (688885224281289 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13172130677 / 1000000000000) (-13172130676 / 1000000000000), orderedInterval (-59316881707 / 1000000000000) (-59316881706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2800280190939369 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8336755243 / 1000000000000) (-8336755242 / 1000000000000), orderedInterval (-28974462051 / 1000000000000) (-28974462050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1870457391184071 / 4000000000000) 2 (IntervalRat.scale (753 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10980514222 / 1000000000000) (-10980514221 / 1000000000000), orderedInterval (-35213952428 / 1000000000000) (-35213952427 / 1000000000000)))) (orderedInterval (-5540760696 / 1000000000000) (-5540760479 / 1000000000000))) = true
  rfl'

theorem compactCertificate505_chunkChecks2 :
    compactCertificate505.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate505.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate505_chunkChecks2_0
    compactCertificate505_chunkChecks2_1 compactCertificate505_chunkChecks2_2

theorem compactCertificate505_chunkChecks3_0 :
    compactCertificate505.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (753 / 2) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11913933008 / 1000000000000) (11913933009 / 1000000000000), orderedInterval (39340862518 / 1000000000000) (39340862519 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1109312783769453 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (47750073061 / 1000000000000) (47750073419 / 1000000000000), orderedInterval (-4019705336 / 1000000000000) (-4019704978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (358728962001549 / 800000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1936895363 / 1000000000000) (1936895364 / 1000000000000), orderedInterval (-37631569516 / 1000000000000) (-37631569515 / 1000000000000)))) (orderedInterval (-11833920001 / 1000000000000) (-11833919959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (323694703638471 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (2316492148 / 1000000000000) (2316492154 / 1000000000000), orderedInterval (88651915395 / 1000000000000) (88651915400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (869489505399387 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2360833146956079 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12000428540 / 1000000000000) (12000428541 / 1000000000000), orderedInterval (30561483563 / 1000000000000) (30561483564 / 1000000000000)))) (orderedInterval (8440272038 / 1000000000000) (8440272145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1738979010799527 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34952236289 / 1000000000000) (34952268306 / 1000000000000), orderedInterval (-15618800574 / 1000000000000) (-15618768557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2979770174952771 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26920220508 / 1000000000000) (-26920220497 / 1000000000000), orderedInterval (-11378890889 / 1000000000000) (-11378890878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2194885224281289 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (9158722276 / 1000000000000) (9158722289 / 1000000000000), orderedInterval (-32815448887 / 1000000000000) (-32815448873 / 1000000000000)))) (orderedInterval (-253554463 / 1000000000000) (-253554340 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate505_chunkChecks3_1 :
    compactCertificate505.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3367518374114247 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18091206793 / 1000000000000) (18091206794 / 1000000000000), orderedInterval (20699081152 / 1000000000000) (20699081153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1944237639795663 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3696212884 / 1000000000000) (3696212886 / 1000000000000), orderedInterval (-36005132858 / 1000000000000) (-36005132856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3450083809928667 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16044712242 / 1000000000000) (16044712487 / 1000000000000), orderedInterval (-21933242273 / 1000000000000) (-21933242028 / 1000000000000)))) (orderedInterval (84338111213 / 1000000000000) (84338113087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3223515828336423 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18640697299 / 1000000000000) (18640698422 / 1000000000000), orderedInterval (-21047104277 / 1000000000000) (-21047103154 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2300452998867159 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27759905284 / 1000000000000) (-27759905283 / 1000000000000), orderedInterval (-18315284913 / 1000000000000) (-18315284912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2608468516198161 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16302897394 / 1000000000000) (-16302897060 / 1000000000000), orderedInterval (26666786318 / 1000000000000) (26666786653 / 1000000000000)))) (orderedInterval (3128394553 / 1000000000000) (3128394966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2174669102292609 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27971624253 / 1000000000000) (-27971624252 / 1000000000000), orderedInterval (-19686230888 / 1000000000000) (-19686230887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1921386102972789 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-16422036692 / 1000000000000) (-16422036691 / 1000000000000), orderedInterval (-32473697571 / 1000000000000) (-32473697570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (556892582262111 / 800000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-15356323223 / 1000000000000) (-15356323022 / 1000000000000), orderedInterval (26063188563 / 1000000000000) (26063188764 / 1000000000000)))) (orderedInterval (-7393766202 / 1000000000000) (-7393766049 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate505_chunkChecks3_2 :
    compactCertificate505.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1540394190187917 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20634113755 / 1000000000000) (20634115182 / 1000000000000), orderedInterval (-35060613520 / 1000000000000) (-35060612093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1305809214420837 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21622779502 / 1000000000000) (21622779503 / 1000000000000), orderedInterval (38471068093 / 1000000000000) (38471068094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (817114775718711 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-42304937197 / 1000000000000) (-42304937196 / 1000000000000), orderedInterval (-36320601588 / 1000000000000) (-36320601587 / 1000000000000)))) (orderedInterval (-4403199469 / 1000000000000) (-4403199142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (439447043982537 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48471319082 / 1000000000000) (-48471319081 / 1000000000000), orderedInterval (-58475888558 / 1000000000000) (-58475888557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1193184209038611 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-27206753806 / 1000000000000) (-27206753805 / 1000000000000), orderedInterval (-37290453999 / 1000000000000) (-37290453998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1629191028986547 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-12593825973 / 1000000000000) (-12593825888 / 1000000000000), orderedInterval (37491176722 / 1000000000000) (37491176808 / 1000000000000)))) (orderedInterval (3194265171 / 1000000000000) (3194265222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (688885224281289 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13172130677 / 1000000000000) (-13172130676 / 1000000000000), orderedInterval (-59316881707 / 1000000000000) (-59316881706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2800280190939369 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8336755243 / 1000000000000) (-8336755242 / 1000000000000), orderedInterval (-28974462051 / 1000000000000) (-28974462050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1870457391184071 / 4000000000000) 3 (IntervalRat.scale (753 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10980514222 / 1000000000000) (-10980514221 / 1000000000000), orderedInterval (-35213952428 / 1000000000000) (-35213952427 / 1000000000000)))) (orderedInterval (-27772113883 / 1000000000000) (-27772113548 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate505_chunkChecks3 :
    compactCertificate505.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate505.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate505_chunkChecks3_0
    compactCertificate505_chunkChecks3_1 compactCertificate505_chunkChecks3_2

theorem compactCertificate505_chunkChecks4_0 :
    compactCertificate505.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (753 / 2) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (11913933008 / 1000000000000) (11913933009 / 1000000000000), orderedInterval (39340862518 / 1000000000000) (39340862519 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1109312783769453 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (47750073061 / 1000000000000) (47750073419 / 1000000000000), orderedInterval (-4019705336 / 1000000000000) (-4019704978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (358728962001549 / 800000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1936895363 / 1000000000000) (1936895364 / 1000000000000), orderedInterval (-37631569516 / 1000000000000) (-37631569515 / 1000000000000)))) (orderedInterval (5144767141 / 1000000000000) (5144767189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (323694703638471 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (2316492148 / 1000000000000) (2316492154 / 1000000000000), orderedInterval (88651915395 / 1000000000000) (88651915400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (869489505399387 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53208973089 / 1000000000000) (-53208973084 / 1000000000000), orderedInterval (-9752015828 / 1000000000000) (-9752015823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2360833146956079 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12000428540 / 1000000000000) (12000428541 / 1000000000000), orderedInterval (30561483563 / 1000000000000) (30561483564 / 1000000000000)))) (orderedInterval (-5412594755 / 1000000000000) (-5412594590 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1738979010799527 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34952236289 / 1000000000000) (34952268306 / 1000000000000), orderedInterval (-15618800574 / 1000000000000) (-15618768557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2979770174952771 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26920220508 / 1000000000000) (-26920220497 / 1000000000000), orderedInterval (-11378890889 / 1000000000000) (-11378890878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2194885224281289 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (9158722276 / 1000000000000) (9158722289 / 1000000000000), orderedInterval (-32815448887 / 1000000000000) (-32815448873 / 1000000000000)))) (orderedInterval (13725659586 / 1000000000000) (13725659813 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate505_chunkChecks4_1 :
    compactCertificate505.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3367518374114247 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (18091206793 / 1000000000000) (18091206794 / 1000000000000), orderedInterval (20699081152 / 1000000000000) (20699081153 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1944237639795663 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3696212884 / 1000000000000) (3696212886 / 1000000000000), orderedInterval (-36005132858 / 1000000000000) (-36005132856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3450083809928667 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16044712242 / 1000000000000) (16044712487 / 1000000000000), orderedInterval (-21933242273 / 1000000000000) (-21933242028 / 1000000000000)))) (orderedInterval (-17229452584 / 1000000000000) (-17229448392 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3223515828336423 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18640697299 / 1000000000000) (18640698422 / 1000000000000), orderedInterval (-21047104277 / 1000000000000) (-21047103154 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2300452998867159 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27759905284 / 1000000000000) (-27759905283 / 1000000000000), orderedInterval (-18315284913 / 1000000000000) (-18315284912 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2608468516198161 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16302897394 / 1000000000000) (-16302897060 / 1000000000000), orderedInterval (26666786318 / 1000000000000) (26666786653 / 1000000000000)))) (orderedInterval (-20629732082 / 1000000000000) (-20629731285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2174669102292609 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27971624253 / 1000000000000) (-27971624252 / 1000000000000), orderedInterval (-19686230888 / 1000000000000) (-19686230887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1921386102972789 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-16422036692 / 1000000000000) (-16422036691 / 1000000000000), orderedInterval (-32473697571 / 1000000000000) (-32473697570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (556892582262111 / 800000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-15356323223 / 1000000000000) (-15356323022 / 1000000000000), orderedInterval (26063188563 / 1000000000000) (26063188764 / 1000000000000)))) (orderedInterval (-3469918791 / 1000000000000) (-3469918541 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate505_chunkChecks4_2 :
    compactCertificate505.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1540394190187917 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20634113755 / 1000000000000) (20634115182 / 1000000000000), orderedInterval (-35060613520 / 1000000000000) (-35060612093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1305809214420837 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21622779502 / 1000000000000) (21622779503 / 1000000000000), orderedInterval (38471068093 / 1000000000000) (38471068094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (817114775718711 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-42304937197 / 1000000000000) (-42304937196 / 1000000000000), orderedInterval (-36320601588 / 1000000000000) (-36320601587 / 1000000000000)))) (orderedInterval (-4398793956 / 1000000000000) (-4398793625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (439447043982537 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-48471319082 / 1000000000000) (-48471319081 / 1000000000000), orderedInterval (-58475888558 / 1000000000000) (-58475888557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1193184209038611 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-27206753806 / 1000000000000) (-27206753805 / 1000000000000), orderedInterval (-37290453999 / 1000000000000) (-37290453998 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1629191028986547 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-12593825973 / 1000000000000) (-12593825888 / 1000000000000), orderedInterval (37491176722 / 1000000000000) (37491176808 / 1000000000000)))) (orderedInterval (1554608119 / 1000000000000) (1554608171 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (688885224281289 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13172130677 / 1000000000000) (-13172130676 / 1000000000000), orderedInterval (-59316881707 / 1000000000000) (-59316881706 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2800280190939369 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-8336755243 / 1000000000000) (-8336755242 / 1000000000000), orderedInterval (-28974462051 / 1000000000000) (-28974462050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1870457391184071 / 4000000000000) 4 (IntervalRat.scale (753 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-10980514222 / 1000000000000) (-10980514221 / 1000000000000), orderedInterval (-35213952428 / 1000000000000) (-35213952427 / 1000000000000)))) (orderedInterval (13158576084 / 1000000000000) (13158576621 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate505_chunkChecks4 :
    compactCertificate505.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate505.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate505_chunkChecks4_0
    compactCertificate505_chunkChecks4_1 compactCertificate505_chunkChecks4_2

theorem compactCertificate505_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate505.chunkCheck r b = true :=
  compactCertificate505.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate505_chunkChecks0
    · exact compactCertificate505_chunkChecks1
    · exact compactCertificate505_chunkChecks2
    · exact compactCertificate505_chunkChecks3
    · exact compactCertificate505_chunkChecks4)

theorem compactCertificate505_coefficient0 :
    compactCertificate505.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate505_coefficient1 :
    compactCertificate505.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate505_coefficient2 :
    compactCertificate505.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate505_coefficient3 :
    compactCertificate505.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate505_coefficient4 :
    compactCertificate505.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate505_coefficients : ∀ r : Fin 5,
    compactCertificate505.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate505_coefficient0
  · exact compactCertificate505_coefficient1
  · exact compactCertificate505_coefficient2
  · exact compactCertificate505_coefficient3
  · exact compactCertificate505_coefficient4

theorem compactCertificate505_lower : (1 : ℚ) ≤ compactCertificate505.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate505, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate505_proves {t : ℝ} (ht : t ∈ compactCertificate505.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate505.proves compactCertificate505_states compactCertificate505_chunks
    compactCertificate505_coefficients compactCertificate505_lower ht

end Erdos232
