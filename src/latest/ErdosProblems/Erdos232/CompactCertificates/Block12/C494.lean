/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate494 : CompactCertificate where
  left := 365
  right := 366
  center := 731 / 2
  grid := fun i =>
    match i.val with
    | 0 => 116
    | 1 => 86
    | 2 => 139
    | 3 => 25
    | 4 => 67
    | 5 => 182
    | 6 => 134
    | 7 => 230
    | 8 => 170
    | 9 => 260
    | 10 => 150
    | 11 => 267
    | 12 => 249
    | 13 => 178
    | 14 => 202
    | 15 => 168
    | 16 => 149
    | 17 => 215
    | 18 => 119
    | 19 => 101
    | 20 => 63
    | 21 => 34
    | 22 => 92
    | 23 => 126
    | 24 => 53
    | 25 => 216
    | _ => 145
  point := fun i =>
    match i.val with
    | 0 => 731 / 2
    | 1 => 1076902582915631 / 4000000000000
    | 2 => 348248168955023 / 800000000000
    | 3 => 314237487861517 / 4000000000000
    | 4 => 844086093555049 / 4000000000000
    | 5 => 2291857942131333 / 4000000000000
    | 6 => 1688172187110829 / 4000000000000
    | 7 => 2892711816587617 / 4000000000000
    | 8 => 2130758431540003 / 4000000000000
    | 9 => 3269131383104269 / 4000000000000
    | 10 => 1887433884051301 / 4000000000000
    | 11 => 3349284548549609 / 4000000000000
    | 12 => 3129336083019821 / 4000000000000
    | 13 => 2233241888674493 / 4000000000000
    | 14 => 2532258280665147 / 4000000000000
    | 15 => 2111132953221643 / 4000000000000
    | 16 => 1865249988410503 / 4000000000000
    | 17 => 540622148251797 / 800000000000
    | 18 => 1495389313449359 / 4000000000000
    | 19 => 1267658081994199 / 4000000000000
    | 20 => 793241568459997 / 4000000000000
    | 21 => 426607953720099 / 4000000000000
    | 22 => 1158323581417297 / 4000000000000
    | 23 => 1581591822296369 / 4000000000000
    | 24 => 668758431540003 / 4000000000000
    | 25 => 2718465895852163 / 4000000000000
    | _ => 1815809233672717 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (39997732212 / 1000000000000) (39997738693 / 1000000000000), orderedInterval (-11969313480 / 1000000000000) (-11969306999 / 1000000000000))
    | 1 => (orderedInterval (-8053771238 / 1000000000000) (-8053771215 / 1000000000000), orderedInterval (47970909394 / 1000000000000) (47970909417 / 1000000000000))
    | 2 => (orderedInterval (21150879533 / 1000000000000) (21150881506 / 1000000000000), orderedInterval (-31884794644 / 1000000000000) (-31884792672 / 1000000000000))
    | 3 => (orderedInterval (-64786584540 / 1000000000000) (-64786584539 / 1000000000000), orderedInterval (-62088631375 / 1000000000000) (-62088631374 / 1000000000000))
    | 4 => (orderedInterval (-53202248676 / 1000000000000) (-53202248674 / 1000000000000), orderedInterval (-13525348220 / 1000000000000) (-13525348218 / 1000000000000))
    | 5 => (orderedInterval (30583670464 / 1000000000000) (30583725070 / 1000000000000), orderedInterval (-13283232391 / 1000000000000) (-13283177784 / 1000000000000))
    | 6 => (orderedInterval (37283324577 / 1000000000000) (37283332780 / 1000000000000), orderedInterval (-10924260918 / 1000000000000) (-10924252716 / 1000000000000))
    | 7 => (orderedInterval (29222352908 / 1000000000000) (29222353150 / 1000000000000), orderedInterval (5114236872 / 1000000000000) (5114237114 / 1000000000000))
    | 8 => (orderedInterval (-19404982662 / 1000000000000) (-19404981408 / 1000000000000), orderedInterval (28628551021 / 1000000000000) (28628552274 / 1000000000000))
    | 9 => (orderedInterval (26520793668 / 1000000000000) (26520793732 / 1000000000000), orderedInterval (8678260601 / 1000000000000) (8678260666 / 1000000000000))
    | 10 => (orderedInterval (36225643549 / 1000000000000) (36225643594 / 1000000000000), orderedInterval (6034280972 / 1000000000000) (6034281017 / 1000000000000))
    | 11 => (orderedInterval (17739209910 / 1000000000000) (17739210587 / 1000000000000), orderedInterval (-21120444687 / 1000000000000) (-21120444010 / 1000000000000))
    | 12 => (orderedInterval (-21668324897 / 1000000000000) (-21668324896 / 1000000000000), orderedInterval (-18539530465 / 1000000000000) (-18539530464 / 1000000000000))
    | 13 => (orderedInterval (-3634657765 / 1000000000000) (-3634657763 / 1000000000000), orderedInterval (33574834034 / 1000000000000) (33574834036 / 1000000000000))
    | 14 => (orderedInterval (-21660842055 / 1000000000000) (-21660837997 / 1000000000000), orderedInterval (23177932444 / 1000000000000) (23177936502 / 1000000000000))
    | 15 => (orderedInterval (24445888566 / 1000000000000) (24445888567 / 1000000000000), orderedInterval (24646923981 / 1000000000000) (24646923982 / 1000000000000))
    | 16 => (orderedInterval (31084945074 / 1000000000000) (31085038822 / 1000000000000), orderedInterval (-20006964132 / 1000000000000) (-20006870384 / 1000000000000))
    | 17 => (orderedInterval (-27633091295 / 1000000000000) (-27633091292 / 1000000000000), orderedInterval (-13338714108 / 1000000000000) (-13338714105 / 1000000000000))
    | 18 => (orderedInterval (-29105522794 / 1000000000000) (-29105522793 / 1000000000000), orderedInterval (-29214373651 / 1000000000000) (-29214373650 / 1000000000000))
    | 19 => (orderedInterval (-17398528288 / 1000000000000) (-17398528287 / 1000000000000), orderedInterval (-41277500303 / 1000000000000) (-41277500302 / 1000000000000))
    | 20 => (orderedInterval (-52274538297 / 1000000000000) (-52274538296 / 1000000000000), orderedInterval (-21721905451 / 1000000000000) (-21721905450 / 1000000000000))
    | 21 => (orderedInterval (45020333841 / 1000000000000) (45020333842 / 1000000000000), orderedInterval (62576858467 / 1000000000000) (62576858468 / 1000000000000))
    | 22 => (orderedInterval (45636902265 / 1000000000000) (45636902269 / 1000000000000), orderedInterval (10677034953 / 1000000000000) (10677034957 / 1000000000000))
    | 23 => (orderedInterval (13470765926 / 1000000000000) (13470765927 / 1000000000000), orderedInterval (37779962397 / 1000000000000) (37779962398 / 1000000000000))
    | 24 => (orderedInterval (-61392853431 / 1000000000000) (-61392853419 / 1000000000000), orderedInterval (-6035085395 / 1000000000000) (-6035085383 / 1000000000000))
    | 25 => (orderedInterval (29678114376 / 1000000000000) (29678134829 / 1000000000000), orderedInterval (-7501320092 / 1000000000000) (-7501299639 / 1000000000000))
    | _ => (orderedInterval (26693863262 / 1000000000000) (26693878802 / 1000000000000), orderedInterval (-26294038188 / 1000000000000) (-26294022648 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17019813035 / 1000000000000) (17019815745 / 1000000000000)
      | 1 => orderedInterval (-3413804540 / 1000000000000) (-3413800613 / 1000000000000)
      | 2 => orderedInterval (-1370314445 / 1000000000000) (-1370314386 / 1000000000000)
      | 3 => orderedInterval (493330388 / 1000000000000) (493330644 / 1000000000000)
      | 4 => orderedInterval (157092773 / 1000000000000) (157092837 / 1000000000000)
      | 5 => orderedInterval (-2204116728 / 1000000000000) (-2204111327 / 1000000000000)
      | 6 => orderedInterval (3936697244 / 1000000000000) (3936697336 / 1000000000000)
      | 7 => orderedInterval (-2899048136 / 1000000000000) (-2899048092 / 1000000000000)
      | _ => orderedInterval (-7794428993 / 1000000000000) (-7794424311 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-6643364291 / 1000000000000) (-6643361555 / 1000000000000)
      | 1 => orderedInterval (1339966117 / 1000000000000) (1339972253 / 1000000000000)
      | 2 => orderedInterval (696276168 / 1000000000000) (696276263 / 1000000000000)
      | 3 => orderedInterval (-9749040137 / 1000000000000) (-9749039586 / 1000000000000)
      | 4 => orderedInterval (5363029928 / 1000000000000) (5363030035 / 1000000000000)
      | 5 => orderedInterval (1240257913 / 1000000000000) (1240264809 / 1000000000000)
      | 6 => orderedInterval (6419893189 / 1000000000000) (6419893274 / 1000000000000)
      | 7 => orderedInterval (-3661342159 / 1000000000000) (-3661342119 / 1000000000000)
      | _ => orderedInterval (7246123094 / 1000000000000) (7246129954 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17555366151 / 1000000000000) (-17555363378 / 1000000000000)
      | 1 => orderedInterval (5954258424 / 1000000000000) (5954268049 / 1000000000000)
      | 2 => orderedInterval (4522845028 / 1000000000000) (4522845186 / 1000000000000)
      | 3 => orderedInterval (5880897473 / 1000000000000) (5880898684 / 1000000000000)
      | 4 => orderedInterval (-1333746956 / 1000000000000) (-1333746776 / 1000000000000)
      | 5 => orderedInterval (4722143511 / 1000000000000) (4722152338 / 1000000000000)
      | 6 => orderedInterval (-5125674308 / 1000000000000) (-5125674226 / 1000000000000)
      | 7 => orderedInterval (1938903747 / 1000000000000) (1938903787 / 1000000000000)
      | _ => orderedInterval (16136183643 / 1000000000000) (16136194126 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (7774492976 / 1000000000000) (7774495787 / 1000000000000)
      | 1 => orderedInterval (-3565666112 / 1000000000000) (-3565651028 / 1000000000000)
      | 2 => orderedInterval (-932408910 / 1000000000000) (-932408642 / 1000000000000)
      | 3 => orderedInterval (52360081339 / 1000000000000) (52360084044 / 1000000000000)
      | 4 => orderedInterval (-13985207915 / 1000000000000) (-13985207608 / 1000000000000)
      | 5 => orderedInterval (-1088936422 / 1000000000000) (-1088925141 / 1000000000000)
      | 6 => orderedInterval (-6394518313 / 1000000000000) (-6394518233 / 1000000000000)
      | 7 => orderedInterval (3809500730 / 1000000000000) (3809500771 / 1000000000000)
      | _ => orderedInterval (-13418088409 / 1000000000000) (-13418071768 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (18286247911 / 1000000000000) (18286250773 / 1000000000000)
      | 1 => orderedInterval (-13324574819 / 1000000000000) (-13324551135 / 1000000000000)
      | 2 => orderedInterval (-15924721372 / 1000000000000) (-15924720907 / 1000000000000)
      | 3 => orderedInterval (-41184183984 / 1000000000000) (-41184177901 / 1000000000000)
      | 4 => orderedInterval (7402789058 / 1000000000000) (7402789589 / 1000000000000)
      | 5 => orderedInterval (-11747799652 / 1000000000000) (-11747785192 / 1000000000000)
      | 6 => orderedInterval (5537745597 / 1000000000000) (5537745675 / 1000000000000)
      | 7 => orderedInterval (-1848755868 / 1000000000000) (-1848755825 / 1000000000000)
      | _ => orderedInterval (-40739121174 / 1000000000000) (-40739093725 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (3925220598 / 1000000000000) (3925237833 / 1000000000000)
    | 1 => orderedInterval (2251799822 / 1000000000000) (2251823328 / 1000000000000)
    | 2 => orderedInterval (15140444411 / 1000000000000) (15140477790 / 1000000000000)
    | 3 => orderedInterval (24559248964 / 1000000000000) (24559298182 / 1000000000000)
    | _ => orderedInterval (-93542374303 / 1000000000000) (-93542298648 / 1000000000000)

theorem compactCertificate494_stateChecks0 :
    compactCertificate494.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (731 / 2)) (orderedInterval (39997732212 / 1000000000000) (39997738693 / 1000000000000), orderedInterval (-11969313480 / 1000000000000) (-11969306999 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1076902582915631 / 4000000000000)) (orderedInterval (-8053771238 / 1000000000000) (-8053771215 / 1000000000000), orderedInterval (47970909394 / 1000000000000) (47970909417 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (348248168955023 / 800000000000)) (orderedInterval (21150879533 / 1000000000000) (21150881506 / 1000000000000), orderedInterval (-31884794644 / 1000000000000) (-31884792672 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_stateChecks1 :
    compactCertificate494.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (314237487861517 / 4000000000000)) (orderedInterval (-64786584540 / 1000000000000) (-64786584539 / 1000000000000), orderedInterval (-62088631375 / 1000000000000) (-62088631374 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (844086093555049 / 4000000000000)) (orderedInterval (-53202248676 / 1000000000000) (-53202248674 / 1000000000000), orderedInterval (-13525348220 / 1000000000000) (-13525348218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2291857942131333 / 4000000000000)) (orderedInterval (30583670464 / 1000000000000) (30583725070 / 1000000000000), orderedInterval (-13283232391 / 1000000000000) (-13283177784 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_stateChecks2 :
    compactCertificate494.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1688172187110829 / 4000000000000)) (orderedInterval (37283324577 / 1000000000000) (37283332780 / 1000000000000), orderedInterval (-10924260918 / 1000000000000) (-10924252716 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2892711816587617 / 4000000000000)) (orderedInterval (29222352908 / 1000000000000) (29222353150 / 1000000000000), orderedInterval (5114236872 / 1000000000000) (5114237114 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2130758431540003 / 4000000000000)) (orderedInterval (-19404982662 / 1000000000000) (-19404981408 / 1000000000000), orderedInterval (28628551021 / 1000000000000) (28628552274 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_stateChecks3 :
    compactCertificate494.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 260 12 (3269131383104269 / 4000000000000)) (orderedInterval (26520793668 / 1000000000000) (26520793732 / 1000000000000), orderedInterval (8678260601 / 1000000000000) (8678260666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1887433884051301 / 4000000000000)) (orderedInterval (36225643549 / 1000000000000) (36225643594 / 1000000000000), orderedInterval (6034280972 / 1000000000000) (6034281017 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3349284548549609 / 4000000000000)) (orderedInterval (17739209910 / 1000000000000) (17739210587 / 1000000000000), orderedInterval (-21120444687 / 1000000000000) (-21120444010 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_stateChecks4 :
    compactCertificate494.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (3129336083019821 / 4000000000000)) (orderedInterval (-21668324897 / 1000000000000) (-21668324896 / 1000000000000), orderedInterval (-18539530465 / 1000000000000) (-18539530464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2233241888674493 / 4000000000000)) (orderedInterval (-3634657765 / 1000000000000) (-3634657763 / 1000000000000), orderedInterval (33574834034 / 1000000000000) (33574834036 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2532258280665147 / 4000000000000)) (orderedInterval (-21660842055 / 1000000000000) (-21660837997 / 1000000000000), orderedInterval (23177932444 / 1000000000000) (23177936502 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_stateChecks5 :
    compactCertificate494.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2111132953221643 / 4000000000000)) (orderedInterval (24445888566 / 1000000000000) (24445888567 / 1000000000000), orderedInterval (24646923981 / 1000000000000) (24646923982 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1865249988410503 / 4000000000000)) (orderedInterval (31084945074 / 1000000000000) (31085038822 / 1000000000000), orderedInterval (-20006964132 / 1000000000000) (-20006870384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (540622148251797 / 800000000000)) (orderedInterval (-27633091295 / 1000000000000) (-27633091292 / 1000000000000), orderedInterval (-13338714108 / 1000000000000) (-13338714105 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_stateChecks6 :
    compactCertificate494.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1495389313449359 / 4000000000000)) (orderedInterval (-29105522794 / 1000000000000) (-29105522793 / 1000000000000), orderedInterval (-29214373651 / 1000000000000) (-29214373650 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1267658081994199 / 4000000000000)) (orderedInterval (-17398528288 / 1000000000000) (-17398528287 / 1000000000000), orderedInterval (-41277500303 / 1000000000000) (-41277500302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (793241568459997 / 4000000000000)) (orderedInterval (-52274538297 / 1000000000000) (-52274538296 / 1000000000000), orderedInterval (-21721905451 / 1000000000000) (-21721905450 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_stateChecks7 :
    compactCertificate494.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (426607953720099 / 4000000000000)) (orderedInterval (45020333841 / 1000000000000) (45020333842 / 1000000000000), orderedInterval (62576858467 / 1000000000000) (62576858468 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1158323581417297 / 4000000000000)) (orderedInterval (45636902265 / 1000000000000) (45636902269 / 1000000000000), orderedInterval (10677034953 / 1000000000000) (10677034957 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1581591822296369 / 4000000000000)) (orderedInterval (13470765926 / 1000000000000) (13470765927 / 1000000000000), orderedInterval (37779962397 / 1000000000000) (37779962398 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_stateChecks8 :
    compactCertificate494.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (668758431540003 / 4000000000000)) (orderedInterval (-61392853431 / 1000000000000) (-61392853419 / 1000000000000), orderedInterval (-6035085395 / 1000000000000) (-6035085383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2718465895852163 / 4000000000000)) (orderedInterval (29678114376 / 1000000000000) (29678134829 / 1000000000000), orderedInterval (-7501320092 / 1000000000000) (-7501299639 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1815809233672717 / 4000000000000)) (orderedInterval (26693863262 / 1000000000000) (26693878802 / 1000000000000), orderedInterval (-26294038188 / 1000000000000) (-26294022648 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_states : ∀ j,
    BesselStateValid (compactCertificate494.point j) (compactCertificate494.state j) :=
  compactCertificate494.statesValid_of_checks3 compactCertificate494_stateChecks0
    compactCertificate494_stateChecks1 compactCertificate494_stateChecks2
    compactCertificate494_stateChecks3 compactCertificate494_stateChecks4
    compactCertificate494_stateChecks5 compactCertificate494_stateChecks6
    compactCertificate494_stateChecks7 compactCertificate494_stateChecks8

theorem compactCertificate494_chunkChecks0_0 :
    compactCertificate494.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (731 / 2) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39997732212 / 1000000000000) (39997738693 / 1000000000000), orderedInterval (-11969313480 / 1000000000000) (-11969306999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1076902582915631 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8053771238 / 1000000000000) (-8053771215 / 1000000000000), orderedInterval (47970909394 / 1000000000000) (47970909417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (348248168955023 / 800000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21150879533 / 1000000000000) (21150881506 / 1000000000000), orderedInterval (-31884794644 / 1000000000000) (-31884792672 / 1000000000000)))) (orderedInterval (17019813035 / 1000000000000) (17019815745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (314237487861517 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64786584540 / 1000000000000) (-64786584539 / 1000000000000), orderedInterval (-62088631375 / 1000000000000) (-62088631374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (844086093555049 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53202248676 / 1000000000000) (-53202248674 / 1000000000000), orderedInterval (-13525348220 / 1000000000000) (-13525348218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2291857942131333 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30583670464 / 1000000000000) (30583725070 / 1000000000000), orderedInterval (-13283232391 / 1000000000000) (-13283177784 / 1000000000000)))) (orderedInterval (-3413804540 / 1000000000000) (-3413800613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1688172187110829 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37283324577 / 1000000000000) (37283332780 / 1000000000000), orderedInterval (-10924260918 / 1000000000000) (-10924252716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2892711816587617 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29222352908 / 1000000000000) (29222353150 / 1000000000000), orderedInterval (5114236872 / 1000000000000) (5114237114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2130758431540003 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19404982662 / 1000000000000) (-19404981408 / 1000000000000), orderedInterval (28628551021 / 1000000000000) (28628552274 / 1000000000000)))) (orderedInterval (-1370314445 / 1000000000000) (-1370314386 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_chunkChecks0_1 :
    compactCertificate494.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3269131383104269 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26520793668 / 1000000000000) (26520793732 / 1000000000000), orderedInterval (8678260601 / 1000000000000) (8678260666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1887433884051301 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36225643549 / 1000000000000) (36225643594 / 1000000000000), orderedInterval (6034280972 / 1000000000000) (6034281017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3349284548549609 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17739209910 / 1000000000000) (17739210587 / 1000000000000), orderedInterval (-21120444687 / 1000000000000) (-21120444010 / 1000000000000)))) (orderedInterval (493330388 / 1000000000000) (493330644 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3129336083019821 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21668324897 / 1000000000000) (-21668324896 / 1000000000000), orderedInterval (-18539530465 / 1000000000000) (-18539530464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2233241888674493 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3634657765 / 1000000000000) (-3634657763 / 1000000000000), orderedInterval (33574834034 / 1000000000000) (33574834036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2532258280665147 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21660842055 / 1000000000000) (-21660837997 / 1000000000000), orderedInterval (23177932444 / 1000000000000) (23177936502 / 1000000000000)))) (orderedInterval (157092773 / 1000000000000) (157092837 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2111132953221643 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24445888566 / 1000000000000) (24445888567 / 1000000000000), orderedInterval (24646923981 / 1000000000000) (24646923982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1865249988410503 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31084945074 / 1000000000000) (31085038822 / 1000000000000), orderedInterval (-20006964132 / 1000000000000) (-20006870384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (540622148251797 / 800000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27633091295 / 1000000000000) (-27633091292 / 1000000000000), orderedInterval (-13338714108 / 1000000000000) (-13338714105 / 1000000000000)))) (orderedInterval (-2204116728 / 1000000000000) (-2204111327 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_chunkChecks0_2 :
    compactCertificate494.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1495389313449359 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29105522794 / 1000000000000) (-29105522793 / 1000000000000), orderedInterval (-29214373651 / 1000000000000) (-29214373650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1267658081994199 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17398528288 / 1000000000000) (-17398528287 / 1000000000000), orderedInterval (-41277500303 / 1000000000000) (-41277500302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (793241568459997 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52274538297 / 1000000000000) (-52274538296 / 1000000000000), orderedInterval (-21721905451 / 1000000000000) (-21721905450 / 1000000000000)))) (orderedInterval (3936697244 / 1000000000000) (3936697336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (426607953720099 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (45020333841 / 1000000000000) (45020333842 / 1000000000000), orderedInterval (62576858467 / 1000000000000) (62576858468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1158323581417297 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45636902265 / 1000000000000) (45636902269 / 1000000000000), orderedInterval (10677034953 / 1000000000000) (10677034957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1581591822296369 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13470765926 / 1000000000000) (13470765927 / 1000000000000), orderedInterval (37779962397 / 1000000000000) (37779962398 / 1000000000000)))) (orderedInterval (-2899048136 / 1000000000000) (-2899048092 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (668758431540003 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61392853431 / 1000000000000) (-61392853419 / 1000000000000), orderedInterval (-6035085395 / 1000000000000) (-6035085383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2718465895852163 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29678114376 / 1000000000000) (29678134829 / 1000000000000), orderedInterval (-7501320092 / 1000000000000) (-7501299639 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1815809233672717 / 4000000000000) 0 (IntervalRat.scale (731 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26693863262 / 1000000000000) (26693878802 / 1000000000000), orderedInterval (-26294038188 / 1000000000000) (-26294022648 / 1000000000000)))) (orderedInterval (-7794428993 / 1000000000000) (-7794424311 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_chunkChecks0 :
    compactCertificate494.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate494.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate494_chunkChecks0_0
    compactCertificate494_chunkChecks0_1 compactCertificate494_chunkChecks0_2

theorem compactCertificate494_chunkChecks1_0 :
    compactCertificate494.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (731 / 2) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39997732212 / 1000000000000) (39997738693 / 1000000000000), orderedInterval (-11969313480 / 1000000000000) (-11969306999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1076902582915631 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8053771238 / 1000000000000) (-8053771215 / 1000000000000), orderedInterval (47970909394 / 1000000000000) (47970909417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (348248168955023 / 800000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21150879533 / 1000000000000) (21150881506 / 1000000000000), orderedInterval (-31884794644 / 1000000000000) (-31884792672 / 1000000000000)))) (orderedInterval (-6643364291 / 1000000000000) (-6643361555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (314237487861517 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64786584540 / 1000000000000) (-64786584539 / 1000000000000), orderedInterval (-62088631375 / 1000000000000) (-62088631374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (844086093555049 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53202248676 / 1000000000000) (-53202248674 / 1000000000000), orderedInterval (-13525348220 / 1000000000000) (-13525348218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2291857942131333 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30583670464 / 1000000000000) (30583725070 / 1000000000000), orderedInterval (-13283232391 / 1000000000000) (-13283177784 / 1000000000000)))) (orderedInterval (1339966117 / 1000000000000) (1339972253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1688172187110829 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37283324577 / 1000000000000) (37283332780 / 1000000000000), orderedInterval (-10924260918 / 1000000000000) (-10924252716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2892711816587617 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29222352908 / 1000000000000) (29222353150 / 1000000000000), orderedInterval (5114236872 / 1000000000000) (5114237114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2130758431540003 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19404982662 / 1000000000000) (-19404981408 / 1000000000000), orderedInterval (28628551021 / 1000000000000) (28628552274 / 1000000000000)))) (orderedInterval (696276168 / 1000000000000) (696276263 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_chunkChecks1_1 :
    compactCertificate494.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3269131383104269 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26520793668 / 1000000000000) (26520793732 / 1000000000000), orderedInterval (8678260601 / 1000000000000) (8678260666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1887433884051301 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36225643549 / 1000000000000) (36225643594 / 1000000000000), orderedInterval (6034280972 / 1000000000000) (6034281017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3349284548549609 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17739209910 / 1000000000000) (17739210587 / 1000000000000), orderedInterval (-21120444687 / 1000000000000) (-21120444010 / 1000000000000)))) (orderedInterval (-9749040137 / 1000000000000) (-9749039586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3129336083019821 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21668324897 / 1000000000000) (-21668324896 / 1000000000000), orderedInterval (-18539530465 / 1000000000000) (-18539530464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2233241888674493 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3634657765 / 1000000000000) (-3634657763 / 1000000000000), orderedInterval (33574834034 / 1000000000000) (33574834036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2532258280665147 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21660842055 / 1000000000000) (-21660837997 / 1000000000000), orderedInterval (23177932444 / 1000000000000) (23177936502 / 1000000000000)))) (orderedInterval (5363029928 / 1000000000000) (5363030035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2111132953221643 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24445888566 / 1000000000000) (24445888567 / 1000000000000), orderedInterval (24646923981 / 1000000000000) (24646923982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1865249988410503 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31084945074 / 1000000000000) (31085038822 / 1000000000000), orderedInterval (-20006964132 / 1000000000000) (-20006870384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (540622148251797 / 800000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27633091295 / 1000000000000) (-27633091292 / 1000000000000), orderedInterval (-13338714108 / 1000000000000) (-13338714105 / 1000000000000)))) (orderedInterval (1240257913 / 1000000000000) (1240264809 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_chunkChecks1_2 :
    compactCertificate494.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1495389313449359 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29105522794 / 1000000000000) (-29105522793 / 1000000000000), orderedInterval (-29214373651 / 1000000000000) (-29214373650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1267658081994199 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17398528288 / 1000000000000) (-17398528287 / 1000000000000), orderedInterval (-41277500303 / 1000000000000) (-41277500302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (793241568459997 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52274538297 / 1000000000000) (-52274538296 / 1000000000000), orderedInterval (-21721905451 / 1000000000000) (-21721905450 / 1000000000000)))) (orderedInterval (6419893189 / 1000000000000) (6419893274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (426607953720099 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (45020333841 / 1000000000000) (45020333842 / 1000000000000), orderedInterval (62576858467 / 1000000000000) (62576858468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1158323581417297 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45636902265 / 1000000000000) (45636902269 / 1000000000000), orderedInterval (10677034953 / 1000000000000) (10677034957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1581591822296369 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13470765926 / 1000000000000) (13470765927 / 1000000000000), orderedInterval (37779962397 / 1000000000000) (37779962398 / 1000000000000)))) (orderedInterval (-3661342159 / 1000000000000) (-3661342119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (668758431540003 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61392853431 / 1000000000000) (-61392853419 / 1000000000000), orderedInterval (-6035085395 / 1000000000000) (-6035085383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2718465895852163 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29678114376 / 1000000000000) (29678134829 / 1000000000000), orderedInterval (-7501320092 / 1000000000000) (-7501299639 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1815809233672717 / 4000000000000) 1 (IntervalRat.scale (731 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26693863262 / 1000000000000) (26693878802 / 1000000000000), orderedInterval (-26294038188 / 1000000000000) (-26294022648 / 1000000000000)))) (orderedInterval (7246123094 / 1000000000000) (7246129954 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_chunkChecks1 :
    compactCertificate494.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate494.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate494_chunkChecks1_0
    compactCertificate494_chunkChecks1_1 compactCertificate494_chunkChecks1_2

theorem compactCertificate494_chunkChecks2_0 :
    compactCertificate494.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (731 / 2) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39997732212 / 1000000000000) (39997738693 / 1000000000000), orderedInterval (-11969313480 / 1000000000000) (-11969306999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1076902582915631 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8053771238 / 1000000000000) (-8053771215 / 1000000000000), orderedInterval (47970909394 / 1000000000000) (47970909417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (348248168955023 / 800000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21150879533 / 1000000000000) (21150881506 / 1000000000000), orderedInterval (-31884794644 / 1000000000000) (-31884792672 / 1000000000000)))) (orderedInterval (-17555366151 / 1000000000000) (-17555363378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (314237487861517 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64786584540 / 1000000000000) (-64786584539 / 1000000000000), orderedInterval (-62088631375 / 1000000000000) (-62088631374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (844086093555049 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53202248676 / 1000000000000) (-53202248674 / 1000000000000), orderedInterval (-13525348220 / 1000000000000) (-13525348218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2291857942131333 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30583670464 / 1000000000000) (30583725070 / 1000000000000), orderedInterval (-13283232391 / 1000000000000) (-13283177784 / 1000000000000)))) (orderedInterval (5954258424 / 1000000000000) (5954268049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1688172187110829 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37283324577 / 1000000000000) (37283332780 / 1000000000000), orderedInterval (-10924260918 / 1000000000000) (-10924252716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2892711816587617 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29222352908 / 1000000000000) (29222353150 / 1000000000000), orderedInterval (5114236872 / 1000000000000) (5114237114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2130758431540003 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19404982662 / 1000000000000) (-19404981408 / 1000000000000), orderedInterval (28628551021 / 1000000000000) (28628552274 / 1000000000000)))) (orderedInterval (4522845028 / 1000000000000) (4522845186 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_chunkChecks2_1 :
    compactCertificate494.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3269131383104269 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26520793668 / 1000000000000) (26520793732 / 1000000000000), orderedInterval (8678260601 / 1000000000000) (8678260666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1887433884051301 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36225643549 / 1000000000000) (36225643594 / 1000000000000), orderedInterval (6034280972 / 1000000000000) (6034281017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3349284548549609 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17739209910 / 1000000000000) (17739210587 / 1000000000000), orderedInterval (-21120444687 / 1000000000000) (-21120444010 / 1000000000000)))) (orderedInterval (5880897473 / 1000000000000) (5880898684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3129336083019821 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21668324897 / 1000000000000) (-21668324896 / 1000000000000), orderedInterval (-18539530465 / 1000000000000) (-18539530464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2233241888674493 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3634657765 / 1000000000000) (-3634657763 / 1000000000000), orderedInterval (33574834034 / 1000000000000) (33574834036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2532258280665147 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21660842055 / 1000000000000) (-21660837997 / 1000000000000), orderedInterval (23177932444 / 1000000000000) (23177936502 / 1000000000000)))) (orderedInterval (-1333746956 / 1000000000000) (-1333746776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2111132953221643 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24445888566 / 1000000000000) (24445888567 / 1000000000000), orderedInterval (24646923981 / 1000000000000) (24646923982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1865249988410503 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31084945074 / 1000000000000) (31085038822 / 1000000000000), orderedInterval (-20006964132 / 1000000000000) (-20006870384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (540622148251797 / 800000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27633091295 / 1000000000000) (-27633091292 / 1000000000000), orderedInterval (-13338714108 / 1000000000000) (-13338714105 / 1000000000000)))) (orderedInterval (4722143511 / 1000000000000) (4722152338 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_chunkChecks2_2 :
    compactCertificate494.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1495389313449359 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29105522794 / 1000000000000) (-29105522793 / 1000000000000), orderedInterval (-29214373651 / 1000000000000) (-29214373650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1267658081994199 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17398528288 / 1000000000000) (-17398528287 / 1000000000000), orderedInterval (-41277500303 / 1000000000000) (-41277500302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (793241568459997 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52274538297 / 1000000000000) (-52274538296 / 1000000000000), orderedInterval (-21721905451 / 1000000000000) (-21721905450 / 1000000000000)))) (orderedInterval (-5125674308 / 1000000000000) (-5125674226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (426607953720099 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (45020333841 / 1000000000000) (45020333842 / 1000000000000), orderedInterval (62576858467 / 1000000000000) (62576858468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1158323581417297 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45636902265 / 1000000000000) (45636902269 / 1000000000000), orderedInterval (10677034953 / 1000000000000) (10677034957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1581591822296369 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13470765926 / 1000000000000) (13470765927 / 1000000000000), orderedInterval (37779962397 / 1000000000000) (37779962398 / 1000000000000)))) (orderedInterval (1938903747 / 1000000000000) (1938903787 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (668758431540003 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61392853431 / 1000000000000) (-61392853419 / 1000000000000), orderedInterval (-6035085395 / 1000000000000) (-6035085383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2718465895852163 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29678114376 / 1000000000000) (29678134829 / 1000000000000), orderedInterval (-7501320092 / 1000000000000) (-7501299639 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1815809233672717 / 4000000000000) 2 (IntervalRat.scale (731 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26693863262 / 1000000000000) (26693878802 / 1000000000000), orderedInterval (-26294038188 / 1000000000000) (-26294022648 / 1000000000000)))) (orderedInterval (16136183643 / 1000000000000) (16136194126 / 1000000000000))) = true
  rfl'

theorem compactCertificate494_chunkChecks2 :
    compactCertificate494.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate494.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate494_chunkChecks2_0
    compactCertificate494_chunkChecks2_1 compactCertificate494_chunkChecks2_2

theorem compactCertificate494_chunkChecks3_0 :
    compactCertificate494.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (731 / 2) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39997732212 / 1000000000000) (39997738693 / 1000000000000), orderedInterval (-11969313480 / 1000000000000) (-11969306999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1076902582915631 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8053771238 / 1000000000000) (-8053771215 / 1000000000000), orderedInterval (47970909394 / 1000000000000) (47970909417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (348248168955023 / 800000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21150879533 / 1000000000000) (21150881506 / 1000000000000), orderedInterval (-31884794644 / 1000000000000) (-31884792672 / 1000000000000)))) (orderedInterval (7774492976 / 1000000000000) (7774495787 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (314237487861517 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64786584540 / 1000000000000) (-64786584539 / 1000000000000), orderedInterval (-62088631375 / 1000000000000) (-62088631374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (844086093555049 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53202248676 / 1000000000000) (-53202248674 / 1000000000000), orderedInterval (-13525348220 / 1000000000000) (-13525348218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2291857942131333 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30583670464 / 1000000000000) (30583725070 / 1000000000000), orderedInterval (-13283232391 / 1000000000000) (-13283177784 / 1000000000000)))) (orderedInterval (-3565666112 / 1000000000000) (-3565651028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1688172187110829 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37283324577 / 1000000000000) (37283332780 / 1000000000000), orderedInterval (-10924260918 / 1000000000000) (-10924252716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2892711816587617 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29222352908 / 1000000000000) (29222353150 / 1000000000000), orderedInterval (5114236872 / 1000000000000) (5114237114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2130758431540003 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19404982662 / 1000000000000) (-19404981408 / 1000000000000), orderedInterval (28628551021 / 1000000000000) (28628552274 / 1000000000000)))) (orderedInterval (-932408910 / 1000000000000) (-932408642 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate494_chunkChecks3_1 :
    compactCertificate494.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3269131383104269 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26520793668 / 1000000000000) (26520793732 / 1000000000000), orderedInterval (8678260601 / 1000000000000) (8678260666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1887433884051301 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36225643549 / 1000000000000) (36225643594 / 1000000000000), orderedInterval (6034280972 / 1000000000000) (6034281017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3349284548549609 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17739209910 / 1000000000000) (17739210587 / 1000000000000), orderedInterval (-21120444687 / 1000000000000) (-21120444010 / 1000000000000)))) (orderedInterval (52360081339 / 1000000000000) (52360084044 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3129336083019821 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21668324897 / 1000000000000) (-21668324896 / 1000000000000), orderedInterval (-18539530465 / 1000000000000) (-18539530464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2233241888674493 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3634657765 / 1000000000000) (-3634657763 / 1000000000000), orderedInterval (33574834034 / 1000000000000) (33574834036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2532258280665147 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21660842055 / 1000000000000) (-21660837997 / 1000000000000), orderedInterval (23177932444 / 1000000000000) (23177936502 / 1000000000000)))) (orderedInterval (-13985207915 / 1000000000000) (-13985207608 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2111132953221643 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24445888566 / 1000000000000) (24445888567 / 1000000000000), orderedInterval (24646923981 / 1000000000000) (24646923982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1865249988410503 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31084945074 / 1000000000000) (31085038822 / 1000000000000), orderedInterval (-20006964132 / 1000000000000) (-20006870384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (540622148251797 / 800000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27633091295 / 1000000000000) (-27633091292 / 1000000000000), orderedInterval (-13338714108 / 1000000000000) (-13338714105 / 1000000000000)))) (orderedInterval (-1088936422 / 1000000000000) (-1088925141 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate494_chunkChecks3_2 :
    compactCertificate494.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1495389313449359 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29105522794 / 1000000000000) (-29105522793 / 1000000000000), orderedInterval (-29214373651 / 1000000000000) (-29214373650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1267658081994199 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17398528288 / 1000000000000) (-17398528287 / 1000000000000), orderedInterval (-41277500303 / 1000000000000) (-41277500302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (793241568459997 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52274538297 / 1000000000000) (-52274538296 / 1000000000000), orderedInterval (-21721905451 / 1000000000000) (-21721905450 / 1000000000000)))) (orderedInterval (-6394518313 / 1000000000000) (-6394518233 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (426607953720099 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (45020333841 / 1000000000000) (45020333842 / 1000000000000), orderedInterval (62576858467 / 1000000000000) (62576858468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1158323581417297 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45636902265 / 1000000000000) (45636902269 / 1000000000000), orderedInterval (10677034953 / 1000000000000) (10677034957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1581591822296369 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13470765926 / 1000000000000) (13470765927 / 1000000000000), orderedInterval (37779962397 / 1000000000000) (37779962398 / 1000000000000)))) (orderedInterval (3809500730 / 1000000000000) (3809500771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (668758431540003 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61392853431 / 1000000000000) (-61392853419 / 1000000000000), orderedInterval (-6035085395 / 1000000000000) (-6035085383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2718465895852163 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29678114376 / 1000000000000) (29678134829 / 1000000000000), orderedInterval (-7501320092 / 1000000000000) (-7501299639 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1815809233672717 / 4000000000000) 3 (IntervalRat.scale (731 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26693863262 / 1000000000000) (26693878802 / 1000000000000), orderedInterval (-26294038188 / 1000000000000) (-26294022648 / 1000000000000)))) (orderedInterval (-13418088409 / 1000000000000) (-13418071768 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate494_chunkChecks3 :
    compactCertificate494.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate494.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate494_chunkChecks3_0
    compactCertificate494_chunkChecks3_1 compactCertificate494_chunkChecks3_2

theorem compactCertificate494_chunkChecks4_0 :
    compactCertificate494.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (731 / 2) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39997732212 / 1000000000000) (39997738693 / 1000000000000), orderedInterval (-11969313480 / 1000000000000) (-11969306999 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1076902582915631 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8053771238 / 1000000000000) (-8053771215 / 1000000000000), orderedInterval (47970909394 / 1000000000000) (47970909417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (348248168955023 / 800000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (21150879533 / 1000000000000) (21150881506 / 1000000000000), orderedInterval (-31884794644 / 1000000000000) (-31884792672 / 1000000000000)))) (orderedInterval (18286247911 / 1000000000000) (18286250773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (314237487861517 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-64786584540 / 1000000000000) (-64786584539 / 1000000000000), orderedInterval (-62088631375 / 1000000000000) (-62088631374 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (844086093555049 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53202248676 / 1000000000000) (-53202248674 / 1000000000000), orderedInterval (-13525348220 / 1000000000000) (-13525348218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2291857942131333 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30583670464 / 1000000000000) (30583725070 / 1000000000000), orderedInterval (-13283232391 / 1000000000000) (-13283177784 / 1000000000000)))) (orderedInterval (-13324574819 / 1000000000000) (-13324551135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1688172187110829 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37283324577 / 1000000000000) (37283332780 / 1000000000000), orderedInterval (-10924260918 / 1000000000000) (-10924252716 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2892711816587617 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (29222352908 / 1000000000000) (29222353150 / 1000000000000), orderedInterval (5114236872 / 1000000000000) (5114237114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2130758431540003 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19404982662 / 1000000000000) (-19404981408 / 1000000000000), orderedInterval (28628551021 / 1000000000000) (28628552274 / 1000000000000)))) (orderedInterval (-15924721372 / 1000000000000) (-15924720907 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate494_chunkChecks4_1 :
    compactCertificate494.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3269131383104269 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26520793668 / 1000000000000) (26520793732 / 1000000000000), orderedInterval (8678260601 / 1000000000000) (8678260666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1887433884051301 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36225643549 / 1000000000000) (36225643594 / 1000000000000), orderedInterval (6034280972 / 1000000000000) (6034281017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3349284548549609 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (17739209910 / 1000000000000) (17739210587 / 1000000000000), orderedInterval (-21120444687 / 1000000000000) (-21120444010 / 1000000000000)))) (orderedInterval (-41184183984 / 1000000000000) (-41184177901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3129336083019821 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21668324897 / 1000000000000) (-21668324896 / 1000000000000), orderedInterval (-18539530465 / 1000000000000) (-18539530464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2233241888674493 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-3634657765 / 1000000000000) (-3634657763 / 1000000000000), orderedInterval (33574834034 / 1000000000000) (33574834036 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2532258280665147 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21660842055 / 1000000000000) (-21660837997 / 1000000000000), orderedInterval (23177932444 / 1000000000000) (23177936502 / 1000000000000)))) (orderedInterval (7402789058 / 1000000000000) (7402789589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2111132953221643 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24445888566 / 1000000000000) (24445888567 / 1000000000000), orderedInterval (24646923981 / 1000000000000) (24646923982 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1865249988410503 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31084945074 / 1000000000000) (31085038822 / 1000000000000), orderedInterval (-20006964132 / 1000000000000) (-20006870384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (540622148251797 / 800000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27633091295 / 1000000000000) (-27633091292 / 1000000000000), orderedInterval (-13338714108 / 1000000000000) (-13338714105 / 1000000000000)))) (orderedInterval (-11747799652 / 1000000000000) (-11747785192 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate494_chunkChecks4_2 :
    compactCertificate494.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1495389313449359 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29105522794 / 1000000000000) (-29105522793 / 1000000000000), orderedInterval (-29214373651 / 1000000000000) (-29214373650 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1267658081994199 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17398528288 / 1000000000000) (-17398528287 / 1000000000000), orderedInterval (-41277500303 / 1000000000000) (-41277500302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (793241568459997 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-52274538297 / 1000000000000) (-52274538296 / 1000000000000), orderedInterval (-21721905451 / 1000000000000) (-21721905450 / 1000000000000)))) (orderedInterval (5537745597 / 1000000000000) (5537745675 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (426607953720099 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (45020333841 / 1000000000000) (45020333842 / 1000000000000), orderedInterval (62576858467 / 1000000000000) (62576858468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1158323581417297 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45636902265 / 1000000000000) (45636902269 / 1000000000000), orderedInterval (10677034953 / 1000000000000) (10677034957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1581591822296369 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (13470765926 / 1000000000000) (13470765927 / 1000000000000), orderedInterval (37779962397 / 1000000000000) (37779962398 / 1000000000000)))) (orderedInterval (-1848755868 / 1000000000000) (-1848755825 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (668758431540003 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61392853431 / 1000000000000) (-61392853419 / 1000000000000), orderedInterval (-6035085395 / 1000000000000) (-6035085383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2718465895852163 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29678114376 / 1000000000000) (29678134829 / 1000000000000), orderedInterval (-7501320092 / 1000000000000) (-7501299639 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1815809233672717 / 4000000000000) 4 (IntervalRat.scale (731 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (26693863262 / 1000000000000) (26693878802 / 1000000000000), orderedInterval (-26294038188 / 1000000000000) (-26294022648 / 1000000000000)))) (orderedInterval (-40739121174 / 1000000000000) (-40739093725 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate494_chunkChecks4 :
    compactCertificate494.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate494.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate494_chunkChecks4_0
    compactCertificate494_chunkChecks4_1 compactCertificate494_chunkChecks4_2

theorem compactCertificate494_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate494.chunkCheck r b = true :=
  compactCertificate494.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate494_chunkChecks0
    · exact compactCertificate494_chunkChecks1
    · exact compactCertificate494_chunkChecks2
    · exact compactCertificate494_chunkChecks3
    · exact compactCertificate494_chunkChecks4)

theorem compactCertificate494_coefficient0 :
    compactCertificate494.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate494_coefficient1 :
    compactCertificate494.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate494_coefficient2 :
    compactCertificate494.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate494_coefficient3 :
    compactCertificate494.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate494_coefficient4 :
    compactCertificate494.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate494_coefficients : ∀ r : Fin 5,
    compactCertificate494.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate494_coefficient0
  · exact compactCertificate494_coefficient1
  · exact compactCertificate494_coefficient2
  · exact compactCertificate494_coefficient3
  · exact compactCertificate494_coefficient4

theorem compactCertificate494_lower : (1 : ℚ) ≤ compactCertificate494.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate494, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate494_proves {t : ℝ} (ht : t ∈ compactCertificate494.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate494.proves compactCertificate494_states compactCertificate494_chunks
    compactCertificate494_coefficients compactCertificate494_lower ht

end Erdos232
