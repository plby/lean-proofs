/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate303 : CompactCertificate where
  left := 176
  right := 177
  center := 353 / 2
  grid := fun i =>
    match i.val with
    | 0 => 56
    | 1 => 41
    | 2 => 67
    | 3 => 12
    | 4 => 32
    | 5 => 88
    | 6 => 65
    | 7 => 111
    | 8 => 82
    | 9 => 126
    | 10 => 73
    | 11 => 129
    | 12 => 120
    | 13 => 86
    | 14 => 97
    | 15 => 81
    | 16 => 72
    | 17 => 104
    | 18 => 57
    | 19 => 49
    | 20 => 30
    | 21 => 16
    | 22 => 45
    | 23 => 61
    | 24 => 26
    | 25 => 105
    | _ => 70
  point := fun i =>
    match i.val with
    | 0 => 353 / 2
    | 1 => 520036404609053 / 4000000000000
    | 2 => 168169088428349 / 800000000000
    | 3 => 151745325875671 / 4000000000000
    | 4 => 407609290047787 / 4000000000000
    | 5 => 1106738513778879 / 4000000000000
    | 6 => 815218580095927 / 4000000000000
    | 7 => 1396890931949971 / 4000000000000
    | 8 => 1028943538076089 / 4000000000000
    | 9 => 1578663992114647 / 4000000000000
    | 10 => 911442080807263 / 4000000000000
    | 11 => 1617369966673067 / 4000000000000
    | 12 => 1511156822580023 / 4000000000000
    | 13 => 1078432813545959 / 4000000000000
    | 14 => 1222827870143361 / 4000000000000
    | 15 => 1019466391911409 / 4000000000000
    | 16 => 900729474567589 / 4000000000000
    | 17 => 261066509347311 / 800000000000
    | 18 => 722123704032317 / 4000000000000
    | 19 => 612152261209237 / 4000000000000
    | 20 => 383056461923911 / 4000000000000
    | 21 => 206009039210937 / 4000000000000
    | 22 => 559354615923811 / 4000000000000
    | 23 => 763750907346947 / 4000000000000
    | 24 => 322943538076089 / 4000000000000
    | 25 => 1312747552990169 / 4000000000000
    | _ => 876854527341271 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (58670921773 / 1000000000000) (58670921776 / 1000000000000), orderedInterval (12664253774 / 1000000000000) (12664253776 / 1000000000000))
    | 1 => (orderedInterval (-63967436211 / 1000000000000) (-63967429095 / 1000000000000), orderedInterval (28616333378 / 1000000000000) (28616340494 / 1000000000000))
    | 2 => (orderedInterval (-26839008281 / 1000000000000) (-26839008280 / 1000000000000), orderedInterval (-47979338171 / 1000000000000) (-47979338170 / 1000000000000))
    | 3 => (orderedInterval (110333590284 / 1000000000000) (110333590285 / 1000000000000), orderedInterval (66421760797 / 1000000000000) (66421760798 / 1000000000000))
    | 4 => (orderedInterval (65908013932 / 1000000000000) (65908045246 / 1000000000000), orderedInterval (-43951999136 / 1000000000000) (-43951967822 / 1000000000000))
    | 5 => (orderedInterval (40605646312 / 1000000000000) (40605646313 / 1000000000000), orderedInterval (25462200474 / 1000000000000) (25462200475 / 1000000000000))
    | 6 => (orderedInterval (-21036908318 / 1000000000000) (-21036908317 / 1000000000000), orderedInterval (-51728035320 / 1000000000000) (-51728035319 / 1000000000000))
    | 7 => (orderedInterval (-41035623584 / 1000000000000) (-41035623581 / 1000000000000), orderedInterval (-11732685555 / 1000000000000) (-11732685552 / 1000000000000))
    | 8 => (orderedInterval (19839022983 / 1000000000000) (19839022984 / 1000000000000), orderedInterval (45582316999 / 1000000000000) (45582317000 / 1000000000000))
    | 9 => (orderedInterval (-15254418105 / 1000000000000) (-15254417876 / 1000000000000), orderedInterval (37172565565 / 1000000000000) (37172565794 / 1000000000000))
    | 10 => (orderedInterval (33682057554 / 1000000000000) (33682074957 / 1000000000000), orderedInterval (-40809906657 / 1000000000000) (-40809889254 / 1000000000000))
    | 11 => (orderedInterval (5453349546 / 1000000000000) (5453349552 / 1000000000000), orderedInterval (-39309655632 / 1000000000000) (-39309655627 / 1000000000000))
    | 12 => (orderedInterval (41047048334 / 1000000000000) (41047048614 / 1000000000000), orderedInterval (-561618445 / 1000000000000) (-561618165 / 1000000000000))
    | 13 => (orderedInterval (10422701678 / 1000000000000) (10422701679 / 1000000000000), orderedInterval (47442744332 / 1000000000000) (47442744333 / 1000000000000))
    | 14 => (orderedInterval (-44841058336 / 1000000000000) (-44841056816 / 1000000000000), orderedInterval (8542573510 / 1000000000000) (8542575030 / 1000000000000))
    | 15 => (orderedInterval (-46257882773 / 1000000000000) (-46257882772 / 1000000000000), orderedInterval (-18831717169 / 1000000000000) (-18831717168 / 1000000000000))
    | 16 => (orderedInterval (-11990153754 / 1000000000000) (-11990153674 / 1000000000000), orderedInterval (51827899263 / 1000000000000) (51827899343 / 1000000000000))
    | 17 => (orderedInterval (16894941643 / 1000000000000) (16894941644 / 1000000000000), orderedInterval (40783309307 / 1000000000000) (40783309308 / 1000000000000))
    | 18 => (orderedInterval (-46395981290 / 1000000000000) (-46395884809 / 1000000000000), orderedInterval (37193112182 / 1000000000000) (37193208662 / 1000000000000))
    | 19 => (orderedInterval (7426011859 / 1000000000000) (7426011885 / 1000000000000), orderedInterval (-64092620196 / 1000000000000) (-64092620170 / 1000000000000))
    | 20 => (orderedInterval (60776544869 / 1000000000000) (60776652577 / 1000000000000), orderedInterval (-54667942035 / 1000000000000) (-54667834327 / 1000000000000))
    | 21 => (orderedInterval (100160001887 / 1000000000000) (100160008521 / 1000000000000), orderedInterval (-49228042620 / 1000000000000) (-49228035986 / 1000000000000))
    | 22 => (orderedInterval (45918108443 / 1000000000000) (45918152962 / 1000000000000), orderedInterval (-49601617385 / 1000000000000) (-49601572866 / 1000000000000))
    | 23 => (orderedInterval (-4920503210 / 1000000000000) (-4920503208 / 1000000000000), orderedInterval (-57519495376 / 1000000000000) (-57519495375 / 1000000000000))
    | 24 => (orderedInterval (-14293887112 / 1000000000000) (-14293887024 / 1000000000000), orderedInterval (87730077129 / 1000000000000) (87730077217 / 1000000000000))
    | 25 => (orderedInterval (34371793891 / 1000000000000) (34371863888 / 1000000000000), orderedInterval (-27591199715 / 1000000000000) (-27591129718 / 1000000000000))
    | _ => (orderedInterval (4681097168 / 1000000000000) (4681097170 / 1000000000000), orderedInterval (53675461360 / 1000000000000) (53675461361 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (21084103480 / 1000000000000) (21084103561 / 1000000000000)
      | 1 => orderedInterval (-1677265394 / 1000000000000) (-1677264229 / 1000000000000)
      | 2 => orderedInterval (1745172853 / 1000000000000) (1745172863 / 1000000000000)
      | 3 => orderedInterval (5981314904 / 1000000000000) (5981316305 / 1000000000000)
      | 4 => orderedInterval (471496209 / 1000000000000) (471496243 / 1000000000000)
      | 5 => orderedInterval (584563119 / 1000000000000) (584563141 / 1000000000000)
      | 6 => orderedInterval (8976636241 / 1000000000000) (8976655221 / 1000000000000)
      | 7 => orderedInterval (-2514103281 / 1000000000000) (-2514102126 / 1000000000000)
      | _ => orderedInterval (-3762397069 / 1000000000000) (-3762391320 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (1862841938 / 1000000000000) (1862842002 / 1000000000000)
      | 1 => orderedInterval (-3918944527 / 1000000000000) (-3918943842 / 1000000000000)
      | 2 => orderedInterval (2321573511 / 1000000000000) (2321573529 / 1000000000000)
      | 3 => orderedInterval (-31474773924 / 1000000000000) (-31474772022 / 1000000000000)
      | 4 => orderedInterval (6799794565 / 1000000000000) (6799794624 / 1000000000000)
      | 5 => orderedInterval (-2167362019 / 1000000000000) (-2167361987 / 1000000000000)
      | 6 => orderedInterval (-3902940604 / 1000000000000) (-3902922880 / 1000000000000)
      | 7 => orderedInterval (5925631037 / 1000000000000) (5925631893 / 1000000000000)
      | _ => orderedInterval (-8090040066 / 1000000000000) (-8090029402 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-20708227398 / 1000000000000) (-20708227344 / 1000000000000)
      | 1 => orderedInterval (6369074425 / 1000000000000) (6369074844 / 1000000000000)
      | 2 => orderedInterval (-5986634741 / 1000000000000) (-5986634709 / 1000000000000)
      | 3 => orderedInterval (-21602106953 / 1000000000000) (-21602104275 / 1000000000000)
      | 4 => orderedInterval (376000479 / 1000000000000) (376000583 / 1000000000000)
      | 5 => orderedInterval (-1469522698 / 1000000000000) (-1469522653 / 1000000000000)
      | 6 => orderedInterval (-8005441276 / 1000000000000) (-8005423964 / 1000000000000)
      | 7 => orderedInterval (336500454 / 1000000000000) (336501123 / 1000000000000)
      | _ => orderedInterval (11092326398 / 1000000000000) (11092346261 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-252351114 / 1000000000000) (-252351067 / 1000000000000)
      | 1 => orderedInterval (7252838220 / 1000000000000) (7252838493 / 1000000000000)
      | 2 => orderedInterval (-6179469360 / 1000000000000) (-6179469303 / 1000000000000)
      | 3 => orderedInterval (147660638188 / 1000000000000) (147660642121 / 1000000000000)
      | 4 => orderedInterval (-15866971331 / 1000000000000) (-15866971144 / 1000000000000)
      | 5 => orderedInterval (222401230 / 1000000000000) (222401297 / 1000000000000)
      | 6 => orderedInterval (4328453043 / 1000000000000) (4328470247 / 1000000000000)
      | 7 => orderedInterval (-6164865761 / 1000000000000) (-6164865232 / 1000000000000)
      | _ => orderedInterval (4742102236 / 1000000000000) (4742139135 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (19912907554 / 1000000000000) (19912907598 / 1000000000000)
      | 1 => orderedInterval (-17249428925 / 1000000000000) (-17249428718 / 1000000000000)
      | 2 => orderedInterval (21631357378 / 1000000000000) (21631357483 / 1000000000000)
      | 3 => orderedInterval (94373779948 / 1000000000000) (94373786120 / 1000000000000)
      | 4 => orderedInterval (-7966232778 / 1000000000000) (-7966232434 / 1000000000000)
      | 5 => orderedInterval (4547995367 / 1000000000000) (4547995469 / 1000000000000)
      | 6 => orderedInterval (8004203735 / 1000000000000) (8004221154 / 1000000000000)
      | 7 => orderedInterval (162453147 / 1000000000000) (162453573 / 1000000000000)
      | _ => orderedInterval (-35592999220 / 1000000000000) (-35592930443 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (30889521062 / 1000000000000) (30889549659 / 1000000000000)
    | 1 => orderedInterval (-32644220089 / 1000000000000) (-32644188085 / 1000000000000)
    | 2 => orderedInterval (-39598031310 / 1000000000000) (-39597990134 / 1000000000000)
    | 3 => orderedInterval (135742775351 / 1000000000000) (135742834547 / 1000000000000)
    | _ => orderedInterval (87824036206 / 1000000000000) (87824129802 / 1000000000000)

theorem compactCertificate303_stateChecks0 :
    compactCertificate303.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (353 / 2)) (orderedInterval (58670921773 / 1000000000000) (58670921776 / 1000000000000), orderedInterval (12664253774 / 1000000000000) (12664253776 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (520036404609053 / 4000000000000)) (orderedInterval (-63967436211 / 1000000000000) (-63967429095 / 1000000000000), orderedInterval (28616333378 / 1000000000000) (28616340494 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (168169088428349 / 800000000000)) (orderedInterval (-26839008281 / 1000000000000) (-26839008280 / 1000000000000), orderedInterval (-47979338171 / 1000000000000) (-47979338170 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_stateChecks1 :
    compactCertificate303.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (151745325875671 / 4000000000000)) (orderedInterval (110333590284 / 1000000000000) (110333590285 / 1000000000000), orderedInterval (66421760797 / 1000000000000) (66421760798 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (407609290047787 / 4000000000000)) (orderedInterval (65908013932 / 1000000000000) (65908045246 / 1000000000000), orderedInterval (-43951999136 / 1000000000000) (-43951967822 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1106738513778879 / 4000000000000)) (orderedInterval (40605646312 / 1000000000000) (40605646313 / 1000000000000), orderedInterval (25462200474 / 1000000000000) (25462200475 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_stateChecks2 :
    compactCertificate303.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (815218580095927 / 4000000000000)) (orderedInterval (-21036908318 / 1000000000000) (-21036908317 / 1000000000000), orderedInterval (-51728035320 / 1000000000000) (-51728035319 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1396890931949971 / 4000000000000)) (orderedInterval (-41035623584 / 1000000000000) (-41035623581 / 1000000000000), orderedInterval (-11732685555 / 1000000000000) (-11732685552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1028943538076089 / 4000000000000)) (orderedInterval (19839022983 / 1000000000000) (19839022984 / 1000000000000), orderedInterval (45582316999 / 1000000000000) (45582317000 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_stateChecks3 :
    compactCertificate303.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1578663992114647 / 4000000000000)) (orderedInterval (-15254418105 / 1000000000000) (-15254417876 / 1000000000000), orderedInterval (37172565565 / 1000000000000) (37172565794 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (911442080807263 / 4000000000000)) (orderedInterval (33682057554 / 1000000000000) (33682074957 / 1000000000000), orderedInterval (-40809906657 / 1000000000000) (-40809889254 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1617369966673067 / 4000000000000)) (orderedInterval (5453349546 / 1000000000000) (5453349552 / 1000000000000), orderedInterval (-39309655632 / 1000000000000) (-39309655627 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_stateChecks4 :
    compactCertificate303.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1511156822580023 / 4000000000000)) (orderedInterval (41047048334 / 1000000000000) (41047048614 / 1000000000000), orderedInterval (-561618445 / 1000000000000) (-561618165 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1078432813545959 / 4000000000000)) (orderedInterval (10422701678 / 1000000000000) (10422701679 / 1000000000000), orderedInterval (47442744332 / 1000000000000) (47442744333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1222827870143361 / 4000000000000)) (orderedInterval (-44841058336 / 1000000000000) (-44841056816 / 1000000000000), orderedInterval (8542573510 / 1000000000000) (8542575030 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_stateChecks5 :
    compactCertificate303.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1019466391911409 / 4000000000000)) (orderedInterval (-46257882773 / 1000000000000) (-46257882772 / 1000000000000), orderedInterval (-18831717169 / 1000000000000) (-18831717168 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (900729474567589 / 4000000000000)) (orderedInterval (-11990153754 / 1000000000000) (-11990153674 / 1000000000000), orderedInterval (51827899263 / 1000000000000) (51827899343 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (261066509347311 / 800000000000)) (orderedInterval (16894941643 / 1000000000000) (16894941644 / 1000000000000), orderedInterval (40783309307 / 1000000000000) (40783309308 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_stateChecks6 :
    compactCertificate303.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (722123704032317 / 4000000000000)) (orderedInterval (-46395981290 / 1000000000000) (-46395884809 / 1000000000000), orderedInterval (37193112182 / 1000000000000) (37193208662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (612152261209237 / 4000000000000)) (orderedInterval (7426011859 / 1000000000000) (7426011885 / 1000000000000), orderedInterval (-64092620196 / 1000000000000) (-64092620170 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (383056461923911 / 4000000000000)) (orderedInterval (60776544869 / 1000000000000) (60776652577 / 1000000000000), orderedInterval (-54667942035 / 1000000000000) (-54667834327 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_stateChecks7 :
    compactCertificate303.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (206009039210937 / 4000000000000)) (orderedInterval (100160001887 / 1000000000000) (100160008521 / 1000000000000), orderedInterval (-49228042620 / 1000000000000) (-49228035986 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (559354615923811 / 4000000000000)) (orderedInterval (45918108443 / 1000000000000) (45918152962 / 1000000000000), orderedInterval (-49601617385 / 1000000000000) (-49601572866 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (763750907346947 / 4000000000000)) (orderedInterval (-4920503210 / 1000000000000) (-4920503208 / 1000000000000), orderedInterval (-57519495376 / 1000000000000) (-57519495375 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_stateChecks8 :
    compactCertificate303.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (322943538076089 / 4000000000000)) (orderedInterval (-14293887112 / 1000000000000) (-14293887024 / 1000000000000), orderedInterval (87730077129 / 1000000000000) (87730077217 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1312747552990169 / 4000000000000)) (orderedInterval (34371793891 / 1000000000000) (34371863888 / 1000000000000), orderedInterval (-27591199715 / 1000000000000) (-27591129718 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (876854527341271 / 4000000000000)) (orderedInterval (4681097168 / 1000000000000) (4681097170 / 1000000000000), orderedInterval (53675461360 / 1000000000000) (53675461361 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_states : ∀ j,
    BesselStateValid (compactCertificate303.point j) (compactCertificate303.state j) :=
  compactCertificate303.statesValid_of_checks3 compactCertificate303_stateChecks0
    compactCertificate303_stateChecks1 compactCertificate303_stateChecks2
    compactCertificate303_stateChecks3 compactCertificate303_stateChecks4
    compactCertificate303_stateChecks5 compactCertificate303_stateChecks6
    compactCertificate303_stateChecks7 compactCertificate303_stateChecks8

theorem compactCertificate303_chunkChecks0_0 :
    compactCertificate303.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (353 / 2) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58670921773 / 1000000000000) (58670921776 / 1000000000000), orderedInterval (12664253774 / 1000000000000) (12664253776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (520036404609053 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-63967436211 / 1000000000000) (-63967429095 / 1000000000000), orderedInterval (28616333378 / 1000000000000) (28616340494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (168169088428349 / 800000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26839008281 / 1000000000000) (-26839008280 / 1000000000000), orderedInterval (-47979338171 / 1000000000000) (-47979338170 / 1000000000000)))) (orderedInterval (21084103480 / 1000000000000) (21084103561 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (151745325875671 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110333590284 / 1000000000000) (110333590285 / 1000000000000), orderedInterval (66421760797 / 1000000000000) (66421760798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (407609290047787 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65908013932 / 1000000000000) (65908045246 / 1000000000000), orderedInterval (-43951999136 / 1000000000000) (-43951967822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1106738513778879 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (40605646312 / 1000000000000) (40605646313 / 1000000000000), orderedInterval (25462200474 / 1000000000000) (25462200475 / 1000000000000)))) (orderedInterval (-1677265394 / 1000000000000) (-1677264229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (815218580095927 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21036908318 / 1000000000000) (-21036908317 / 1000000000000), orderedInterval (-51728035320 / 1000000000000) (-51728035319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1396890931949971 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-41035623584 / 1000000000000) (-41035623581 / 1000000000000), orderedInterval (-11732685555 / 1000000000000) (-11732685552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1028943538076089 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19839022983 / 1000000000000) (19839022984 / 1000000000000), orderedInterval (45582316999 / 1000000000000) (45582317000 / 1000000000000)))) (orderedInterval (1745172853 / 1000000000000) (1745172863 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_chunkChecks0_1 :
    compactCertificate303.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1578663992114647 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15254418105 / 1000000000000) (-15254417876 / 1000000000000), orderedInterval (37172565565 / 1000000000000) (37172565794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (911442080807263 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33682057554 / 1000000000000) (33682074957 / 1000000000000), orderedInterval (-40809906657 / 1000000000000) (-40809889254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1617369966673067 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5453349546 / 1000000000000) (5453349552 / 1000000000000), orderedInterval (-39309655632 / 1000000000000) (-39309655627 / 1000000000000)))) (orderedInterval (5981314904 / 1000000000000) (5981316305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1511156822580023 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41047048334 / 1000000000000) (41047048614 / 1000000000000), orderedInterval (-561618445 / 1000000000000) (-561618165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1078432813545959 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10422701678 / 1000000000000) (10422701679 / 1000000000000), orderedInterval (47442744332 / 1000000000000) (47442744333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1222827870143361 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-44841058336 / 1000000000000) (-44841056816 / 1000000000000), orderedInterval (8542573510 / 1000000000000) (8542575030 / 1000000000000)))) (orderedInterval (471496209 / 1000000000000) (471496243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1019466391911409 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-46257882773 / 1000000000000) (-46257882772 / 1000000000000), orderedInterval (-18831717169 / 1000000000000) (-18831717168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (900729474567589 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11990153754 / 1000000000000) (-11990153674 / 1000000000000), orderedInterval (51827899263 / 1000000000000) (51827899343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (261066509347311 / 800000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16894941643 / 1000000000000) (16894941644 / 1000000000000), orderedInterval (40783309307 / 1000000000000) (40783309308 / 1000000000000)))) (orderedInterval (584563119 / 1000000000000) (584563141 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_chunkChecks0_2 :
    compactCertificate303.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (722123704032317 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46395981290 / 1000000000000) (-46395884809 / 1000000000000), orderedInterval (37193112182 / 1000000000000) (37193208662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (612152261209237 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (7426011859 / 1000000000000) (7426011885 / 1000000000000), orderedInterval (-64092620196 / 1000000000000) (-64092620170 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (383056461923911 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60776544869 / 1000000000000) (60776652577 / 1000000000000), orderedInterval (-54667942035 / 1000000000000) (-54667834327 / 1000000000000)))) (orderedInterval (8976636241 / 1000000000000) (8976655221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (206009039210937 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (100160001887 / 1000000000000) (100160008521 / 1000000000000), orderedInterval (-49228042620 / 1000000000000) (-49228035986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (559354615923811 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45918108443 / 1000000000000) (45918152962 / 1000000000000), orderedInterval (-49601617385 / 1000000000000) (-49601572866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (763750907346947 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-4920503210 / 1000000000000) (-4920503208 / 1000000000000), orderedInterval (-57519495376 / 1000000000000) (-57519495375 / 1000000000000)))) (orderedInterval (-2514103281 / 1000000000000) (-2514102126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (322943538076089 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-14293887112 / 1000000000000) (-14293887024 / 1000000000000), orderedInterval (87730077129 / 1000000000000) (87730077217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1312747552990169 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34371793891 / 1000000000000) (34371863888 / 1000000000000), orderedInterval (-27591199715 / 1000000000000) (-27591129718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (876854527341271 / 4000000000000) 0 (IntervalRat.scale (353 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4681097168 / 1000000000000) (4681097170 / 1000000000000), orderedInterval (53675461360 / 1000000000000) (53675461361 / 1000000000000)))) (orderedInterval (-3762397069 / 1000000000000) (-3762391320 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_chunkChecks0 :
    compactCertificate303.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate303.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate303_chunkChecks0_0
    compactCertificate303_chunkChecks0_1 compactCertificate303_chunkChecks0_2

theorem compactCertificate303_chunkChecks1_0 :
    compactCertificate303.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (353 / 2) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58670921773 / 1000000000000) (58670921776 / 1000000000000), orderedInterval (12664253774 / 1000000000000) (12664253776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (520036404609053 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-63967436211 / 1000000000000) (-63967429095 / 1000000000000), orderedInterval (28616333378 / 1000000000000) (28616340494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (168169088428349 / 800000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26839008281 / 1000000000000) (-26839008280 / 1000000000000), orderedInterval (-47979338171 / 1000000000000) (-47979338170 / 1000000000000)))) (orderedInterval (1862841938 / 1000000000000) (1862842002 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (151745325875671 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110333590284 / 1000000000000) (110333590285 / 1000000000000), orderedInterval (66421760797 / 1000000000000) (66421760798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (407609290047787 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65908013932 / 1000000000000) (65908045246 / 1000000000000), orderedInterval (-43951999136 / 1000000000000) (-43951967822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1106738513778879 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (40605646312 / 1000000000000) (40605646313 / 1000000000000), orderedInterval (25462200474 / 1000000000000) (25462200475 / 1000000000000)))) (orderedInterval (-3918944527 / 1000000000000) (-3918943842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (815218580095927 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21036908318 / 1000000000000) (-21036908317 / 1000000000000), orderedInterval (-51728035320 / 1000000000000) (-51728035319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1396890931949971 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-41035623584 / 1000000000000) (-41035623581 / 1000000000000), orderedInterval (-11732685555 / 1000000000000) (-11732685552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1028943538076089 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19839022983 / 1000000000000) (19839022984 / 1000000000000), orderedInterval (45582316999 / 1000000000000) (45582317000 / 1000000000000)))) (orderedInterval (2321573511 / 1000000000000) (2321573529 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_chunkChecks1_1 :
    compactCertificate303.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1578663992114647 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15254418105 / 1000000000000) (-15254417876 / 1000000000000), orderedInterval (37172565565 / 1000000000000) (37172565794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (911442080807263 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33682057554 / 1000000000000) (33682074957 / 1000000000000), orderedInterval (-40809906657 / 1000000000000) (-40809889254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1617369966673067 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5453349546 / 1000000000000) (5453349552 / 1000000000000), orderedInterval (-39309655632 / 1000000000000) (-39309655627 / 1000000000000)))) (orderedInterval (-31474773924 / 1000000000000) (-31474772022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1511156822580023 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41047048334 / 1000000000000) (41047048614 / 1000000000000), orderedInterval (-561618445 / 1000000000000) (-561618165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1078432813545959 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10422701678 / 1000000000000) (10422701679 / 1000000000000), orderedInterval (47442744332 / 1000000000000) (47442744333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1222827870143361 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-44841058336 / 1000000000000) (-44841056816 / 1000000000000), orderedInterval (8542573510 / 1000000000000) (8542575030 / 1000000000000)))) (orderedInterval (6799794565 / 1000000000000) (6799794624 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1019466391911409 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-46257882773 / 1000000000000) (-46257882772 / 1000000000000), orderedInterval (-18831717169 / 1000000000000) (-18831717168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (900729474567589 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11990153754 / 1000000000000) (-11990153674 / 1000000000000), orderedInterval (51827899263 / 1000000000000) (51827899343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (261066509347311 / 800000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16894941643 / 1000000000000) (16894941644 / 1000000000000), orderedInterval (40783309307 / 1000000000000) (40783309308 / 1000000000000)))) (orderedInterval (-2167362019 / 1000000000000) (-2167361987 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_chunkChecks1_2 :
    compactCertificate303.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (722123704032317 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46395981290 / 1000000000000) (-46395884809 / 1000000000000), orderedInterval (37193112182 / 1000000000000) (37193208662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (612152261209237 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (7426011859 / 1000000000000) (7426011885 / 1000000000000), orderedInterval (-64092620196 / 1000000000000) (-64092620170 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (383056461923911 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60776544869 / 1000000000000) (60776652577 / 1000000000000), orderedInterval (-54667942035 / 1000000000000) (-54667834327 / 1000000000000)))) (orderedInterval (-3902940604 / 1000000000000) (-3902922880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (206009039210937 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (100160001887 / 1000000000000) (100160008521 / 1000000000000), orderedInterval (-49228042620 / 1000000000000) (-49228035986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (559354615923811 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45918108443 / 1000000000000) (45918152962 / 1000000000000), orderedInterval (-49601617385 / 1000000000000) (-49601572866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (763750907346947 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-4920503210 / 1000000000000) (-4920503208 / 1000000000000), orderedInterval (-57519495376 / 1000000000000) (-57519495375 / 1000000000000)))) (orderedInterval (5925631037 / 1000000000000) (5925631893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (322943538076089 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-14293887112 / 1000000000000) (-14293887024 / 1000000000000), orderedInterval (87730077129 / 1000000000000) (87730077217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1312747552990169 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34371793891 / 1000000000000) (34371863888 / 1000000000000), orderedInterval (-27591199715 / 1000000000000) (-27591129718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (876854527341271 / 4000000000000) 1 (IntervalRat.scale (353 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4681097168 / 1000000000000) (4681097170 / 1000000000000), orderedInterval (53675461360 / 1000000000000) (53675461361 / 1000000000000)))) (orderedInterval (-8090040066 / 1000000000000) (-8090029402 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_chunkChecks1 :
    compactCertificate303.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate303.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate303_chunkChecks1_0
    compactCertificate303_chunkChecks1_1 compactCertificate303_chunkChecks1_2

theorem compactCertificate303_chunkChecks2_0 :
    compactCertificate303.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (353 / 2) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58670921773 / 1000000000000) (58670921776 / 1000000000000), orderedInterval (12664253774 / 1000000000000) (12664253776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (520036404609053 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-63967436211 / 1000000000000) (-63967429095 / 1000000000000), orderedInterval (28616333378 / 1000000000000) (28616340494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (168169088428349 / 800000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26839008281 / 1000000000000) (-26839008280 / 1000000000000), orderedInterval (-47979338171 / 1000000000000) (-47979338170 / 1000000000000)))) (orderedInterval (-20708227398 / 1000000000000) (-20708227344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (151745325875671 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110333590284 / 1000000000000) (110333590285 / 1000000000000), orderedInterval (66421760797 / 1000000000000) (66421760798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (407609290047787 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65908013932 / 1000000000000) (65908045246 / 1000000000000), orderedInterval (-43951999136 / 1000000000000) (-43951967822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1106738513778879 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (40605646312 / 1000000000000) (40605646313 / 1000000000000), orderedInterval (25462200474 / 1000000000000) (25462200475 / 1000000000000)))) (orderedInterval (6369074425 / 1000000000000) (6369074844 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (815218580095927 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21036908318 / 1000000000000) (-21036908317 / 1000000000000), orderedInterval (-51728035320 / 1000000000000) (-51728035319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1396890931949971 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-41035623584 / 1000000000000) (-41035623581 / 1000000000000), orderedInterval (-11732685555 / 1000000000000) (-11732685552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1028943538076089 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19839022983 / 1000000000000) (19839022984 / 1000000000000), orderedInterval (45582316999 / 1000000000000) (45582317000 / 1000000000000)))) (orderedInterval (-5986634741 / 1000000000000) (-5986634709 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_chunkChecks2_1 :
    compactCertificate303.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1578663992114647 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15254418105 / 1000000000000) (-15254417876 / 1000000000000), orderedInterval (37172565565 / 1000000000000) (37172565794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (911442080807263 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33682057554 / 1000000000000) (33682074957 / 1000000000000), orderedInterval (-40809906657 / 1000000000000) (-40809889254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1617369966673067 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5453349546 / 1000000000000) (5453349552 / 1000000000000), orderedInterval (-39309655632 / 1000000000000) (-39309655627 / 1000000000000)))) (orderedInterval (-21602106953 / 1000000000000) (-21602104275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1511156822580023 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41047048334 / 1000000000000) (41047048614 / 1000000000000), orderedInterval (-561618445 / 1000000000000) (-561618165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1078432813545959 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10422701678 / 1000000000000) (10422701679 / 1000000000000), orderedInterval (47442744332 / 1000000000000) (47442744333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1222827870143361 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-44841058336 / 1000000000000) (-44841056816 / 1000000000000), orderedInterval (8542573510 / 1000000000000) (8542575030 / 1000000000000)))) (orderedInterval (376000479 / 1000000000000) (376000583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1019466391911409 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-46257882773 / 1000000000000) (-46257882772 / 1000000000000), orderedInterval (-18831717169 / 1000000000000) (-18831717168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (900729474567589 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11990153754 / 1000000000000) (-11990153674 / 1000000000000), orderedInterval (51827899263 / 1000000000000) (51827899343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (261066509347311 / 800000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16894941643 / 1000000000000) (16894941644 / 1000000000000), orderedInterval (40783309307 / 1000000000000) (40783309308 / 1000000000000)))) (orderedInterval (-1469522698 / 1000000000000) (-1469522653 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_chunkChecks2_2 :
    compactCertificate303.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (722123704032317 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46395981290 / 1000000000000) (-46395884809 / 1000000000000), orderedInterval (37193112182 / 1000000000000) (37193208662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (612152261209237 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (7426011859 / 1000000000000) (7426011885 / 1000000000000), orderedInterval (-64092620196 / 1000000000000) (-64092620170 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (383056461923911 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60776544869 / 1000000000000) (60776652577 / 1000000000000), orderedInterval (-54667942035 / 1000000000000) (-54667834327 / 1000000000000)))) (orderedInterval (-8005441276 / 1000000000000) (-8005423964 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (206009039210937 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (100160001887 / 1000000000000) (100160008521 / 1000000000000), orderedInterval (-49228042620 / 1000000000000) (-49228035986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (559354615923811 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45918108443 / 1000000000000) (45918152962 / 1000000000000), orderedInterval (-49601617385 / 1000000000000) (-49601572866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (763750907346947 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-4920503210 / 1000000000000) (-4920503208 / 1000000000000), orderedInterval (-57519495376 / 1000000000000) (-57519495375 / 1000000000000)))) (orderedInterval (336500454 / 1000000000000) (336501123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (322943538076089 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-14293887112 / 1000000000000) (-14293887024 / 1000000000000), orderedInterval (87730077129 / 1000000000000) (87730077217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1312747552990169 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34371793891 / 1000000000000) (34371863888 / 1000000000000), orderedInterval (-27591199715 / 1000000000000) (-27591129718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (876854527341271 / 4000000000000) 2 (IntervalRat.scale (353 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4681097168 / 1000000000000) (4681097170 / 1000000000000), orderedInterval (53675461360 / 1000000000000) (53675461361 / 1000000000000)))) (orderedInterval (11092326398 / 1000000000000) (11092346261 / 1000000000000))) = true
  rfl'

theorem compactCertificate303_chunkChecks2 :
    compactCertificate303.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate303.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate303_chunkChecks2_0
    compactCertificate303_chunkChecks2_1 compactCertificate303_chunkChecks2_2

theorem compactCertificate303_chunkChecks3_0 :
    compactCertificate303.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (353 / 2) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58670921773 / 1000000000000) (58670921776 / 1000000000000), orderedInterval (12664253774 / 1000000000000) (12664253776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (520036404609053 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-63967436211 / 1000000000000) (-63967429095 / 1000000000000), orderedInterval (28616333378 / 1000000000000) (28616340494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (168169088428349 / 800000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26839008281 / 1000000000000) (-26839008280 / 1000000000000), orderedInterval (-47979338171 / 1000000000000) (-47979338170 / 1000000000000)))) (orderedInterval (-252351114 / 1000000000000) (-252351067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (151745325875671 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110333590284 / 1000000000000) (110333590285 / 1000000000000), orderedInterval (66421760797 / 1000000000000) (66421760798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (407609290047787 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65908013932 / 1000000000000) (65908045246 / 1000000000000), orderedInterval (-43951999136 / 1000000000000) (-43951967822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1106738513778879 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (40605646312 / 1000000000000) (40605646313 / 1000000000000), orderedInterval (25462200474 / 1000000000000) (25462200475 / 1000000000000)))) (orderedInterval (7252838220 / 1000000000000) (7252838493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (815218580095927 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21036908318 / 1000000000000) (-21036908317 / 1000000000000), orderedInterval (-51728035320 / 1000000000000) (-51728035319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1396890931949971 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-41035623584 / 1000000000000) (-41035623581 / 1000000000000), orderedInterval (-11732685555 / 1000000000000) (-11732685552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1028943538076089 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19839022983 / 1000000000000) (19839022984 / 1000000000000), orderedInterval (45582316999 / 1000000000000) (45582317000 / 1000000000000)))) (orderedInterval (-6179469360 / 1000000000000) (-6179469303 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate303_chunkChecks3_1 :
    compactCertificate303.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1578663992114647 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15254418105 / 1000000000000) (-15254417876 / 1000000000000), orderedInterval (37172565565 / 1000000000000) (37172565794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (911442080807263 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33682057554 / 1000000000000) (33682074957 / 1000000000000), orderedInterval (-40809906657 / 1000000000000) (-40809889254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1617369966673067 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5453349546 / 1000000000000) (5453349552 / 1000000000000), orderedInterval (-39309655632 / 1000000000000) (-39309655627 / 1000000000000)))) (orderedInterval (147660638188 / 1000000000000) (147660642121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1511156822580023 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41047048334 / 1000000000000) (41047048614 / 1000000000000), orderedInterval (-561618445 / 1000000000000) (-561618165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1078432813545959 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10422701678 / 1000000000000) (10422701679 / 1000000000000), orderedInterval (47442744332 / 1000000000000) (47442744333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1222827870143361 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-44841058336 / 1000000000000) (-44841056816 / 1000000000000), orderedInterval (8542573510 / 1000000000000) (8542575030 / 1000000000000)))) (orderedInterval (-15866971331 / 1000000000000) (-15866971144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1019466391911409 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-46257882773 / 1000000000000) (-46257882772 / 1000000000000), orderedInterval (-18831717169 / 1000000000000) (-18831717168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (900729474567589 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11990153754 / 1000000000000) (-11990153674 / 1000000000000), orderedInterval (51827899263 / 1000000000000) (51827899343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (261066509347311 / 800000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16894941643 / 1000000000000) (16894941644 / 1000000000000), orderedInterval (40783309307 / 1000000000000) (40783309308 / 1000000000000)))) (orderedInterval (222401230 / 1000000000000) (222401297 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate303_chunkChecks3_2 :
    compactCertificate303.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (722123704032317 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46395981290 / 1000000000000) (-46395884809 / 1000000000000), orderedInterval (37193112182 / 1000000000000) (37193208662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (612152261209237 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (7426011859 / 1000000000000) (7426011885 / 1000000000000), orderedInterval (-64092620196 / 1000000000000) (-64092620170 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (383056461923911 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60776544869 / 1000000000000) (60776652577 / 1000000000000), orderedInterval (-54667942035 / 1000000000000) (-54667834327 / 1000000000000)))) (orderedInterval (4328453043 / 1000000000000) (4328470247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (206009039210937 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (100160001887 / 1000000000000) (100160008521 / 1000000000000), orderedInterval (-49228042620 / 1000000000000) (-49228035986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (559354615923811 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45918108443 / 1000000000000) (45918152962 / 1000000000000), orderedInterval (-49601617385 / 1000000000000) (-49601572866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (763750907346947 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-4920503210 / 1000000000000) (-4920503208 / 1000000000000), orderedInterval (-57519495376 / 1000000000000) (-57519495375 / 1000000000000)))) (orderedInterval (-6164865761 / 1000000000000) (-6164865232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (322943538076089 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-14293887112 / 1000000000000) (-14293887024 / 1000000000000), orderedInterval (87730077129 / 1000000000000) (87730077217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1312747552990169 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34371793891 / 1000000000000) (34371863888 / 1000000000000), orderedInterval (-27591199715 / 1000000000000) (-27591129718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (876854527341271 / 4000000000000) 3 (IntervalRat.scale (353 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4681097168 / 1000000000000) (4681097170 / 1000000000000), orderedInterval (53675461360 / 1000000000000) (53675461361 / 1000000000000)))) (orderedInterval (4742102236 / 1000000000000) (4742139135 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate303_chunkChecks3 :
    compactCertificate303.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate303.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate303_chunkChecks3_0
    compactCertificate303_chunkChecks3_1 compactCertificate303_chunkChecks3_2

theorem compactCertificate303_chunkChecks4_0 :
    compactCertificate303.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (353 / 2) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58670921773 / 1000000000000) (58670921776 / 1000000000000), orderedInterval (12664253774 / 1000000000000) (12664253776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (520036404609053 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-63967436211 / 1000000000000) (-63967429095 / 1000000000000), orderedInterval (28616333378 / 1000000000000) (28616340494 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (168169088428349 / 800000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-26839008281 / 1000000000000) (-26839008280 / 1000000000000), orderedInterval (-47979338171 / 1000000000000) (-47979338170 / 1000000000000)))) (orderedInterval (19912907554 / 1000000000000) (19912907598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (151745325875671 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110333590284 / 1000000000000) (110333590285 / 1000000000000), orderedInterval (66421760797 / 1000000000000) (66421760798 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (407609290047787 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (65908013932 / 1000000000000) (65908045246 / 1000000000000), orderedInterval (-43951999136 / 1000000000000) (-43951967822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1106738513778879 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (40605646312 / 1000000000000) (40605646313 / 1000000000000), orderedInterval (25462200474 / 1000000000000) (25462200475 / 1000000000000)))) (orderedInterval (-17249428925 / 1000000000000) (-17249428718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (815218580095927 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-21036908318 / 1000000000000) (-21036908317 / 1000000000000), orderedInterval (-51728035320 / 1000000000000) (-51728035319 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1396890931949971 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-41035623584 / 1000000000000) (-41035623581 / 1000000000000), orderedInterval (-11732685555 / 1000000000000) (-11732685552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1028943538076089 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19839022983 / 1000000000000) (19839022984 / 1000000000000), orderedInterval (45582316999 / 1000000000000) (45582317000 / 1000000000000)))) (orderedInterval (21631357378 / 1000000000000) (21631357483 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate303_chunkChecks4_1 :
    compactCertificate303.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1578663992114647 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15254418105 / 1000000000000) (-15254417876 / 1000000000000), orderedInterval (37172565565 / 1000000000000) (37172565794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (911442080807263 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33682057554 / 1000000000000) (33682074957 / 1000000000000), orderedInterval (-40809906657 / 1000000000000) (-40809889254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1617369966673067 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5453349546 / 1000000000000) (5453349552 / 1000000000000), orderedInterval (-39309655632 / 1000000000000) (-39309655627 / 1000000000000)))) (orderedInterval (94373779948 / 1000000000000) (94373786120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1511156822580023 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41047048334 / 1000000000000) (41047048614 / 1000000000000), orderedInterval (-561618445 / 1000000000000) (-561618165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1078432813545959 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (10422701678 / 1000000000000) (10422701679 / 1000000000000), orderedInterval (47442744332 / 1000000000000) (47442744333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1222827870143361 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-44841058336 / 1000000000000) (-44841056816 / 1000000000000), orderedInterval (8542573510 / 1000000000000) (8542575030 / 1000000000000)))) (orderedInterval (-7966232778 / 1000000000000) (-7966232434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1019466391911409 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-46257882773 / 1000000000000) (-46257882772 / 1000000000000), orderedInterval (-18831717169 / 1000000000000) (-18831717168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (900729474567589 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11990153754 / 1000000000000) (-11990153674 / 1000000000000), orderedInterval (51827899263 / 1000000000000) (51827899343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (261066509347311 / 800000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16894941643 / 1000000000000) (16894941644 / 1000000000000), orderedInterval (40783309307 / 1000000000000) (40783309308 / 1000000000000)))) (orderedInterval (4547995367 / 1000000000000) (4547995469 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate303_chunkChecks4_2 :
    compactCertificate303.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (722123704032317 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46395981290 / 1000000000000) (-46395884809 / 1000000000000), orderedInterval (37193112182 / 1000000000000) (37193208662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (612152261209237 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (7426011859 / 1000000000000) (7426011885 / 1000000000000), orderedInterval (-64092620196 / 1000000000000) (-64092620170 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (383056461923911 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60776544869 / 1000000000000) (60776652577 / 1000000000000), orderedInterval (-54667942035 / 1000000000000) (-54667834327 / 1000000000000)))) (orderedInterval (8004203735 / 1000000000000) (8004221154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (206009039210937 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (100160001887 / 1000000000000) (100160008521 / 1000000000000), orderedInterval (-49228042620 / 1000000000000) (-49228035986 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (559354615923811 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45918108443 / 1000000000000) (45918152962 / 1000000000000), orderedInterval (-49601617385 / 1000000000000) (-49601572866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (763750907346947 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-4920503210 / 1000000000000) (-4920503208 / 1000000000000), orderedInterval (-57519495376 / 1000000000000) (-57519495375 / 1000000000000)))) (orderedInterval (162453147 / 1000000000000) (162453573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (322943538076089 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-14293887112 / 1000000000000) (-14293887024 / 1000000000000), orderedInterval (87730077129 / 1000000000000) (87730077217 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1312747552990169 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (34371793891 / 1000000000000) (34371863888 / 1000000000000), orderedInterval (-27591199715 / 1000000000000) (-27591129718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (876854527341271 / 4000000000000) 4 (IntervalRat.scale (353 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4681097168 / 1000000000000) (4681097170 / 1000000000000), orderedInterval (53675461360 / 1000000000000) (53675461361 / 1000000000000)))) (orderedInterval (-35592999220 / 1000000000000) (-35592930443 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate303_chunkChecks4 :
    compactCertificate303.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate303.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate303_chunkChecks4_0
    compactCertificate303_chunkChecks4_1 compactCertificate303_chunkChecks4_2

theorem compactCertificate303_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate303.chunkCheck r b = true :=
  compactCertificate303.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate303_chunkChecks0
    · exact compactCertificate303_chunkChecks1
    · exact compactCertificate303_chunkChecks2
    · exact compactCertificate303_chunkChecks3
    · exact compactCertificate303_chunkChecks4)

theorem compactCertificate303_coefficient0 :
    compactCertificate303.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate303_coefficient1 :
    compactCertificate303.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate303_coefficient2 :
    compactCertificate303.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate303_coefficient3 :
    compactCertificate303.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate303_coefficient4 :
    compactCertificate303.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate303_coefficients : ∀ r : Fin 5,
    compactCertificate303.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate303_coefficient0
  · exact compactCertificate303_coefficient1
  · exact compactCertificate303_coefficient2
  · exact compactCertificate303_coefficient3
  · exact compactCertificate303_coefficient4

theorem compactCertificate303_lower : (1 : ℚ) ≤ compactCertificate303.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate303, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate303_proves {t : ℝ} (ht : t ∈ compactCertificate303.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate303.proves compactCertificate303_states compactCertificate303_chunks
    compactCertificate303_coefficients compactCertificate303_lower ht

end Erdos232
