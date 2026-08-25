/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate333 : CompactCertificate where
  left := 205
  right := 206
  center := 411 / 2
  grid := fun i =>
    match i.val with
    | 0 => 65
    | 1 => 48
    | 2 => 78
    | 3 => 14
    | 4 => 38
    | 5 => 103
    | 6 => 76
    | 7 => 129
    | 8 => 95
    | 9 => 146
    | 10 => 84
    | 11 => 150
    | 12 => 140
    | 13 => 100
    | 14 => 113
    | 15 => 95
    | 16 => 83
    | 17 => 121
    | 18 => 67
    | 19 => 57
    | 20 => 36
    | 21 => 19
    | 22 => 52
    | 23 => 71
    | 24 => 30
    | 25 => 122
    | _ => 81
  point := fun i =>
    match i.val with
    | 0 => 411 / 2
    | 1 => 605481479587311 / 4000000000000
    | 2 => 195800270096463 / 800000000000
    | 3 => 176677985651277 / 4000000000000
    | 4 => 474581921273769 / 4000000000000
    | 5 => 1288582235589573 / 4000000000000
    | 6 => 949163842547949 / 4000000000000
    | 7 => 1626408422185377 / 4000000000000
    | 8 => 1198005082575843 / 4000000000000
    | 9 => 1838047877504589 / 4000000000000
    | 10 => 1061197436860581 / 4000000000000
    | 11 => 1883113473945129 / 4000000000000
    | 12 => 1759448878414701 / 4000000000000
    | 13 => 1255625740417533 / 4000000000000
    | 14 => 1423745763821307 / 4000000000000
    | 15 => 1186970784916683 / 4000000000000
    | 16 => 1048724685686343 / 4000000000000
    | 17 => 303961289919957 / 800000000000
    | 18 => 840772924524879 / 4000000000000
    | 19 => 712732519424919 / 4000000000000
    | 20 => 445994917424157 / 4000000000000
    | 21 => 239857549902819 / 4000000000000
    | 22 => 651259906925457 / 4000000000000
    | 23 => 889239724984689 / 4000000000000
    | 24 => 376005082575843 / 4000000000000
    | 25 => 1528439785492803 / 4000000000000
    | _ => 1020926942598477 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-48563081518 / 1000000000000) (-48563056025 / 1000000000000), orderedInterval (27312444267 / 1000000000000) (27312469761 / 1000000000000))
    | 1 => (orderedInterval (63395259975 / 1000000000000) (63395259977 / 1000000000000), orderedInterval (13455494725 / 1000000000000) (13455494727 / 1000000000000))
    | 2 => (orderedInterval (24047252006 / 1000000000000) (24047252007 / 1000000000000), orderedInterval (44926771371 / 1000000000000) (44926771372 / 1000000000000))
    | 3 => (orderedInterval (99012426385 / 1000000000000) (99012426386 / 1000000000000), orderedInterval (66771263431 / 1000000000000) (66771263432 / 1000000000000))
    | 4 => (orderedInterval (3610104935 / 1000000000000) (3610104938 / 1000000000000), orderedInterval (73147248772 / 1000000000000) (73147248775 / 1000000000000))
    | 5 => (orderedInterval (27025920905 / 1000000000000) (27025928421 / 1000000000000), orderedInterval (-35337654315 / 1000000000000) (-35337646799 / 1000000000000))
    | 6 => (orderedInterval (-32778555752 / 1000000000000) (-32778540008 / 1000000000000), orderedInterval (40174341721 / 1000000000000) (40174357464 / 1000000000000))
    | 7 => (orderedInterval (-33713972570 / 1000000000000) (-33713882985 / 1000000000000), orderedInterval (20755597406 / 1000000000000) (20755686991 / 1000000000000))
    | 8 => (orderedInterval (-44505023855 / 1000000000000) (-44505020370 / 1000000000000), orderedInterval (12111738730 / 1000000000000) (12111742215 / 1000000000000))
    | 9 => (orderedInterval (37167500088 / 1000000000000) (37167500882 / 1000000000000), orderedInterval (-2040934309 / 1000000000000) (-2040933516 / 1000000000000))
    | 10 => (orderedInterval (39876905985 / 1000000000000) (39876993519 / 1000000000000), orderedInterval (-28526125908 / 1000000000000) (-28526038374 / 1000000000000))
    | 11 => (orderedInterval (11728180653 / 1000000000000) (11728180654 / 1000000000000), orderedInterval (34840392236 / 1000000000000) (34840392237 / 1000000000000))
    | 12 => (orderedInterval (27928367672 / 1000000000000) (27928367673 / 1000000000000), orderedInterval (25800839988 / 1000000000000) (25800839989 / 1000000000000))
    | 13 => (orderedInterval (22850395506 / 1000000000000) (22850395507 / 1000000000000), orderedInterval (38769743144 / 1000000000000) (38769743145 / 1000000000000))
    | 14 => (orderedInterval (-41812091524 / 1000000000000) (-41812090178 / 1000000000000), orderedInterval (6408890892 / 1000000000000) (6408892238 / 1000000000000))
    | 15 => (orderedInterval (36952203933 / 1000000000000) (36952305700 / 1000000000000), orderedInterval (-27988812911 / 1000000000000) (-27988711144 / 1000000000000))
    | 16 => (orderedInterval (-39432837156 / 1000000000000) (-39432732054 / 1000000000000), orderedInterval (29625468429 / 1000000000000) (29625573531 / 1000000000000))
    | 17 => (orderedInterval (-23246579955 / 1000000000000) (-23246579954 / 1000000000000), orderedInterval (-33661033337 / 1000000000000) (-33661033336 / 1000000000000))
    | 18 => (orderedInterval (-25964770938 / 1000000000000) (-25964770937 / 1000000000000), orderedInterval (-48462160953 / 1000000000000) (-48462160952 / 1000000000000))
    | 19 => (orderedInterval (6143060556 / 1000000000000) (6143060574 / 1000000000000), orderedInterval (-59474082308 / 1000000000000) (-59474082290 / 1000000000000))
    | 20 => (orderedInterval (-54953592469 / 1000000000000) (-54953503512 / 1000000000000), orderedInterval (52109308707 / 1000000000000) (52109397664 / 1000000000000))
    | 21 => (orderedInterval (-89754166196 / 1000000000000) (-89754166195 / 1000000000000), orderedInterval (-49854320906 / 1000000000000) (-49854320905 / 1000000000000))
    | 22 => (orderedInterval (14668566912 / 1000000000000) (14668566913 / 1000000000000), orderedInterval (60740895383 / 1000000000000) (60740895384 / 1000000000000))
    | 23 => (orderedInterval (-2230247019 / 1000000000000) (-2230247017 / 1000000000000), orderedInterval (-53461720640 / 1000000000000) (-53461720638 / 1000000000000))
    | 24 => (orderedInterval (42138110929 / 1000000000000) (42138110930 / 1000000000000), orderedInterval (70464514479 / 1000000000000) (70464514480 / 1000000000000))
    | 25 => (orderedInterval (-15112966087 / 1000000000000) (-15112965869 / 1000000000000), orderedInterval (37936311217 / 1000000000000) (37936311435 / 1000000000000))
    | _ => (orderedInterval (-49929342991 / 1000000000000) (-49929342917 / 1000000000000), orderedInterval (-1058621432 / 1000000000000) (-1058621359 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-17246864476 / 1000000000000) (-17246854356 / 1000000000000)
      | 1 => orderedInterval (-2863666954 / 1000000000000) (-2863666394 / 1000000000000)
      | 2 => orderedInterval (-35727584 / 1000000000000) (-35724724 / 1000000000000)
      | 3 => orderedInterval (-1982435619 / 1000000000000) (-1982428910 / 1000000000000)
      | 4 => orderedInterval (1868198912 / 1000000000000) (1868198944 / 1000000000000)
      | 5 => orderedInterval (2088111796 / 1000000000000) (2088119006 / 1000000000000)
      | 6 => orderedInterval (2014844552 / 1000000000000) (2014847501 / 1000000000000)
      | 7 => orderedInterval (1495461025 / 1000000000000) (1495461051 / 1000000000000)
      | _ => orderedInterval (10852313810 / 1000000000000) (10852313899 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14057946177 / 1000000000000) (14057956299 / 1000000000000)
      | 1 => orderedInterval (5324321793 / 1000000000000) (5324322659 / 1000000000000)
      | 2 => orderedInterval (-840062792 / 1000000000000) (-840057181 / 1000000000000)
      | 3 => orderedInterval (9428581311 / 1000000000000) (9428590169 / 1000000000000)
      | 4 => orderedInterval (4547015897 / 1000000000000) (4547015950 / 1000000000000)
      | 5 => orderedInterval (-4223197877 / 1000000000000) (-4223188477 / 1000000000000)
      | 6 => orderedInterval (11764899457 / 1000000000000) (11764901078 / 1000000000000)
      | 7 => orderedInterval (3609232439 / 1000000000000) (3609232462 / 1000000000000)
      | _ => orderedInterval (-5301029787 / 1000000000000) (-5301029656 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16858133211 / 1000000000000) (16858143384 / 1000000000000)
      | 1 => orderedInterval (4701143950 / 1000000000000) (4701145306 / 1000000000000)
      | 2 => orderedInterval (-1782194343 / 1000000000000) (-1782183283 / 1000000000000)
      | 3 => orderedInterval (19301001207 / 1000000000000) (19301013127 / 1000000000000)
      | 4 => orderedInterval (-3388798723 / 1000000000000) (-3388798636 / 1000000000000)
      | 5 => orderedInterval (-2507641361 / 1000000000000) (-2507629032 / 1000000000000)
      | 6 => orderedInterval (-3612548195 / 1000000000000) (-3612547287 / 1000000000000)
      | 7 => orderedInterval (-149812982 / 1000000000000) (-149812959 / 1000000000000)
      | _ => orderedInterval (-18731689364 / 1000000000000) (-18731689163 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-15411393888 / 1000000000000) (-15411383712 / 1000000000000)
      | 1 => orderedInterval (-10207081003 / 1000000000000) (-10207078879 / 1000000000000)
      | 2 => orderedInterval (4061316631 / 1000000000000) (4061338414 / 1000000000000)
      | 3 => orderedInterval (-59147897453 / 1000000000000) (-59147881072 / 1000000000000)
      | 4 => orderedInterval (-8314238640 / 1000000000000) (-8314238492 / 1000000000000)
      | 5 => orderedInterval (9953319284 / 1000000000000) (9953335438 / 1000000000000)
      | 6 => orderedInterval (-10739316859 / 1000000000000) (-10739316347 / 1000000000000)
      | 7 => orderedInterval (-4523923589 / 1000000000000) (-4523923565 / 1000000000000)
      | _ => orderedInterval (19522478808 / 1000000000000) (19522479131 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16085128311 / 1000000000000) (-16085118083 / 1000000000000)
      | 1 => orderedInterval (-11490607953 / 1000000000000) (-11490604616 / 1000000000000)
      | 2 => orderedInterval (11044723584 / 1000000000000) (11044766643 / 1000000000000)
      | 3 => orderedInterval (-110400911891 / 1000000000000) (-110400888433 / 1000000000000)
      | 4 => orderedInterval (3166341184 / 1000000000000) (3166341441 / 1000000000000)
      | 5 => orderedInterval (781587555 / 1000000000000) (781608860 / 1000000000000)
      | 6 => orderedInterval (4296881747 / 1000000000000) (4296882047 / 1000000000000)
      | 7 => orderedInterval (159006667 / 1000000000000) (159006692 / 1000000000000)
      | _ => orderedInterval (36818124569 / 1000000000000) (36818125108 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3809764538 / 1000000000000) (-3809733983 / 1000000000000)
    | 1 => orderedInterval (38367706618 / 1000000000000) (38367743303 / 1000000000000)
    | 2 => orderedInterval (10687593400 / 1000000000000) (10687641457 / 1000000000000)
    | 3 => orderedInterval (-74806736709 / 1000000000000) (-74806669084 / 1000000000000)
    | _ => orderedInterval (-81709982849 / 1000000000000) (-81709880341 / 1000000000000)

theorem compactCertificate333_stateChecks0 :
    compactCertificate333.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (411 / 2)) (orderedInterval (-48563081518 / 1000000000000) (-48563056025 / 1000000000000), orderedInterval (27312444267 / 1000000000000) (27312469761 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (605481479587311 / 4000000000000)) (orderedInterval (63395259975 / 1000000000000) (63395259977 / 1000000000000), orderedInterval (13455494725 / 1000000000000) (13455494727 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (195800270096463 / 800000000000)) (orderedInterval (24047252006 / 1000000000000) (24047252007 / 1000000000000), orderedInterval (44926771371 / 1000000000000) (44926771372 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_stateChecks1 :
    compactCertificate333.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (176677985651277 / 4000000000000)) (orderedInterval (99012426385 / 1000000000000) (99012426386 / 1000000000000), orderedInterval (66771263431 / 1000000000000) (66771263432 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (474581921273769 / 4000000000000)) (orderedInterval (3610104935 / 1000000000000) (3610104938 / 1000000000000), orderedInterval (73147248772 / 1000000000000) (73147248775 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1288582235589573 / 4000000000000)) (orderedInterval (27025920905 / 1000000000000) (27025928421 / 1000000000000), orderedInterval (-35337654315 / 1000000000000) (-35337646799 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_stateChecks2 :
    compactCertificate333.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (949163842547949 / 4000000000000)) (orderedInterval (-32778555752 / 1000000000000) (-32778540008 / 1000000000000), orderedInterval (40174341721 / 1000000000000) (40174357464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1626408422185377 / 4000000000000)) (orderedInterval (-33713972570 / 1000000000000) (-33713882985 / 1000000000000), orderedInterval (20755597406 / 1000000000000) (20755686991 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1198005082575843 / 4000000000000)) (orderedInterval (-44505023855 / 1000000000000) (-44505020370 / 1000000000000), orderedInterval (12111738730 / 1000000000000) (12111742215 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_stateChecks3 :
    compactCertificate333.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1838047877504589 / 4000000000000)) (orderedInterval (37167500088 / 1000000000000) (37167500882 / 1000000000000), orderedInterval (-2040934309 / 1000000000000) (-2040933516 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1061197436860581 / 4000000000000)) (orderedInterval (39876905985 / 1000000000000) (39876993519 / 1000000000000), orderedInterval (-28526125908 / 1000000000000) (-28526038374 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1883113473945129 / 4000000000000)) (orderedInterval (11728180653 / 1000000000000) (11728180654 / 1000000000000), orderedInterval (34840392236 / 1000000000000) (34840392237 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_stateChecks4 :
    compactCertificate333.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1759448878414701 / 4000000000000)) (orderedInterval (27928367672 / 1000000000000) (27928367673 / 1000000000000), orderedInterval (25800839988 / 1000000000000) (25800839989 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1255625740417533 / 4000000000000)) (orderedInterval (22850395506 / 1000000000000) (22850395507 / 1000000000000), orderedInterval (38769743144 / 1000000000000) (38769743145 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1423745763821307 / 4000000000000)) (orderedInterval (-41812091524 / 1000000000000) (-41812090178 / 1000000000000), orderedInterval (6408890892 / 1000000000000) (6408892238 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_stateChecks5 :
    compactCertificate333.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1186970784916683 / 4000000000000)) (orderedInterval (36952203933 / 1000000000000) (36952305700 / 1000000000000), orderedInterval (-27988812911 / 1000000000000) (-27988711144 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1048724685686343 / 4000000000000)) (orderedInterval (-39432837156 / 1000000000000) (-39432732054 / 1000000000000), orderedInterval (29625468429 / 1000000000000) (29625573531 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (303961289919957 / 800000000000)) (orderedInterval (-23246579955 / 1000000000000) (-23246579954 / 1000000000000), orderedInterval (-33661033337 / 1000000000000) (-33661033336 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_stateChecks6 :
    compactCertificate333.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (840772924524879 / 4000000000000)) (orderedInterval (-25964770938 / 1000000000000) (-25964770937 / 1000000000000), orderedInterval (-48462160953 / 1000000000000) (-48462160952 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (712732519424919 / 4000000000000)) (orderedInterval (6143060556 / 1000000000000) (6143060574 / 1000000000000), orderedInterval (-59474082308 / 1000000000000) (-59474082290 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (445994917424157 / 4000000000000)) (orderedInterval (-54953592469 / 1000000000000) (-54953503512 / 1000000000000), orderedInterval (52109308707 / 1000000000000) (52109397664 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_stateChecks7 :
    compactCertificate333.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (239857549902819 / 4000000000000)) (orderedInterval (-89754166196 / 1000000000000) (-89754166195 / 1000000000000), orderedInterval (-49854320906 / 1000000000000) (-49854320905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (651259906925457 / 4000000000000)) (orderedInterval (14668566912 / 1000000000000) (14668566913 / 1000000000000), orderedInterval (60740895383 / 1000000000000) (60740895384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (889239724984689 / 4000000000000)) (orderedInterval (-2230247019 / 1000000000000) (-2230247017 / 1000000000000), orderedInterval (-53461720640 / 1000000000000) (-53461720638 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_stateChecks8 :
    compactCertificate333.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (376005082575843 / 4000000000000)) (orderedInterval (42138110929 / 1000000000000) (42138110930 / 1000000000000), orderedInterval (70464514479 / 1000000000000) (70464514480 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1528439785492803 / 4000000000000)) (orderedInterval (-15112966087 / 1000000000000) (-15112965869 / 1000000000000), orderedInterval (37936311217 / 1000000000000) (37936311435 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1020926942598477 / 4000000000000)) (orderedInterval (-49929342991 / 1000000000000) (-49929342917 / 1000000000000), orderedInterval (-1058621432 / 1000000000000) (-1058621359 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_states : ∀ j,
    BesselStateValid (compactCertificate333.point j) (compactCertificate333.state j) :=
  compactCertificate333.statesValid_of_checks3 compactCertificate333_stateChecks0
    compactCertificate333_stateChecks1 compactCertificate333_stateChecks2
    compactCertificate333_stateChecks3 compactCertificate333_stateChecks4
    compactCertificate333_stateChecks5 compactCertificate333_stateChecks6
    compactCertificate333_stateChecks7 compactCertificate333_stateChecks8

theorem compactCertificate333_chunkChecks0_0 :
    compactCertificate333.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (411 / 2) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48563081518 / 1000000000000) (-48563056025 / 1000000000000), orderedInterval (27312444267 / 1000000000000) (27312469761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (605481479587311 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (63395259975 / 1000000000000) (63395259977 / 1000000000000), orderedInterval (13455494725 / 1000000000000) (13455494727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (195800270096463 / 800000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24047252006 / 1000000000000) (24047252007 / 1000000000000), orderedInterval (44926771371 / 1000000000000) (44926771372 / 1000000000000)))) (orderedInterval (-17246864476 / 1000000000000) (-17246854356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (176677985651277 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99012426385 / 1000000000000) (99012426386 / 1000000000000), orderedInterval (66771263431 / 1000000000000) (66771263432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (474581921273769 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3610104935 / 1000000000000) (3610104938 / 1000000000000), orderedInterval (73147248772 / 1000000000000) (73147248775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1288582235589573 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27025920905 / 1000000000000) (27025928421 / 1000000000000), orderedInterval (-35337654315 / 1000000000000) (-35337646799 / 1000000000000)))) (orderedInterval (-2863666954 / 1000000000000) (-2863666394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (949163842547949 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32778555752 / 1000000000000) (-32778540008 / 1000000000000), orderedInterval (40174341721 / 1000000000000) (40174357464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1626408422185377 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33713972570 / 1000000000000) (-33713882985 / 1000000000000), orderedInterval (20755597406 / 1000000000000) (20755686991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1198005082575843 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44505023855 / 1000000000000) (-44505020370 / 1000000000000), orderedInterval (12111738730 / 1000000000000) (12111742215 / 1000000000000)))) (orderedInterval (-35727584 / 1000000000000) (-35724724 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_chunkChecks0_1 :
    compactCertificate333.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1838047877504589 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37167500088 / 1000000000000) (37167500882 / 1000000000000), orderedInterval (-2040934309 / 1000000000000) (-2040933516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1061197436860581 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39876905985 / 1000000000000) (39876993519 / 1000000000000), orderedInterval (-28526125908 / 1000000000000) (-28526038374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1883113473945129 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11728180653 / 1000000000000) (11728180654 / 1000000000000), orderedInterval (34840392236 / 1000000000000) (34840392237 / 1000000000000)))) (orderedInterval (-1982435619 / 1000000000000) (-1982428910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1759448878414701 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27928367672 / 1000000000000) (27928367673 / 1000000000000), orderedInterval (25800839988 / 1000000000000) (25800839989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1255625740417533 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22850395506 / 1000000000000) (22850395507 / 1000000000000), orderedInterval (38769743144 / 1000000000000) (38769743145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1423745763821307 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41812091524 / 1000000000000) (-41812090178 / 1000000000000), orderedInterval (6408890892 / 1000000000000) (6408892238 / 1000000000000)))) (orderedInterval (1868198912 / 1000000000000) (1868198944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1186970784916683 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (36952203933 / 1000000000000) (36952305700 / 1000000000000), orderedInterval (-27988812911 / 1000000000000) (-27988711144 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1048724685686343 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39432837156 / 1000000000000) (-39432732054 / 1000000000000), orderedInterval (29625468429 / 1000000000000) (29625573531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (303961289919957 / 800000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23246579955 / 1000000000000) (-23246579954 / 1000000000000), orderedInterval (-33661033337 / 1000000000000) (-33661033336 / 1000000000000)))) (orderedInterval (2088111796 / 1000000000000) (2088119006 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_chunkChecks0_2 :
    compactCertificate333.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (840772924524879 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25964770938 / 1000000000000) (-25964770937 / 1000000000000), orderedInterval (-48462160953 / 1000000000000) (-48462160952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (712732519424919 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (6143060556 / 1000000000000) (6143060574 / 1000000000000), orderedInterval (-59474082308 / 1000000000000) (-59474082290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (445994917424157 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54953592469 / 1000000000000) (-54953503512 / 1000000000000), orderedInterval (52109308707 / 1000000000000) (52109397664 / 1000000000000)))) (orderedInterval (2014844552 / 1000000000000) (2014847501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (239857549902819 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-89754166196 / 1000000000000) (-89754166195 / 1000000000000), orderedInterval (-49854320906 / 1000000000000) (-49854320905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (651259906925457 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14668566912 / 1000000000000) (14668566913 / 1000000000000), orderedInterval (60740895383 / 1000000000000) (60740895384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (889239724984689 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2230247019 / 1000000000000) (-2230247017 / 1000000000000), orderedInterval (-53461720640 / 1000000000000) (-53461720638 / 1000000000000)))) (orderedInterval (1495461025 / 1000000000000) (1495461051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (376005082575843 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42138110929 / 1000000000000) (42138110930 / 1000000000000), orderedInterval (70464514479 / 1000000000000) (70464514480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1528439785492803 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15112966087 / 1000000000000) (-15112965869 / 1000000000000), orderedInterval (37936311217 / 1000000000000) (37936311435 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1020926942598477 / 4000000000000) 0 (IntervalRat.scale (411 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49929342991 / 1000000000000) (-49929342917 / 1000000000000), orderedInterval (-1058621432 / 1000000000000) (-1058621359 / 1000000000000)))) (orderedInterval (10852313810 / 1000000000000) (10852313899 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_chunkChecks0 :
    compactCertificate333.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate333.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate333_chunkChecks0_0
    compactCertificate333_chunkChecks0_1 compactCertificate333_chunkChecks0_2

theorem compactCertificate333_chunkChecks1_0 :
    compactCertificate333.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (411 / 2) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48563081518 / 1000000000000) (-48563056025 / 1000000000000), orderedInterval (27312444267 / 1000000000000) (27312469761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (605481479587311 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (63395259975 / 1000000000000) (63395259977 / 1000000000000), orderedInterval (13455494725 / 1000000000000) (13455494727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (195800270096463 / 800000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24047252006 / 1000000000000) (24047252007 / 1000000000000), orderedInterval (44926771371 / 1000000000000) (44926771372 / 1000000000000)))) (orderedInterval (14057946177 / 1000000000000) (14057956299 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (176677985651277 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99012426385 / 1000000000000) (99012426386 / 1000000000000), orderedInterval (66771263431 / 1000000000000) (66771263432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (474581921273769 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3610104935 / 1000000000000) (3610104938 / 1000000000000), orderedInterval (73147248772 / 1000000000000) (73147248775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1288582235589573 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27025920905 / 1000000000000) (27025928421 / 1000000000000), orderedInterval (-35337654315 / 1000000000000) (-35337646799 / 1000000000000)))) (orderedInterval (5324321793 / 1000000000000) (5324322659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (949163842547949 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32778555752 / 1000000000000) (-32778540008 / 1000000000000), orderedInterval (40174341721 / 1000000000000) (40174357464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1626408422185377 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33713972570 / 1000000000000) (-33713882985 / 1000000000000), orderedInterval (20755597406 / 1000000000000) (20755686991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1198005082575843 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44505023855 / 1000000000000) (-44505020370 / 1000000000000), orderedInterval (12111738730 / 1000000000000) (12111742215 / 1000000000000)))) (orderedInterval (-840062792 / 1000000000000) (-840057181 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_chunkChecks1_1 :
    compactCertificate333.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1838047877504589 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37167500088 / 1000000000000) (37167500882 / 1000000000000), orderedInterval (-2040934309 / 1000000000000) (-2040933516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1061197436860581 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39876905985 / 1000000000000) (39876993519 / 1000000000000), orderedInterval (-28526125908 / 1000000000000) (-28526038374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1883113473945129 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11728180653 / 1000000000000) (11728180654 / 1000000000000), orderedInterval (34840392236 / 1000000000000) (34840392237 / 1000000000000)))) (orderedInterval (9428581311 / 1000000000000) (9428590169 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1759448878414701 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27928367672 / 1000000000000) (27928367673 / 1000000000000), orderedInterval (25800839988 / 1000000000000) (25800839989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1255625740417533 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22850395506 / 1000000000000) (22850395507 / 1000000000000), orderedInterval (38769743144 / 1000000000000) (38769743145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1423745763821307 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41812091524 / 1000000000000) (-41812090178 / 1000000000000), orderedInterval (6408890892 / 1000000000000) (6408892238 / 1000000000000)))) (orderedInterval (4547015897 / 1000000000000) (4547015950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1186970784916683 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (36952203933 / 1000000000000) (36952305700 / 1000000000000), orderedInterval (-27988812911 / 1000000000000) (-27988711144 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1048724685686343 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39432837156 / 1000000000000) (-39432732054 / 1000000000000), orderedInterval (29625468429 / 1000000000000) (29625573531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (303961289919957 / 800000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23246579955 / 1000000000000) (-23246579954 / 1000000000000), orderedInterval (-33661033337 / 1000000000000) (-33661033336 / 1000000000000)))) (orderedInterval (-4223197877 / 1000000000000) (-4223188477 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_chunkChecks1_2 :
    compactCertificate333.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (840772924524879 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25964770938 / 1000000000000) (-25964770937 / 1000000000000), orderedInterval (-48462160953 / 1000000000000) (-48462160952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (712732519424919 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (6143060556 / 1000000000000) (6143060574 / 1000000000000), orderedInterval (-59474082308 / 1000000000000) (-59474082290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (445994917424157 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54953592469 / 1000000000000) (-54953503512 / 1000000000000), orderedInterval (52109308707 / 1000000000000) (52109397664 / 1000000000000)))) (orderedInterval (11764899457 / 1000000000000) (11764901078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (239857549902819 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-89754166196 / 1000000000000) (-89754166195 / 1000000000000), orderedInterval (-49854320906 / 1000000000000) (-49854320905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (651259906925457 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14668566912 / 1000000000000) (14668566913 / 1000000000000), orderedInterval (60740895383 / 1000000000000) (60740895384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (889239724984689 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2230247019 / 1000000000000) (-2230247017 / 1000000000000), orderedInterval (-53461720640 / 1000000000000) (-53461720638 / 1000000000000)))) (orderedInterval (3609232439 / 1000000000000) (3609232462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (376005082575843 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42138110929 / 1000000000000) (42138110930 / 1000000000000), orderedInterval (70464514479 / 1000000000000) (70464514480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1528439785492803 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15112966087 / 1000000000000) (-15112965869 / 1000000000000), orderedInterval (37936311217 / 1000000000000) (37936311435 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1020926942598477 / 4000000000000) 1 (IntervalRat.scale (411 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49929342991 / 1000000000000) (-49929342917 / 1000000000000), orderedInterval (-1058621432 / 1000000000000) (-1058621359 / 1000000000000)))) (orderedInterval (-5301029787 / 1000000000000) (-5301029656 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_chunkChecks1 :
    compactCertificate333.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate333.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate333_chunkChecks1_0
    compactCertificate333_chunkChecks1_1 compactCertificate333_chunkChecks1_2

theorem compactCertificate333_chunkChecks2_0 :
    compactCertificate333.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (411 / 2) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48563081518 / 1000000000000) (-48563056025 / 1000000000000), orderedInterval (27312444267 / 1000000000000) (27312469761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (605481479587311 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (63395259975 / 1000000000000) (63395259977 / 1000000000000), orderedInterval (13455494725 / 1000000000000) (13455494727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (195800270096463 / 800000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24047252006 / 1000000000000) (24047252007 / 1000000000000), orderedInterval (44926771371 / 1000000000000) (44926771372 / 1000000000000)))) (orderedInterval (16858133211 / 1000000000000) (16858143384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (176677985651277 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99012426385 / 1000000000000) (99012426386 / 1000000000000), orderedInterval (66771263431 / 1000000000000) (66771263432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (474581921273769 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3610104935 / 1000000000000) (3610104938 / 1000000000000), orderedInterval (73147248772 / 1000000000000) (73147248775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1288582235589573 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27025920905 / 1000000000000) (27025928421 / 1000000000000), orderedInterval (-35337654315 / 1000000000000) (-35337646799 / 1000000000000)))) (orderedInterval (4701143950 / 1000000000000) (4701145306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (949163842547949 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32778555752 / 1000000000000) (-32778540008 / 1000000000000), orderedInterval (40174341721 / 1000000000000) (40174357464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1626408422185377 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33713972570 / 1000000000000) (-33713882985 / 1000000000000), orderedInterval (20755597406 / 1000000000000) (20755686991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1198005082575843 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44505023855 / 1000000000000) (-44505020370 / 1000000000000), orderedInterval (12111738730 / 1000000000000) (12111742215 / 1000000000000)))) (orderedInterval (-1782194343 / 1000000000000) (-1782183283 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_chunkChecks2_1 :
    compactCertificate333.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1838047877504589 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37167500088 / 1000000000000) (37167500882 / 1000000000000), orderedInterval (-2040934309 / 1000000000000) (-2040933516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1061197436860581 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39876905985 / 1000000000000) (39876993519 / 1000000000000), orderedInterval (-28526125908 / 1000000000000) (-28526038374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1883113473945129 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11728180653 / 1000000000000) (11728180654 / 1000000000000), orderedInterval (34840392236 / 1000000000000) (34840392237 / 1000000000000)))) (orderedInterval (19301001207 / 1000000000000) (19301013127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1759448878414701 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27928367672 / 1000000000000) (27928367673 / 1000000000000), orderedInterval (25800839988 / 1000000000000) (25800839989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1255625740417533 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22850395506 / 1000000000000) (22850395507 / 1000000000000), orderedInterval (38769743144 / 1000000000000) (38769743145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1423745763821307 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41812091524 / 1000000000000) (-41812090178 / 1000000000000), orderedInterval (6408890892 / 1000000000000) (6408892238 / 1000000000000)))) (orderedInterval (-3388798723 / 1000000000000) (-3388798636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1186970784916683 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (36952203933 / 1000000000000) (36952305700 / 1000000000000), orderedInterval (-27988812911 / 1000000000000) (-27988711144 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1048724685686343 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39432837156 / 1000000000000) (-39432732054 / 1000000000000), orderedInterval (29625468429 / 1000000000000) (29625573531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (303961289919957 / 800000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23246579955 / 1000000000000) (-23246579954 / 1000000000000), orderedInterval (-33661033337 / 1000000000000) (-33661033336 / 1000000000000)))) (orderedInterval (-2507641361 / 1000000000000) (-2507629032 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_chunkChecks2_2 :
    compactCertificate333.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (840772924524879 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25964770938 / 1000000000000) (-25964770937 / 1000000000000), orderedInterval (-48462160953 / 1000000000000) (-48462160952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (712732519424919 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (6143060556 / 1000000000000) (6143060574 / 1000000000000), orderedInterval (-59474082308 / 1000000000000) (-59474082290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (445994917424157 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54953592469 / 1000000000000) (-54953503512 / 1000000000000), orderedInterval (52109308707 / 1000000000000) (52109397664 / 1000000000000)))) (orderedInterval (-3612548195 / 1000000000000) (-3612547287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (239857549902819 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-89754166196 / 1000000000000) (-89754166195 / 1000000000000), orderedInterval (-49854320906 / 1000000000000) (-49854320905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (651259906925457 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14668566912 / 1000000000000) (14668566913 / 1000000000000), orderedInterval (60740895383 / 1000000000000) (60740895384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (889239724984689 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2230247019 / 1000000000000) (-2230247017 / 1000000000000), orderedInterval (-53461720640 / 1000000000000) (-53461720638 / 1000000000000)))) (orderedInterval (-149812982 / 1000000000000) (-149812959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (376005082575843 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42138110929 / 1000000000000) (42138110930 / 1000000000000), orderedInterval (70464514479 / 1000000000000) (70464514480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1528439785492803 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15112966087 / 1000000000000) (-15112965869 / 1000000000000), orderedInterval (37936311217 / 1000000000000) (37936311435 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1020926942598477 / 4000000000000) 2 (IntervalRat.scale (411 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49929342991 / 1000000000000) (-49929342917 / 1000000000000), orderedInterval (-1058621432 / 1000000000000) (-1058621359 / 1000000000000)))) (orderedInterval (-18731689364 / 1000000000000) (-18731689163 / 1000000000000))) = true
  rfl'

theorem compactCertificate333_chunkChecks2 :
    compactCertificate333.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate333.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate333_chunkChecks2_0
    compactCertificate333_chunkChecks2_1 compactCertificate333_chunkChecks2_2

theorem compactCertificate333_chunkChecks3_0 :
    compactCertificate333.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (411 / 2) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48563081518 / 1000000000000) (-48563056025 / 1000000000000), orderedInterval (27312444267 / 1000000000000) (27312469761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (605481479587311 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (63395259975 / 1000000000000) (63395259977 / 1000000000000), orderedInterval (13455494725 / 1000000000000) (13455494727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (195800270096463 / 800000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24047252006 / 1000000000000) (24047252007 / 1000000000000), orderedInterval (44926771371 / 1000000000000) (44926771372 / 1000000000000)))) (orderedInterval (-15411393888 / 1000000000000) (-15411383712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (176677985651277 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99012426385 / 1000000000000) (99012426386 / 1000000000000), orderedInterval (66771263431 / 1000000000000) (66771263432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (474581921273769 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3610104935 / 1000000000000) (3610104938 / 1000000000000), orderedInterval (73147248772 / 1000000000000) (73147248775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1288582235589573 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27025920905 / 1000000000000) (27025928421 / 1000000000000), orderedInterval (-35337654315 / 1000000000000) (-35337646799 / 1000000000000)))) (orderedInterval (-10207081003 / 1000000000000) (-10207078879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (949163842547949 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32778555752 / 1000000000000) (-32778540008 / 1000000000000), orderedInterval (40174341721 / 1000000000000) (40174357464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1626408422185377 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33713972570 / 1000000000000) (-33713882985 / 1000000000000), orderedInterval (20755597406 / 1000000000000) (20755686991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1198005082575843 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44505023855 / 1000000000000) (-44505020370 / 1000000000000), orderedInterval (12111738730 / 1000000000000) (12111742215 / 1000000000000)))) (orderedInterval (4061316631 / 1000000000000) (4061338414 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate333_chunkChecks3_1 :
    compactCertificate333.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1838047877504589 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37167500088 / 1000000000000) (37167500882 / 1000000000000), orderedInterval (-2040934309 / 1000000000000) (-2040933516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1061197436860581 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39876905985 / 1000000000000) (39876993519 / 1000000000000), orderedInterval (-28526125908 / 1000000000000) (-28526038374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1883113473945129 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11728180653 / 1000000000000) (11728180654 / 1000000000000), orderedInterval (34840392236 / 1000000000000) (34840392237 / 1000000000000)))) (orderedInterval (-59147897453 / 1000000000000) (-59147881072 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1759448878414701 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27928367672 / 1000000000000) (27928367673 / 1000000000000), orderedInterval (25800839988 / 1000000000000) (25800839989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1255625740417533 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22850395506 / 1000000000000) (22850395507 / 1000000000000), orderedInterval (38769743144 / 1000000000000) (38769743145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1423745763821307 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41812091524 / 1000000000000) (-41812090178 / 1000000000000), orderedInterval (6408890892 / 1000000000000) (6408892238 / 1000000000000)))) (orderedInterval (-8314238640 / 1000000000000) (-8314238492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1186970784916683 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (36952203933 / 1000000000000) (36952305700 / 1000000000000), orderedInterval (-27988812911 / 1000000000000) (-27988711144 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1048724685686343 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39432837156 / 1000000000000) (-39432732054 / 1000000000000), orderedInterval (29625468429 / 1000000000000) (29625573531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (303961289919957 / 800000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23246579955 / 1000000000000) (-23246579954 / 1000000000000), orderedInterval (-33661033337 / 1000000000000) (-33661033336 / 1000000000000)))) (orderedInterval (9953319284 / 1000000000000) (9953335438 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate333_chunkChecks3_2 :
    compactCertificate333.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (840772924524879 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25964770938 / 1000000000000) (-25964770937 / 1000000000000), orderedInterval (-48462160953 / 1000000000000) (-48462160952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (712732519424919 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (6143060556 / 1000000000000) (6143060574 / 1000000000000), orderedInterval (-59474082308 / 1000000000000) (-59474082290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (445994917424157 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54953592469 / 1000000000000) (-54953503512 / 1000000000000), orderedInterval (52109308707 / 1000000000000) (52109397664 / 1000000000000)))) (orderedInterval (-10739316859 / 1000000000000) (-10739316347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (239857549902819 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-89754166196 / 1000000000000) (-89754166195 / 1000000000000), orderedInterval (-49854320906 / 1000000000000) (-49854320905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (651259906925457 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14668566912 / 1000000000000) (14668566913 / 1000000000000), orderedInterval (60740895383 / 1000000000000) (60740895384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (889239724984689 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2230247019 / 1000000000000) (-2230247017 / 1000000000000), orderedInterval (-53461720640 / 1000000000000) (-53461720638 / 1000000000000)))) (orderedInterval (-4523923589 / 1000000000000) (-4523923565 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (376005082575843 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42138110929 / 1000000000000) (42138110930 / 1000000000000), orderedInterval (70464514479 / 1000000000000) (70464514480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1528439785492803 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15112966087 / 1000000000000) (-15112965869 / 1000000000000), orderedInterval (37936311217 / 1000000000000) (37936311435 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1020926942598477 / 4000000000000) 3 (IntervalRat.scale (411 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49929342991 / 1000000000000) (-49929342917 / 1000000000000), orderedInterval (-1058621432 / 1000000000000) (-1058621359 / 1000000000000)))) (orderedInterval (19522478808 / 1000000000000) (19522479131 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate333_chunkChecks3 :
    compactCertificate333.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate333.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate333_chunkChecks3_0
    compactCertificate333_chunkChecks3_1 compactCertificate333_chunkChecks3_2

theorem compactCertificate333_chunkChecks4_0 :
    compactCertificate333.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (411 / 2) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-48563081518 / 1000000000000) (-48563056025 / 1000000000000), orderedInterval (27312444267 / 1000000000000) (27312469761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (605481479587311 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (63395259975 / 1000000000000) (63395259977 / 1000000000000), orderedInterval (13455494725 / 1000000000000) (13455494727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (195800270096463 / 800000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (24047252006 / 1000000000000) (24047252007 / 1000000000000), orderedInterval (44926771371 / 1000000000000) (44926771372 / 1000000000000)))) (orderedInterval (-16085128311 / 1000000000000) (-16085118083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (176677985651277 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (99012426385 / 1000000000000) (99012426386 / 1000000000000), orderedInterval (66771263431 / 1000000000000) (66771263432 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (474581921273769 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3610104935 / 1000000000000) (3610104938 / 1000000000000), orderedInterval (73147248772 / 1000000000000) (73147248775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1288582235589573 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27025920905 / 1000000000000) (27025928421 / 1000000000000), orderedInterval (-35337654315 / 1000000000000) (-35337646799 / 1000000000000)))) (orderedInterval (-11490607953 / 1000000000000) (-11490604616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (949163842547949 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32778555752 / 1000000000000) (-32778540008 / 1000000000000), orderedInterval (40174341721 / 1000000000000) (40174357464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1626408422185377 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-33713972570 / 1000000000000) (-33713882985 / 1000000000000), orderedInterval (20755597406 / 1000000000000) (20755686991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1198005082575843 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44505023855 / 1000000000000) (-44505020370 / 1000000000000), orderedInterval (12111738730 / 1000000000000) (12111742215 / 1000000000000)))) (orderedInterval (11044723584 / 1000000000000) (11044766643 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate333_chunkChecks4_1 :
    compactCertificate333.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1838047877504589 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (37167500088 / 1000000000000) (37167500882 / 1000000000000), orderedInterval (-2040934309 / 1000000000000) (-2040933516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1061197436860581 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39876905985 / 1000000000000) (39876993519 / 1000000000000), orderedInterval (-28526125908 / 1000000000000) (-28526038374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1883113473945129 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11728180653 / 1000000000000) (11728180654 / 1000000000000), orderedInterval (34840392236 / 1000000000000) (34840392237 / 1000000000000)))) (orderedInterval (-110400911891 / 1000000000000) (-110400888433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1759448878414701 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27928367672 / 1000000000000) (27928367673 / 1000000000000), orderedInterval (25800839988 / 1000000000000) (25800839989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1255625740417533 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22850395506 / 1000000000000) (22850395507 / 1000000000000), orderedInterval (38769743144 / 1000000000000) (38769743145 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1423745763821307 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41812091524 / 1000000000000) (-41812090178 / 1000000000000), orderedInterval (6408890892 / 1000000000000) (6408892238 / 1000000000000)))) (orderedInterval (3166341184 / 1000000000000) (3166341441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1186970784916683 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (36952203933 / 1000000000000) (36952305700 / 1000000000000), orderedInterval (-27988812911 / 1000000000000) (-27988711144 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1048724685686343 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39432837156 / 1000000000000) (-39432732054 / 1000000000000), orderedInterval (29625468429 / 1000000000000) (29625573531 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (303961289919957 / 800000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23246579955 / 1000000000000) (-23246579954 / 1000000000000), orderedInterval (-33661033337 / 1000000000000) (-33661033336 / 1000000000000)))) (orderedInterval (781587555 / 1000000000000) (781608860 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate333_chunkChecks4_2 :
    compactCertificate333.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (840772924524879 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25964770938 / 1000000000000) (-25964770937 / 1000000000000), orderedInterval (-48462160953 / 1000000000000) (-48462160952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (712732519424919 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (6143060556 / 1000000000000) (6143060574 / 1000000000000), orderedInterval (-59474082308 / 1000000000000) (-59474082290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (445994917424157 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-54953592469 / 1000000000000) (-54953503512 / 1000000000000), orderedInterval (52109308707 / 1000000000000) (52109397664 / 1000000000000)))) (orderedInterval (4296881747 / 1000000000000) (4296882047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (239857549902819 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-89754166196 / 1000000000000) (-89754166195 / 1000000000000), orderedInterval (-49854320906 / 1000000000000) (-49854320905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (651259906925457 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (14668566912 / 1000000000000) (14668566913 / 1000000000000), orderedInterval (60740895383 / 1000000000000) (60740895384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (889239724984689 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2230247019 / 1000000000000) (-2230247017 / 1000000000000), orderedInterval (-53461720640 / 1000000000000) (-53461720638 / 1000000000000)))) (orderedInterval (159006667 / 1000000000000) (159006692 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (376005082575843 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42138110929 / 1000000000000) (42138110930 / 1000000000000), orderedInterval (70464514479 / 1000000000000) (70464514480 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1528439785492803 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15112966087 / 1000000000000) (-15112965869 / 1000000000000), orderedInterval (37936311217 / 1000000000000) (37936311435 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1020926942598477 / 4000000000000) 4 (IntervalRat.scale (411 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-49929342991 / 1000000000000) (-49929342917 / 1000000000000), orderedInterval (-1058621432 / 1000000000000) (-1058621359 / 1000000000000)))) (orderedInterval (36818124569 / 1000000000000) (36818125108 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate333_chunkChecks4 :
    compactCertificate333.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate333.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate333_chunkChecks4_0
    compactCertificate333_chunkChecks4_1 compactCertificate333_chunkChecks4_2

theorem compactCertificate333_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate333.chunkCheck r b = true :=
  compactCertificate333.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate333_chunkChecks0
    · exact compactCertificate333_chunkChecks1
    · exact compactCertificate333_chunkChecks2
    · exact compactCertificate333_chunkChecks3
    · exact compactCertificate333_chunkChecks4)

theorem compactCertificate333_coefficient0 :
    compactCertificate333.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate333_coefficient1 :
    compactCertificate333.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate333_coefficient2 :
    compactCertificate333.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate333_coefficient3 :
    compactCertificate333.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate333_coefficient4 :
    compactCertificate333.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate333_coefficients : ∀ r : Fin 5,
    compactCertificate333.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate333_coefficient0
  · exact compactCertificate333_coefficient1
  · exact compactCertificate333_coefficient2
  · exact compactCertificate333_coefficient3
  · exact compactCertificate333_coefficient4

theorem compactCertificate333_lower : (1 : ℚ) ≤ compactCertificate333.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate333, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate333_proves {t : ℝ} (ht : t ∈ compactCertificate333.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate333.proves compactCertificate333_states compactCertificate333_chunks
    compactCertificate333_coefficients compactCertificate333_lower ht

end Erdos232
