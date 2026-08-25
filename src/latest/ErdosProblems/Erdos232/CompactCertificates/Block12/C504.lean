/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate504 : CompactCertificate where
  left := 375
  right := 376
  center := 751 / 2
  grid := fun i =>
    match i.val with
    | 0 => 120
    | 1 => 88
    | 2 => 142
    | 3 => 26
    | 4 => 69
    | 5 => 187
    | 6 => 138
    | 7 => 237
    | 8 => 174
    | 9 => 267
    | 10 => 154
    | 11 => 274
    | 12 => 256
    | 13 => 183
    | 14 => 207
    | 15 => 173
    | 16 => 153
    | 17 => 221
    | 18 => 122
    | 19 => 104
    | 20 => 65
    | 21 => 35
    | 22 => 95
    | 23 => 129
    | 24 => 55
    | 25 => 222
    | _ => 149
  point := fun i =>
    match i.val with
    | 0 => 751 / 2
    | 1 => 1106366401873651 / 4000000000000
    | 2 => 357776162633683 / 800000000000
    | 3 => 322834956749657 / 4000000000000
    | 4 => 867180104322629 / 4000000000000
    | 5 => 2354562673790193 / 4000000000000
    | 6 => 1734360208646009 / 4000000000000
    | 7 => 2971855778737757 / 4000000000000
    | 8 => 2189055515850263 / 4000000000000
    | 9 => 3358574102204249 / 4000000000000
    | 10 => 1939073662000721 / 4000000000000
    | 11 => 3440920240712389 / 4000000000000
    | 12 => 3214954033307641 / 4000000000000
    | 13 => 2294342897940553 / 4000000000000
    | 14 => 2601540312967887 / 4000000000000
    | 15 => 2168893088740703 / 4000000000000
    | 16 => 1916282819830763 / 4000000000000
    | 17 => 555413451897537 / 800000000000
    | 18 => 1536302837757139 / 4000000000000
    | 19 => 1302340929654779 / 4000000000000
    | 20 => 814944484149737 / 4000000000000
    | 21 => 438279853958679 / 4000000000000
    | 22 => 1190015061073037 / 4000000000000
    | 23 => 1624863828378349 / 4000000000000
    | 24 => 687055515850263 / 4000000000000
    | 25 => 2792842527749623 / 4000000000000
    | _ => 1865489376864857 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-26715888485 / 1000000000000) (-26715878756 / 1000000000000), orderedInterval (31366926719 / 1000000000000) (31366936448 / 1000000000000))
    | 1 => (orderedInterval (38064368880 / 1000000000000) (38064368881 / 1000000000000), orderedInterval (29133290865 / 1000000000000) (29133290866 / 1000000000000))
    | 2 => (orderedInterval (35713441893 / 1000000000000) (35713456347 / 1000000000000), orderedInterval (-12207633737 / 1000000000000) (-12207619283 / 1000000000000))
    | 3 => (orderedInterval (-16670190472 / 1000000000000) (-16670190344 / 1000000000000), orderedInterval (87339226027 / 1000000000000) (87339226155 / 1000000000000))
    | 4 => (orderedInterval (-39247033781 / 1000000000000) (-39247033780 / 1000000000000), orderedInterval (-37274914456 / 1000000000000) (-37274914455 / 1000000000000))
    | 5 => (orderedInterval (-30574004964 / 1000000000000) (-30573960712 / 1000000000000), orderedInterval (12139557916 / 1000000000000) (12139602168 / 1000000000000))
    | 6 => (orderedInterval (28414495441 / 1000000000000) (28414495442 / 1000000000000), orderedInterval (25674607321 / 1000000000000) (25674607322 / 1000000000000))
    | 7 => (orderedInterval (21166855473 / 1000000000000) (21166859558 / 1000000000000), orderedInterval (-20233769484 / 1000000000000) (-20233765399 / 1000000000000))
    | 8 => (orderedInterval (33677332639 / 1000000000000) (33677332726 / 1000000000000), orderedInterval (5365000823 / 1000000000000) (5365000910 / 1000000000000))
    | 9 => (orderedInterval (-27497190720 / 1000000000000) (-27497183999 / 1000000000000), orderedInterval (1467919100 / 1000000000000) (1467925821 / 1000000000000))
    | 10 => (orderedInterval (35669395869 / 1000000000000) (35669399634 / 1000000000000), orderedInterval (-6435116645 / 1000000000000) (-6435112881 / 1000000000000))
    | 11 => (orderedInterval (5908200316 / 1000000000000) (5908200317 / 1000000000000), orderedInterval (26551242670 / 1000000000000) (26551242671 / 1000000000000))
    | 12 => (orderedInterval (7670300299 / 1000000000000) (7670300300 / 1000000000000), orderedInterval (27073630710 / 1000000000000) (27073630711 / 1000000000000))
    | 13 => (orderedInterval (17144218269 / 1000000000000) (17144218768 / 1000000000000), orderedInterval (-28580145843 / 1000000000000) (-28580145345 / 1000000000000))
    | 14 => (orderedInterval (-23722460978 / 1000000000000) (-23722460977 / 1000000000000), orderedInterval (-20379800587 / 1000000000000) (-20379800586 / 1000000000000))
    | 15 => (orderedInterval (16037932514 / 1000000000000) (16037932823 / 1000000000000), orderedInterval (-30294758888 / 1000000000000) (-30294758579 / 1000000000000))
    | 16 => (orderedInterval (26348340616 / 1000000000000) (26348356398 / 1000000000000), orderedInterval (-25219339172 / 1000000000000) (-25219323390 / 1000000000000))
    | 17 => (orderedInterval (-20862787860 / 1000000000000) (-20862787859 / 1000000000000), orderedInterval (-21932893193 / 1000000000000) (-21932893192 / 1000000000000))
    | 18 => (orderedInterval (40707839203 / 1000000000000) (40707839508 / 1000000000000), orderedInterval (-691431179 / 1000000000000) (-691430875 / 1000000000000))
    | 19 => (orderedInterval (-15386187397 / 1000000000000) (-15386187165 / 1000000000000), orderedInterval (41479340876 / 1000000000000) (41479341108 / 1000000000000))
    | 20 => (orderedInterval (-17445098888 / 1000000000000) (-17445098887 / 1000000000000), orderedInterval (-53064655408 / 1000000000000) (-53064655407 / 1000000000000))
    | 21 => (orderedInterval (-29576155539 / 1000000000000) (-29576155538 / 1000000000000), orderedInterval (-70117868454 / 1000000000000) (-70117868453 / 1000000000000))
    | 22 => (orderedInterval (7486686340 / 1000000000000) (7486686358 / 1000000000000), orderedInterval (-45661500351 / 1000000000000) (-45661500333 / 1000000000000))
    | 23 => (orderedInterval (-39051444000 / 1000000000000) (-39051441885 / 1000000000000), orderedInterval (6542607054 / 1000000000000) (6542609169 / 1000000000000))
    | 24 => (orderedInterval (14414899852 / 1000000000000) (14414899989 / 1000000000000), orderedInterval (-59190844729 / 1000000000000) (-59190844592 / 1000000000000))
    | 25 => (orderedInterval (30194721144 / 1000000000000) (30194722730 / 1000000000000), orderedInterval (235471062 / 1000000000000) (235472648 / 1000000000000))
    | _ => (orderedInterval (29832750407 / 1000000000000) (29832806549 / 1000000000000), orderedInterval (-21827680357 / 1000000000000) (-21827624215 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8138851409 / 1000000000000) (-8138846678 / 1000000000000)
      | 1 => orderedInterval (921373886 / 1000000000000) (921377078 / 1000000000000)
      | 2 => orderedInterval (161044036 / 1000000000000) (161044186 / 1000000000000)
      | 3 => orderedInterval (8368611718 / 1000000000000) (8368613340 / 1000000000000)
      | 4 => orderedInterval (1602783118 / 1000000000000) (1602783210 / 1000000000000)
      | 5 => orderedInterval (-1856797924 / 1000000000000) (-1856796981 / 1000000000000)
      | 6 => orderedInterval (-6205948320 / 1000000000000) (-6205948164 / 1000000000000)
      | 7 => orderedInterval (3369136107 / 1000000000000) (3369136315 / 1000000000000)
      | _ => orderedInterval (-7968432277 / 1000000000000) (-7968421510 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11779530469 / 1000000000000) (11779535365 / 1000000000000)
      | 1 => orderedInterval (-2342279526 / 1000000000000) (-2342274543 / 1000000000000)
      | 2 => orderedInterval (1423796582 / 1000000000000) (1423796871 / 1000000000000)
      | 3 => orderedInterval (7448007631 / 1000000000000) (7448010970 / 1000000000000)
      | 4 => orderedInterval (-4995859795 / 1000000000000) (-4995859650 / 1000000000000)
      | 5 => orderedInterval (297834639 / 1000000000000) (297835848 / 1000000000000)
      | 6 => orderedInterval (-2859881942 / 1000000000000) (-2859881793 / 1000000000000)
      | 7 => orderedInterval (656108959 / 1000000000000) (656109175 / 1000000000000)
      | _ => orderedInterval (4887691655 / 1000000000000) (4887705125 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (7392710095 / 1000000000000) (7392715201 / 1000000000000)
      | 1 => orderedInterval (-4865663988 / 1000000000000) (-4865656173 / 1000000000000)
      | 2 => orderedInterval (823269986 / 1000000000000) (823270550 / 1000000000000)
      | 3 => orderedInterval (-33261987396 / 1000000000000) (-33261980289 / 1000000000000)
      | 4 => orderedInterval (-3495243468 / 1000000000000) (-3495243237 / 1000000000000)
      | 5 => orderedInterval (3893404204 / 1000000000000) (3893405763 / 1000000000000)
      | 6 => orderedInterval (6329656393 / 1000000000000) (6329656537 / 1000000000000)
      | 7 => orderedInterval (-3444147205 / 1000000000000) (-3444146974 / 1000000000000)
      | _ => orderedInterval (17101245876 / 1000000000000) (17101262823 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-11350633874 / 1000000000000) (-11350628532 / 1000000000000)
      | 1 => orderedInterval (3608798604 / 1000000000000) (3608810849 / 1000000000000)
      | 2 => orderedInterval (-5237735659 / 1000000000000) (-5237734557 / 1000000000000)
      | 3 => orderedInterval (-41349217299 / 1000000000000) (-41349201879 / 1000000000000)
      | 4 => orderedInterval (13899179509 / 1000000000000) (13899179881 / 1000000000000)
      | 5 => orderedInterval (1595246610 / 1000000000000) (1595248620 / 1000000000000)
      | 6 => orderedInterval (1671176413 / 1000000000000) (1671176555 / 1000000000000)
      | 7 => orderedInterval (96619076 / 1000000000000) (96619324 / 1000000000000)
      | _ => orderedInterval (-7734529083 / 1000000000000) (-7734507694 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-6207586916 / 1000000000000) (-6207581279 / 1000000000000)
      | 1 => orderedInterval (12947514828 / 1000000000000) (12947534054 / 1000000000000)
      | 2 => orderedInterval (-6305847425 / 1000000000000) (-6305845259 / 1000000000000)
      | 3 => orderedInterval (152842435809 / 1000000000000) (152842469735 / 1000000000000)
      | 4 => orderedInterval (6926371108 / 1000000000000) (6926371720 / 1000000000000)
      | 5 => orderedInterval (-9440499464 / 1000000000000) (-9440496857 / 1000000000000)
      | 6 => orderedInterval (-6690005498 / 1000000000000) (-6690005357 / 1000000000000)
      | 7 => orderedInterval (4035460375 / 1000000000000) (4035460642 / 1000000000000)
      | _ => orderedInterval (-42655427219 / 1000000000000) (-42655399964 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9747081065 / 1000000000000) (-9747059204 / 1000000000000)
    | 1 => orderedInterval (16294948672 / 1000000000000) (16294977368 / 1000000000000)
    | 2 => orderedInterval (-9526755503 / 1000000000000) (-9526715799 / 1000000000000)
    | 3 => orderedInterval (-44801095703 / 1000000000000) (-44801037433 / 1000000000000)
    | _ => orderedInterval (105452415598 / 1000000000000) (105452507435 / 1000000000000)

theorem compactCertificate504_stateChecks0 :
    compactCertificate504.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (751 / 2)) (orderedInterval (-26715888485 / 1000000000000) (-26715878756 / 1000000000000), orderedInterval (31366926719 / 1000000000000) (31366936448 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1106366401873651 / 4000000000000)) (orderedInterval (38064368880 / 1000000000000) (38064368881 / 1000000000000), orderedInterval (29133290865 / 1000000000000) (29133290866 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (357776162633683 / 800000000000)) (orderedInterval (35713441893 / 1000000000000) (35713456347 / 1000000000000), orderedInterval (-12207633737 / 1000000000000) (-12207619283 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_stateChecks1 :
    compactCertificate504.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (322834956749657 / 4000000000000)) (orderedInterval (-16670190472 / 1000000000000) (-16670190344 / 1000000000000), orderedInterval (87339226027 / 1000000000000) (87339226155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (867180104322629 / 4000000000000)) (orderedInterval (-39247033781 / 1000000000000) (-39247033780 / 1000000000000), orderedInterval (-37274914456 / 1000000000000) (-37274914455 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2354562673790193 / 4000000000000)) (orderedInterval (-30574004964 / 1000000000000) (-30573960712 / 1000000000000), orderedInterval (12139557916 / 1000000000000) (12139602168 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_stateChecks2 :
    compactCertificate504.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1734360208646009 / 4000000000000)) (orderedInterval (28414495441 / 1000000000000) (28414495442 / 1000000000000), orderedInterval (25674607321 / 1000000000000) (25674607322 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2971855778737757 / 4000000000000)) (orderedInterval (21166855473 / 1000000000000) (21166859558 / 1000000000000), orderedInterval (-20233769484 / 1000000000000) (-20233765399 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2189055515850263 / 4000000000000)) (orderedInterval (33677332639 / 1000000000000) (33677332726 / 1000000000000), orderedInterval (5365000823 / 1000000000000) (5365000910 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_stateChecks3 :
    compactCertificate504.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3358574102204249 / 4000000000000)) (orderedInterval (-27497190720 / 1000000000000) (-27497183999 / 1000000000000), orderedInterval (1467919100 / 1000000000000) (1467925821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1939073662000721 / 4000000000000)) (orderedInterval (35669395869 / 1000000000000) (35669399634 / 1000000000000), orderedInterval (-6435116645 / 1000000000000) (-6435112881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (3440920240712389 / 4000000000000)) (orderedInterval (5908200316 / 1000000000000) (5908200317 / 1000000000000), orderedInterval (26551242670 / 1000000000000) (26551242671 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_stateChecks4 :
    compactCertificate504.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (3214954033307641 / 4000000000000)) (orderedInterval (7670300299 / 1000000000000) (7670300300 / 1000000000000), orderedInterval (27073630710 / 1000000000000) (27073630711 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2294342897940553 / 4000000000000)) (orderedInterval (17144218269 / 1000000000000) (17144218768 / 1000000000000), orderedInterval (-28580145843 / 1000000000000) (-28580145345 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2601540312967887 / 4000000000000)) (orderedInterval (-23722460978 / 1000000000000) (-23722460977 / 1000000000000), orderedInterval (-20379800587 / 1000000000000) (-20379800586 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_stateChecks5 :
    compactCertificate504.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2168893088740703 / 4000000000000)) (orderedInterval (16037932514 / 1000000000000) (16037932823 / 1000000000000), orderedInterval (-30294758888 / 1000000000000) (-30294758579 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1916282819830763 / 4000000000000)) (orderedInterval (26348340616 / 1000000000000) (26348356398 / 1000000000000), orderedInterval (-25219339172 / 1000000000000) (-25219323390 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (555413451897537 / 800000000000)) (orderedInterval (-20862787860 / 1000000000000) (-20862787859 / 1000000000000), orderedInterval (-21932893193 / 1000000000000) (-21932893192 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_stateChecks6 :
    compactCertificate504.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1536302837757139 / 4000000000000)) (orderedInterval (40707839203 / 1000000000000) (40707839508 / 1000000000000), orderedInterval (-691431179 / 1000000000000) (-691430875 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1302340929654779 / 4000000000000)) (orderedInterval (-15386187397 / 1000000000000) (-15386187165 / 1000000000000), orderedInterval (41479340876 / 1000000000000) (41479341108 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (814944484149737 / 4000000000000)) (orderedInterval (-17445098888 / 1000000000000) (-17445098887 / 1000000000000), orderedInterval (-53064655408 / 1000000000000) (-53064655407 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_stateChecks7 :
    compactCertificate504.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (438279853958679 / 4000000000000)) (orderedInterval (-29576155539 / 1000000000000) (-29576155538 / 1000000000000), orderedInterval (-70117868454 / 1000000000000) (-70117868453 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1190015061073037 / 4000000000000)) (orderedInterval (7486686340 / 1000000000000) (7486686358 / 1000000000000), orderedInterval (-45661500351 / 1000000000000) (-45661500333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1624863828378349 / 4000000000000)) (orderedInterval (-39051444000 / 1000000000000) (-39051441885 / 1000000000000), orderedInterval (6542607054 / 1000000000000) (6542609169 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_stateChecks8 :
    compactCertificate504.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (687055515850263 / 4000000000000)) (orderedInterval (14414899852 / 1000000000000) (14414899989 / 1000000000000), orderedInterval (-59190844729 / 1000000000000) (-59190844592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2792842527749623 / 4000000000000)) (orderedInterval (30194721144 / 1000000000000) (30194722730 / 1000000000000), orderedInterval (235471062 / 1000000000000) (235472648 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1865489376864857 / 4000000000000)) (orderedInterval (29832750407 / 1000000000000) (29832806549 / 1000000000000), orderedInterval (-21827680357 / 1000000000000) (-21827624215 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_states : ∀ j,
    BesselStateValid (compactCertificate504.point j) (compactCertificate504.state j) :=
  compactCertificate504.statesValid_of_checks3 compactCertificate504_stateChecks0
    compactCertificate504_stateChecks1 compactCertificate504_stateChecks2
    compactCertificate504_stateChecks3 compactCertificate504_stateChecks4
    compactCertificate504_stateChecks5 compactCertificate504_stateChecks6
    compactCertificate504_stateChecks7 compactCertificate504_stateChecks8

theorem compactCertificate504_chunkChecks0_0 :
    compactCertificate504.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (751 / 2) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26715888485 / 1000000000000) (-26715878756 / 1000000000000), orderedInterval (31366926719 / 1000000000000) (31366936448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1106366401873651 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38064368880 / 1000000000000) (38064368881 / 1000000000000), orderedInterval (29133290865 / 1000000000000) (29133290866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (357776162633683 / 800000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35713441893 / 1000000000000) (35713456347 / 1000000000000), orderedInterval (-12207633737 / 1000000000000) (-12207619283 / 1000000000000)))) (orderedInterval (-8138851409 / 1000000000000) (-8138846678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (322834956749657 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-16670190472 / 1000000000000) (-16670190344 / 1000000000000), orderedInterval (87339226027 / 1000000000000) (87339226155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (867180104322629 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39247033781 / 1000000000000) (-39247033780 / 1000000000000), orderedInterval (-37274914456 / 1000000000000) (-37274914455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2354562673790193 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30574004964 / 1000000000000) (-30573960712 / 1000000000000), orderedInterval (12139557916 / 1000000000000) (12139602168 / 1000000000000)))) (orderedInterval (921373886 / 1000000000000) (921377078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1734360208646009 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28414495441 / 1000000000000) (28414495442 / 1000000000000), orderedInterval (25674607321 / 1000000000000) (25674607322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2971855778737757 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21166855473 / 1000000000000) (21166859558 / 1000000000000), orderedInterval (-20233769484 / 1000000000000) (-20233765399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2189055515850263 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33677332639 / 1000000000000) (33677332726 / 1000000000000), orderedInterval (5365000823 / 1000000000000) (5365000910 / 1000000000000)))) (orderedInterval (161044036 / 1000000000000) (161044186 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_chunkChecks0_1 :
    compactCertificate504.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3358574102204249 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27497190720 / 1000000000000) (-27497183999 / 1000000000000), orderedInterval (1467919100 / 1000000000000) (1467925821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1939073662000721 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35669395869 / 1000000000000) (35669399634 / 1000000000000), orderedInterval (-6435116645 / 1000000000000) (-6435112881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3440920240712389 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5908200316 / 1000000000000) (5908200317 / 1000000000000), orderedInterval (26551242670 / 1000000000000) (26551242671 / 1000000000000)))) (orderedInterval (8368611718 / 1000000000000) (8368613340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3214954033307641 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7670300299 / 1000000000000) (7670300300 / 1000000000000), orderedInterval (27073630710 / 1000000000000) (27073630711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2294342897940553 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17144218269 / 1000000000000) (17144218768 / 1000000000000), orderedInterval (-28580145843 / 1000000000000) (-28580145345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2601540312967887 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23722460978 / 1000000000000) (-23722460977 / 1000000000000), orderedInterval (-20379800587 / 1000000000000) (-20379800586 / 1000000000000)))) (orderedInterval (1602783118 / 1000000000000) (1602783210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2168893088740703 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16037932514 / 1000000000000) (16037932823 / 1000000000000), orderedInterval (-30294758888 / 1000000000000) (-30294758579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1916282819830763 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26348340616 / 1000000000000) (26348356398 / 1000000000000), orderedInterval (-25219339172 / 1000000000000) (-25219323390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (555413451897537 / 800000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20862787860 / 1000000000000) (-20862787859 / 1000000000000), orderedInterval (-21932893193 / 1000000000000) (-21932893192 / 1000000000000)))) (orderedInterval (-1856797924 / 1000000000000) (-1856796981 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_chunkChecks0_2 :
    compactCertificate504.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1536302837757139 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40707839203 / 1000000000000) (40707839508 / 1000000000000), orderedInterval (-691431179 / 1000000000000) (-691430875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1302340929654779 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-15386187397 / 1000000000000) (-15386187165 / 1000000000000), orderedInterval (41479340876 / 1000000000000) (41479341108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (814944484149737 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-17445098888 / 1000000000000) (-17445098887 / 1000000000000), orderedInterval (-53064655408 / 1000000000000) (-53064655407 / 1000000000000)))) (orderedInterval (-6205948320 / 1000000000000) (-6205948164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (438279853958679 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29576155539 / 1000000000000) (-29576155538 / 1000000000000), orderedInterval (-70117868454 / 1000000000000) (-70117868453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1190015061073037 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7486686340 / 1000000000000) (7486686358 / 1000000000000), orderedInterval (-45661500351 / 1000000000000) (-45661500333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1624863828378349 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39051444000 / 1000000000000) (-39051441885 / 1000000000000), orderedInterval (6542607054 / 1000000000000) (6542609169 / 1000000000000)))) (orderedInterval (3369136107 / 1000000000000) (3369136315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (687055515850263 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (14414899852 / 1000000000000) (14414899989 / 1000000000000), orderedInterval (-59190844729 / 1000000000000) (-59190844592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2792842527749623 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30194721144 / 1000000000000) (30194722730 / 1000000000000), orderedInterval (235471062 / 1000000000000) (235472648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1865489376864857 / 4000000000000) 0 (IntervalRat.scale (751 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29832750407 / 1000000000000) (29832806549 / 1000000000000), orderedInterval (-21827680357 / 1000000000000) (-21827624215 / 1000000000000)))) (orderedInterval (-7968432277 / 1000000000000) (-7968421510 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_chunkChecks0 :
    compactCertificate504.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate504.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate504_chunkChecks0_0
    compactCertificate504_chunkChecks0_1 compactCertificate504_chunkChecks0_2

theorem compactCertificate504_chunkChecks1_0 :
    compactCertificate504.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (751 / 2) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26715888485 / 1000000000000) (-26715878756 / 1000000000000), orderedInterval (31366926719 / 1000000000000) (31366936448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1106366401873651 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38064368880 / 1000000000000) (38064368881 / 1000000000000), orderedInterval (29133290865 / 1000000000000) (29133290866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (357776162633683 / 800000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35713441893 / 1000000000000) (35713456347 / 1000000000000), orderedInterval (-12207633737 / 1000000000000) (-12207619283 / 1000000000000)))) (orderedInterval (11779530469 / 1000000000000) (11779535365 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (322834956749657 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-16670190472 / 1000000000000) (-16670190344 / 1000000000000), orderedInterval (87339226027 / 1000000000000) (87339226155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (867180104322629 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39247033781 / 1000000000000) (-39247033780 / 1000000000000), orderedInterval (-37274914456 / 1000000000000) (-37274914455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2354562673790193 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30574004964 / 1000000000000) (-30573960712 / 1000000000000), orderedInterval (12139557916 / 1000000000000) (12139602168 / 1000000000000)))) (orderedInterval (-2342279526 / 1000000000000) (-2342274543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1734360208646009 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28414495441 / 1000000000000) (28414495442 / 1000000000000), orderedInterval (25674607321 / 1000000000000) (25674607322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2971855778737757 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21166855473 / 1000000000000) (21166859558 / 1000000000000), orderedInterval (-20233769484 / 1000000000000) (-20233765399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2189055515850263 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33677332639 / 1000000000000) (33677332726 / 1000000000000), orderedInterval (5365000823 / 1000000000000) (5365000910 / 1000000000000)))) (orderedInterval (1423796582 / 1000000000000) (1423796871 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_chunkChecks1_1 :
    compactCertificate504.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3358574102204249 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27497190720 / 1000000000000) (-27497183999 / 1000000000000), orderedInterval (1467919100 / 1000000000000) (1467925821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1939073662000721 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35669395869 / 1000000000000) (35669399634 / 1000000000000), orderedInterval (-6435116645 / 1000000000000) (-6435112881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3440920240712389 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5908200316 / 1000000000000) (5908200317 / 1000000000000), orderedInterval (26551242670 / 1000000000000) (26551242671 / 1000000000000)))) (orderedInterval (7448007631 / 1000000000000) (7448010970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3214954033307641 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7670300299 / 1000000000000) (7670300300 / 1000000000000), orderedInterval (27073630710 / 1000000000000) (27073630711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2294342897940553 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17144218269 / 1000000000000) (17144218768 / 1000000000000), orderedInterval (-28580145843 / 1000000000000) (-28580145345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2601540312967887 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23722460978 / 1000000000000) (-23722460977 / 1000000000000), orderedInterval (-20379800587 / 1000000000000) (-20379800586 / 1000000000000)))) (orderedInterval (-4995859795 / 1000000000000) (-4995859650 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2168893088740703 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16037932514 / 1000000000000) (16037932823 / 1000000000000), orderedInterval (-30294758888 / 1000000000000) (-30294758579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1916282819830763 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26348340616 / 1000000000000) (26348356398 / 1000000000000), orderedInterval (-25219339172 / 1000000000000) (-25219323390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (555413451897537 / 800000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20862787860 / 1000000000000) (-20862787859 / 1000000000000), orderedInterval (-21932893193 / 1000000000000) (-21932893192 / 1000000000000)))) (orderedInterval (297834639 / 1000000000000) (297835848 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_chunkChecks1_2 :
    compactCertificate504.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1536302837757139 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40707839203 / 1000000000000) (40707839508 / 1000000000000), orderedInterval (-691431179 / 1000000000000) (-691430875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1302340929654779 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-15386187397 / 1000000000000) (-15386187165 / 1000000000000), orderedInterval (41479340876 / 1000000000000) (41479341108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (814944484149737 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-17445098888 / 1000000000000) (-17445098887 / 1000000000000), orderedInterval (-53064655408 / 1000000000000) (-53064655407 / 1000000000000)))) (orderedInterval (-2859881942 / 1000000000000) (-2859881793 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (438279853958679 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29576155539 / 1000000000000) (-29576155538 / 1000000000000), orderedInterval (-70117868454 / 1000000000000) (-70117868453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1190015061073037 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7486686340 / 1000000000000) (7486686358 / 1000000000000), orderedInterval (-45661500351 / 1000000000000) (-45661500333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1624863828378349 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39051444000 / 1000000000000) (-39051441885 / 1000000000000), orderedInterval (6542607054 / 1000000000000) (6542609169 / 1000000000000)))) (orderedInterval (656108959 / 1000000000000) (656109175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (687055515850263 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (14414899852 / 1000000000000) (14414899989 / 1000000000000), orderedInterval (-59190844729 / 1000000000000) (-59190844592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2792842527749623 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30194721144 / 1000000000000) (30194722730 / 1000000000000), orderedInterval (235471062 / 1000000000000) (235472648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1865489376864857 / 4000000000000) 1 (IntervalRat.scale (751 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29832750407 / 1000000000000) (29832806549 / 1000000000000), orderedInterval (-21827680357 / 1000000000000) (-21827624215 / 1000000000000)))) (orderedInterval (4887691655 / 1000000000000) (4887705125 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_chunkChecks1 :
    compactCertificate504.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate504.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate504_chunkChecks1_0
    compactCertificate504_chunkChecks1_1 compactCertificate504_chunkChecks1_2

theorem compactCertificate504_chunkChecks2_0 :
    compactCertificate504.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (751 / 2) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26715888485 / 1000000000000) (-26715878756 / 1000000000000), orderedInterval (31366926719 / 1000000000000) (31366936448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1106366401873651 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38064368880 / 1000000000000) (38064368881 / 1000000000000), orderedInterval (29133290865 / 1000000000000) (29133290866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (357776162633683 / 800000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35713441893 / 1000000000000) (35713456347 / 1000000000000), orderedInterval (-12207633737 / 1000000000000) (-12207619283 / 1000000000000)))) (orderedInterval (7392710095 / 1000000000000) (7392715201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (322834956749657 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-16670190472 / 1000000000000) (-16670190344 / 1000000000000), orderedInterval (87339226027 / 1000000000000) (87339226155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (867180104322629 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39247033781 / 1000000000000) (-39247033780 / 1000000000000), orderedInterval (-37274914456 / 1000000000000) (-37274914455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2354562673790193 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30574004964 / 1000000000000) (-30573960712 / 1000000000000), orderedInterval (12139557916 / 1000000000000) (12139602168 / 1000000000000)))) (orderedInterval (-4865663988 / 1000000000000) (-4865656173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1734360208646009 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28414495441 / 1000000000000) (28414495442 / 1000000000000), orderedInterval (25674607321 / 1000000000000) (25674607322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2971855778737757 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21166855473 / 1000000000000) (21166859558 / 1000000000000), orderedInterval (-20233769484 / 1000000000000) (-20233765399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2189055515850263 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33677332639 / 1000000000000) (33677332726 / 1000000000000), orderedInterval (5365000823 / 1000000000000) (5365000910 / 1000000000000)))) (orderedInterval (823269986 / 1000000000000) (823270550 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_chunkChecks2_1 :
    compactCertificate504.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3358574102204249 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27497190720 / 1000000000000) (-27497183999 / 1000000000000), orderedInterval (1467919100 / 1000000000000) (1467925821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1939073662000721 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35669395869 / 1000000000000) (35669399634 / 1000000000000), orderedInterval (-6435116645 / 1000000000000) (-6435112881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3440920240712389 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5908200316 / 1000000000000) (5908200317 / 1000000000000), orderedInterval (26551242670 / 1000000000000) (26551242671 / 1000000000000)))) (orderedInterval (-33261987396 / 1000000000000) (-33261980289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3214954033307641 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7670300299 / 1000000000000) (7670300300 / 1000000000000), orderedInterval (27073630710 / 1000000000000) (27073630711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2294342897940553 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17144218269 / 1000000000000) (17144218768 / 1000000000000), orderedInterval (-28580145843 / 1000000000000) (-28580145345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2601540312967887 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23722460978 / 1000000000000) (-23722460977 / 1000000000000), orderedInterval (-20379800587 / 1000000000000) (-20379800586 / 1000000000000)))) (orderedInterval (-3495243468 / 1000000000000) (-3495243237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2168893088740703 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16037932514 / 1000000000000) (16037932823 / 1000000000000), orderedInterval (-30294758888 / 1000000000000) (-30294758579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1916282819830763 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26348340616 / 1000000000000) (26348356398 / 1000000000000), orderedInterval (-25219339172 / 1000000000000) (-25219323390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (555413451897537 / 800000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20862787860 / 1000000000000) (-20862787859 / 1000000000000), orderedInterval (-21932893193 / 1000000000000) (-21932893192 / 1000000000000)))) (orderedInterval (3893404204 / 1000000000000) (3893405763 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_chunkChecks2_2 :
    compactCertificate504.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1536302837757139 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40707839203 / 1000000000000) (40707839508 / 1000000000000), orderedInterval (-691431179 / 1000000000000) (-691430875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1302340929654779 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-15386187397 / 1000000000000) (-15386187165 / 1000000000000), orderedInterval (41479340876 / 1000000000000) (41479341108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (814944484149737 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-17445098888 / 1000000000000) (-17445098887 / 1000000000000), orderedInterval (-53064655408 / 1000000000000) (-53064655407 / 1000000000000)))) (orderedInterval (6329656393 / 1000000000000) (6329656537 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (438279853958679 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29576155539 / 1000000000000) (-29576155538 / 1000000000000), orderedInterval (-70117868454 / 1000000000000) (-70117868453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1190015061073037 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7486686340 / 1000000000000) (7486686358 / 1000000000000), orderedInterval (-45661500351 / 1000000000000) (-45661500333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1624863828378349 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39051444000 / 1000000000000) (-39051441885 / 1000000000000), orderedInterval (6542607054 / 1000000000000) (6542609169 / 1000000000000)))) (orderedInterval (-3444147205 / 1000000000000) (-3444146974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (687055515850263 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (14414899852 / 1000000000000) (14414899989 / 1000000000000), orderedInterval (-59190844729 / 1000000000000) (-59190844592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2792842527749623 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30194721144 / 1000000000000) (30194722730 / 1000000000000), orderedInterval (235471062 / 1000000000000) (235472648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1865489376864857 / 4000000000000) 2 (IntervalRat.scale (751 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29832750407 / 1000000000000) (29832806549 / 1000000000000), orderedInterval (-21827680357 / 1000000000000) (-21827624215 / 1000000000000)))) (orderedInterval (17101245876 / 1000000000000) (17101262823 / 1000000000000))) = true
  rfl'

theorem compactCertificate504_chunkChecks2 :
    compactCertificate504.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate504.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate504_chunkChecks2_0
    compactCertificate504_chunkChecks2_1 compactCertificate504_chunkChecks2_2

theorem compactCertificate504_chunkChecks3_0 :
    compactCertificate504.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (751 / 2) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26715888485 / 1000000000000) (-26715878756 / 1000000000000), orderedInterval (31366926719 / 1000000000000) (31366936448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1106366401873651 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38064368880 / 1000000000000) (38064368881 / 1000000000000), orderedInterval (29133290865 / 1000000000000) (29133290866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (357776162633683 / 800000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35713441893 / 1000000000000) (35713456347 / 1000000000000), orderedInterval (-12207633737 / 1000000000000) (-12207619283 / 1000000000000)))) (orderedInterval (-11350633874 / 1000000000000) (-11350628532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (322834956749657 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-16670190472 / 1000000000000) (-16670190344 / 1000000000000), orderedInterval (87339226027 / 1000000000000) (87339226155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (867180104322629 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39247033781 / 1000000000000) (-39247033780 / 1000000000000), orderedInterval (-37274914456 / 1000000000000) (-37274914455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2354562673790193 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30574004964 / 1000000000000) (-30573960712 / 1000000000000), orderedInterval (12139557916 / 1000000000000) (12139602168 / 1000000000000)))) (orderedInterval (3608798604 / 1000000000000) (3608810849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1734360208646009 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28414495441 / 1000000000000) (28414495442 / 1000000000000), orderedInterval (25674607321 / 1000000000000) (25674607322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2971855778737757 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21166855473 / 1000000000000) (21166859558 / 1000000000000), orderedInterval (-20233769484 / 1000000000000) (-20233765399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2189055515850263 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33677332639 / 1000000000000) (33677332726 / 1000000000000), orderedInterval (5365000823 / 1000000000000) (5365000910 / 1000000000000)))) (orderedInterval (-5237735659 / 1000000000000) (-5237734557 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate504_chunkChecks3_1 :
    compactCertificate504.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3358574102204249 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27497190720 / 1000000000000) (-27497183999 / 1000000000000), orderedInterval (1467919100 / 1000000000000) (1467925821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1939073662000721 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35669395869 / 1000000000000) (35669399634 / 1000000000000), orderedInterval (-6435116645 / 1000000000000) (-6435112881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3440920240712389 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5908200316 / 1000000000000) (5908200317 / 1000000000000), orderedInterval (26551242670 / 1000000000000) (26551242671 / 1000000000000)))) (orderedInterval (-41349217299 / 1000000000000) (-41349201879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3214954033307641 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7670300299 / 1000000000000) (7670300300 / 1000000000000), orderedInterval (27073630710 / 1000000000000) (27073630711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2294342897940553 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17144218269 / 1000000000000) (17144218768 / 1000000000000), orderedInterval (-28580145843 / 1000000000000) (-28580145345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2601540312967887 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23722460978 / 1000000000000) (-23722460977 / 1000000000000), orderedInterval (-20379800587 / 1000000000000) (-20379800586 / 1000000000000)))) (orderedInterval (13899179509 / 1000000000000) (13899179881 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2168893088740703 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16037932514 / 1000000000000) (16037932823 / 1000000000000), orderedInterval (-30294758888 / 1000000000000) (-30294758579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1916282819830763 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26348340616 / 1000000000000) (26348356398 / 1000000000000), orderedInterval (-25219339172 / 1000000000000) (-25219323390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (555413451897537 / 800000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20862787860 / 1000000000000) (-20862787859 / 1000000000000), orderedInterval (-21932893193 / 1000000000000) (-21932893192 / 1000000000000)))) (orderedInterval (1595246610 / 1000000000000) (1595248620 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate504_chunkChecks3_2 :
    compactCertificate504.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1536302837757139 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40707839203 / 1000000000000) (40707839508 / 1000000000000), orderedInterval (-691431179 / 1000000000000) (-691430875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1302340929654779 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-15386187397 / 1000000000000) (-15386187165 / 1000000000000), orderedInterval (41479340876 / 1000000000000) (41479341108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (814944484149737 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-17445098888 / 1000000000000) (-17445098887 / 1000000000000), orderedInterval (-53064655408 / 1000000000000) (-53064655407 / 1000000000000)))) (orderedInterval (1671176413 / 1000000000000) (1671176555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (438279853958679 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29576155539 / 1000000000000) (-29576155538 / 1000000000000), orderedInterval (-70117868454 / 1000000000000) (-70117868453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1190015061073037 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7486686340 / 1000000000000) (7486686358 / 1000000000000), orderedInterval (-45661500351 / 1000000000000) (-45661500333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1624863828378349 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39051444000 / 1000000000000) (-39051441885 / 1000000000000), orderedInterval (6542607054 / 1000000000000) (6542609169 / 1000000000000)))) (orderedInterval (96619076 / 1000000000000) (96619324 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (687055515850263 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (14414899852 / 1000000000000) (14414899989 / 1000000000000), orderedInterval (-59190844729 / 1000000000000) (-59190844592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2792842527749623 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30194721144 / 1000000000000) (30194722730 / 1000000000000), orderedInterval (235471062 / 1000000000000) (235472648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1865489376864857 / 4000000000000) 3 (IntervalRat.scale (751 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29832750407 / 1000000000000) (29832806549 / 1000000000000), orderedInterval (-21827680357 / 1000000000000) (-21827624215 / 1000000000000)))) (orderedInterval (-7734529083 / 1000000000000) (-7734507694 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate504_chunkChecks3 :
    compactCertificate504.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate504.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate504_chunkChecks3_0
    compactCertificate504_chunkChecks3_1 compactCertificate504_chunkChecks3_2

theorem compactCertificate504_chunkChecks4_0 :
    compactCertificate504.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (751 / 2) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-26715888485 / 1000000000000) (-26715878756 / 1000000000000), orderedInterval (31366926719 / 1000000000000) (31366936448 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1106366401873651 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38064368880 / 1000000000000) (38064368881 / 1000000000000), orderedInterval (29133290865 / 1000000000000) (29133290866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (357776162633683 / 800000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35713441893 / 1000000000000) (35713456347 / 1000000000000), orderedInterval (-12207633737 / 1000000000000) (-12207619283 / 1000000000000)))) (orderedInterval (-6207586916 / 1000000000000) (-6207581279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (322834956749657 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-16670190472 / 1000000000000) (-16670190344 / 1000000000000), orderedInterval (87339226027 / 1000000000000) (87339226155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (867180104322629 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-39247033781 / 1000000000000) (-39247033780 / 1000000000000), orderedInterval (-37274914456 / 1000000000000) (-37274914455 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2354562673790193 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30574004964 / 1000000000000) (-30573960712 / 1000000000000), orderedInterval (12139557916 / 1000000000000) (12139602168 / 1000000000000)))) (orderedInterval (12947514828 / 1000000000000) (12947534054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1734360208646009 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28414495441 / 1000000000000) (28414495442 / 1000000000000), orderedInterval (25674607321 / 1000000000000) (25674607322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2971855778737757 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21166855473 / 1000000000000) (21166859558 / 1000000000000), orderedInterval (-20233769484 / 1000000000000) (-20233765399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2189055515850263 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33677332639 / 1000000000000) (33677332726 / 1000000000000), orderedInterval (5365000823 / 1000000000000) (5365000910 / 1000000000000)))) (orderedInterval (-6305847425 / 1000000000000) (-6305845259 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate504_chunkChecks4_1 :
    compactCertificate504.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3358574102204249 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27497190720 / 1000000000000) (-27497183999 / 1000000000000), orderedInterval (1467919100 / 1000000000000) (1467925821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1939073662000721 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35669395869 / 1000000000000) (35669399634 / 1000000000000), orderedInterval (-6435116645 / 1000000000000) (-6435112881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3440920240712389 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (5908200316 / 1000000000000) (5908200317 / 1000000000000), orderedInterval (26551242670 / 1000000000000) (26551242671 / 1000000000000)))) (orderedInterval (152842435809 / 1000000000000) (152842469735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3214954033307641 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7670300299 / 1000000000000) (7670300300 / 1000000000000), orderedInterval (27073630710 / 1000000000000) (27073630711 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2294342897940553 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17144218269 / 1000000000000) (17144218768 / 1000000000000), orderedInterval (-28580145843 / 1000000000000) (-28580145345 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2601540312967887 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-23722460978 / 1000000000000) (-23722460977 / 1000000000000), orderedInterval (-20379800587 / 1000000000000) (-20379800586 / 1000000000000)))) (orderedInterval (6926371108 / 1000000000000) (6926371720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2168893088740703 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16037932514 / 1000000000000) (16037932823 / 1000000000000), orderedInterval (-30294758888 / 1000000000000) (-30294758579 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1916282819830763 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (26348340616 / 1000000000000) (26348356398 / 1000000000000), orderedInterval (-25219339172 / 1000000000000) (-25219323390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (555413451897537 / 800000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20862787860 / 1000000000000) (-20862787859 / 1000000000000), orderedInterval (-21932893193 / 1000000000000) (-21932893192 / 1000000000000)))) (orderedInterval (-9440499464 / 1000000000000) (-9440496857 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate504_chunkChecks4_2 :
    compactCertificate504.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1536302837757139 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40707839203 / 1000000000000) (40707839508 / 1000000000000), orderedInterval (-691431179 / 1000000000000) (-691430875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1302340929654779 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-15386187397 / 1000000000000) (-15386187165 / 1000000000000), orderedInterval (41479340876 / 1000000000000) (41479341108 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (814944484149737 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-17445098888 / 1000000000000) (-17445098887 / 1000000000000), orderedInterval (-53064655408 / 1000000000000) (-53064655407 / 1000000000000)))) (orderedInterval (-6690005498 / 1000000000000) (-6690005357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (438279853958679 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-29576155539 / 1000000000000) (-29576155538 / 1000000000000), orderedInterval (-70117868454 / 1000000000000) (-70117868453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1190015061073037 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (7486686340 / 1000000000000) (7486686358 / 1000000000000), orderedInterval (-45661500351 / 1000000000000) (-45661500333 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1624863828378349 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39051444000 / 1000000000000) (-39051441885 / 1000000000000), orderedInterval (6542607054 / 1000000000000) (6542609169 / 1000000000000)))) (orderedInterval (4035460375 / 1000000000000) (4035460642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (687055515850263 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (14414899852 / 1000000000000) (14414899989 / 1000000000000), orderedInterval (-59190844729 / 1000000000000) (-59190844592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2792842527749623 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30194721144 / 1000000000000) (30194722730 / 1000000000000), orderedInterval (235471062 / 1000000000000) (235472648 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1865489376864857 / 4000000000000) 4 (IntervalRat.scale (751 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (29832750407 / 1000000000000) (29832806549 / 1000000000000), orderedInterval (-21827680357 / 1000000000000) (-21827624215 / 1000000000000)))) (orderedInterval (-42655427219 / 1000000000000) (-42655399964 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate504_chunkChecks4 :
    compactCertificate504.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate504.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate504_chunkChecks4_0
    compactCertificate504_chunkChecks4_1 compactCertificate504_chunkChecks4_2

theorem compactCertificate504_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate504.chunkCheck r b = true :=
  compactCertificate504.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate504_chunkChecks0
    · exact compactCertificate504_chunkChecks1
    · exact compactCertificate504_chunkChecks2
    · exact compactCertificate504_chunkChecks3
    · exact compactCertificate504_chunkChecks4)

theorem compactCertificate504_coefficient0 :
    compactCertificate504.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate504_coefficient1 :
    compactCertificate504.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate504_coefficient2 :
    compactCertificate504.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate504_coefficient3 :
    compactCertificate504.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate504_coefficient4 :
    compactCertificate504.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate504_coefficients : ∀ r : Fin 5,
    compactCertificate504.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate504_coefficient0
  · exact compactCertificate504_coefficient1
  · exact compactCertificate504_coefficient2
  · exact compactCertificate504_coefficient3
  · exact compactCertificate504_coefficient4

theorem compactCertificate504_lower : (1 : ℚ) ≤ compactCertificate504.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate504, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate504_proves {t : ℝ} (ht : t ∈ compactCertificate504.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate504.proves compactCertificate504_states compactCertificate504_chunks
    compactCertificate504_coefficients compactCertificate504_lower ht

end Erdos232
