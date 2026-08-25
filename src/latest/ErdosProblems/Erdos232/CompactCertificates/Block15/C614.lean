/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate614 : CompactCertificate where
  left := 485
  right := 486
  center := 971 / 2
  grid := fun i =>
    match i.val with
    | 0 => 155
    | 1 => 114
    | 2 => 184
    | 3 => 33
    | 4 => 89
    | 5 => 242
    | 6 => 179
    | 7 => 306
    | 8 => 225
    | 9 => 346
    | 10 => 200
    | 11 => 354
    | 12 => 331
    | 13 => 236
    | 14 => 268
    | 15 => 223
    | 16 => 197
    | 17 => 286
    | 18 => 158
    | 19 => 134
    | 20 => 84
    | 21 => 45
    | 22 => 123
    | 23 => 167
    | 24 => 71
    | 25 => 287
    | _ => 192
  point := fun i =>
    match i.val with
    | 0 => 971 / 2
    | 1 => 1430468410411871 / 4000000000000
    | 2 => 462584093098943 / 800000000000
    | 3 => 417407114519197 / 4000000000000
    | 4 => 1121214222766009 / 4000000000000
    | 5 => 3044314722037653 / 4000000000000
    | 6 => 2242428445532989 / 4000000000000
    | 7 => 3842439362389297 / 4000000000000
    | 8 => 2830323443263123 / 4000000000000
    | 9 => 4342444012304029 / 4000000000000
    | 10 => 2507111219444341 / 4000000000000
    | 11 => 4448912854502969 / 4000000000000
    | 12 => 4156751486473661 / 4000000000000
    | 13 => 2966453999867213 / 4000000000000
    | 14 => 3363642668298027 / 4000000000000
    | 15 => 2804254579450363 / 4000000000000
    | 16 => 2477643965453623 / 4000000000000
    | 17 => 718117792000677 / 800000000000
    | 18 => 1986351605142719 / 4000000000000
    | 19 => 1683852253921159 / 4000000000000
    | 20 => 1053676556736877 / 4000000000000
    | 21 => 566670756583059 / 4000000000000
    | 22 => 1538621337286177 / 4000000000000
    | 23 => 2100855895280129 / 4000000000000
    | 24 => 888323443263123 / 4000000000000
    | 25 => 3610985478621683 / 4000000000000
    | _ => 2411970951978397 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (22251006587 / 1000000000000) (22251010024 / 1000000000000), orderedInterval (-28591414975 / 1000000000000) (-28591411538 / 1000000000000))
    | 1 => (orderedInterval (10870760235 / 1000000000000) (10870760236 / 1000000000000), orderedInterval (40752430173 / 1000000000000) (40752430174 / 1000000000000))
    | 2 => (orderedInterval (27224355686 / 1000000000000) (27224355687 / 1000000000000), orderedInterval (18945230041 / 1000000000000) (18945230042 / 1000000000000))
    | 3 => (orderedInterval (-77656755942 / 1000000000000) (-77656755935 / 1000000000000), orderedInterval (-7998595012 / 1000000000000) (-7998595006 / 1000000000000))
    | 4 => (orderedInterval (-47488685864 / 1000000000000) (-47488685828 / 1000000000000), orderedInterval (-3915409650 / 1000000000000) (-3915409614 / 1000000000000))
    | 5 => (orderedInterval (28910701050 / 1000000000000) (28910704438 / 1000000000000), orderedInterval (-819908871 / 1000000000000) (-819905483 / 1000000000000))
    | 6 => (orderedInterval (27465614454 / 1000000000000) (27465655738 / 1000000000000), orderedInterval (-19549592950 / 1000000000000) (-19549551666 / 1000000000000))
    | 7 => (orderedInterval (1742954302 / 1000000000000) (1742954303 / 1000000000000), orderedInterval (25683461560 / 1000000000000) (25683461561 / 1000000000000))
    | 8 => (orderedInterval (-29935593511 / 1000000000000) (-29935592627 / 1000000000000), orderedInterval (-1869124136 / 1000000000000) (-1869123252 / 1000000000000))
    | 9 => (orderedInterval (-13568724158 / 1000000000000) (-13568724129 / 1000000000000), orderedInterval (20063812743 / 1000000000000) (20063812772 / 1000000000000))
    | 10 => (orderedInterval (-21852440128 / 1000000000000) (-21852435767 / 1000000000000), orderedInterval (23215995936 / 1000000000000) (23216000298 / 1000000000000))
    | 11 => (orderedInterval (18586544375 / 1000000000000) (18586544378 / 1000000000000), orderedInterval (15055597541 / 1000000000000) (15055597543 / 1000000000000))
    | 12 => (orderedInterval (-2618233381 / 1000000000000) (-2618233380 / 1000000000000), orderedInterval (-24610885721 / 1000000000000) (-24610885720 / 1000000000000))
    | 13 => (orderedInterval (24379283038 / 1000000000000) (24379283039 / 1000000000000), orderedInterval (16233971293 / 1000000000000) (16233971294 / 1000000000000))
    | 14 => (orderedInterval (-6831629642 / 1000000000000) (-6831629641 / 1000000000000), orderedInterval (26657183540 / 1000000000000) (26657183542 / 1000000000000))
    | 15 => (orderedInterval (-28814170938 / 1000000000000) (-28814170902 / 1000000000000), orderedInterval (-8801034830 / 1000000000000) (-8801034794 / 1000000000000))
    | 16 => (orderedInterval (-30911542171 / 1000000000000) (-30911542141 / 1000000000000), orderedInterval (-8475563288 / 1000000000000) (-8475563258 / 1000000000000))
    | 17 => (orderedInterval (-1676642647 / 1000000000000) (-1676642646 / 1000000000000), orderedInterval (26579088104 / 1000000000000) (26579088105 / 1000000000000))
    | 18 => (orderedInterval (30155961647 / 1000000000000) (30155961648 / 1000000000000), orderedInterval (19272636360 / 1000000000000) (19272636361 / 1000000000000))
    | 19 => (orderedInterval (27203732339 / 1000000000000) (27203732340 / 1000000000000), orderedInterval (27757086545 / 1000000000000) (27757086546 / 1000000000000))
    | 20 => (orderedInterval (15009929791 / 1000000000000) (15009929792 / 1000000000000), orderedInterval (46784557924 / 1000000000000) (46784557925 / 1000000000000))
    | 21 => (orderedInterval (-59139185030 / 1000000000000) (-59139185029 / 1000000000000), orderedInterval (-31355425146 / 1000000000000) (-31355425145 / 1000000000000))
    | 22 => (orderedInterval (33683800902 / 1000000000000) (33683909104 / 1000000000000), orderedInterval (-22856920634 / 1000000000000) (-22856812433 / 1000000000000))
    | 23 => (orderedInterval (-33994164290 / 1000000000000) (-33994164259 / 1000000000000), orderedInterval (-7485042093 / 1000000000000) (-7485042062 / 1000000000000))
    | 24 => (orderedInterval (9973968145 / 1000000000000) (9973968191 / 1000000000000), orderedInterval (-52626060281 / 1000000000000) (-52626060235 / 1000000000000))
    | 25 => (orderedInterval (-25176199065 / 1000000000000) (-25176089321 / 1000000000000), orderedInterval (8461667728 / 1000000000000) (8461777472 / 1000000000000))
    | _ => (orderedInterval (18135314864 / 1000000000000) (18135314865 / 1000000000000), orderedInterval (26945625995 / 1000000000000) (26945625996 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (10518370677 / 1000000000000) (10518372073 / 1000000000000)
      | 1 => orderedInterval (-2946625722 / 1000000000000) (-2946625421 / 1000000000000)
      | 2 => orderedInterval (-777243930 / 1000000000000) (-777243881 / 1000000000000)
      | 3 => orderedInterval (3434099158 / 1000000000000) (3434099679 / 1000000000000)
      | 4 => orderedInterval (2387214019 / 1000000000000) (2387214078 / 1000000000000)
      | 5 => orderedInterval (1393299602 / 1000000000000) (1393299651 / 1000000000000)
      | 6 => orderedInterval (-5872788131 / 1000000000000) (-5872788009 / 1000000000000)
      | 7 => orderedInterval (2933104080 / 1000000000000) (2933106595 / 1000000000000)
      | _ => orderedInterval (-1293161451 / 1000000000000) (-1293152383 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-9728859164 / 1000000000000) (-9728857764 / 1000000000000)
      | 1 => orderedInterval (27486316 / 1000000000000) (27486761 / 1000000000000)
      | 2 => orderedInterval (-1633244452 / 1000000000000) (-1633244373 / 1000000000000)
      | 3 => orderedInterval (-848078415 / 1000000000000) (-848077587 / 1000000000000)
      | 4 => orderedInterval (3062302789 / 1000000000000) (3062302884 / 1000000000000)
      | 5 => orderedInterval (1730293101 / 1000000000000) (1730293171 / 1000000000000)
      | 6 => orderedInterval (-3687753712 / 1000000000000) (-3687753599 / 1000000000000)
      | 7 => orderedInterval (1200354690 / 1000000000000) (1200356690 / 1000000000000)
      | _ => orderedInterval (-7705105230 / 1000000000000) (-7705088429 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11120542354 / 1000000000000) (-11120540945 / 1000000000000)
      | 1 => orderedInterval (5589616086 / 1000000000000) (5589616771 / 1000000000000)
      | 2 => orderedInterval (1750573639 / 1000000000000) (1750573769 / 1000000000000)
      | 3 => orderedInterval (-23221461614 / 1000000000000) (-23221460192 / 1000000000000)
      | 4 => orderedInterval (-5705787216 / 1000000000000) (-5705787060 / 1000000000000)
      | 5 => orderedInterval (-2042386134 / 1000000000000) (-2042386030 / 1000000000000)
      | 6 => orderedInterval (6065794605 / 1000000000000) (6065794713 / 1000000000000)
      | 7 => orderedInterval (-2664693351 / 1000000000000) (-2664691751 / 1000000000000)
      | _ => orderedInterval (-1833457327 / 1000000000000) (-1833426127 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (9325574466 / 1000000000000) (9325575882 / 1000000000000)
      | 1 => orderedInterval (-209401946 / 1000000000000) (-209400879 / 1000000000000)
      | 2 => orderedInterval (6272403798 / 1000000000000) (6272404018 / 1000000000000)
      | 3 => orderedInterval (10473529598 / 1000000000000) (10473532228 / 1000000000000)
      | 4 => orderedInterval (-9115879309 / 1000000000000) (-9115879045 / 1000000000000)
      | 5 => orderedInterval (-4998292731 / 1000000000000) (-4998292572 / 1000000000000)
      | 6 => orderedInterval (4065880691 / 1000000000000) (4065880795 / 1000000000000)
      | 7 => orderedInterval (-993031644 / 1000000000000) (-993030363 / 1000000000000)
      | _ => orderedInterval (14148375081 / 1000000000000) (14148433006 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12025291893 / 1000000000000) (12025293320 / 1000000000000)
      | 1 => orderedInterval (-12601528132 / 1000000000000) (-12601526462 / 1000000000000)
      | 2 => orderedInterval (-4113954668 / 1000000000000) (-4113954287 / 1000000000000)
      | 3 => orderedInterval (128509253662 / 1000000000000) (128509258862 / 1000000000000)
      | 4 => orderedInterval (13892315474 / 1000000000000) (13892315932 / 1000000000000)
      | 5 => orderedInterval (2759050032 / 1000000000000) (2759050283 / 1000000000000)
      | 6 => orderedInterval (-6122170618 / 1000000000000) (-6122170515 / 1000000000000)
      | 7 => orderedInterval (3279022772 / 1000000000000) (3279023804 / 1000000000000)
      | _ => orderedInterval (16345454514 / 1000000000000) (16345562229 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (9776268302 / 1000000000000) (9776282382 / 1000000000000)
    | 1 => orderedInterval (-17582604077 / 1000000000000) (-17582582246 / 1000000000000)
    | 2 => orderedInterval (-33182343666 / 1000000000000) (-33182306852 / 1000000000000)
    | 3 => orderedInterval (28969158004 / 1000000000000) (28969223070 / 1000000000000)
    | _ => orderedInterval (153972734929 / 1000000000000) (153972853166 / 1000000000000)

theorem compactCertificate614_stateChecks0 :
    compactCertificate614.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (971 / 2)) (orderedInterval (22251006587 / 1000000000000) (22251010024 / 1000000000000), orderedInterval (-28591414975 / 1000000000000) (-28591411538 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1430468410411871 / 4000000000000)) (orderedInterval (10870760235 / 1000000000000) (10870760236 / 1000000000000), orderedInterval (40752430173 / 1000000000000) (40752430174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (462584093098943 / 800000000000)) (orderedInterval (27224355686 / 1000000000000) (27224355687 / 1000000000000), orderedInterval (18945230041 / 1000000000000) (18945230042 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_stateChecks1 :
    compactCertificate614.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (417407114519197 / 4000000000000)) (orderedInterval (-77656755942 / 1000000000000) (-77656755935 / 1000000000000), orderedInterval (-7998595012 / 1000000000000) (-7998595006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1121214222766009 / 4000000000000)) (orderedInterval (-47488685864 / 1000000000000) (-47488685828 / 1000000000000), orderedInterval (-3915409650 / 1000000000000) (-3915409614 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3044314722037653 / 4000000000000)) (orderedInterval (28910701050 / 1000000000000) (28910704438 / 1000000000000), orderedInterval (-819908871 / 1000000000000) (-819905483 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_stateChecks2 :
    compactCertificate614.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2242428445532989 / 4000000000000)) (orderedInterval (27465614454 / 1000000000000) (27465655738 / 1000000000000), orderedInterval (-19549592950 / 1000000000000) (-19549551666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 306 12 (3842439362389297 / 4000000000000)) (orderedInterval (1742954302 / 1000000000000) (1742954303 / 1000000000000), orderedInterval (25683461560 / 1000000000000) (25683461561 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2830323443263123 / 4000000000000)) (orderedInterval (-29935593511 / 1000000000000) (-29935592627 / 1000000000000), orderedInterval (-1869124136 / 1000000000000) (-1869123252 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_stateChecks3 :
    compactCertificate614.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 346 12 (4342444012304029 / 4000000000000)) (orderedInterval (-13568724158 / 1000000000000) (-13568724129 / 1000000000000), orderedInterval (20063812743 / 1000000000000) (20063812772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2507111219444341 / 4000000000000)) (orderedInterval (-21852440128 / 1000000000000) (-21852435767 / 1000000000000), orderedInterval (23215995936 / 1000000000000) (23216000298 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 354 12 (4448912854502969 / 4000000000000)) (orderedInterval (18586544375 / 1000000000000) (18586544378 / 1000000000000), orderedInterval (15055597541 / 1000000000000) (15055597543 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_stateChecks4 :
    compactCertificate614.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 331 12 (4156751486473661 / 4000000000000)) (orderedInterval (-2618233381 / 1000000000000) (-2618233380 / 1000000000000), orderedInterval (-24610885721 / 1000000000000) (-24610885720 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (2966453999867213 / 4000000000000)) (orderedInterval (24379283038 / 1000000000000) (24379283039 / 1000000000000), orderedInterval (16233971293 / 1000000000000) (16233971294 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 268 12 (3363642668298027 / 4000000000000)) (orderedInterval (-6831629642 / 1000000000000) (-6831629641 / 1000000000000), orderedInterval (26657183540 / 1000000000000) (26657183542 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_stateChecks5 :
    compactCertificate614.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2804254579450363 / 4000000000000)) (orderedInterval (-28814170938 / 1000000000000) (-28814170902 / 1000000000000), orderedInterval (-8801034830 / 1000000000000) (-8801034794 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2477643965453623 / 4000000000000)) (orderedInterval (-30911542171 / 1000000000000) (-30911542141 / 1000000000000), orderedInterval (-8475563288 / 1000000000000) (-8475563258 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 286 12 (718117792000677 / 800000000000)) (orderedInterval (-1676642647 / 1000000000000) (-1676642646 / 1000000000000), orderedInterval (26579088104 / 1000000000000) (26579088105 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_stateChecks6 :
    compactCertificate614.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1986351605142719 / 4000000000000)) (orderedInterval (30155961647 / 1000000000000) (30155961648 / 1000000000000), orderedInterval (19272636360 / 1000000000000) (19272636361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1683852253921159 / 4000000000000)) (orderedInterval (27203732339 / 1000000000000) (27203732340 / 1000000000000), orderedInterval (27757086545 / 1000000000000) (27757086546 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1053676556736877 / 4000000000000)) (orderedInterval (15009929791 / 1000000000000) (15009929792 / 1000000000000), orderedInterval (46784557924 / 1000000000000) (46784557925 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_stateChecks7 :
    compactCertificate614.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (566670756583059 / 4000000000000)) (orderedInterval (-59139185030 / 1000000000000) (-59139185029 / 1000000000000), orderedInterval (-31355425146 / 1000000000000) (-31355425145 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1538621337286177 / 4000000000000)) (orderedInterval (33683800902 / 1000000000000) (33683909104 / 1000000000000), orderedInterval (-22856920634 / 1000000000000) (-22856812433 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2100855895280129 / 4000000000000)) (orderedInterval (-33994164290 / 1000000000000) (-33994164259 / 1000000000000), orderedInterval (-7485042093 / 1000000000000) (-7485042062 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_stateChecks8 :
    compactCertificate614.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (888323443263123 / 4000000000000)) (orderedInterval (9973968145 / 1000000000000) (9973968191 / 1000000000000), orderedInterval (-52626060281 / 1000000000000) (-52626060235 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 287 12 (3610985478621683 / 4000000000000)) (orderedInterval (-25176199065 / 1000000000000) (-25176089321 / 1000000000000), orderedInterval (8461667728 / 1000000000000) (8461777472 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2411970951978397 / 4000000000000)) (orderedInterval (18135314864 / 1000000000000) (18135314865 / 1000000000000), orderedInterval (26945625995 / 1000000000000) (26945625996 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_states : ∀ j,
    BesselStateValid (compactCertificate614.point j) (compactCertificate614.state j) :=
  compactCertificate614.statesValid_of_checks3 compactCertificate614_stateChecks0
    compactCertificate614_stateChecks1 compactCertificate614_stateChecks2
    compactCertificate614_stateChecks3 compactCertificate614_stateChecks4
    compactCertificate614_stateChecks5 compactCertificate614_stateChecks6
    compactCertificate614_stateChecks7 compactCertificate614_stateChecks8

theorem compactCertificate614_chunkChecks0_0 :
    compactCertificate614.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (971 / 2) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22251006587 / 1000000000000) (22251010024 / 1000000000000), orderedInterval (-28591414975 / 1000000000000) (-28591411538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1430468410411871 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10870760235 / 1000000000000) (10870760236 / 1000000000000), orderedInterval (40752430173 / 1000000000000) (40752430174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (462584093098943 / 800000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27224355686 / 1000000000000) (27224355687 / 1000000000000), orderedInterval (18945230041 / 1000000000000) (18945230042 / 1000000000000)))) (orderedInterval (10518370677 / 1000000000000) (10518372073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (417407114519197 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77656755942 / 1000000000000) (-77656755935 / 1000000000000), orderedInterval (-7998595012 / 1000000000000) (-7998595006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1121214222766009 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47488685864 / 1000000000000) (-47488685828 / 1000000000000), orderedInterval (-3915409650 / 1000000000000) (-3915409614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3044314722037653 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28910701050 / 1000000000000) (28910704438 / 1000000000000), orderedInterval (-819908871 / 1000000000000) (-819905483 / 1000000000000)))) (orderedInterval (-2946625722 / 1000000000000) (-2946625421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2242428445532989 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27465614454 / 1000000000000) (27465655738 / 1000000000000), orderedInterval (-19549592950 / 1000000000000) (-19549551666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3842439362389297 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1742954302 / 1000000000000) (1742954303 / 1000000000000), orderedInterval (25683461560 / 1000000000000) (25683461561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2830323443263123 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29935593511 / 1000000000000) (-29935592627 / 1000000000000), orderedInterval (-1869124136 / 1000000000000) (-1869123252 / 1000000000000)))) (orderedInterval (-777243930 / 1000000000000) (-777243881 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_chunkChecks0_1 :
    compactCertificate614.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4342444012304029 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13568724158 / 1000000000000) (-13568724129 / 1000000000000), orderedInterval (20063812743 / 1000000000000) (20063812772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2507111219444341 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21852440128 / 1000000000000) (-21852435767 / 1000000000000), orderedInterval (23215995936 / 1000000000000) (23216000298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4448912854502969 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18586544375 / 1000000000000) (18586544378 / 1000000000000), orderedInterval (15055597541 / 1000000000000) (15055597543 / 1000000000000)))) (orderedInterval (3434099158 / 1000000000000) (3434099679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4156751486473661 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2618233381 / 1000000000000) (-2618233380 / 1000000000000), orderedInterval (-24610885721 / 1000000000000) (-24610885720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2966453999867213 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24379283038 / 1000000000000) (24379283039 / 1000000000000), orderedInterval (16233971293 / 1000000000000) (16233971294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3363642668298027 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6831629642 / 1000000000000) (-6831629641 / 1000000000000), orderedInterval (26657183540 / 1000000000000) (26657183542 / 1000000000000)))) (orderedInterval (2387214019 / 1000000000000) (2387214078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2804254579450363 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28814170938 / 1000000000000) (-28814170902 / 1000000000000), orderedInterval (-8801034830 / 1000000000000) (-8801034794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2477643965453623 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30911542171 / 1000000000000) (-30911542141 / 1000000000000), orderedInterval (-8475563288 / 1000000000000) (-8475563258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (718117792000677 / 800000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1676642647 / 1000000000000) (-1676642646 / 1000000000000), orderedInterval (26579088104 / 1000000000000) (26579088105 / 1000000000000)))) (orderedInterval (1393299602 / 1000000000000) (1393299651 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_chunkChecks0_2 :
    compactCertificate614.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1986351605142719 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30155961647 / 1000000000000) (30155961648 / 1000000000000), orderedInterval (19272636360 / 1000000000000) (19272636361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1683852253921159 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27203732339 / 1000000000000) (27203732340 / 1000000000000), orderedInterval (27757086545 / 1000000000000) (27757086546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1053676556736877 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (15009929791 / 1000000000000) (15009929792 / 1000000000000), orderedInterval (46784557924 / 1000000000000) (46784557925 / 1000000000000)))) (orderedInterval (-5872788131 / 1000000000000) (-5872788009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (566670756583059 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59139185030 / 1000000000000) (-59139185029 / 1000000000000), orderedInterval (-31355425146 / 1000000000000) (-31355425145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1538621337286177 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33683800902 / 1000000000000) (33683909104 / 1000000000000), orderedInterval (-22856920634 / 1000000000000) (-22856812433 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2100855895280129 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33994164290 / 1000000000000) (-33994164259 / 1000000000000), orderedInterval (-7485042093 / 1000000000000) (-7485042062 / 1000000000000)))) (orderedInterval (2933104080 / 1000000000000) (2933106595 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (888323443263123 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9973968145 / 1000000000000) (9973968191 / 1000000000000), orderedInterval (-52626060281 / 1000000000000) (-52626060235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3610985478621683 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25176199065 / 1000000000000) (-25176089321 / 1000000000000), orderedInterval (8461667728 / 1000000000000) (8461777472 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2411970951978397 / 4000000000000) 0 (IntervalRat.scale (971 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18135314864 / 1000000000000) (18135314865 / 1000000000000), orderedInterval (26945625995 / 1000000000000) (26945625996 / 1000000000000)))) (orderedInterval (-1293161451 / 1000000000000) (-1293152383 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_chunkChecks0 :
    compactCertificate614.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate614.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate614_chunkChecks0_0
    compactCertificate614_chunkChecks0_1 compactCertificate614_chunkChecks0_2

theorem compactCertificate614_chunkChecks1_0 :
    compactCertificate614.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (971 / 2) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22251006587 / 1000000000000) (22251010024 / 1000000000000), orderedInterval (-28591414975 / 1000000000000) (-28591411538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1430468410411871 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10870760235 / 1000000000000) (10870760236 / 1000000000000), orderedInterval (40752430173 / 1000000000000) (40752430174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (462584093098943 / 800000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27224355686 / 1000000000000) (27224355687 / 1000000000000), orderedInterval (18945230041 / 1000000000000) (18945230042 / 1000000000000)))) (orderedInterval (-9728859164 / 1000000000000) (-9728857764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (417407114519197 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77656755942 / 1000000000000) (-77656755935 / 1000000000000), orderedInterval (-7998595012 / 1000000000000) (-7998595006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1121214222766009 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47488685864 / 1000000000000) (-47488685828 / 1000000000000), orderedInterval (-3915409650 / 1000000000000) (-3915409614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3044314722037653 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28910701050 / 1000000000000) (28910704438 / 1000000000000), orderedInterval (-819908871 / 1000000000000) (-819905483 / 1000000000000)))) (orderedInterval (27486316 / 1000000000000) (27486761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2242428445532989 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27465614454 / 1000000000000) (27465655738 / 1000000000000), orderedInterval (-19549592950 / 1000000000000) (-19549551666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3842439362389297 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1742954302 / 1000000000000) (1742954303 / 1000000000000), orderedInterval (25683461560 / 1000000000000) (25683461561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2830323443263123 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29935593511 / 1000000000000) (-29935592627 / 1000000000000), orderedInterval (-1869124136 / 1000000000000) (-1869123252 / 1000000000000)))) (orderedInterval (-1633244452 / 1000000000000) (-1633244373 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_chunkChecks1_1 :
    compactCertificate614.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4342444012304029 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13568724158 / 1000000000000) (-13568724129 / 1000000000000), orderedInterval (20063812743 / 1000000000000) (20063812772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2507111219444341 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21852440128 / 1000000000000) (-21852435767 / 1000000000000), orderedInterval (23215995936 / 1000000000000) (23216000298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4448912854502969 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18586544375 / 1000000000000) (18586544378 / 1000000000000), orderedInterval (15055597541 / 1000000000000) (15055597543 / 1000000000000)))) (orderedInterval (-848078415 / 1000000000000) (-848077587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4156751486473661 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2618233381 / 1000000000000) (-2618233380 / 1000000000000), orderedInterval (-24610885721 / 1000000000000) (-24610885720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2966453999867213 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24379283038 / 1000000000000) (24379283039 / 1000000000000), orderedInterval (16233971293 / 1000000000000) (16233971294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3363642668298027 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6831629642 / 1000000000000) (-6831629641 / 1000000000000), orderedInterval (26657183540 / 1000000000000) (26657183542 / 1000000000000)))) (orderedInterval (3062302789 / 1000000000000) (3062302884 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2804254579450363 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28814170938 / 1000000000000) (-28814170902 / 1000000000000), orderedInterval (-8801034830 / 1000000000000) (-8801034794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2477643965453623 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30911542171 / 1000000000000) (-30911542141 / 1000000000000), orderedInterval (-8475563288 / 1000000000000) (-8475563258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (718117792000677 / 800000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1676642647 / 1000000000000) (-1676642646 / 1000000000000), orderedInterval (26579088104 / 1000000000000) (26579088105 / 1000000000000)))) (orderedInterval (1730293101 / 1000000000000) (1730293171 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_chunkChecks1_2 :
    compactCertificate614.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1986351605142719 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30155961647 / 1000000000000) (30155961648 / 1000000000000), orderedInterval (19272636360 / 1000000000000) (19272636361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1683852253921159 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27203732339 / 1000000000000) (27203732340 / 1000000000000), orderedInterval (27757086545 / 1000000000000) (27757086546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1053676556736877 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (15009929791 / 1000000000000) (15009929792 / 1000000000000), orderedInterval (46784557924 / 1000000000000) (46784557925 / 1000000000000)))) (orderedInterval (-3687753712 / 1000000000000) (-3687753599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (566670756583059 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59139185030 / 1000000000000) (-59139185029 / 1000000000000), orderedInterval (-31355425146 / 1000000000000) (-31355425145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1538621337286177 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33683800902 / 1000000000000) (33683909104 / 1000000000000), orderedInterval (-22856920634 / 1000000000000) (-22856812433 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2100855895280129 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33994164290 / 1000000000000) (-33994164259 / 1000000000000), orderedInterval (-7485042093 / 1000000000000) (-7485042062 / 1000000000000)))) (orderedInterval (1200354690 / 1000000000000) (1200356690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (888323443263123 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9973968145 / 1000000000000) (9973968191 / 1000000000000), orderedInterval (-52626060281 / 1000000000000) (-52626060235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3610985478621683 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25176199065 / 1000000000000) (-25176089321 / 1000000000000), orderedInterval (8461667728 / 1000000000000) (8461777472 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2411970951978397 / 4000000000000) 1 (IntervalRat.scale (971 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18135314864 / 1000000000000) (18135314865 / 1000000000000), orderedInterval (26945625995 / 1000000000000) (26945625996 / 1000000000000)))) (orderedInterval (-7705105230 / 1000000000000) (-7705088429 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_chunkChecks1 :
    compactCertificate614.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate614.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate614_chunkChecks1_0
    compactCertificate614_chunkChecks1_1 compactCertificate614_chunkChecks1_2

theorem compactCertificate614_chunkChecks2_0 :
    compactCertificate614.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (971 / 2) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22251006587 / 1000000000000) (22251010024 / 1000000000000), orderedInterval (-28591414975 / 1000000000000) (-28591411538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1430468410411871 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10870760235 / 1000000000000) (10870760236 / 1000000000000), orderedInterval (40752430173 / 1000000000000) (40752430174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (462584093098943 / 800000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27224355686 / 1000000000000) (27224355687 / 1000000000000), orderedInterval (18945230041 / 1000000000000) (18945230042 / 1000000000000)))) (orderedInterval (-11120542354 / 1000000000000) (-11120540945 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (417407114519197 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77656755942 / 1000000000000) (-77656755935 / 1000000000000), orderedInterval (-7998595012 / 1000000000000) (-7998595006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1121214222766009 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47488685864 / 1000000000000) (-47488685828 / 1000000000000), orderedInterval (-3915409650 / 1000000000000) (-3915409614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3044314722037653 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28910701050 / 1000000000000) (28910704438 / 1000000000000), orderedInterval (-819908871 / 1000000000000) (-819905483 / 1000000000000)))) (orderedInterval (5589616086 / 1000000000000) (5589616771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2242428445532989 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27465614454 / 1000000000000) (27465655738 / 1000000000000), orderedInterval (-19549592950 / 1000000000000) (-19549551666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3842439362389297 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1742954302 / 1000000000000) (1742954303 / 1000000000000), orderedInterval (25683461560 / 1000000000000) (25683461561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2830323443263123 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29935593511 / 1000000000000) (-29935592627 / 1000000000000), orderedInterval (-1869124136 / 1000000000000) (-1869123252 / 1000000000000)))) (orderedInterval (1750573639 / 1000000000000) (1750573769 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_chunkChecks2_1 :
    compactCertificate614.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4342444012304029 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13568724158 / 1000000000000) (-13568724129 / 1000000000000), orderedInterval (20063812743 / 1000000000000) (20063812772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2507111219444341 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21852440128 / 1000000000000) (-21852435767 / 1000000000000), orderedInterval (23215995936 / 1000000000000) (23216000298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4448912854502969 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18586544375 / 1000000000000) (18586544378 / 1000000000000), orderedInterval (15055597541 / 1000000000000) (15055597543 / 1000000000000)))) (orderedInterval (-23221461614 / 1000000000000) (-23221460192 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4156751486473661 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2618233381 / 1000000000000) (-2618233380 / 1000000000000), orderedInterval (-24610885721 / 1000000000000) (-24610885720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2966453999867213 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24379283038 / 1000000000000) (24379283039 / 1000000000000), orderedInterval (16233971293 / 1000000000000) (16233971294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3363642668298027 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6831629642 / 1000000000000) (-6831629641 / 1000000000000), orderedInterval (26657183540 / 1000000000000) (26657183542 / 1000000000000)))) (orderedInterval (-5705787216 / 1000000000000) (-5705787060 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2804254579450363 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28814170938 / 1000000000000) (-28814170902 / 1000000000000), orderedInterval (-8801034830 / 1000000000000) (-8801034794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2477643965453623 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30911542171 / 1000000000000) (-30911542141 / 1000000000000), orderedInterval (-8475563288 / 1000000000000) (-8475563258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (718117792000677 / 800000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1676642647 / 1000000000000) (-1676642646 / 1000000000000), orderedInterval (26579088104 / 1000000000000) (26579088105 / 1000000000000)))) (orderedInterval (-2042386134 / 1000000000000) (-2042386030 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_chunkChecks2_2 :
    compactCertificate614.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1986351605142719 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30155961647 / 1000000000000) (30155961648 / 1000000000000), orderedInterval (19272636360 / 1000000000000) (19272636361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1683852253921159 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27203732339 / 1000000000000) (27203732340 / 1000000000000), orderedInterval (27757086545 / 1000000000000) (27757086546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1053676556736877 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (15009929791 / 1000000000000) (15009929792 / 1000000000000), orderedInterval (46784557924 / 1000000000000) (46784557925 / 1000000000000)))) (orderedInterval (6065794605 / 1000000000000) (6065794713 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (566670756583059 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59139185030 / 1000000000000) (-59139185029 / 1000000000000), orderedInterval (-31355425146 / 1000000000000) (-31355425145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1538621337286177 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33683800902 / 1000000000000) (33683909104 / 1000000000000), orderedInterval (-22856920634 / 1000000000000) (-22856812433 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2100855895280129 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33994164290 / 1000000000000) (-33994164259 / 1000000000000), orderedInterval (-7485042093 / 1000000000000) (-7485042062 / 1000000000000)))) (orderedInterval (-2664693351 / 1000000000000) (-2664691751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (888323443263123 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9973968145 / 1000000000000) (9973968191 / 1000000000000), orderedInterval (-52626060281 / 1000000000000) (-52626060235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3610985478621683 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25176199065 / 1000000000000) (-25176089321 / 1000000000000), orderedInterval (8461667728 / 1000000000000) (8461777472 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2411970951978397 / 4000000000000) 2 (IntervalRat.scale (971 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18135314864 / 1000000000000) (18135314865 / 1000000000000), orderedInterval (26945625995 / 1000000000000) (26945625996 / 1000000000000)))) (orderedInterval (-1833457327 / 1000000000000) (-1833426127 / 1000000000000))) = true
  rfl'

theorem compactCertificate614_chunkChecks2 :
    compactCertificate614.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate614.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate614_chunkChecks2_0
    compactCertificate614_chunkChecks2_1 compactCertificate614_chunkChecks2_2

theorem compactCertificate614_chunkChecks3_0 :
    compactCertificate614.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (971 / 2) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22251006587 / 1000000000000) (22251010024 / 1000000000000), orderedInterval (-28591414975 / 1000000000000) (-28591411538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1430468410411871 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10870760235 / 1000000000000) (10870760236 / 1000000000000), orderedInterval (40752430173 / 1000000000000) (40752430174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (462584093098943 / 800000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27224355686 / 1000000000000) (27224355687 / 1000000000000), orderedInterval (18945230041 / 1000000000000) (18945230042 / 1000000000000)))) (orderedInterval (9325574466 / 1000000000000) (9325575882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (417407114519197 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77656755942 / 1000000000000) (-77656755935 / 1000000000000), orderedInterval (-7998595012 / 1000000000000) (-7998595006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1121214222766009 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47488685864 / 1000000000000) (-47488685828 / 1000000000000), orderedInterval (-3915409650 / 1000000000000) (-3915409614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3044314722037653 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28910701050 / 1000000000000) (28910704438 / 1000000000000), orderedInterval (-819908871 / 1000000000000) (-819905483 / 1000000000000)))) (orderedInterval (-209401946 / 1000000000000) (-209400879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2242428445532989 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27465614454 / 1000000000000) (27465655738 / 1000000000000), orderedInterval (-19549592950 / 1000000000000) (-19549551666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3842439362389297 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1742954302 / 1000000000000) (1742954303 / 1000000000000), orderedInterval (25683461560 / 1000000000000) (25683461561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2830323443263123 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29935593511 / 1000000000000) (-29935592627 / 1000000000000), orderedInterval (-1869124136 / 1000000000000) (-1869123252 / 1000000000000)))) (orderedInterval (6272403798 / 1000000000000) (6272404018 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate614_chunkChecks3_1 :
    compactCertificate614.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4342444012304029 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13568724158 / 1000000000000) (-13568724129 / 1000000000000), orderedInterval (20063812743 / 1000000000000) (20063812772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2507111219444341 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21852440128 / 1000000000000) (-21852435767 / 1000000000000), orderedInterval (23215995936 / 1000000000000) (23216000298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4448912854502969 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18586544375 / 1000000000000) (18586544378 / 1000000000000), orderedInterval (15055597541 / 1000000000000) (15055597543 / 1000000000000)))) (orderedInterval (10473529598 / 1000000000000) (10473532228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4156751486473661 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2618233381 / 1000000000000) (-2618233380 / 1000000000000), orderedInterval (-24610885721 / 1000000000000) (-24610885720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2966453999867213 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24379283038 / 1000000000000) (24379283039 / 1000000000000), orderedInterval (16233971293 / 1000000000000) (16233971294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3363642668298027 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6831629642 / 1000000000000) (-6831629641 / 1000000000000), orderedInterval (26657183540 / 1000000000000) (26657183542 / 1000000000000)))) (orderedInterval (-9115879309 / 1000000000000) (-9115879045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2804254579450363 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28814170938 / 1000000000000) (-28814170902 / 1000000000000), orderedInterval (-8801034830 / 1000000000000) (-8801034794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2477643965453623 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30911542171 / 1000000000000) (-30911542141 / 1000000000000), orderedInterval (-8475563288 / 1000000000000) (-8475563258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (718117792000677 / 800000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1676642647 / 1000000000000) (-1676642646 / 1000000000000), orderedInterval (26579088104 / 1000000000000) (26579088105 / 1000000000000)))) (orderedInterval (-4998292731 / 1000000000000) (-4998292572 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate614_chunkChecks3_2 :
    compactCertificate614.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1986351605142719 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30155961647 / 1000000000000) (30155961648 / 1000000000000), orderedInterval (19272636360 / 1000000000000) (19272636361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1683852253921159 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27203732339 / 1000000000000) (27203732340 / 1000000000000), orderedInterval (27757086545 / 1000000000000) (27757086546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1053676556736877 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (15009929791 / 1000000000000) (15009929792 / 1000000000000), orderedInterval (46784557924 / 1000000000000) (46784557925 / 1000000000000)))) (orderedInterval (4065880691 / 1000000000000) (4065880795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (566670756583059 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59139185030 / 1000000000000) (-59139185029 / 1000000000000), orderedInterval (-31355425146 / 1000000000000) (-31355425145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1538621337286177 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33683800902 / 1000000000000) (33683909104 / 1000000000000), orderedInterval (-22856920634 / 1000000000000) (-22856812433 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2100855895280129 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33994164290 / 1000000000000) (-33994164259 / 1000000000000), orderedInterval (-7485042093 / 1000000000000) (-7485042062 / 1000000000000)))) (orderedInterval (-993031644 / 1000000000000) (-993030363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (888323443263123 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9973968145 / 1000000000000) (9973968191 / 1000000000000), orderedInterval (-52626060281 / 1000000000000) (-52626060235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3610985478621683 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25176199065 / 1000000000000) (-25176089321 / 1000000000000), orderedInterval (8461667728 / 1000000000000) (8461777472 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2411970951978397 / 4000000000000) 3 (IntervalRat.scale (971 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18135314864 / 1000000000000) (18135314865 / 1000000000000), orderedInterval (26945625995 / 1000000000000) (26945625996 / 1000000000000)))) (orderedInterval (14148375081 / 1000000000000) (14148433006 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate614_chunkChecks3 :
    compactCertificate614.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate614.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate614_chunkChecks3_0
    compactCertificate614_chunkChecks3_1 compactCertificate614_chunkChecks3_2

theorem compactCertificate614_chunkChecks4_0 :
    compactCertificate614.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (971 / 2) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22251006587 / 1000000000000) (22251010024 / 1000000000000), orderedInterval (-28591414975 / 1000000000000) (-28591411538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1430468410411871 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10870760235 / 1000000000000) (10870760236 / 1000000000000), orderedInterval (40752430173 / 1000000000000) (40752430174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (462584093098943 / 800000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27224355686 / 1000000000000) (27224355687 / 1000000000000), orderedInterval (18945230041 / 1000000000000) (18945230042 / 1000000000000)))) (orderedInterval (12025291893 / 1000000000000) (12025293320 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (417407114519197 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77656755942 / 1000000000000) (-77656755935 / 1000000000000), orderedInterval (-7998595012 / 1000000000000) (-7998595006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1121214222766009 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47488685864 / 1000000000000) (-47488685828 / 1000000000000), orderedInterval (-3915409650 / 1000000000000) (-3915409614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3044314722037653 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28910701050 / 1000000000000) (28910704438 / 1000000000000), orderedInterval (-819908871 / 1000000000000) (-819905483 / 1000000000000)))) (orderedInterval (-12601528132 / 1000000000000) (-12601526462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2242428445532989 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (27465614454 / 1000000000000) (27465655738 / 1000000000000), orderedInterval (-19549592950 / 1000000000000) (-19549551666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3842439362389297 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1742954302 / 1000000000000) (1742954303 / 1000000000000), orderedInterval (25683461560 / 1000000000000) (25683461561 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2830323443263123 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29935593511 / 1000000000000) (-29935592627 / 1000000000000), orderedInterval (-1869124136 / 1000000000000) (-1869123252 / 1000000000000)))) (orderedInterval (-4113954668 / 1000000000000) (-4113954287 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate614_chunkChecks4_1 :
    compactCertificate614.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4342444012304029 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-13568724158 / 1000000000000) (-13568724129 / 1000000000000), orderedInterval (20063812743 / 1000000000000) (20063812772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2507111219444341 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-21852440128 / 1000000000000) (-21852435767 / 1000000000000), orderedInterval (23215995936 / 1000000000000) (23216000298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4448912854502969 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18586544375 / 1000000000000) (18586544378 / 1000000000000), orderedInterval (15055597541 / 1000000000000) (15055597543 / 1000000000000)))) (orderedInterval (128509253662 / 1000000000000) (128509258862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4156751486473661 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-2618233381 / 1000000000000) (-2618233380 / 1000000000000), orderedInterval (-24610885721 / 1000000000000) (-24610885720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2966453999867213 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24379283038 / 1000000000000) (24379283039 / 1000000000000), orderedInterval (16233971293 / 1000000000000) (16233971294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3363642668298027 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-6831629642 / 1000000000000) (-6831629641 / 1000000000000), orderedInterval (26657183540 / 1000000000000) (26657183542 / 1000000000000)))) (orderedInterval (13892315474 / 1000000000000) (13892315932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2804254579450363 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28814170938 / 1000000000000) (-28814170902 / 1000000000000), orderedInterval (-8801034830 / 1000000000000) (-8801034794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2477643965453623 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30911542171 / 1000000000000) (-30911542141 / 1000000000000), orderedInterval (-8475563288 / 1000000000000) (-8475563258 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (718117792000677 / 800000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1676642647 / 1000000000000) (-1676642646 / 1000000000000), orderedInterval (26579088104 / 1000000000000) (26579088105 / 1000000000000)))) (orderedInterval (2759050032 / 1000000000000) (2759050283 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate614_chunkChecks4_2 :
    compactCertificate614.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1986351605142719 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (30155961647 / 1000000000000) (30155961648 / 1000000000000), orderedInterval (19272636360 / 1000000000000) (19272636361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1683852253921159 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (27203732339 / 1000000000000) (27203732340 / 1000000000000), orderedInterval (27757086545 / 1000000000000) (27757086546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1053676556736877 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (15009929791 / 1000000000000) (15009929792 / 1000000000000), orderedInterval (46784557924 / 1000000000000) (46784557925 / 1000000000000)))) (orderedInterval (-6122170618 / 1000000000000) (-6122170515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (566670756583059 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-59139185030 / 1000000000000) (-59139185029 / 1000000000000), orderedInterval (-31355425146 / 1000000000000) (-31355425145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1538621337286177 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33683800902 / 1000000000000) (33683909104 / 1000000000000), orderedInterval (-22856920634 / 1000000000000) (-22856812433 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2100855895280129 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33994164290 / 1000000000000) (-33994164259 / 1000000000000), orderedInterval (-7485042093 / 1000000000000) (-7485042062 / 1000000000000)))) (orderedInterval (3279022772 / 1000000000000) (3279023804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (888323443263123 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9973968145 / 1000000000000) (9973968191 / 1000000000000), orderedInterval (-52626060281 / 1000000000000) (-52626060235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3610985478621683 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25176199065 / 1000000000000) (-25176089321 / 1000000000000), orderedInterval (8461667728 / 1000000000000) (8461777472 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2411970951978397 / 4000000000000) 4 (IntervalRat.scale (971 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18135314864 / 1000000000000) (18135314865 / 1000000000000), orderedInterval (26945625995 / 1000000000000) (26945625996 / 1000000000000)))) (orderedInterval (16345454514 / 1000000000000) (16345562229 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate614_chunkChecks4 :
    compactCertificate614.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate614.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate614_chunkChecks4_0
    compactCertificate614_chunkChecks4_1 compactCertificate614_chunkChecks4_2

theorem compactCertificate614_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate614.chunkCheck r b = true :=
  compactCertificate614.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate614_chunkChecks0
    · exact compactCertificate614_chunkChecks1
    · exact compactCertificate614_chunkChecks2
    · exact compactCertificate614_chunkChecks3
    · exact compactCertificate614_chunkChecks4)

theorem compactCertificate614_coefficient0 :
    compactCertificate614.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate614_coefficient1 :
    compactCertificate614.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate614_coefficient2 :
    compactCertificate614.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate614_coefficient3 :
    compactCertificate614.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate614_coefficient4 :
    compactCertificate614.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate614_coefficients : ∀ r : Fin 5,
    compactCertificate614.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate614_coefficient0
  · exact compactCertificate614_coefficient1
  · exact compactCertificate614_coefficient2
  · exact compactCertificate614_coefficient3
  · exact compactCertificate614_coefficient4

theorem compactCertificate614_lower : (1 : ℚ) ≤ compactCertificate614.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate614, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate614_proves {t : ℝ} (ht : t ∈ compactCertificate614.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate614.proves compactCertificate614_states compactCertificate614_chunks
    compactCertificate614_coefficients compactCertificate614_lower ht

end Erdos232
