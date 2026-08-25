/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate433 : CompactCertificate where
  left := 304
  right := 305
  center := 609 / 2
  grid := fun i =>
    match i.val with
    | 0 => 97
    | 1 => 71
    | 2 => 115
    | 3 => 21
    | 4 => 56
    | 5 => 152
    | 6 => 112
    | 7 => 192
    | 8 => 141
    | 9 => 217
    | 10 => 125
    | 11 => 222
    | 12 => 208
    | 13 => 148
    | 14 => 168
    | 15 => 140
    | 16 => 124
    | 17 => 179
    | 18 => 99
    | 19 => 84
    | 20 => 53
    | 21 => 28
    | 22 => 77
    | 23 => 105
    | 24 => 44
    | 25 => 180
    | _ => 120
  point := fun i =>
    match i.val with
    | 0 => 609 / 2
    | 1 => 897173287271709 / 4000000000000
    | 2 => 290127407515197 / 800000000000
    | 3 => 261792927643863 / 4000000000000
    | 4 => 703212627872811 / 4000000000000
    | 5 => 1909359079012287 / 4000000000000
    | 6 => 1406425255746231 / 4000000000000
    | 7 => 2409933647471763 / 4000000000000
    | 8 => 1775146217247417 / 4000000000000
    | 9 => 2723530796594391 / 4000000000000
    | 10 => 1572431238559839 / 4000000000000
    | 11 => 2790306826356651 / 4000000000000
    | 12 => 2607066586264119 / 4000000000000
    | 13 => 1860525732151527 / 4000000000000
    | 14 => 2109637883618433 / 4000000000000
    | 15 => 1758796126555377 / 4000000000000
    | 16 => 1553949716746917 / 4000000000000
    | 17 => 450395196012783 / 800000000000
    | 18 => 1245816815171901 / 4000000000000
    | 19 => 1056092711264661 / 4000000000000
    | 20 => 660853782752583 / 4000000000000
    | 21 => 355409362264761 / 4000000000000
    | 22 => 965005555517283 / 4000000000000
    | 23 => 1317632585196291 / 4000000000000
    | 24 => 557146217247417 / 4000000000000
    | 25 => 2264768441277657 / 4000000000000
    | _ => 1512760360200663 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-23918953229 / 1000000000000) (-23918953228 / 1000000000000), orderedInterval (-38929818234 / 1000000000000) (-38929818233 / 1000000000000))
    | 1 => (orderedInterval (-47872392760 / 1000000000000) (-47872376354 / 1000000000000), orderedInterval (23485465899 / 1000000000000) (23485482304 / 1000000000000))
    | 2 => (orderedInterval (-34806149987 / 1000000000000) (-34806046546 / 1000000000000), orderedInterval (23370799089 / 1000000000000) (23370902530 / 1000000000000))
    | 3 => (orderedInterval (-25189960234 / 1000000000000) (-25189960233 / 1000000000000), orderedInterval (-95163671879 / 1000000000000) (-95163671878 / 1000000000000))
    | 4 => (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000))
    | 5 => (orderedInterval (20705519659 / 1000000000000) (20705519660 / 1000000000000), orderedInterval (30060937353 / 1000000000000) (30060937354 / 1000000000000))
    | 6 => (orderedInterval (21620323285 / 1000000000000) (21620323286 / 1000000000000), orderedInterval (36618490074 / 1000000000000) (36618490075 / 1000000000000))
    | 7 => (orderedInterval (2688869968 / 1000000000000) (2688869969 / 1000000000000), orderedInterval (32392671767 / 1000000000000) (32392671768 / 1000000000000))
    | 8 => (orderedInterval (-37850053562 / 1000000000000) (-37850052980 / 1000000000000), orderedInterval (1417597050 / 1000000000000) (1417597632 / 1000000000000))
    | 9 => (orderedInterval (1763109450 / 1000000000000) (1763109451 / 1000000000000), orderedInterval (-30528062360 / 1000000000000) (-30528062359 / 1000000000000))
    | 10 => (orderedInterval (-37416495690 / 1000000000000) (-37416495688 / 1000000000000), orderedInterval (-14766533752 / 1000000000000) (-14766533750 / 1000000000000))
    | 11 => (orderedInterval (24186849130 / 1000000000000) (24186849131 / 1000000000000), orderedInterval (18082730491 / 1000000000000) (18082730492 / 1000000000000))
    | 12 => (orderedInterval (-24470157680 / 1000000000000) (-24470141269 / 1000000000000), orderedInterval (19460265562 / 1000000000000) (19460281973 / 1000000000000))
    | 13 => (orderedInterval (30324642728 / 1000000000000) (30324642729 / 1000000000000), orderedInterval (21159468758 / 1000000000000) (21159468759 / 1000000000000))
    | 14 => (orderedInterval (13755303404 / 1000000000000) (13755303405 / 1000000000000), orderedInterval (31890897957 / 1000000000000) (31890897958 / 1000000000000))
    | 15 => (orderedInterval (23364773873 / 1000000000000) (23364773874 / 1000000000000), orderedInterval (30005764395 / 1000000000000) (30005764396 / 1000000000000))
    | 16 => (orderedInterval (-11380896358 / 1000000000000) (-11380896302 / 1000000000000), orderedInterval (38862946177 / 1000000000000) (38862946233 / 1000000000000))
    | 17 => (orderedInterval (-33313248165 / 1000000000000) (-33313248032 / 1000000000000), orderedInterval (-4553262074 / 1000000000000) (-4553261941 / 1000000000000))
    | 18 => (orderedInterval (-42481170037 / 1000000000000) (-42481170035 / 1000000000000), orderedInterval (-15403449373 / 1000000000000) (-15403449372 / 1000000000000))
    | 19 => (orderedInterval (38897770974 / 1000000000000) (38897770975 / 1000000000000), orderedInterval (29896140669 / 1000000000000) (29896140670 / 1000000000000))
    | 20 => (orderedInterval (30104188028 / 1000000000000) (30104191718 / 1000000000000), orderedInterval (-54377976042 / 1000000000000) (-54377972352 / 1000000000000))
    | 21 => (orderedInterval (84214305596 / 1000000000000) (84214305726 / 1000000000000), orderedInterval (-9003717356 / 1000000000000) (-9003717226 / 1000000000000))
    | 22 => (orderedInterval (-6844317958 / 1000000000000) (-6844317957 / 1000000000000), orderedInterval (-50897346341 / 1000000000000) (-50897346340 / 1000000000000))
    | 23 => (orderedInterval (-14076300878 / 1000000000000) (-14076300877 / 1000000000000), orderedInterval (-41625680591 / 1000000000000) (-41625680590 / 1000000000000))
    | 24 => (orderedInterval (65153235269 / 1000000000000) (65153236782 / 1000000000000), orderedInterval (-18278449789 / 1000000000000) (-18278448276 / 1000000000000))
    | 25 => (orderedInterval (33424148185 / 1000000000000) (33424148476 / 1000000000000), orderedInterval (2656400997 / 1000000000000) (2656401288 / 1000000000000))
    | _ => (orderedInterval (37574773168 / 1000000000000) (37574796413 / 1000000000000), orderedInterval (-16525952950 / 1000000000000) (-16525929705 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-11969178128 / 1000000000000) (-11969171883 / 1000000000000)
      | 1 => orderedInterval (146116156 / 1000000000000) (146116193 / 1000000000000)
      | 2 => orderedInterval (-997696633 / 1000000000000) (-997696601 / 1000000000000)
      | 3 => orderedInterval (352765360 / 1000000000000) (352765482 / 1000000000000)
      | 4 => orderedInterval (3239736915 / 1000000000000) (3239737248 / 1000000000000)
      | 5 => orderedInterval (68148820 / 1000000000000) (68148856 / 1000000000000)
      | 6 => orderedInterval (5570855851 / 1000000000000) (5570856049 / 1000000000000)
      | 7 => orderedInterval (-320959137 / 1000000000000) (-320959097 / 1000000000000)
      | _ => orderedInterval (-9378048604 / 1000000000000) (-9378044125 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-13635855091 / 1000000000000) (-13635847725 / 1000000000000)
      | 1 => orderedInterval (-2127157610 / 1000000000000) (-2127157567 / 1000000000000)
      | 2 => orderedInterval (-1926924895 / 1000000000000) (-1926924844 / 1000000000000)
      | 3 => orderedInterval (16605921239 / 1000000000000) (16605921490 / 1000000000000)
      | 4 => orderedInterval (2024917441 / 1000000000000) (2024918135 / 1000000000000)
      | 5 => orderedInterval (-2552628644 / 1000000000000) (-2552628591 / 1000000000000)
      | 6 => orderedInterval (91443018 / 1000000000000) (91443154 / 1000000000000)
      | 7 => orderedInterval (4414466806 / 1000000000000) (4414466840 / 1000000000000)
      | _ => orderedInterval (3398608475 / 1000000000000) (3398614059 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (12664631196 / 1000000000000) (12664639941 / 1000000000000)
      | 1 => orderedInterval (3163308008 / 1000000000000) (3163308066 / 1000000000000)
      | 2 => orderedInterval (2274046919 / 1000000000000) (2274047003 / 1000000000000)
      | 3 => orderedInterval (-11912554542 / 1000000000000) (-11912554004 / 1000000000000)
      | 4 => orderedInterval (-8512793906 / 1000000000000) (-8512792448 / 1000000000000)
      | 5 => orderedInterval (1301468469 / 1000000000000) (1301468549 / 1000000000000)
      | 6 => orderedInterval (-5739826070 / 1000000000000) (-5739825967 / 1000000000000)
      | 7 => orderedInterval (-1242064096 / 1000000000000) (-1242064063 / 1000000000000)
      | _ => orderedInterval (20188748845 / 1000000000000) (20188755850 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (12984311752 / 1000000000000) (12984322129 / 1000000000000)
      | 1 => orderedInterval (7878145681 / 1000000000000) (7878145768 / 1000000000000)
      | 2 => orderedInterval (7625557617 / 1000000000000) (7625557758 / 1000000000000)
      | 3 => orderedInterval (-89160020980 / 1000000000000) (-89160019801 / 1000000000000)
      | 4 => orderedInterval (-2819890428 / 1000000000000) (-2819887352 / 1000000000000)
      | 5 => orderedInterval (4307786088 / 1000000000000) (4307786213 / 1000000000000)
      | 6 => orderedInterval (-1230859739 / 1000000000000) (-1230859654 / 1000000000000)
      | 7 => orderedInterval (-4613067999 / 1000000000000) (-4613067964 / 1000000000000)
      | _ => orderedInterval (-4606169275 / 1000000000000) (-4606160474 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13806708589 / 1000000000000) (-13806696225 / 1000000000000)
      | 1 => orderedInterval (-8790725580 / 1000000000000) (-8790725447 / 1000000000000)
      | 2 => orderedInterval (-5448333536 / 1000000000000) (-5448333294 / 1000000000000)
      | 3 => orderedInterval (79755504631 / 1000000000000) (79755507249 / 1000000000000)
      | 4 => orderedInterval (24277072103 / 1000000000000) (24277078628 / 1000000000000)
      | 5 => orderedInterval (-7097204477 / 1000000000000) (-7097204275 / 1000000000000)
      | 6 => orderedInterval (6283060913 / 1000000000000) (6283060988 / 1000000000000)
      | 7 => orderedInterval (1557689846 / 1000000000000) (1557689882 / 1000000000000)
      | _ => orderedInterval (-49251822040 / 1000000000000) (-49251810890 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13288259400 / 1000000000000) (-13288247878 / 1000000000000)
    | 1 => orderedInterval (6292790739 / 1000000000000) (6292804951 / 1000000000000)
    | 2 => orderedInterval (12184964823 / 1000000000000) (12184982927 / 1000000000000)
    | 3 => orderedInterval (-69634207283 / 1000000000000) (-69634183377 / 1000000000000)
    | _ => orderedInterval (27478533271 / 1000000000000) (27478566616 / 1000000000000)

theorem compactCertificate433_stateChecks0 :
    compactCertificate433.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (609 / 2)) (orderedInterval (-23918953229 / 1000000000000) (-23918953228 / 1000000000000), orderedInterval (-38929818234 / 1000000000000) (-38929818233 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (897173287271709 / 4000000000000)) (orderedInterval (-47872392760 / 1000000000000) (-47872376354 / 1000000000000), orderedInterval (23485465899 / 1000000000000) (23485482304 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (290127407515197 / 800000000000)) (orderedInterval (-34806149987 / 1000000000000) (-34806046546 / 1000000000000), orderedInterval (23370799089 / 1000000000000) (23370902530 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_stateChecks1 :
    compactCertificate433.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (261792927643863 / 4000000000000)) (orderedInterval (-25189960234 / 1000000000000) (-25189960233 / 1000000000000), orderedInterval (-95163671879 / 1000000000000) (-95163671878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (703212627872811 / 4000000000000)) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1909359079012287 / 4000000000000)) (orderedInterval (20705519659 / 1000000000000) (20705519660 / 1000000000000), orderedInterval (30060937353 / 1000000000000) (30060937354 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_stateChecks2 :
    compactCertificate433.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1406425255746231 / 4000000000000)) (orderedInterval (21620323285 / 1000000000000) (21620323286 / 1000000000000), orderedInterval (36618490074 / 1000000000000) (36618490075 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2409933647471763 / 4000000000000)) (orderedInterval (2688869968 / 1000000000000) (2688869969 / 1000000000000), orderedInterval (32392671767 / 1000000000000) (32392671768 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1775146217247417 / 4000000000000)) (orderedInterval (-37850053562 / 1000000000000) (-37850052980 / 1000000000000), orderedInterval (1417597050 / 1000000000000) (1417597632 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_stateChecks3 :
    compactCertificate433.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2723530796594391 / 4000000000000)) (orderedInterval (1763109450 / 1000000000000) (1763109451 / 1000000000000), orderedInterval (-30528062360 / 1000000000000) (-30528062359 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1572431238559839 / 4000000000000)) (orderedInterval (-37416495690 / 1000000000000) (-37416495688 / 1000000000000), orderedInterval (-14766533752 / 1000000000000) (-14766533750 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2790306826356651 / 4000000000000)) (orderedInterval (24186849130 / 1000000000000) (24186849131 / 1000000000000), orderedInterval (18082730491 / 1000000000000) (18082730492 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_stateChecks4 :
    compactCertificate433.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2607066586264119 / 4000000000000)) (orderedInterval (-24470157680 / 1000000000000) (-24470141269 / 1000000000000), orderedInterval (19460265562 / 1000000000000) (19460281973 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1860525732151527 / 4000000000000)) (orderedInterval (30324642728 / 1000000000000) (30324642729 / 1000000000000), orderedInterval (21159468758 / 1000000000000) (21159468759 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2109637883618433 / 4000000000000)) (orderedInterval (13755303404 / 1000000000000) (13755303405 / 1000000000000), orderedInterval (31890897957 / 1000000000000) (31890897958 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_stateChecks5 :
    compactCertificate433.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1758796126555377 / 4000000000000)) (orderedInterval (23364773873 / 1000000000000) (23364773874 / 1000000000000), orderedInterval (30005764395 / 1000000000000) (30005764396 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1553949716746917 / 4000000000000)) (orderedInterval (-11380896358 / 1000000000000) (-11380896302 / 1000000000000), orderedInterval (38862946177 / 1000000000000) (38862946233 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (450395196012783 / 800000000000)) (orderedInterval (-33313248165 / 1000000000000) (-33313248032 / 1000000000000), orderedInterval (-4553262074 / 1000000000000) (-4553261941 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_stateChecks6 :
    compactCertificate433.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1245816815171901 / 4000000000000)) (orderedInterval (-42481170037 / 1000000000000) (-42481170035 / 1000000000000), orderedInterval (-15403449373 / 1000000000000) (-15403449372 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1056092711264661 / 4000000000000)) (orderedInterval (38897770974 / 1000000000000) (38897770975 / 1000000000000), orderedInterval (29896140669 / 1000000000000) (29896140670 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (660853782752583 / 4000000000000)) (orderedInterval (30104188028 / 1000000000000) (30104191718 / 1000000000000), orderedInterval (-54377976042 / 1000000000000) (-54377972352 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_stateChecks7 :
    compactCertificate433.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (355409362264761 / 4000000000000)) (orderedInterval (84214305596 / 1000000000000) (84214305726 / 1000000000000), orderedInterval (-9003717356 / 1000000000000) (-9003717226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (965005555517283 / 4000000000000)) (orderedInterval (-6844317958 / 1000000000000) (-6844317957 / 1000000000000), orderedInterval (-50897346341 / 1000000000000) (-50897346340 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1317632585196291 / 4000000000000)) (orderedInterval (-14076300878 / 1000000000000) (-14076300877 / 1000000000000), orderedInterval (-41625680591 / 1000000000000) (-41625680590 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_stateChecks8 :
    compactCertificate433.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (557146217247417 / 4000000000000)) (orderedInterval (65153235269 / 1000000000000) (65153236782 / 1000000000000), orderedInterval (-18278449789 / 1000000000000) (-18278448276 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2264768441277657 / 4000000000000)) (orderedInterval (33424148185 / 1000000000000) (33424148476 / 1000000000000), orderedInterval (2656400997 / 1000000000000) (2656401288 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1512760360200663 / 4000000000000)) (orderedInterval (37574773168 / 1000000000000) (37574796413 / 1000000000000), orderedInterval (-16525952950 / 1000000000000) (-16525929705 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_states : ∀ j,
    BesselStateValid (compactCertificate433.point j) (compactCertificate433.state j) :=
  compactCertificate433.statesValid_of_checks3 compactCertificate433_stateChecks0
    compactCertificate433_stateChecks1 compactCertificate433_stateChecks2
    compactCertificate433_stateChecks3 compactCertificate433_stateChecks4
    compactCertificate433_stateChecks5 compactCertificate433_stateChecks6
    compactCertificate433_stateChecks7 compactCertificate433_stateChecks8

theorem compactCertificate433_chunkChecks0_0 :
    compactCertificate433.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (609 / 2) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23918953229 / 1000000000000) (-23918953228 / 1000000000000), orderedInterval (-38929818234 / 1000000000000) (-38929818233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (897173287271709 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47872392760 / 1000000000000) (-47872376354 / 1000000000000), orderedInterval (23485465899 / 1000000000000) (23485482304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (290127407515197 / 800000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34806149987 / 1000000000000) (-34806046546 / 1000000000000), orderedInterval (23370799089 / 1000000000000) (23370902530 / 1000000000000)))) (orderedInterval (-11969178128 / 1000000000000) (-11969171883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (261792927643863 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-25189960234 / 1000000000000) (-25189960233 / 1000000000000), orderedInterval (-95163671879 / 1000000000000) (-95163671878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (703212627872811 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1909359079012287 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20705519659 / 1000000000000) (20705519660 / 1000000000000), orderedInterval (30060937353 / 1000000000000) (30060937354 / 1000000000000)))) (orderedInterval (146116156 / 1000000000000) (146116193 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1406425255746231 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21620323285 / 1000000000000) (21620323286 / 1000000000000), orderedInterval (36618490074 / 1000000000000) (36618490075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2409933647471763 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2688869968 / 1000000000000) (2688869969 / 1000000000000), orderedInterval (32392671767 / 1000000000000) (32392671768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1775146217247417 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37850053562 / 1000000000000) (-37850052980 / 1000000000000), orderedInterval (1417597050 / 1000000000000) (1417597632 / 1000000000000)))) (orderedInterval (-997696633 / 1000000000000) (-997696601 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_chunkChecks0_1 :
    compactCertificate433.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2723530796594391 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1763109450 / 1000000000000) (1763109451 / 1000000000000), orderedInterval (-30528062360 / 1000000000000) (-30528062359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1572431238559839 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37416495690 / 1000000000000) (-37416495688 / 1000000000000), orderedInterval (-14766533752 / 1000000000000) (-14766533750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2790306826356651 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24186849130 / 1000000000000) (24186849131 / 1000000000000), orderedInterval (18082730491 / 1000000000000) (18082730492 / 1000000000000)))) (orderedInterval (352765360 / 1000000000000) (352765482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2607066586264119 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24470157680 / 1000000000000) (-24470141269 / 1000000000000), orderedInterval (19460265562 / 1000000000000) (19460281973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1860525732151527 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30324642728 / 1000000000000) (30324642729 / 1000000000000), orderedInterval (21159468758 / 1000000000000) (21159468759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2109637883618433 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13755303404 / 1000000000000) (13755303405 / 1000000000000), orderedInterval (31890897957 / 1000000000000) (31890897958 / 1000000000000)))) (orderedInterval (3239736915 / 1000000000000) (3239737248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1758796126555377 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23364773873 / 1000000000000) (23364773874 / 1000000000000), orderedInterval (30005764395 / 1000000000000) (30005764396 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1553949716746917 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11380896358 / 1000000000000) (-11380896302 / 1000000000000), orderedInterval (38862946177 / 1000000000000) (38862946233 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (450395196012783 / 800000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33313248165 / 1000000000000) (-33313248032 / 1000000000000), orderedInterval (-4553262074 / 1000000000000) (-4553261941 / 1000000000000)))) (orderedInterval (68148820 / 1000000000000) (68148856 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_chunkChecks0_2 :
    compactCertificate433.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1245816815171901 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42481170037 / 1000000000000) (-42481170035 / 1000000000000), orderedInterval (-15403449373 / 1000000000000) (-15403449372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1056092711264661 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38897770974 / 1000000000000) (38897770975 / 1000000000000), orderedInterval (29896140669 / 1000000000000) (29896140670 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (660853782752583 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (30104188028 / 1000000000000) (30104191718 / 1000000000000), orderedInterval (-54377976042 / 1000000000000) (-54377972352 / 1000000000000)))) (orderedInterval (5570855851 / 1000000000000) (5570856049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (355409362264761 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84214305596 / 1000000000000) (84214305726 / 1000000000000), orderedInterval (-9003717356 / 1000000000000) (-9003717226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (965005555517283 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6844317958 / 1000000000000) (-6844317957 / 1000000000000), orderedInterval (-50897346341 / 1000000000000) (-50897346340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1317632585196291 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14076300878 / 1000000000000) (-14076300877 / 1000000000000), orderedInterval (-41625680591 / 1000000000000) (-41625680590 / 1000000000000)))) (orderedInterval (-320959137 / 1000000000000) (-320959097 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (557146217247417 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65153235269 / 1000000000000) (65153236782 / 1000000000000), orderedInterval (-18278449789 / 1000000000000) (-18278448276 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2264768441277657 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33424148185 / 1000000000000) (33424148476 / 1000000000000), orderedInterval (2656400997 / 1000000000000) (2656401288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1512760360200663 / 4000000000000) 0 (IntervalRat.scale (609 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (37574773168 / 1000000000000) (37574796413 / 1000000000000), orderedInterval (-16525952950 / 1000000000000) (-16525929705 / 1000000000000)))) (orderedInterval (-9378048604 / 1000000000000) (-9378044125 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_chunkChecks0 :
    compactCertificate433.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate433.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate433_chunkChecks0_0
    compactCertificate433_chunkChecks0_1 compactCertificate433_chunkChecks0_2

theorem compactCertificate433_chunkChecks1_0 :
    compactCertificate433.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (609 / 2) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23918953229 / 1000000000000) (-23918953228 / 1000000000000), orderedInterval (-38929818234 / 1000000000000) (-38929818233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (897173287271709 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47872392760 / 1000000000000) (-47872376354 / 1000000000000), orderedInterval (23485465899 / 1000000000000) (23485482304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (290127407515197 / 800000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34806149987 / 1000000000000) (-34806046546 / 1000000000000), orderedInterval (23370799089 / 1000000000000) (23370902530 / 1000000000000)))) (orderedInterval (-13635855091 / 1000000000000) (-13635847725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (261792927643863 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-25189960234 / 1000000000000) (-25189960233 / 1000000000000), orderedInterval (-95163671879 / 1000000000000) (-95163671878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (703212627872811 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1909359079012287 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20705519659 / 1000000000000) (20705519660 / 1000000000000), orderedInterval (30060937353 / 1000000000000) (30060937354 / 1000000000000)))) (orderedInterval (-2127157610 / 1000000000000) (-2127157567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1406425255746231 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21620323285 / 1000000000000) (21620323286 / 1000000000000), orderedInterval (36618490074 / 1000000000000) (36618490075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2409933647471763 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2688869968 / 1000000000000) (2688869969 / 1000000000000), orderedInterval (32392671767 / 1000000000000) (32392671768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1775146217247417 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37850053562 / 1000000000000) (-37850052980 / 1000000000000), orderedInterval (1417597050 / 1000000000000) (1417597632 / 1000000000000)))) (orderedInterval (-1926924895 / 1000000000000) (-1926924844 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_chunkChecks1_1 :
    compactCertificate433.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2723530796594391 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1763109450 / 1000000000000) (1763109451 / 1000000000000), orderedInterval (-30528062360 / 1000000000000) (-30528062359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1572431238559839 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37416495690 / 1000000000000) (-37416495688 / 1000000000000), orderedInterval (-14766533752 / 1000000000000) (-14766533750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2790306826356651 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24186849130 / 1000000000000) (24186849131 / 1000000000000), orderedInterval (18082730491 / 1000000000000) (18082730492 / 1000000000000)))) (orderedInterval (16605921239 / 1000000000000) (16605921490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2607066586264119 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24470157680 / 1000000000000) (-24470141269 / 1000000000000), orderedInterval (19460265562 / 1000000000000) (19460281973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1860525732151527 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30324642728 / 1000000000000) (30324642729 / 1000000000000), orderedInterval (21159468758 / 1000000000000) (21159468759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2109637883618433 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13755303404 / 1000000000000) (13755303405 / 1000000000000), orderedInterval (31890897957 / 1000000000000) (31890897958 / 1000000000000)))) (orderedInterval (2024917441 / 1000000000000) (2024918135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1758796126555377 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23364773873 / 1000000000000) (23364773874 / 1000000000000), orderedInterval (30005764395 / 1000000000000) (30005764396 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1553949716746917 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11380896358 / 1000000000000) (-11380896302 / 1000000000000), orderedInterval (38862946177 / 1000000000000) (38862946233 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (450395196012783 / 800000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33313248165 / 1000000000000) (-33313248032 / 1000000000000), orderedInterval (-4553262074 / 1000000000000) (-4553261941 / 1000000000000)))) (orderedInterval (-2552628644 / 1000000000000) (-2552628591 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_chunkChecks1_2 :
    compactCertificate433.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1245816815171901 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42481170037 / 1000000000000) (-42481170035 / 1000000000000), orderedInterval (-15403449373 / 1000000000000) (-15403449372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1056092711264661 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38897770974 / 1000000000000) (38897770975 / 1000000000000), orderedInterval (29896140669 / 1000000000000) (29896140670 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (660853782752583 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (30104188028 / 1000000000000) (30104191718 / 1000000000000), orderedInterval (-54377976042 / 1000000000000) (-54377972352 / 1000000000000)))) (orderedInterval (91443018 / 1000000000000) (91443154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (355409362264761 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84214305596 / 1000000000000) (84214305726 / 1000000000000), orderedInterval (-9003717356 / 1000000000000) (-9003717226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (965005555517283 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6844317958 / 1000000000000) (-6844317957 / 1000000000000), orderedInterval (-50897346341 / 1000000000000) (-50897346340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1317632585196291 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14076300878 / 1000000000000) (-14076300877 / 1000000000000), orderedInterval (-41625680591 / 1000000000000) (-41625680590 / 1000000000000)))) (orderedInterval (4414466806 / 1000000000000) (4414466840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (557146217247417 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65153235269 / 1000000000000) (65153236782 / 1000000000000), orderedInterval (-18278449789 / 1000000000000) (-18278448276 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2264768441277657 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33424148185 / 1000000000000) (33424148476 / 1000000000000), orderedInterval (2656400997 / 1000000000000) (2656401288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1512760360200663 / 4000000000000) 1 (IntervalRat.scale (609 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (37574773168 / 1000000000000) (37574796413 / 1000000000000), orderedInterval (-16525952950 / 1000000000000) (-16525929705 / 1000000000000)))) (orderedInterval (3398608475 / 1000000000000) (3398614059 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_chunkChecks1 :
    compactCertificate433.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate433.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate433_chunkChecks1_0
    compactCertificate433_chunkChecks1_1 compactCertificate433_chunkChecks1_2

theorem compactCertificate433_chunkChecks2_0 :
    compactCertificate433.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (609 / 2) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23918953229 / 1000000000000) (-23918953228 / 1000000000000), orderedInterval (-38929818234 / 1000000000000) (-38929818233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (897173287271709 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47872392760 / 1000000000000) (-47872376354 / 1000000000000), orderedInterval (23485465899 / 1000000000000) (23485482304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (290127407515197 / 800000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34806149987 / 1000000000000) (-34806046546 / 1000000000000), orderedInterval (23370799089 / 1000000000000) (23370902530 / 1000000000000)))) (orderedInterval (12664631196 / 1000000000000) (12664639941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (261792927643863 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-25189960234 / 1000000000000) (-25189960233 / 1000000000000), orderedInterval (-95163671879 / 1000000000000) (-95163671878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (703212627872811 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1909359079012287 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20705519659 / 1000000000000) (20705519660 / 1000000000000), orderedInterval (30060937353 / 1000000000000) (30060937354 / 1000000000000)))) (orderedInterval (3163308008 / 1000000000000) (3163308066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1406425255746231 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21620323285 / 1000000000000) (21620323286 / 1000000000000), orderedInterval (36618490074 / 1000000000000) (36618490075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2409933647471763 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2688869968 / 1000000000000) (2688869969 / 1000000000000), orderedInterval (32392671767 / 1000000000000) (32392671768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1775146217247417 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37850053562 / 1000000000000) (-37850052980 / 1000000000000), orderedInterval (1417597050 / 1000000000000) (1417597632 / 1000000000000)))) (orderedInterval (2274046919 / 1000000000000) (2274047003 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_chunkChecks2_1 :
    compactCertificate433.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2723530796594391 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1763109450 / 1000000000000) (1763109451 / 1000000000000), orderedInterval (-30528062360 / 1000000000000) (-30528062359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1572431238559839 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37416495690 / 1000000000000) (-37416495688 / 1000000000000), orderedInterval (-14766533752 / 1000000000000) (-14766533750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2790306826356651 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24186849130 / 1000000000000) (24186849131 / 1000000000000), orderedInterval (18082730491 / 1000000000000) (18082730492 / 1000000000000)))) (orderedInterval (-11912554542 / 1000000000000) (-11912554004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2607066586264119 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24470157680 / 1000000000000) (-24470141269 / 1000000000000), orderedInterval (19460265562 / 1000000000000) (19460281973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1860525732151527 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30324642728 / 1000000000000) (30324642729 / 1000000000000), orderedInterval (21159468758 / 1000000000000) (21159468759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2109637883618433 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13755303404 / 1000000000000) (13755303405 / 1000000000000), orderedInterval (31890897957 / 1000000000000) (31890897958 / 1000000000000)))) (orderedInterval (-8512793906 / 1000000000000) (-8512792448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1758796126555377 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23364773873 / 1000000000000) (23364773874 / 1000000000000), orderedInterval (30005764395 / 1000000000000) (30005764396 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1553949716746917 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11380896358 / 1000000000000) (-11380896302 / 1000000000000), orderedInterval (38862946177 / 1000000000000) (38862946233 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (450395196012783 / 800000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33313248165 / 1000000000000) (-33313248032 / 1000000000000), orderedInterval (-4553262074 / 1000000000000) (-4553261941 / 1000000000000)))) (orderedInterval (1301468469 / 1000000000000) (1301468549 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_chunkChecks2_2 :
    compactCertificate433.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1245816815171901 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42481170037 / 1000000000000) (-42481170035 / 1000000000000), orderedInterval (-15403449373 / 1000000000000) (-15403449372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1056092711264661 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38897770974 / 1000000000000) (38897770975 / 1000000000000), orderedInterval (29896140669 / 1000000000000) (29896140670 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (660853782752583 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (30104188028 / 1000000000000) (30104191718 / 1000000000000), orderedInterval (-54377976042 / 1000000000000) (-54377972352 / 1000000000000)))) (orderedInterval (-5739826070 / 1000000000000) (-5739825967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (355409362264761 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84214305596 / 1000000000000) (84214305726 / 1000000000000), orderedInterval (-9003717356 / 1000000000000) (-9003717226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (965005555517283 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6844317958 / 1000000000000) (-6844317957 / 1000000000000), orderedInterval (-50897346341 / 1000000000000) (-50897346340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1317632585196291 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14076300878 / 1000000000000) (-14076300877 / 1000000000000), orderedInterval (-41625680591 / 1000000000000) (-41625680590 / 1000000000000)))) (orderedInterval (-1242064096 / 1000000000000) (-1242064063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (557146217247417 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65153235269 / 1000000000000) (65153236782 / 1000000000000), orderedInterval (-18278449789 / 1000000000000) (-18278448276 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2264768441277657 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33424148185 / 1000000000000) (33424148476 / 1000000000000), orderedInterval (2656400997 / 1000000000000) (2656401288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1512760360200663 / 4000000000000) 2 (IntervalRat.scale (609 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (37574773168 / 1000000000000) (37574796413 / 1000000000000), orderedInterval (-16525952950 / 1000000000000) (-16525929705 / 1000000000000)))) (orderedInterval (20188748845 / 1000000000000) (20188755850 / 1000000000000))) = true
  rfl'

theorem compactCertificate433_chunkChecks2 :
    compactCertificate433.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate433.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate433_chunkChecks2_0
    compactCertificate433_chunkChecks2_1 compactCertificate433_chunkChecks2_2

theorem compactCertificate433_chunkChecks3_0 :
    compactCertificate433.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (609 / 2) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23918953229 / 1000000000000) (-23918953228 / 1000000000000), orderedInterval (-38929818234 / 1000000000000) (-38929818233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (897173287271709 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47872392760 / 1000000000000) (-47872376354 / 1000000000000), orderedInterval (23485465899 / 1000000000000) (23485482304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (290127407515197 / 800000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34806149987 / 1000000000000) (-34806046546 / 1000000000000), orderedInterval (23370799089 / 1000000000000) (23370902530 / 1000000000000)))) (orderedInterval (12984311752 / 1000000000000) (12984322129 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (261792927643863 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-25189960234 / 1000000000000) (-25189960233 / 1000000000000), orderedInterval (-95163671879 / 1000000000000) (-95163671878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (703212627872811 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1909359079012287 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20705519659 / 1000000000000) (20705519660 / 1000000000000), orderedInterval (30060937353 / 1000000000000) (30060937354 / 1000000000000)))) (orderedInterval (7878145681 / 1000000000000) (7878145768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1406425255746231 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21620323285 / 1000000000000) (21620323286 / 1000000000000), orderedInterval (36618490074 / 1000000000000) (36618490075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2409933647471763 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2688869968 / 1000000000000) (2688869969 / 1000000000000), orderedInterval (32392671767 / 1000000000000) (32392671768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1775146217247417 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37850053562 / 1000000000000) (-37850052980 / 1000000000000), orderedInterval (1417597050 / 1000000000000) (1417597632 / 1000000000000)))) (orderedInterval (7625557617 / 1000000000000) (7625557758 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate433_chunkChecks3_1 :
    compactCertificate433.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2723530796594391 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1763109450 / 1000000000000) (1763109451 / 1000000000000), orderedInterval (-30528062360 / 1000000000000) (-30528062359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1572431238559839 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37416495690 / 1000000000000) (-37416495688 / 1000000000000), orderedInterval (-14766533752 / 1000000000000) (-14766533750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2790306826356651 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24186849130 / 1000000000000) (24186849131 / 1000000000000), orderedInterval (18082730491 / 1000000000000) (18082730492 / 1000000000000)))) (orderedInterval (-89160020980 / 1000000000000) (-89160019801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2607066586264119 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24470157680 / 1000000000000) (-24470141269 / 1000000000000), orderedInterval (19460265562 / 1000000000000) (19460281973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1860525732151527 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30324642728 / 1000000000000) (30324642729 / 1000000000000), orderedInterval (21159468758 / 1000000000000) (21159468759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2109637883618433 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13755303404 / 1000000000000) (13755303405 / 1000000000000), orderedInterval (31890897957 / 1000000000000) (31890897958 / 1000000000000)))) (orderedInterval (-2819890428 / 1000000000000) (-2819887352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1758796126555377 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23364773873 / 1000000000000) (23364773874 / 1000000000000), orderedInterval (30005764395 / 1000000000000) (30005764396 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1553949716746917 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11380896358 / 1000000000000) (-11380896302 / 1000000000000), orderedInterval (38862946177 / 1000000000000) (38862946233 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (450395196012783 / 800000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33313248165 / 1000000000000) (-33313248032 / 1000000000000), orderedInterval (-4553262074 / 1000000000000) (-4553261941 / 1000000000000)))) (orderedInterval (4307786088 / 1000000000000) (4307786213 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate433_chunkChecks3_2 :
    compactCertificate433.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1245816815171901 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42481170037 / 1000000000000) (-42481170035 / 1000000000000), orderedInterval (-15403449373 / 1000000000000) (-15403449372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1056092711264661 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38897770974 / 1000000000000) (38897770975 / 1000000000000), orderedInterval (29896140669 / 1000000000000) (29896140670 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (660853782752583 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (30104188028 / 1000000000000) (30104191718 / 1000000000000), orderedInterval (-54377976042 / 1000000000000) (-54377972352 / 1000000000000)))) (orderedInterval (-1230859739 / 1000000000000) (-1230859654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (355409362264761 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84214305596 / 1000000000000) (84214305726 / 1000000000000), orderedInterval (-9003717356 / 1000000000000) (-9003717226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (965005555517283 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6844317958 / 1000000000000) (-6844317957 / 1000000000000), orderedInterval (-50897346341 / 1000000000000) (-50897346340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1317632585196291 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14076300878 / 1000000000000) (-14076300877 / 1000000000000), orderedInterval (-41625680591 / 1000000000000) (-41625680590 / 1000000000000)))) (orderedInterval (-4613067999 / 1000000000000) (-4613067964 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (557146217247417 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65153235269 / 1000000000000) (65153236782 / 1000000000000), orderedInterval (-18278449789 / 1000000000000) (-18278448276 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2264768441277657 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33424148185 / 1000000000000) (33424148476 / 1000000000000), orderedInterval (2656400997 / 1000000000000) (2656401288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1512760360200663 / 4000000000000) 3 (IntervalRat.scale (609 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (37574773168 / 1000000000000) (37574796413 / 1000000000000), orderedInterval (-16525952950 / 1000000000000) (-16525929705 / 1000000000000)))) (orderedInterval (-4606169275 / 1000000000000) (-4606160474 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate433_chunkChecks3 :
    compactCertificate433.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate433.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate433_chunkChecks3_0
    compactCertificate433_chunkChecks3_1 compactCertificate433_chunkChecks3_2

theorem compactCertificate433_chunkChecks4_0 :
    compactCertificate433.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (609 / 2) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23918953229 / 1000000000000) (-23918953228 / 1000000000000), orderedInterval (-38929818234 / 1000000000000) (-38929818233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (897173287271709 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47872392760 / 1000000000000) (-47872376354 / 1000000000000), orderedInterval (23485465899 / 1000000000000) (23485482304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (290127407515197 / 800000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34806149987 / 1000000000000) (-34806046546 / 1000000000000), orderedInterval (23370799089 / 1000000000000) (23370902530 / 1000000000000)))) (orderedInterval (-13806708589 / 1000000000000) (-13806696225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (261792927643863 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-25189960234 / 1000000000000) (-25189960233 / 1000000000000), orderedInterval (-95163671879 / 1000000000000) (-95163671878 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (703212627872811 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (36831186465 / 1000000000000) (36831186466 / 1000000000000), orderedInterval (47483853609 / 1000000000000) (47483853610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1909359079012287 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (20705519659 / 1000000000000) (20705519660 / 1000000000000), orderedInterval (30060937353 / 1000000000000) (30060937354 / 1000000000000)))) (orderedInterval (-8790725580 / 1000000000000) (-8790725447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1406425255746231 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21620323285 / 1000000000000) (21620323286 / 1000000000000), orderedInterval (36618490074 / 1000000000000) (36618490075 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2409933647471763 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2688869968 / 1000000000000) (2688869969 / 1000000000000), orderedInterval (32392671767 / 1000000000000) (32392671768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1775146217247417 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-37850053562 / 1000000000000) (-37850052980 / 1000000000000), orderedInterval (1417597050 / 1000000000000) (1417597632 / 1000000000000)))) (orderedInterval (-5448333536 / 1000000000000) (-5448333294 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate433_chunkChecks4_1 :
    compactCertificate433.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2723530796594391 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1763109450 / 1000000000000) (1763109451 / 1000000000000), orderedInterval (-30528062360 / 1000000000000) (-30528062359 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1572431238559839 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-37416495690 / 1000000000000) (-37416495688 / 1000000000000), orderedInterval (-14766533752 / 1000000000000) (-14766533750 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2790306826356651 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24186849130 / 1000000000000) (24186849131 / 1000000000000), orderedInterval (18082730491 / 1000000000000) (18082730492 / 1000000000000)))) (orderedInterval (79755504631 / 1000000000000) (79755507249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2607066586264119 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24470157680 / 1000000000000) (-24470141269 / 1000000000000), orderedInterval (19460265562 / 1000000000000) (19460281973 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1860525732151527 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30324642728 / 1000000000000) (30324642729 / 1000000000000), orderedInterval (21159468758 / 1000000000000) (21159468759 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2109637883618433 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13755303404 / 1000000000000) (13755303405 / 1000000000000), orderedInterval (31890897957 / 1000000000000) (31890897958 / 1000000000000)))) (orderedInterval (24277072103 / 1000000000000) (24277078628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1758796126555377 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (23364773873 / 1000000000000) (23364773874 / 1000000000000), orderedInterval (30005764395 / 1000000000000) (30005764396 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1553949716746917 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11380896358 / 1000000000000) (-11380896302 / 1000000000000), orderedInterval (38862946177 / 1000000000000) (38862946233 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (450395196012783 / 800000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33313248165 / 1000000000000) (-33313248032 / 1000000000000), orderedInterval (-4553262074 / 1000000000000) (-4553261941 / 1000000000000)))) (orderedInterval (-7097204477 / 1000000000000) (-7097204275 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate433_chunkChecks4_2 :
    compactCertificate433.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1245816815171901 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-42481170037 / 1000000000000) (-42481170035 / 1000000000000), orderedInterval (-15403449373 / 1000000000000) (-15403449372 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1056092711264661 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38897770974 / 1000000000000) (38897770975 / 1000000000000), orderedInterval (29896140669 / 1000000000000) (29896140670 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (660853782752583 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (30104188028 / 1000000000000) (30104191718 / 1000000000000), orderedInterval (-54377976042 / 1000000000000) (-54377972352 / 1000000000000)))) (orderedInterval (6283060913 / 1000000000000) (6283060988 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (355409362264761 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84214305596 / 1000000000000) (84214305726 / 1000000000000), orderedInterval (-9003717356 / 1000000000000) (-9003717226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (965005555517283 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6844317958 / 1000000000000) (-6844317957 / 1000000000000), orderedInterval (-50897346341 / 1000000000000) (-50897346340 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1317632585196291 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-14076300878 / 1000000000000) (-14076300877 / 1000000000000), orderedInterval (-41625680591 / 1000000000000) (-41625680590 / 1000000000000)))) (orderedInterval (1557689846 / 1000000000000) (1557689882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (557146217247417 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65153235269 / 1000000000000) (65153236782 / 1000000000000), orderedInterval (-18278449789 / 1000000000000) (-18278448276 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2264768441277657 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33424148185 / 1000000000000) (33424148476 / 1000000000000), orderedInterval (2656400997 / 1000000000000) (2656401288 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1512760360200663 / 4000000000000) 4 (IntervalRat.scale (609 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (37574773168 / 1000000000000) (37574796413 / 1000000000000), orderedInterval (-16525952950 / 1000000000000) (-16525929705 / 1000000000000)))) (orderedInterval (-49251822040 / 1000000000000) (-49251810890 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate433_chunkChecks4 :
    compactCertificate433.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate433.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate433_chunkChecks4_0
    compactCertificate433_chunkChecks4_1 compactCertificate433_chunkChecks4_2

theorem compactCertificate433_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate433.chunkCheck r b = true :=
  compactCertificate433.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate433_chunkChecks0
    · exact compactCertificate433_chunkChecks1
    · exact compactCertificate433_chunkChecks2
    · exact compactCertificate433_chunkChecks3
    · exact compactCertificate433_chunkChecks4)

theorem compactCertificate433_coefficient0 :
    compactCertificate433.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate433_coefficient1 :
    compactCertificate433.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate433_coefficient2 :
    compactCertificate433.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate433_coefficient3 :
    compactCertificate433.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate433_coefficient4 :
    compactCertificate433.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate433_coefficients : ∀ r : Fin 5,
    compactCertificate433.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate433_coefficient0
  · exact compactCertificate433_coefficient1
  · exact compactCertificate433_coefficient2
  · exact compactCertificate433_coefficient3
  · exact compactCertificate433_coefficient4

theorem compactCertificate433_lower : (1 : ℚ) ≤ compactCertificate433.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate433, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate433_proves {t : ℝ} (ht : t ∈ compactCertificate433.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate433.proves compactCertificate433_states compactCertificate433_chunks
    compactCertificate433_coefficients compactCertificate433_lower ht

end Erdos232
