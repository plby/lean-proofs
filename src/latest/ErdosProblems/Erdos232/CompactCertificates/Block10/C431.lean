/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate431 : CompactCertificate where
  left := 302
  right := 303
  center := 605 / 2
  grid := fun i =>
    match i.val with
    | 0 => 96
    | 1 => 71
    | 2 => 115
    | 3 => 21
    | 4 => 56
    | 5 => 151
    | 6 => 111
    | 7 => 191
    | 8 => 140
    | 9 => 215
    | 10 => 124
    | 11 => 221
    | 12 => 206
    | 13 => 147
    | 14 => 167
    | 15 => 139
    | 16 => 123
    | 17 => 178
    | 18 => 99
    | 19 => 84
    | 20 => 52
    | 21 => 28
    | 22 => 76
    | 23 => 104
    | 24 => 44
    | 25 => 179
    | _ => 120
  point := fun i =>
    match i.val with
    | 0 => 605 / 2
    | 1 => 178256104696021 / 800000000000
    | 2 => 57644361755893 / 160000000000
    | 3 => 52014686773247 / 800000000000
    | 4 => 139718765143859 / 800000000000
    | 5 => 379363626536103 / 800000000000
    | 6 => 279437530287839 / 800000000000
    | 7 => 478820971008347 / 800000000000
    | 8 => 352697360077073 / 800000000000
    | 9 => 541128450554879 / 800000000000
    | 10 => 312420656593991 / 800000000000
    | 11 => 554395937584819 / 800000000000
    | 12 => 517988599241311 / 800000000000
    | 13 => 369661106059663 / 800000000000
    | 14 => 419156295431577 / 800000000000
    | 15 => 349448819890313 / 800000000000
    | 16 => 308748630092573 / 800000000000
    | 17 => 89487387056727 / 160000000000
    | 18 => 247526822062069 / 800000000000
    | 19 => 209831228346509 / 800000000000
    | 20 => 131302639922927 / 800000000000
    | 21 => 70614996443409 / 800000000000
    | 22 => 191733451917227 / 800000000000
    | 23 => 261795636795979 / 800000000000
    | 24 => 110697360077073 / 800000000000
    | 25 => 449978622979633 / 800000000000
    | _ => 300564866312447 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (45538056671 / 1000000000000) (45538057358 / 1000000000000), orderedInterval (-5626012366 / 1000000000000) (-5626011680 / 1000000000000))
    | 1 => (orderedInterval (-28024630322 / 1000000000000) (-28024630321 / 1000000000000), orderedInterval (-45453320262 / 1000000000000) (-45453320261 / 1000000000000))
    | 2 => (orderedInterval (9208079435 / 1000000000000) (9208079462 / 1000000000000), orderedInterval (-41027900228 / 1000000000000) (-41027900202 / 1000000000000))
    | 3 => (orderedInterval (16897714354 / 1000000000000) (16897714466 / 1000000000000), orderedInterval (-97629295363 / 1000000000000) (-97629295251 / 1000000000000))
    | 4 => (orderedInterval (-28735768196 / 1000000000000) (-28735765061 / 1000000000000), orderedInterval (53180415812 / 1000000000000) (53180418948 / 1000000000000))
    | 5 => (orderedInterval (-20965220112 / 1000000000000) (-20965220111 / 1000000000000), orderedInterval (-30027190463 / 1000000000000) (-30027190462 / 1000000000000))
    | 6 => (orderedInterval (-41792219742 / 1000000000000) (-41792219732 / 1000000000000), orderedInterval (-8657029356 / 1000000000000) (-8657029347 / 1000000000000))
    | 7 => (orderedInterval (21816811491 / 1000000000000) (21816815478 / 1000000000000), orderedInterval (-24260180364 / 1000000000000) (-24260176376 / 1000000000000))
    | 8 => (orderedInterval (36692897720 / 1000000000000) (36692905028 / 1000000000000), orderedInterval (-9922535060 / 1000000000000) (-9922527752 / 1000000000000))
    | 9 => (orderedInterval (-30168744232 / 1000000000000) (-30168733425 / 1000000000000), orderedInterval (5591905502 / 1000000000000) (5591916310 / 1000000000000))
    | 10 => (orderedInterval (39703887294 / 1000000000000) (39703889655 / 1000000000000), orderedInterval (-7382990318 / 1000000000000) (-7382987957 / 1000000000000))
    | 11 => (orderedInterval (14844838099 / 1000000000000) (14844838254 / 1000000000000), orderedInterval (-26435715640 / 1000000000000) (-26435715485 / 1000000000000))
    | 12 => (orderedInterval (27985640503 / 1000000000000) (27985640505 / 1000000000000), orderedInterval (14121300697 / 1000000000000) (14121300699 / 1000000000000))
    | 13 => (orderedInterval (-32148592216 / 1000000000000) (-32148592215 / 1000000000000), orderedInterval (-18517967690 / 1000000000000) (-18517967689 / 1000000000000))
    | 14 => (orderedInterval (-2943895336 / 1000000000000) (-2943895335 / 1000000000000), orderedInterval (-34730228710 / 1000000000000) (-34730228709 / 1000000000000))
    | 15 => (orderedInterval (-30251423318 / 1000000000000) (-30251423317 / 1000000000000), orderedInterval (-23252218667 / 1000000000000) (-23252218666 / 1000000000000))
    | 16 => (orderedInterval (-12194955527 / 1000000000000) (-12194955526 / 1000000000000), orderedInterval (-38724781924 / 1000000000000) (-38724781923 / 1000000000000))
    | 17 => (orderedInterval (25956925474 / 1000000000000) (25956925475 / 1000000000000), orderedInterval (21528814875 / 1000000000000) (21528814876 / 1000000000000))
    | 18 => (orderedInterval (33292966723 / 1000000000000) (33293007487 / 1000000000000), orderedInterval (-30861525181 / 1000000000000) (-30861484418 / 1000000000000))
    | 19 => (orderedInterval (-36014991184 / 1000000000000) (-36014942701 / 1000000000000), orderedInterval (33685450403 / 1000000000000) (33685498885 / 1000000000000))
    | 20 => (orderedInterval (62266501541 / 1000000000000) (62266501579 / 1000000000000), orderedInterval (1098038950 / 1000000000000) (1098038989 / 1000000000000))
    | 21 => (orderedInterval (75222920101 / 1000000000000) (75222920102 / 1000000000000), orderedInterval (38991373105 / 1000000000000) (38991373106 / 1000000000000))
    | 22 => (orderedInterval (51169225983 / 1000000000000) (51169226438 / 1000000000000), orderedInterval (-6269110549 / 1000000000000) (-6269110095 / 1000000000000))
    | 23 => (orderedInterval (42545272819 / 1000000000000) (42545272822 / 1000000000000), orderedInterval (11566521164 / 1000000000000) (11566521168 / 1000000000000))
    | 24 => (orderedInterval (54215208284 / 1000000000000) (54215208285 / 1000000000000), orderedInterval (40565568619 / 1000000000000) (40565568620 / 1000000000000))
    | 25 => (orderedInterval (-26630352267 / 1000000000000) (-26630352266 / 1000000000000), orderedInterval (-20534695007 / 1000000000000) (-20534695006 / 1000000000000))
    | _ => (orderedInterval (-19733910186 / 1000000000000) (-19733909153 / 1000000000000), orderedInterval (36151541972 / 1000000000000) (36151543005 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (18328896914 / 1000000000000) (18328897210 / 1000000000000)
      | 1 => orderedInterval (257888662 / 1000000000000) (257888814 / 1000000000000)
      | 2 => orderedInterval (213877056 / 1000000000000) (213877373 / 1000000000000)
      | 3 => orderedInterval (10412632139 / 1000000000000) (10412634376 / 1000000000000)
      | 4 => orderedInterval (-3530392405 / 1000000000000) (-3530392368 / 1000000000000)
      | 5 => orderedInterval (1013143135 / 1000000000000) (1013143164 / 1000000000000)
      | 6 => orderedInterval (-1257753303 / 1000000000000) (-1257743963 / 1000000000000)
      | 7 => orderedInterval (-5810490851 / 1000000000000) (-5810490804 / 1000000000000)
      | _ => orderedInterval (6197189851 / 1000000000000) (6197190129 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-5409336399 / 1000000000000) (-5409336101 / 1000000000000)
      | 1 => orderedInterval (4694982297 / 1000000000000) (4694982406 / 1000000000000)
      | 2 => orderedInterval (1131045056 / 1000000000000) (1131045587 / 1000000000000)
      | 3 => orderedInterval (-11537147981 / 1000000000000) (-11537143162 / 1000000000000)
      | 4 => orderedInterval (-2916122561 / 1000000000000) (-2916122501 / 1000000000000)
      | 5 => orderedInterval (3458769373 / 1000000000000) (3458769415 / 1000000000000)
      | 6 => orderedInterval (3413452470 / 1000000000000) (3413461587 / 1000000000000)
      | 7 => orderedInterval (-1056360765 / 1000000000000) (-1056360723 / 1000000000000)
      | _ => orderedInterval (-5204509311 / 1000000000000) (-5204508952 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-18656586681 / 1000000000000) (-18656586378 / 1000000000000)
      | 1 => orderedInterval (-3319894152 / 1000000000000) (-3319894056 / 1000000000000)
      | 2 => orderedInterval (746999899 / 1000000000000) (747000810 / 1000000000000)
      | 3 => orderedInterval (-42743006389 / 1000000000000) (-42742995832 / 1000000000000)
      | 4 => orderedInterval (9373135834 / 1000000000000) (9373135931 / 1000000000000)
      | 5 => orderedInterval (-2690890486 / 1000000000000) (-2690890423 / 1000000000000)
      | 6 => orderedInterval (3428654841 / 1000000000000) (3428663821 / 1000000000000)
      | 7 => orderedInterval (4666336846 / 1000000000000) (4666336886 / 1000000000000)
      | _ => orderedInterval (-13257583662 / 1000000000000) (-13257583188 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (6528195561 / 1000000000000) (6528195868 / 1000000000000)
      | 1 => orderedInterval (-8596395119 / 1000000000000) (-8596395011 / 1000000000000)
      | 2 => orderedInterval (-5056210996 / 1000000000000) (-5056209398 / 1000000000000)
      | 3 => orderedInterval (57609580917 / 1000000000000) (57609604229 / 1000000000000)
      | 4 => orderedInterval (7797095102 / 1000000000000) (7797095267 / 1000000000000)
      | 5 => orderedInterval (-7268689474 / 1000000000000) (-7268689377 / 1000000000000)
      | 6 => orderedInterval (-4054535645 / 1000000000000) (-4054526787 / 1000000000000)
      | 7 => orderedInterval (1053975380 / 1000000000000) (1053975420 / 1000000000000)
      | _ => orderedInterval (2269642663 / 1000000000000) (2269643304 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (19016661946 / 1000000000000) (19016662261 / 1000000000000)
      | 1 => orderedInterval (8940339180 / 1000000000000) (8940339325 / 1000000000000)
      | 2 => orderedInterval (-6278739407 / 1000000000000) (-6278736538 / 1000000000000)
      | 3 => orderedInterval (199930082130 / 1000000000000) (199930133967 / 1000000000000)
      | 4 => orderedInterval (-27073709541 / 1000000000000) (-27073709255 / 1000000000000)
      | 5 => orderedInterval (8144699781 / 1000000000000) (8144699935 / 1000000000000)
      | 6 => orderedInterval (-4471819130 / 1000000000000) (-4471810323 / 1000000000000)
      | 7 => orderedInterval (-4940095394 / 1000000000000) (-4940095354 / 1000000000000)
      | _ => orderedInterval (34722571852 / 1000000000000) (34722572747 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (25824991198 / 1000000000000) (25825003931 / 1000000000000)
    | 1 => orderedInterval (-13425227821 / 1000000000000) (-13425212444 / 1000000000000)
    | 2 => orderedInterval (-62452833950 / 1000000000000) (-62452812429 / 1000000000000)
    | 3 => orderedInterval (50282658389 / 1000000000000) (50282693515 / 1000000000000)
    | _ => orderedInterval (227989991417 / 1000000000000) (227990056765 / 1000000000000)

theorem compactCertificate431_stateChecks0 :
    compactCertificate431.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (605 / 2)) (orderedInterval (45538056671 / 1000000000000) (45538057358 / 1000000000000), orderedInterval (-5626012366 / 1000000000000) (-5626011680 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (178256104696021 / 800000000000)) (orderedInterval (-28024630322 / 1000000000000) (-28024630321 / 1000000000000), orderedInterval (-45453320262 / 1000000000000) (-45453320261 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (57644361755893 / 160000000000)) (orderedInterval (9208079435 / 1000000000000) (9208079462 / 1000000000000), orderedInterval (-41027900228 / 1000000000000) (-41027900202 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_stateChecks1 :
    compactCertificate431.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (52014686773247 / 800000000000)) (orderedInterval (16897714354 / 1000000000000) (16897714466 / 1000000000000), orderedInterval (-97629295363 / 1000000000000) (-97629295251 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (139718765143859 / 800000000000)) (orderedInterval (-28735768196 / 1000000000000) (-28735765061 / 1000000000000), orderedInterval (53180415812 / 1000000000000) (53180418948 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (379363626536103 / 800000000000)) (orderedInterval (-20965220112 / 1000000000000) (-20965220111 / 1000000000000), orderedInterval (-30027190463 / 1000000000000) (-30027190462 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_stateChecks2 :
    compactCertificate431.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (279437530287839 / 800000000000)) (orderedInterval (-41792219742 / 1000000000000) (-41792219732 / 1000000000000), orderedInterval (-8657029356 / 1000000000000) (-8657029347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (478820971008347 / 800000000000)) (orderedInterval (21816811491 / 1000000000000) (21816815478 / 1000000000000), orderedInterval (-24260180364 / 1000000000000) (-24260176376 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (352697360077073 / 800000000000)) (orderedInterval (36692897720 / 1000000000000) (36692905028 / 1000000000000), orderedInterval (-9922535060 / 1000000000000) (-9922527752 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_stateChecks3 :
    compactCertificate431.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (541128450554879 / 800000000000)) (orderedInterval (-30168744232 / 1000000000000) (-30168733425 / 1000000000000), orderedInterval (5591905502 / 1000000000000) (5591916310 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (312420656593991 / 800000000000)) (orderedInterval (39703887294 / 1000000000000) (39703889655 / 1000000000000), orderedInterval (-7382990318 / 1000000000000) (-7382987957 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (554395937584819 / 800000000000)) (orderedInterval (14844838099 / 1000000000000) (14844838254 / 1000000000000), orderedInterval (-26435715640 / 1000000000000) (-26435715485 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_stateChecks4 :
    compactCertificate431.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (517988599241311 / 800000000000)) (orderedInterval (27985640503 / 1000000000000) (27985640505 / 1000000000000), orderedInterval (14121300697 / 1000000000000) (14121300699 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (369661106059663 / 800000000000)) (orderedInterval (-32148592216 / 1000000000000) (-32148592215 / 1000000000000), orderedInterval (-18517967690 / 1000000000000) (-18517967689 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (419156295431577 / 800000000000)) (orderedInterval (-2943895336 / 1000000000000) (-2943895335 / 1000000000000), orderedInterval (-34730228710 / 1000000000000) (-34730228709 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_stateChecks5 :
    compactCertificate431.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (349448819890313 / 800000000000)) (orderedInterval (-30251423318 / 1000000000000) (-30251423317 / 1000000000000), orderedInterval (-23252218667 / 1000000000000) (-23252218666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (308748630092573 / 800000000000)) (orderedInterval (-12194955527 / 1000000000000) (-12194955526 / 1000000000000), orderedInterval (-38724781924 / 1000000000000) (-38724781923 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (89487387056727 / 160000000000)) (orderedInterval (25956925474 / 1000000000000) (25956925475 / 1000000000000), orderedInterval (21528814875 / 1000000000000) (21528814876 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_stateChecks6 :
    compactCertificate431.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (247526822062069 / 800000000000)) (orderedInterval (33292966723 / 1000000000000) (33293007487 / 1000000000000), orderedInterval (-30861525181 / 1000000000000) (-30861484418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (209831228346509 / 800000000000)) (orderedInterval (-36014991184 / 1000000000000) (-36014942701 / 1000000000000), orderedInterval (33685450403 / 1000000000000) (33685498885 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (131302639922927 / 800000000000)) (orderedInterval (62266501541 / 1000000000000) (62266501579 / 1000000000000), orderedInterval (1098038950 / 1000000000000) (1098038989 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_stateChecks7 :
    compactCertificate431.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (70614996443409 / 800000000000)) (orderedInterval (75222920101 / 1000000000000) (75222920102 / 1000000000000), orderedInterval (38991373105 / 1000000000000) (38991373106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (191733451917227 / 800000000000)) (orderedInterval (51169225983 / 1000000000000) (51169226438 / 1000000000000), orderedInterval (-6269110549 / 1000000000000) (-6269110095 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (261795636795979 / 800000000000)) (orderedInterval (42545272819 / 1000000000000) (42545272822 / 1000000000000), orderedInterval (11566521164 / 1000000000000) (11566521168 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_stateChecks8 :
    compactCertificate431.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (110697360077073 / 800000000000)) (orderedInterval (54215208284 / 1000000000000) (54215208285 / 1000000000000), orderedInterval (40565568619 / 1000000000000) (40565568620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (449978622979633 / 800000000000)) (orderedInterval (-26630352267 / 1000000000000) (-26630352266 / 1000000000000), orderedInterval (-20534695007 / 1000000000000) (-20534695006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (300564866312447 / 800000000000)) (orderedInterval (-19733910186 / 1000000000000) (-19733909153 / 1000000000000), orderedInterval (36151541972 / 1000000000000) (36151543005 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_states : ∀ j,
    BesselStateValid (compactCertificate431.point j) (compactCertificate431.state j) :=
  compactCertificate431.statesValid_of_checks3 compactCertificate431_stateChecks0
    compactCertificate431_stateChecks1 compactCertificate431_stateChecks2
    compactCertificate431_stateChecks3 compactCertificate431_stateChecks4
    compactCertificate431_stateChecks5 compactCertificate431_stateChecks6
    compactCertificate431_stateChecks7 compactCertificate431_stateChecks8

theorem compactCertificate431_chunkChecks0_0 :
    compactCertificate431.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (605 / 2) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (45538056671 / 1000000000000) (45538057358 / 1000000000000), orderedInterval (-5626012366 / 1000000000000) (-5626011680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (178256104696021 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28024630322 / 1000000000000) (-28024630321 / 1000000000000), orderedInterval (-45453320262 / 1000000000000) (-45453320261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (57644361755893 / 160000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9208079435 / 1000000000000) (9208079462 / 1000000000000), orderedInterval (-41027900228 / 1000000000000) (-41027900202 / 1000000000000)))) (orderedInterval (18328896914 / 1000000000000) (18328897210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (52014686773247 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16897714354 / 1000000000000) (16897714466 / 1000000000000), orderedInterval (-97629295363 / 1000000000000) (-97629295251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (139718765143859 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-28735768196 / 1000000000000) (-28735765061 / 1000000000000), orderedInterval (53180415812 / 1000000000000) (53180418948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (379363626536103 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20965220112 / 1000000000000) (-20965220111 / 1000000000000), orderedInterval (-30027190463 / 1000000000000) (-30027190462 / 1000000000000)))) (orderedInterval (257888662 / 1000000000000) (257888814 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (279437530287839 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41792219742 / 1000000000000) (-41792219732 / 1000000000000), orderedInterval (-8657029356 / 1000000000000) (-8657029347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (478820971008347 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21816811491 / 1000000000000) (21816815478 / 1000000000000), orderedInterval (-24260180364 / 1000000000000) (-24260176376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (352697360077073 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36692897720 / 1000000000000) (36692905028 / 1000000000000), orderedInterval (-9922535060 / 1000000000000) (-9922527752 / 1000000000000)))) (orderedInterval (213877056 / 1000000000000) (213877373 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_chunkChecks0_1 :
    compactCertificate431.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (541128450554879 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30168744232 / 1000000000000) (-30168733425 / 1000000000000), orderedInterval (5591905502 / 1000000000000) (5591916310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (312420656593991 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39703887294 / 1000000000000) (39703889655 / 1000000000000), orderedInterval (-7382990318 / 1000000000000) (-7382987957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (554395937584819 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14844838099 / 1000000000000) (14844838254 / 1000000000000), orderedInterval (-26435715640 / 1000000000000) (-26435715485 / 1000000000000)))) (orderedInterval (10412632139 / 1000000000000) (10412634376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (517988599241311 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27985640503 / 1000000000000) (27985640505 / 1000000000000), orderedInterval (14121300697 / 1000000000000) (14121300699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (369661106059663 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32148592216 / 1000000000000) (-32148592215 / 1000000000000), orderedInterval (-18517967690 / 1000000000000) (-18517967689 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (419156295431577 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2943895336 / 1000000000000) (-2943895335 / 1000000000000), orderedInterval (-34730228710 / 1000000000000) (-34730228709 / 1000000000000)))) (orderedInterval (-3530392405 / 1000000000000) (-3530392368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (349448819890313 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30251423318 / 1000000000000) (-30251423317 / 1000000000000), orderedInterval (-23252218667 / 1000000000000) (-23252218666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (308748630092573 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-12194955527 / 1000000000000) (-12194955526 / 1000000000000), orderedInterval (-38724781924 / 1000000000000) (-38724781923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (89487387056727 / 160000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25956925474 / 1000000000000) (25956925475 / 1000000000000), orderedInterval (21528814875 / 1000000000000) (21528814876 / 1000000000000)))) (orderedInterval (1013143135 / 1000000000000) (1013143164 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_chunkChecks0_2 :
    compactCertificate431.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (247526822062069 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33292966723 / 1000000000000) (33293007487 / 1000000000000), orderedInterval (-30861525181 / 1000000000000) (-30861484418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (209831228346509 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36014991184 / 1000000000000) (-36014942701 / 1000000000000), orderedInterval (33685450403 / 1000000000000) (33685498885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (131302639922927 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62266501541 / 1000000000000) (62266501579 / 1000000000000), orderedInterval (1098038950 / 1000000000000) (1098038989 / 1000000000000)))) (orderedInterval (-1257753303 / 1000000000000) (-1257743963 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (70614996443409 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75222920101 / 1000000000000) (75222920102 / 1000000000000), orderedInterval (38991373105 / 1000000000000) (38991373106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (191733451917227 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51169225983 / 1000000000000) (51169226438 / 1000000000000), orderedInterval (-6269110549 / 1000000000000) (-6269110095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (261795636795979 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42545272819 / 1000000000000) (42545272822 / 1000000000000), orderedInterval (11566521164 / 1000000000000) (11566521168 / 1000000000000)))) (orderedInterval (-5810490851 / 1000000000000) (-5810490804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (110697360077073 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54215208284 / 1000000000000) (54215208285 / 1000000000000), orderedInterval (40565568619 / 1000000000000) (40565568620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (449978622979633 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26630352267 / 1000000000000) (-26630352266 / 1000000000000), orderedInterval (-20534695007 / 1000000000000) (-20534695006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (300564866312447 / 800000000000) 0 (IntervalRat.scale (605 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19733910186 / 1000000000000) (-19733909153 / 1000000000000), orderedInterval (36151541972 / 1000000000000) (36151543005 / 1000000000000)))) (orderedInterval (6197189851 / 1000000000000) (6197190129 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_chunkChecks0 :
    compactCertificate431.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate431.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate431_chunkChecks0_0
    compactCertificate431_chunkChecks0_1 compactCertificate431_chunkChecks0_2

theorem compactCertificate431_chunkChecks1_0 :
    compactCertificate431.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (605 / 2) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (45538056671 / 1000000000000) (45538057358 / 1000000000000), orderedInterval (-5626012366 / 1000000000000) (-5626011680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (178256104696021 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28024630322 / 1000000000000) (-28024630321 / 1000000000000), orderedInterval (-45453320262 / 1000000000000) (-45453320261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (57644361755893 / 160000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9208079435 / 1000000000000) (9208079462 / 1000000000000), orderedInterval (-41027900228 / 1000000000000) (-41027900202 / 1000000000000)))) (orderedInterval (-5409336399 / 1000000000000) (-5409336101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (52014686773247 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16897714354 / 1000000000000) (16897714466 / 1000000000000), orderedInterval (-97629295363 / 1000000000000) (-97629295251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (139718765143859 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-28735768196 / 1000000000000) (-28735765061 / 1000000000000), orderedInterval (53180415812 / 1000000000000) (53180418948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (379363626536103 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20965220112 / 1000000000000) (-20965220111 / 1000000000000), orderedInterval (-30027190463 / 1000000000000) (-30027190462 / 1000000000000)))) (orderedInterval (4694982297 / 1000000000000) (4694982406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (279437530287839 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41792219742 / 1000000000000) (-41792219732 / 1000000000000), orderedInterval (-8657029356 / 1000000000000) (-8657029347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (478820971008347 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21816811491 / 1000000000000) (21816815478 / 1000000000000), orderedInterval (-24260180364 / 1000000000000) (-24260176376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (352697360077073 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36692897720 / 1000000000000) (36692905028 / 1000000000000), orderedInterval (-9922535060 / 1000000000000) (-9922527752 / 1000000000000)))) (orderedInterval (1131045056 / 1000000000000) (1131045587 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_chunkChecks1_1 :
    compactCertificate431.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (541128450554879 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30168744232 / 1000000000000) (-30168733425 / 1000000000000), orderedInterval (5591905502 / 1000000000000) (5591916310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (312420656593991 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39703887294 / 1000000000000) (39703889655 / 1000000000000), orderedInterval (-7382990318 / 1000000000000) (-7382987957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (554395937584819 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14844838099 / 1000000000000) (14844838254 / 1000000000000), orderedInterval (-26435715640 / 1000000000000) (-26435715485 / 1000000000000)))) (orderedInterval (-11537147981 / 1000000000000) (-11537143162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (517988599241311 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27985640503 / 1000000000000) (27985640505 / 1000000000000), orderedInterval (14121300697 / 1000000000000) (14121300699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (369661106059663 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32148592216 / 1000000000000) (-32148592215 / 1000000000000), orderedInterval (-18517967690 / 1000000000000) (-18517967689 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (419156295431577 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2943895336 / 1000000000000) (-2943895335 / 1000000000000), orderedInterval (-34730228710 / 1000000000000) (-34730228709 / 1000000000000)))) (orderedInterval (-2916122561 / 1000000000000) (-2916122501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (349448819890313 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30251423318 / 1000000000000) (-30251423317 / 1000000000000), orderedInterval (-23252218667 / 1000000000000) (-23252218666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (308748630092573 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-12194955527 / 1000000000000) (-12194955526 / 1000000000000), orderedInterval (-38724781924 / 1000000000000) (-38724781923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (89487387056727 / 160000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25956925474 / 1000000000000) (25956925475 / 1000000000000), orderedInterval (21528814875 / 1000000000000) (21528814876 / 1000000000000)))) (orderedInterval (3458769373 / 1000000000000) (3458769415 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_chunkChecks1_2 :
    compactCertificate431.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (247526822062069 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33292966723 / 1000000000000) (33293007487 / 1000000000000), orderedInterval (-30861525181 / 1000000000000) (-30861484418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (209831228346509 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36014991184 / 1000000000000) (-36014942701 / 1000000000000), orderedInterval (33685450403 / 1000000000000) (33685498885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (131302639922927 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62266501541 / 1000000000000) (62266501579 / 1000000000000), orderedInterval (1098038950 / 1000000000000) (1098038989 / 1000000000000)))) (orderedInterval (3413452470 / 1000000000000) (3413461587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (70614996443409 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75222920101 / 1000000000000) (75222920102 / 1000000000000), orderedInterval (38991373105 / 1000000000000) (38991373106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (191733451917227 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51169225983 / 1000000000000) (51169226438 / 1000000000000), orderedInterval (-6269110549 / 1000000000000) (-6269110095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (261795636795979 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42545272819 / 1000000000000) (42545272822 / 1000000000000), orderedInterval (11566521164 / 1000000000000) (11566521168 / 1000000000000)))) (orderedInterval (-1056360765 / 1000000000000) (-1056360723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (110697360077073 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54215208284 / 1000000000000) (54215208285 / 1000000000000), orderedInterval (40565568619 / 1000000000000) (40565568620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (449978622979633 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26630352267 / 1000000000000) (-26630352266 / 1000000000000), orderedInterval (-20534695007 / 1000000000000) (-20534695006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (300564866312447 / 800000000000) 1 (IntervalRat.scale (605 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19733910186 / 1000000000000) (-19733909153 / 1000000000000), orderedInterval (36151541972 / 1000000000000) (36151543005 / 1000000000000)))) (orderedInterval (-5204509311 / 1000000000000) (-5204508952 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_chunkChecks1 :
    compactCertificate431.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate431.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate431_chunkChecks1_0
    compactCertificate431_chunkChecks1_1 compactCertificate431_chunkChecks1_2

theorem compactCertificate431_chunkChecks2_0 :
    compactCertificate431.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (605 / 2) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (45538056671 / 1000000000000) (45538057358 / 1000000000000), orderedInterval (-5626012366 / 1000000000000) (-5626011680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (178256104696021 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28024630322 / 1000000000000) (-28024630321 / 1000000000000), orderedInterval (-45453320262 / 1000000000000) (-45453320261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (57644361755893 / 160000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9208079435 / 1000000000000) (9208079462 / 1000000000000), orderedInterval (-41027900228 / 1000000000000) (-41027900202 / 1000000000000)))) (orderedInterval (-18656586681 / 1000000000000) (-18656586378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (52014686773247 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16897714354 / 1000000000000) (16897714466 / 1000000000000), orderedInterval (-97629295363 / 1000000000000) (-97629295251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (139718765143859 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-28735768196 / 1000000000000) (-28735765061 / 1000000000000), orderedInterval (53180415812 / 1000000000000) (53180418948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (379363626536103 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20965220112 / 1000000000000) (-20965220111 / 1000000000000), orderedInterval (-30027190463 / 1000000000000) (-30027190462 / 1000000000000)))) (orderedInterval (-3319894152 / 1000000000000) (-3319894056 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (279437530287839 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41792219742 / 1000000000000) (-41792219732 / 1000000000000), orderedInterval (-8657029356 / 1000000000000) (-8657029347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (478820971008347 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21816811491 / 1000000000000) (21816815478 / 1000000000000), orderedInterval (-24260180364 / 1000000000000) (-24260176376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (352697360077073 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36692897720 / 1000000000000) (36692905028 / 1000000000000), orderedInterval (-9922535060 / 1000000000000) (-9922527752 / 1000000000000)))) (orderedInterval (746999899 / 1000000000000) (747000810 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_chunkChecks2_1 :
    compactCertificate431.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (541128450554879 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30168744232 / 1000000000000) (-30168733425 / 1000000000000), orderedInterval (5591905502 / 1000000000000) (5591916310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (312420656593991 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39703887294 / 1000000000000) (39703889655 / 1000000000000), orderedInterval (-7382990318 / 1000000000000) (-7382987957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (554395937584819 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14844838099 / 1000000000000) (14844838254 / 1000000000000), orderedInterval (-26435715640 / 1000000000000) (-26435715485 / 1000000000000)))) (orderedInterval (-42743006389 / 1000000000000) (-42742995832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (517988599241311 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27985640503 / 1000000000000) (27985640505 / 1000000000000), orderedInterval (14121300697 / 1000000000000) (14121300699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (369661106059663 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32148592216 / 1000000000000) (-32148592215 / 1000000000000), orderedInterval (-18517967690 / 1000000000000) (-18517967689 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (419156295431577 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2943895336 / 1000000000000) (-2943895335 / 1000000000000), orderedInterval (-34730228710 / 1000000000000) (-34730228709 / 1000000000000)))) (orderedInterval (9373135834 / 1000000000000) (9373135931 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (349448819890313 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30251423318 / 1000000000000) (-30251423317 / 1000000000000), orderedInterval (-23252218667 / 1000000000000) (-23252218666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (308748630092573 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-12194955527 / 1000000000000) (-12194955526 / 1000000000000), orderedInterval (-38724781924 / 1000000000000) (-38724781923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (89487387056727 / 160000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25956925474 / 1000000000000) (25956925475 / 1000000000000), orderedInterval (21528814875 / 1000000000000) (21528814876 / 1000000000000)))) (orderedInterval (-2690890486 / 1000000000000) (-2690890423 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_chunkChecks2_2 :
    compactCertificate431.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (247526822062069 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33292966723 / 1000000000000) (33293007487 / 1000000000000), orderedInterval (-30861525181 / 1000000000000) (-30861484418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (209831228346509 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36014991184 / 1000000000000) (-36014942701 / 1000000000000), orderedInterval (33685450403 / 1000000000000) (33685498885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (131302639922927 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62266501541 / 1000000000000) (62266501579 / 1000000000000), orderedInterval (1098038950 / 1000000000000) (1098038989 / 1000000000000)))) (orderedInterval (3428654841 / 1000000000000) (3428663821 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (70614996443409 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75222920101 / 1000000000000) (75222920102 / 1000000000000), orderedInterval (38991373105 / 1000000000000) (38991373106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (191733451917227 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51169225983 / 1000000000000) (51169226438 / 1000000000000), orderedInterval (-6269110549 / 1000000000000) (-6269110095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (261795636795979 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42545272819 / 1000000000000) (42545272822 / 1000000000000), orderedInterval (11566521164 / 1000000000000) (11566521168 / 1000000000000)))) (orderedInterval (4666336846 / 1000000000000) (4666336886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (110697360077073 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54215208284 / 1000000000000) (54215208285 / 1000000000000), orderedInterval (40565568619 / 1000000000000) (40565568620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (449978622979633 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26630352267 / 1000000000000) (-26630352266 / 1000000000000), orderedInterval (-20534695007 / 1000000000000) (-20534695006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (300564866312447 / 800000000000) 2 (IntervalRat.scale (605 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19733910186 / 1000000000000) (-19733909153 / 1000000000000), orderedInterval (36151541972 / 1000000000000) (36151543005 / 1000000000000)))) (orderedInterval (-13257583662 / 1000000000000) (-13257583188 / 1000000000000))) = true
  rfl'

theorem compactCertificate431_chunkChecks2 :
    compactCertificate431.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate431.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate431_chunkChecks2_0
    compactCertificate431_chunkChecks2_1 compactCertificate431_chunkChecks2_2

theorem compactCertificate431_chunkChecks3_0 :
    compactCertificate431.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (605 / 2) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (45538056671 / 1000000000000) (45538057358 / 1000000000000), orderedInterval (-5626012366 / 1000000000000) (-5626011680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (178256104696021 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28024630322 / 1000000000000) (-28024630321 / 1000000000000), orderedInterval (-45453320262 / 1000000000000) (-45453320261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (57644361755893 / 160000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9208079435 / 1000000000000) (9208079462 / 1000000000000), orderedInterval (-41027900228 / 1000000000000) (-41027900202 / 1000000000000)))) (orderedInterval (6528195561 / 1000000000000) (6528195868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (52014686773247 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16897714354 / 1000000000000) (16897714466 / 1000000000000), orderedInterval (-97629295363 / 1000000000000) (-97629295251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (139718765143859 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-28735768196 / 1000000000000) (-28735765061 / 1000000000000), orderedInterval (53180415812 / 1000000000000) (53180418948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (379363626536103 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20965220112 / 1000000000000) (-20965220111 / 1000000000000), orderedInterval (-30027190463 / 1000000000000) (-30027190462 / 1000000000000)))) (orderedInterval (-8596395119 / 1000000000000) (-8596395011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (279437530287839 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41792219742 / 1000000000000) (-41792219732 / 1000000000000), orderedInterval (-8657029356 / 1000000000000) (-8657029347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (478820971008347 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21816811491 / 1000000000000) (21816815478 / 1000000000000), orderedInterval (-24260180364 / 1000000000000) (-24260176376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (352697360077073 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36692897720 / 1000000000000) (36692905028 / 1000000000000), orderedInterval (-9922535060 / 1000000000000) (-9922527752 / 1000000000000)))) (orderedInterval (-5056210996 / 1000000000000) (-5056209398 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate431_chunkChecks3_1 :
    compactCertificate431.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (541128450554879 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30168744232 / 1000000000000) (-30168733425 / 1000000000000), orderedInterval (5591905502 / 1000000000000) (5591916310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (312420656593991 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39703887294 / 1000000000000) (39703889655 / 1000000000000), orderedInterval (-7382990318 / 1000000000000) (-7382987957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (554395937584819 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14844838099 / 1000000000000) (14844838254 / 1000000000000), orderedInterval (-26435715640 / 1000000000000) (-26435715485 / 1000000000000)))) (orderedInterval (57609580917 / 1000000000000) (57609604229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (517988599241311 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27985640503 / 1000000000000) (27985640505 / 1000000000000), orderedInterval (14121300697 / 1000000000000) (14121300699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (369661106059663 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32148592216 / 1000000000000) (-32148592215 / 1000000000000), orderedInterval (-18517967690 / 1000000000000) (-18517967689 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (419156295431577 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2943895336 / 1000000000000) (-2943895335 / 1000000000000), orderedInterval (-34730228710 / 1000000000000) (-34730228709 / 1000000000000)))) (orderedInterval (7797095102 / 1000000000000) (7797095267 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (349448819890313 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30251423318 / 1000000000000) (-30251423317 / 1000000000000), orderedInterval (-23252218667 / 1000000000000) (-23252218666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (308748630092573 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-12194955527 / 1000000000000) (-12194955526 / 1000000000000), orderedInterval (-38724781924 / 1000000000000) (-38724781923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (89487387056727 / 160000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25956925474 / 1000000000000) (25956925475 / 1000000000000), orderedInterval (21528814875 / 1000000000000) (21528814876 / 1000000000000)))) (orderedInterval (-7268689474 / 1000000000000) (-7268689377 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate431_chunkChecks3_2 :
    compactCertificate431.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (247526822062069 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33292966723 / 1000000000000) (33293007487 / 1000000000000), orderedInterval (-30861525181 / 1000000000000) (-30861484418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (209831228346509 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36014991184 / 1000000000000) (-36014942701 / 1000000000000), orderedInterval (33685450403 / 1000000000000) (33685498885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (131302639922927 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62266501541 / 1000000000000) (62266501579 / 1000000000000), orderedInterval (1098038950 / 1000000000000) (1098038989 / 1000000000000)))) (orderedInterval (-4054535645 / 1000000000000) (-4054526787 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (70614996443409 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75222920101 / 1000000000000) (75222920102 / 1000000000000), orderedInterval (38991373105 / 1000000000000) (38991373106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (191733451917227 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51169225983 / 1000000000000) (51169226438 / 1000000000000), orderedInterval (-6269110549 / 1000000000000) (-6269110095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (261795636795979 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42545272819 / 1000000000000) (42545272822 / 1000000000000), orderedInterval (11566521164 / 1000000000000) (11566521168 / 1000000000000)))) (orderedInterval (1053975380 / 1000000000000) (1053975420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (110697360077073 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54215208284 / 1000000000000) (54215208285 / 1000000000000), orderedInterval (40565568619 / 1000000000000) (40565568620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (449978622979633 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26630352267 / 1000000000000) (-26630352266 / 1000000000000), orderedInterval (-20534695007 / 1000000000000) (-20534695006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (300564866312447 / 800000000000) 3 (IntervalRat.scale (605 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19733910186 / 1000000000000) (-19733909153 / 1000000000000), orderedInterval (36151541972 / 1000000000000) (36151543005 / 1000000000000)))) (orderedInterval (2269642663 / 1000000000000) (2269643304 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate431_chunkChecks3 :
    compactCertificate431.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate431.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate431_chunkChecks3_0
    compactCertificate431_chunkChecks3_1 compactCertificate431_chunkChecks3_2

theorem compactCertificate431_chunkChecks4_0 :
    compactCertificate431.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (605 / 2) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (45538056671 / 1000000000000) (45538057358 / 1000000000000), orderedInterval (-5626012366 / 1000000000000) (-5626011680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (178256104696021 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28024630322 / 1000000000000) (-28024630321 / 1000000000000), orderedInterval (-45453320262 / 1000000000000) (-45453320261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (57644361755893 / 160000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9208079435 / 1000000000000) (9208079462 / 1000000000000), orderedInterval (-41027900228 / 1000000000000) (-41027900202 / 1000000000000)))) (orderedInterval (19016661946 / 1000000000000) (19016662261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (52014686773247 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16897714354 / 1000000000000) (16897714466 / 1000000000000), orderedInterval (-97629295363 / 1000000000000) (-97629295251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (139718765143859 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-28735768196 / 1000000000000) (-28735765061 / 1000000000000), orderedInterval (53180415812 / 1000000000000) (53180418948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (379363626536103 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-20965220112 / 1000000000000) (-20965220111 / 1000000000000), orderedInterval (-30027190463 / 1000000000000) (-30027190462 / 1000000000000)))) (orderedInterval (8940339180 / 1000000000000) (8940339325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (279437530287839 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-41792219742 / 1000000000000) (-41792219732 / 1000000000000), orderedInterval (-8657029356 / 1000000000000) (-8657029347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (478820971008347 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21816811491 / 1000000000000) (21816815478 / 1000000000000), orderedInterval (-24260180364 / 1000000000000) (-24260176376 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (352697360077073 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36692897720 / 1000000000000) (36692905028 / 1000000000000), orderedInterval (-9922535060 / 1000000000000) (-9922527752 / 1000000000000)))) (orderedInterval (-6278739407 / 1000000000000) (-6278736538 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate431_chunkChecks4_1 :
    compactCertificate431.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (541128450554879 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-30168744232 / 1000000000000) (-30168733425 / 1000000000000), orderedInterval (5591905502 / 1000000000000) (5591916310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (312420656593991 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39703887294 / 1000000000000) (39703889655 / 1000000000000), orderedInterval (-7382990318 / 1000000000000) (-7382987957 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (554395937584819 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (14844838099 / 1000000000000) (14844838254 / 1000000000000), orderedInterval (-26435715640 / 1000000000000) (-26435715485 / 1000000000000)))) (orderedInterval (199930082130 / 1000000000000) (199930133967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (517988599241311 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27985640503 / 1000000000000) (27985640505 / 1000000000000), orderedInterval (14121300697 / 1000000000000) (14121300699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (369661106059663 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32148592216 / 1000000000000) (-32148592215 / 1000000000000), orderedInterval (-18517967690 / 1000000000000) (-18517967689 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (419156295431577 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2943895336 / 1000000000000) (-2943895335 / 1000000000000), orderedInterval (-34730228710 / 1000000000000) (-34730228709 / 1000000000000)))) (orderedInterval (-27073709541 / 1000000000000) (-27073709255 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (349448819890313 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30251423318 / 1000000000000) (-30251423317 / 1000000000000), orderedInterval (-23252218667 / 1000000000000) (-23252218666 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (308748630092573 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-12194955527 / 1000000000000) (-12194955526 / 1000000000000), orderedInterval (-38724781924 / 1000000000000) (-38724781923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (89487387056727 / 160000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25956925474 / 1000000000000) (25956925475 / 1000000000000), orderedInterval (21528814875 / 1000000000000) (21528814876 / 1000000000000)))) (orderedInterval (8144699781 / 1000000000000) (8144699935 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate431_chunkChecks4_2 :
    compactCertificate431.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (247526822062069 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33292966723 / 1000000000000) (33293007487 / 1000000000000), orderedInterval (-30861525181 / 1000000000000) (-30861484418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (209831228346509 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36014991184 / 1000000000000) (-36014942701 / 1000000000000), orderedInterval (33685450403 / 1000000000000) (33685498885 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (131302639922927 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (62266501541 / 1000000000000) (62266501579 / 1000000000000), orderedInterval (1098038950 / 1000000000000) (1098038989 / 1000000000000)))) (orderedInterval (-4471819130 / 1000000000000) (-4471810323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (70614996443409 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75222920101 / 1000000000000) (75222920102 / 1000000000000), orderedInterval (38991373105 / 1000000000000) (38991373106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (191733451917227 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51169225983 / 1000000000000) (51169226438 / 1000000000000), orderedInterval (-6269110549 / 1000000000000) (-6269110095 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (261795636795979 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42545272819 / 1000000000000) (42545272822 / 1000000000000), orderedInterval (11566521164 / 1000000000000) (11566521168 / 1000000000000)))) (orderedInterval (-4940095394 / 1000000000000) (-4940095354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (110697360077073 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54215208284 / 1000000000000) (54215208285 / 1000000000000), orderedInterval (40565568619 / 1000000000000) (40565568620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (449978622979633 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26630352267 / 1000000000000) (-26630352266 / 1000000000000), orderedInterval (-20534695007 / 1000000000000) (-20534695006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (300564866312447 / 800000000000) 4 (IntervalRat.scale (605 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19733910186 / 1000000000000) (-19733909153 / 1000000000000), orderedInterval (36151541972 / 1000000000000) (36151543005 / 1000000000000)))) (orderedInterval (34722571852 / 1000000000000) (34722572747 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate431_chunkChecks4 :
    compactCertificate431.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate431.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate431_chunkChecks4_0
    compactCertificate431_chunkChecks4_1 compactCertificate431_chunkChecks4_2

theorem compactCertificate431_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate431.chunkCheck r b = true :=
  compactCertificate431.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate431_chunkChecks0
    · exact compactCertificate431_chunkChecks1
    · exact compactCertificate431_chunkChecks2
    · exact compactCertificate431_chunkChecks3
    · exact compactCertificate431_chunkChecks4)

theorem compactCertificate431_coefficient0 :
    compactCertificate431.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate431_coefficient1 :
    compactCertificate431.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate431_coefficient2 :
    compactCertificate431.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate431_coefficient3 :
    compactCertificate431.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate431_coefficient4 :
    compactCertificate431.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate431_coefficients : ∀ r : Fin 5,
    compactCertificate431.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate431_coefficient0
  · exact compactCertificate431_coefficient1
  · exact compactCertificate431_coefficient2
  · exact compactCertificate431_coefficient3
  · exact compactCertificate431_coefficient4

theorem compactCertificate431_lower : (1 : ℚ) ≤ compactCertificate431.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate431, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate431_proves {t : ℝ} (ht : t ∈ compactCertificate431.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate431.proves compactCertificate431_states compactCertificate431_chunks
    compactCertificate431_coefficients compactCertificate431_lower ht

end Erdos232
