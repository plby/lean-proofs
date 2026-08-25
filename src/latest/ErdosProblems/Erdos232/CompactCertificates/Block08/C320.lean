/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate320 : CompactCertificate where
  left := 192
  right := 193
  center := 385 / 2
  grid := fun i =>
    match i.val with
    | 0 => 61
    | 1 => 45
    | 2 => 73
    | 3 => 13
    | 4 => 35
    | 5 => 96
    | 6 => 71
    | 7 => 121
    | 8 => 89
    | 9 => 137
    | 10 => 79
    | 11 => 140
    | 12 => 131
    | 13 => 94
    | 14 => 106
    | 15 => 89
    | 16 => 78
    | 17 => 113
    | 18 => 63
    | 19 => 53
    | 20 => 33
    | 21 => 18
    | 22 => 49
    | 23 => 66
    | 24 => 28
    | 25 => 114
    | _ => 76
  point := fun i =>
    match i.val with
    | 0 => 385 / 2
    | 1 => 113435702988377 / 800000000000
    | 2 => 36682775662841 / 160000000000
    | 3 => 33100255219339 / 800000000000
    | 4 => 88911941455183 / 800000000000
    | 5 => 241413216886611 / 800000000000
    | 6 => 177823882910443 / 800000000000
    | 7 => 304704254278039 / 800000000000
    | 8 => 224443774594501 / 800000000000
    | 9 => 344354468534923 / 800000000000
    | 10 => 198813145105267 / 800000000000
    | 11 => 352797414826703 / 800000000000
    | 12 => 329629108608107 / 800000000000
    | 13 => 235238885674331 / 800000000000
    | 14 => 266735824365549 / 800000000000
    | 15 => 222376521748381 / 800000000000
    | 16 => 196476400968001 / 800000000000
    | 17 => 56946519036099 / 160000000000
    | 18 => 157517068584953 / 800000000000
    | 19 => 133528963493233 / 800000000000
    | 20 => 83556225405499 / 800000000000
    | 21 => 44936815918533 / 800000000000
    | 22 => 122012196674599 / 800000000000
    | 23 => 166597223415623 / 800000000000
    | 24 => 70443774594501 / 800000000000
    | 25 => 286350032805221 / 800000000000
    | _ => 191268551289739 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-57337914709 / 1000000000000) (-57337914519 / 1000000000000), orderedInterval (4561209593 / 1000000000000) (4561209783 / 1000000000000))
    | 1 => (orderedInterval (-62631278793 / 1000000000000) (-62631278792 / 1000000000000), orderedInterval (-23591611313 / 1000000000000) (-23591611312 / 1000000000000))
    | 2 => (orderedInterval (-34584955806 / 1000000000000) (-34584955805 / 1000000000000), orderedInterval (-39681826380 / 1000000000000) (-39681826379 / 1000000000000))
    | 3 => (orderedInterval (-120064024356 / 1000000000000) (-120064024355 / 1000000000000), orderedInterval (-29695905531 / 1000000000000) (-29695905530 / 1000000000000))
    | 4 => (orderedInterval (-69778121861 / 1000000000000) (-69778116601 / 1000000000000), orderedInterval (29623737063 / 1000000000000) (29623742323 / 1000000000000))
    | 5 => (orderedInterval (37589499533 / 1000000000000) (37589499534 / 1000000000000), orderedInterval (26332262962 / 1000000000000) (26332262963 / 1000000000000))
    | 6 => (orderedInterval (-621371224 / 1000000000000) (-621371221 / 1000000000000), orderedInterval (-53511846921 / 1000000000000) (-53511846919 / 1000000000000))
    | 7 => (orderedInterval (-40853568354 / 1000000000000) (-40853568208 / 1000000000000), orderedInterval (-1504446925 / 1000000000000) (-1504446780 / 1000000000000))
    | 8 => (orderedInterval (-46971794437 / 1000000000000) (-46971793394 / 1000000000000), orderedInterval (8007960759 / 1000000000000) (8007961802 / 1000000000000))
    | 9 => (orderedInterval (-28379058150 / 1000000000000) (-28379058149 / 1000000000000), orderedInterval (-25921149866 / 1000000000000) (-25921149865 / 1000000000000))
    | 10 => (orderedInterval (-45457245318 / 1000000000000) (-45457245317 / 1000000000000), orderedInterval (-22164249719 / 1000000000000) (-22164249718 / 1000000000000))
    | 11 => (orderedInterval (35168725244 / 1000000000000) (35168749984 / 1000000000000), orderedInterval (-14418760784 / 1000000000000) (-14418736045 / 1000000000000))
    | 12 => (orderedInterval (-37575298054 / 1000000000000) (-37575298051 / 1000000000000), orderedInterval (-11493605984 / 1000000000000) (-11493605980 / 1000000000000))
    | 13 => (orderedInterval (-21326532303 / 1000000000000) (-21326531034 / 1000000000000), orderedInterval (41390782489 / 1000000000000) (41390783757 / 1000000000000))
    | 14 => (orderedInterval (40662668757 / 1000000000000) (40662668759 / 1000000000000), orderedInterval (15936207264 / 1000000000000) (15936207266 / 1000000000000))
    | 15 => (orderedInterval (35831554646 / 1000000000000) (35831611624 / 1000000000000), orderedInterval (-31787311744 / 1000000000000) (-31787254766 / 1000000000000))
    | 16 => (orderedInterval (49518053304 / 1000000000000) (49518053307 / 1000000000000), orderedInterval (11735789819 / 1000000000000) (11735789822 / 1000000000000))
    | 17 => (orderedInterval (-41935775197 / 1000000000000) (-41935774142 / 1000000000000), orderedInterval (5542543676 / 1000000000000) (5542544732 / 1000000000000))
    | 18 => (orderedInterval (13474113485 / 1000000000000) (13474113601 / 1000000000000), orderedInterval (-55276693979 / 1000000000000) (-55276693863 / 1000000000000))
    | 19 => (orderedInterval (-57367684124 / 1000000000000) (-57367684123 / 1000000000000), orderedInterval (-22698630589 / 1000000000000) (-22698630588 / 1000000000000))
    | 20 => (orderedInterval (-78064104304 / 1000000000000) (-78064104277 / 1000000000000), orderedInterval (-709187371 / 1000000000000) (-709187343 / 1000000000000))
    | 21 => (orderedInterval (41997553893 / 1000000000000) (41997553894 / 1000000000000), orderedInterval (97453146474 / 1000000000000) (97453146475 / 1000000000000))
    | 22 => (orderedInterval (38490705109 / 1000000000000) (38490720215 / 1000000000000), orderedInterval (-52016558515 / 1000000000000) (-52016543409 / 1000000000000))
    | 23 => (orderedInterval (54922655939 / 1000000000000) (54922656290 / 1000000000000), orderedInterval (-6499122669 / 1000000000000) (-6499122318 / 1000000000000))
    | 24 => (orderedInterval (65213495523 / 1000000000000) (65213495524 / 1000000000000), orderedInterval (54191598237 / 1000000000000) (54191598238 / 1000000000000))
    | 25 => (orderedInterval (23148137504 / 1000000000000) (23148137505 / 1000000000000), orderedInterval (35220214067 / 1000000000000) (35220214068 / 1000000000000))
    | _ => (orderedInterval (46208490582 / 1000000000000) (46208490583 / 1000000000000), orderedInterval (22870694997 / 1000000000000) (22870694998 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-25339828817 / 1000000000000) (-25339828727 / 1000000000000)
      | 1 => orderedInterval (-3917335562 / 1000000000000) (-3917335346 / 1000000000000)
      | 2 => orderedInterval (124871897 / 1000000000000) (124871938 / 1000000000000)
      | 3 => orderedInterval (6674049643 / 1000000000000) (6674053237 / 1000000000000)
      | 4 => orderedInterval (-1544124467 / 1000000000000) (-1544124323 / 1000000000000)
      | 5 => orderedInterval (-3493704175 / 1000000000000) (-3493703470 / 1000000000000)
      | 6 => orderedInterval (-1448798626 / 1000000000000) (-1448798557 / 1000000000000)
      | 7 => orderedInterval (-5857933731 / 1000000000000) (-5857933338 / 1000000000000)
      | _ => orderedInterval (-10161109819 / 1000000000000) (-10161109765 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-1127351304 / 1000000000000) (-1127351213 / 1000000000000)
      | 1 => orderedInterval (-2240786277 / 1000000000000) (-2240786139 / 1000000000000)
      | 2 => orderedInterval (373878739 / 1000000000000) (373878804 / 1000000000000)
      | 3 => orderedInterval (3483325073 / 1000000000000) (3483333289 / 1000000000000)
      | 4 => orderedInterval (6283230015 / 1000000000000) (6283230236 / 1000000000000)
      | 5 => orderedInterval (-1124509907 / 1000000000000) (-1124508879 / 1000000000000)
      | 6 => orderedInterval (10141611705 / 1000000000000) (10141611770 / 1000000000000)
      | 7 => orderedInterval (948715622 / 1000000000000) (948715944 / 1000000000000)
      | _ => orderedInterval (-10511110896 / 1000000000000) (-10511110820 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (25928026653 / 1000000000000) (25928026747 / 1000000000000)
      | 1 => orderedInterval (7367498793 / 1000000000000) (7367498895 / 1000000000000)
      | 2 => orderedInterval (-2523696791 / 1000000000000) (-2523696686 / 1000000000000)
      | 3 => orderedInterval (-45855854108 / 1000000000000) (-45855835268 / 1000000000000)
      | 4 => orderedInterval (2182442724 / 1000000000000) (2182443067 / 1000000000000)
      | 5 => orderedInterval (7426115554 / 1000000000000) (7426117064 / 1000000000000)
      | 6 => orderedInterval (508263132 / 1000000000000) (508263195 / 1000000000000)
      | 7 => orderedInterval (5535249451 / 1000000000000) (5535249721 / 1000000000000)
      | _ => orderedInterval (19861185652 / 1000000000000) (19861185764 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (2079142163 / 1000000000000) (2079142260 / 1000000000000)
      | 1 => orderedInterval (6961642535 / 1000000000000) (6961642627 / 1000000000000)
      | 2 => orderedInterval (-945448990 / 1000000000000) (-945448816 / 1000000000000)
      | 3 => orderedInterval (-23079809896 / 1000000000000) (-23079766773 / 1000000000000)
      | 4 => orderedInterval (-15577409179 / 1000000000000) (-15577408644 / 1000000000000)
      | 5 => orderedInterval (1564373269 / 1000000000000) (1564375490 / 1000000000000)
      | 6 => orderedInterval (-10293982135 / 1000000000000) (-10293982073 / 1000000000000)
      | 7 => orderedInterval (-1201506424 / 1000000000000) (-1201506197 / 1000000000000)
      | _ => orderedInterval (26517881877 / 1000000000000) (26517882049 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-27002939225 / 1000000000000) (-27002939125 / 1000000000000)
      | 1 => orderedInterval (-16489851623 / 1000000000000) (-16489851516 / 1000000000000)
      | 2 => orderedInterval (14200124267 / 1000000000000) (14200124564 / 1000000000000)
      | 3 => orderedInterval (254650353286 / 1000000000000) (254650452247 / 1000000000000)
      | 4 => orderedInterval (1568906712 / 1000000000000) (1568907553 / 1000000000000)
      | 5 => orderedInterval (-18272494334 / 1000000000000) (-18272491037 / 1000000000000)
      | 6 => orderedInterval (-636066130 / 1000000000000) (-636066068 / 1000000000000)
      | 7 => orderedInterval (-6101930822 / 1000000000000) (-6101930625 / 1000000000000)
      | _ => orderedInterval (-43412694157 / 1000000000000) (-43412693881 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-44963913657 / 1000000000000) (-44963908351 / 1000000000000)
    | 1 => orderedInterval (6227002770 / 1000000000000) (6227012992 / 1000000000000)
    | 2 => orderedInterval (20429231060 / 1000000000000) (20429252499 / 1000000000000)
    | 3 => orderedInterval (-13975116780 / 1000000000000) (-13975070077 / 1000000000000)
    | _ => orderedInterval (158503407974 / 1000000000000) (158503512112 / 1000000000000)

theorem compactCertificate320_stateChecks0 :
    compactCertificate320.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (385 / 2)) (orderedInterval (-57337914709 / 1000000000000) (-57337914519 / 1000000000000), orderedInterval (4561209593 / 1000000000000) (4561209783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (113435702988377 / 800000000000)) (orderedInterval (-62631278793 / 1000000000000) (-62631278792 / 1000000000000), orderedInterval (-23591611313 / 1000000000000) (-23591611312 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (36682775662841 / 160000000000)) (orderedInterval (-34584955806 / 1000000000000) (-34584955805 / 1000000000000), orderedInterval (-39681826380 / 1000000000000) (-39681826379 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_stateChecks1 :
    compactCertificate320.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (33100255219339 / 800000000000)) (orderedInterval (-120064024356 / 1000000000000) (-120064024355 / 1000000000000), orderedInterval (-29695905531 / 1000000000000) (-29695905530 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (88911941455183 / 800000000000)) (orderedInterval (-69778121861 / 1000000000000) (-69778116601 / 1000000000000), orderedInterval (29623737063 / 1000000000000) (29623742323 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (241413216886611 / 800000000000)) (orderedInterval (37589499533 / 1000000000000) (37589499534 / 1000000000000), orderedInterval (26332262962 / 1000000000000) (26332262963 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_stateChecks2 :
    compactCertificate320.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (177823882910443 / 800000000000)) (orderedInterval (-621371224 / 1000000000000) (-621371221 / 1000000000000), orderedInterval (-53511846921 / 1000000000000) (-53511846919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (304704254278039 / 800000000000)) (orderedInterval (-40853568354 / 1000000000000) (-40853568208 / 1000000000000), orderedInterval (-1504446925 / 1000000000000) (-1504446780 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (224443774594501 / 800000000000)) (orderedInterval (-46971794437 / 1000000000000) (-46971793394 / 1000000000000), orderedInterval (8007960759 / 1000000000000) (8007961802 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_stateChecks3 :
    compactCertificate320.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (344354468534923 / 800000000000)) (orderedInterval (-28379058150 / 1000000000000) (-28379058149 / 1000000000000), orderedInterval (-25921149866 / 1000000000000) (-25921149865 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (198813145105267 / 800000000000)) (orderedInterval (-45457245318 / 1000000000000) (-45457245317 / 1000000000000), orderedInterval (-22164249719 / 1000000000000) (-22164249718 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (352797414826703 / 800000000000)) (orderedInterval (35168725244 / 1000000000000) (35168749984 / 1000000000000), orderedInterval (-14418760784 / 1000000000000) (-14418736045 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_stateChecks4 :
    compactCertificate320.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (329629108608107 / 800000000000)) (orderedInterval (-37575298054 / 1000000000000) (-37575298051 / 1000000000000), orderedInterval (-11493605984 / 1000000000000) (-11493605980 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (235238885674331 / 800000000000)) (orderedInterval (-21326532303 / 1000000000000) (-21326531034 / 1000000000000), orderedInterval (41390782489 / 1000000000000) (41390783757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (266735824365549 / 800000000000)) (orderedInterval (40662668757 / 1000000000000) (40662668759 / 1000000000000), orderedInterval (15936207264 / 1000000000000) (15936207266 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_stateChecks5 :
    compactCertificate320.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (222376521748381 / 800000000000)) (orderedInterval (35831554646 / 1000000000000) (35831611624 / 1000000000000), orderedInterval (-31787311744 / 1000000000000) (-31787254766 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (196476400968001 / 800000000000)) (orderedInterval (49518053304 / 1000000000000) (49518053307 / 1000000000000), orderedInterval (11735789819 / 1000000000000) (11735789822 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (56946519036099 / 160000000000)) (orderedInterval (-41935775197 / 1000000000000) (-41935774142 / 1000000000000), orderedInterval (5542543676 / 1000000000000) (5542544732 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_stateChecks6 :
    compactCertificate320.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (157517068584953 / 800000000000)) (orderedInterval (13474113485 / 1000000000000) (13474113601 / 1000000000000), orderedInterval (-55276693979 / 1000000000000) (-55276693863 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (133528963493233 / 800000000000)) (orderedInterval (-57367684124 / 1000000000000) (-57367684123 / 1000000000000), orderedInterval (-22698630589 / 1000000000000) (-22698630588 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (83556225405499 / 800000000000)) (orderedInterval (-78064104304 / 1000000000000) (-78064104277 / 1000000000000), orderedInterval (-709187371 / 1000000000000) (-709187343 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_stateChecks7 :
    compactCertificate320.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (44936815918533 / 800000000000)) (orderedInterval (41997553893 / 1000000000000) (41997553894 / 1000000000000), orderedInterval (97453146474 / 1000000000000) (97453146475 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (122012196674599 / 800000000000)) (orderedInterval (38490705109 / 1000000000000) (38490720215 / 1000000000000), orderedInterval (-52016558515 / 1000000000000) (-52016543409 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (166597223415623 / 800000000000)) (orderedInterval (54922655939 / 1000000000000) (54922656290 / 1000000000000), orderedInterval (-6499122669 / 1000000000000) (-6499122318 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_stateChecks8 :
    compactCertificate320.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (70443774594501 / 800000000000)) (orderedInterval (65213495523 / 1000000000000) (65213495524 / 1000000000000), orderedInterval (54191598237 / 1000000000000) (54191598238 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (286350032805221 / 800000000000)) (orderedInterval (23148137504 / 1000000000000) (23148137505 / 1000000000000), orderedInterval (35220214067 / 1000000000000) (35220214068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (191268551289739 / 800000000000)) (orderedInterval (46208490582 / 1000000000000) (46208490583 / 1000000000000), orderedInterval (22870694997 / 1000000000000) (22870694998 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_states : ∀ j,
    BesselStateValid (compactCertificate320.point j) (compactCertificate320.state j) :=
  compactCertificate320.statesValid_of_checks3 compactCertificate320_stateChecks0
    compactCertificate320_stateChecks1 compactCertificate320_stateChecks2
    compactCertificate320_stateChecks3 compactCertificate320_stateChecks4
    compactCertificate320_stateChecks5 compactCertificate320_stateChecks6
    compactCertificate320_stateChecks7 compactCertificate320_stateChecks8

theorem compactCertificate320_chunkChecks0_0 :
    compactCertificate320.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (385 / 2) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-57337914709 / 1000000000000) (-57337914519 / 1000000000000), orderedInterval (4561209593 / 1000000000000) (4561209783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (113435702988377 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62631278793 / 1000000000000) (-62631278792 / 1000000000000), orderedInterval (-23591611313 / 1000000000000) (-23591611312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (36682775662841 / 160000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34584955806 / 1000000000000) (-34584955805 / 1000000000000), orderedInterval (-39681826380 / 1000000000000) (-39681826379 / 1000000000000)))) (orderedInterval (-25339828817 / 1000000000000) (-25339828727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (33100255219339 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-120064024356 / 1000000000000) (-120064024355 / 1000000000000), orderedInterval (-29695905531 / 1000000000000) (-29695905530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (88911941455183 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-69778121861 / 1000000000000) (-69778116601 / 1000000000000), orderedInterval (29623737063 / 1000000000000) (29623742323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (241413216886611 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (37589499533 / 1000000000000) (37589499534 / 1000000000000), orderedInterval (26332262962 / 1000000000000) (26332262963 / 1000000000000)))) (orderedInterval (-3917335562 / 1000000000000) (-3917335346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (177823882910443 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-621371224 / 1000000000000) (-621371221 / 1000000000000), orderedInterval (-53511846921 / 1000000000000) (-53511846919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (304704254278039 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-40853568354 / 1000000000000) (-40853568208 / 1000000000000), orderedInterval (-1504446925 / 1000000000000) (-1504446780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (224443774594501 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-46971794437 / 1000000000000) (-46971793394 / 1000000000000), orderedInterval (8007960759 / 1000000000000) (8007961802 / 1000000000000)))) (orderedInterval (124871897 / 1000000000000) (124871938 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_chunkChecks0_1 :
    compactCertificate320.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (344354468534923 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28379058150 / 1000000000000) (-28379058149 / 1000000000000), orderedInterval (-25921149866 / 1000000000000) (-25921149865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (198813145105267 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45457245318 / 1000000000000) (-45457245317 / 1000000000000), orderedInterval (-22164249719 / 1000000000000) (-22164249718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (352797414826703 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35168725244 / 1000000000000) (35168749984 / 1000000000000), orderedInterval (-14418760784 / 1000000000000) (-14418736045 / 1000000000000)))) (orderedInterval (6674049643 / 1000000000000) (6674053237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (329629108608107 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-37575298054 / 1000000000000) (-37575298051 / 1000000000000), orderedInterval (-11493605984 / 1000000000000) (-11493605980 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (235238885674331 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-21326532303 / 1000000000000) (-21326531034 / 1000000000000), orderedInterval (41390782489 / 1000000000000) (41390783757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (266735824365549 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (40662668757 / 1000000000000) (40662668759 / 1000000000000), orderedInterval (15936207264 / 1000000000000) (15936207266 / 1000000000000)))) (orderedInterval (-1544124467 / 1000000000000) (-1544124323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (222376521748381 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35831554646 / 1000000000000) (35831611624 / 1000000000000), orderedInterval (-31787311744 / 1000000000000) (-31787254766 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (196476400968001 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49518053304 / 1000000000000) (49518053307 / 1000000000000), orderedInterval (11735789819 / 1000000000000) (11735789822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (56946519036099 / 160000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-41935775197 / 1000000000000) (-41935774142 / 1000000000000), orderedInterval (5542543676 / 1000000000000) (5542544732 / 1000000000000)))) (orderedInterval (-3493704175 / 1000000000000) (-3493703470 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_chunkChecks0_2 :
    compactCertificate320.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (157517068584953 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13474113485 / 1000000000000) (13474113601 / 1000000000000), orderedInterval (-55276693979 / 1000000000000) (-55276693863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (133528963493233 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57367684124 / 1000000000000) (-57367684123 / 1000000000000), orderedInterval (-22698630589 / 1000000000000) (-22698630588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (83556225405499 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-78064104304 / 1000000000000) (-78064104277 / 1000000000000), orderedInterval (-709187371 / 1000000000000) (-709187343 / 1000000000000)))) (orderedInterval (-1448798626 / 1000000000000) (-1448798557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (44936815918533 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41997553893 / 1000000000000) (41997553894 / 1000000000000), orderedInterval (97453146474 / 1000000000000) (97453146475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (122012196674599 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (38490705109 / 1000000000000) (38490720215 / 1000000000000), orderedInterval (-52016558515 / 1000000000000) (-52016543409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (166597223415623 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54922655939 / 1000000000000) (54922656290 / 1000000000000), orderedInterval (-6499122669 / 1000000000000) (-6499122318 / 1000000000000)))) (orderedInterval (-5857933731 / 1000000000000) (-5857933338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (70443774594501 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65213495523 / 1000000000000) (65213495524 / 1000000000000), orderedInterval (54191598237 / 1000000000000) (54191598238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (286350032805221 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23148137504 / 1000000000000) (23148137505 / 1000000000000), orderedInterval (35220214067 / 1000000000000) (35220214068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (191268551289739 / 800000000000) 0 (IntervalRat.scale (385 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46208490582 / 1000000000000) (46208490583 / 1000000000000), orderedInterval (22870694997 / 1000000000000) (22870694998 / 1000000000000)))) (orderedInterval (-10161109819 / 1000000000000) (-10161109765 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_chunkChecks0 :
    compactCertificate320.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate320.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate320_chunkChecks0_0
    compactCertificate320_chunkChecks0_1 compactCertificate320_chunkChecks0_2

theorem compactCertificate320_chunkChecks1_0 :
    compactCertificate320.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (385 / 2) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-57337914709 / 1000000000000) (-57337914519 / 1000000000000), orderedInterval (4561209593 / 1000000000000) (4561209783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (113435702988377 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62631278793 / 1000000000000) (-62631278792 / 1000000000000), orderedInterval (-23591611313 / 1000000000000) (-23591611312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (36682775662841 / 160000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34584955806 / 1000000000000) (-34584955805 / 1000000000000), orderedInterval (-39681826380 / 1000000000000) (-39681826379 / 1000000000000)))) (orderedInterval (-1127351304 / 1000000000000) (-1127351213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (33100255219339 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-120064024356 / 1000000000000) (-120064024355 / 1000000000000), orderedInterval (-29695905531 / 1000000000000) (-29695905530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (88911941455183 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-69778121861 / 1000000000000) (-69778116601 / 1000000000000), orderedInterval (29623737063 / 1000000000000) (29623742323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (241413216886611 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (37589499533 / 1000000000000) (37589499534 / 1000000000000), orderedInterval (26332262962 / 1000000000000) (26332262963 / 1000000000000)))) (orderedInterval (-2240786277 / 1000000000000) (-2240786139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (177823882910443 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-621371224 / 1000000000000) (-621371221 / 1000000000000), orderedInterval (-53511846921 / 1000000000000) (-53511846919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (304704254278039 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-40853568354 / 1000000000000) (-40853568208 / 1000000000000), orderedInterval (-1504446925 / 1000000000000) (-1504446780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (224443774594501 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-46971794437 / 1000000000000) (-46971793394 / 1000000000000), orderedInterval (8007960759 / 1000000000000) (8007961802 / 1000000000000)))) (orderedInterval (373878739 / 1000000000000) (373878804 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_chunkChecks1_1 :
    compactCertificate320.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (344354468534923 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28379058150 / 1000000000000) (-28379058149 / 1000000000000), orderedInterval (-25921149866 / 1000000000000) (-25921149865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (198813145105267 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45457245318 / 1000000000000) (-45457245317 / 1000000000000), orderedInterval (-22164249719 / 1000000000000) (-22164249718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (352797414826703 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35168725244 / 1000000000000) (35168749984 / 1000000000000), orderedInterval (-14418760784 / 1000000000000) (-14418736045 / 1000000000000)))) (orderedInterval (3483325073 / 1000000000000) (3483333289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (329629108608107 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-37575298054 / 1000000000000) (-37575298051 / 1000000000000), orderedInterval (-11493605984 / 1000000000000) (-11493605980 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (235238885674331 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-21326532303 / 1000000000000) (-21326531034 / 1000000000000), orderedInterval (41390782489 / 1000000000000) (41390783757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (266735824365549 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (40662668757 / 1000000000000) (40662668759 / 1000000000000), orderedInterval (15936207264 / 1000000000000) (15936207266 / 1000000000000)))) (orderedInterval (6283230015 / 1000000000000) (6283230236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (222376521748381 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35831554646 / 1000000000000) (35831611624 / 1000000000000), orderedInterval (-31787311744 / 1000000000000) (-31787254766 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (196476400968001 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49518053304 / 1000000000000) (49518053307 / 1000000000000), orderedInterval (11735789819 / 1000000000000) (11735789822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (56946519036099 / 160000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-41935775197 / 1000000000000) (-41935774142 / 1000000000000), orderedInterval (5542543676 / 1000000000000) (5542544732 / 1000000000000)))) (orderedInterval (-1124509907 / 1000000000000) (-1124508879 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_chunkChecks1_2 :
    compactCertificate320.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (157517068584953 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13474113485 / 1000000000000) (13474113601 / 1000000000000), orderedInterval (-55276693979 / 1000000000000) (-55276693863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (133528963493233 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57367684124 / 1000000000000) (-57367684123 / 1000000000000), orderedInterval (-22698630589 / 1000000000000) (-22698630588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (83556225405499 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-78064104304 / 1000000000000) (-78064104277 / 1000000000000), orderedInterval (-709187371 / 1000000000000) (-709187343 / 1000000000000)))) (orderedInterval (10141611705 / 1000000000000) (10141611770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (44936815918533 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41997553893 / 1000000000000) (41997553894 / 1000000000000), orderedInterval (97453146474 / 1000000000000) (97453146475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (122012196674599 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (38490705109 / 1000000000000) (38490720215 / 1000000000000), orderedInterval (-52016558515 / 1000000000000) (-52016543409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (166597223415623 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54922655939 / 1000000000000) (54922656290 / 1000000000000), orderedInterval (-6499122669 / 1000000000000) (-6499122318 / 1000000000000)))) (orderedInterval (948715622 / 1000000000000) (948715944 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (70443774594501 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65213495523 / 1000000000000) (65213495524 / 1000000000000), orderedInterval (54191598237 / 1000000000000) (54191598238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (286350032805221 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23148137504 / 1000000000000) (23148137505 / 1000000000000), orderedInterval (35220214067 / 1000000000000) (35220214068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (191268551289739 / 800000000000) 1 (IntervalRat.scale (385 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46208490582 / 1000000000000) (46208490583 / 1000000000000), orderedInterval (22870694997 / 1000000000000) (22870694998 / 1000000000000)))) (orderedInterval (-10511110896 / 1000000000000) (-10511110820 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_chunkChecks1 :
    compactCertificate320.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate320.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate320_chunkChecks1_0
    compactCertificate320_chunkChecks1_1 compactCertificate320_chunkChecks1_2

theorem compactCertificate320_chunkChecks2_0 :
    compactCertificate320.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (385 / 2) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-57337914709 / 1000000000000) (-57337914519 / 1000000000000), orderedInterval (4561209593 / 1000000000000) (4561209783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (113435702988377 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62631278793 / 1000000000000) (-62631278792 / 1000000000000), orderedInterval (-23591611313 / 1000000000000) (-23591611312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (36682775662841 / 160000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34584955806 / 1000000000000) (-34584955805 / 1000000000000), orderedInterval (-39681826380 / 1000000000000) (-39681826379 / 1000000000000)))) (orderedInterval (25928026653 / 1000000000000) (25928026747 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (33100255219339 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-120064024356 / 1000000000000) (-120064024355 / 1000000000000), orderedInterval (-29695905531 / 1000000000000) (-29695905530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (88911941455183 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-69778121861 / 1000000000000) (-69778116601 / 1000000000000), orderedInterval (29623737063 / 1000000000000) (29623742323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (241413216886611 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (37589499533 / 1000000000000) (37589499534 / 1000000000000), orderedInterval (26332262962 / 1000000000000) (26332262963 / 1000000000000)))) (orderedInterval (7367498793 / 1000000000000) (7367498895 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (177823882910443 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-621371224 / 1000000000000) (-621371221 / 1000000000000), orderedInterval (-53511846921 / 1000000000000) (-53511846919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (304704254278039 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-40853568354 / 1000000000000) (-40853568208 / 1000000000000), orderedInterval (-1504446925 / 1000000000000) (-1504446780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (224443774594501 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-46971794437 / 1000000000000) (-46971793394 / 1000000000000), orderedInterval (8007960759 / 1000000000000) (8007961802 / 1000000000000)))) (orderedInterval (-2523696791 / 1000000000000) (-2523696686 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_chunkChecks2_1 :
    compactCertificate320.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (344354468534923 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28379058150 / 1000000000000) (-28379058149 / 1000000000000), orderedInterval (-25921149866 / 1000000000000) (-25921149865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (198813145105267 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45457245318 / 1000000000000) (-45457245317 / 1000000000000), orderedInterval (-22164249719 / 1000000000000) (-22164249718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (352797414826703 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35168725244 / 1000000000000) (35168749984 / 1000000000000), orderedInterval (-14418760784 / 1000000000000) (-14418736045 / 1000000000000)))) (orderedInterval (-45855854108 / 1000000000000) (-45855835268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (329629108608107 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-37575298054 / 1000000000000) (-37575298051 / 1000000000000), orderedInterval (-11493605984 / 1000000000000) (-11493605980 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (235238885674331 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-21326532303 / 1000000000000) (-21326531034 / 1000000000000), orderedInterval (41390782489 / 1000000000000) (41390783757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (266735824365549 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (40662668757 / 1000000000000) (40662668759 / 1000000000000), orderedInterval (15936207264 / 1000000000000) (15936207266 / 1000000000000)))) (orderedInterval (2182442724 / 1000000000000) (2182443067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (222376521748381 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35831554646 / 1000000000000) (35831611624 / 1000000000000), orderedInterval (-31787311744 / 1000000000000) (-31787254766 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (196476400968001 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49518053304 / 1000000000000) (49518053307 / 1000000000000), orderedInterval (11735789819 / 1000000000000) (11735789822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (56946519036099 / 160000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-41935775197 / 1000000000000) (-41935774142 / 1000000000000), orderedInterval (5542543676 / 1000000000000) (5542544732 / 1000000000000)))) (orderedInterval (7426115554 / 1000000000000) (7426117064 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_chunkChecks2_2 :
    compactCertificate320.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (157517068584953 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13474113485 / 1000000000000) (13474113601 / 1000000000000), orderedInterval (-55276693979 / 1000000000000) (-55276693863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (133528963493233 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57367684124 / 1000000000000) (-57367684123 / 1000000000000), orderedInterval (-22698630589 / 1000000000000) (-22698630588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (83556225405499 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-78064104304 / 1000000000000) (-78064104277 / 1000000000000), orderedInterval (-709187371 / 1000000000000) (-709187343 / 1000000000000)))) (orderedInterval (508263132 / 1000000000000) (508263195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (44936815918533 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41997553893 / 1000000000000) (41997553894 / 1000000000000), orderedInterval (97453146474 / 1000000000000) (97453146475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (122012196674599 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (38490705109 / 1000000000000) (38490720215 / 1000000000000), orderedInterval (-52016558515 / 1000000000000) (-52016543409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (166597223415623 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54922655939 / 1000000000000) (54922656290 / 1000000000000), orderedInterval (-6499122669 / 1000000000000) (-6499122318 / 1000000000000)))) (orderedInterval (5535249451 / 1000000000000) (5535249721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (70443774594501 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65213495523 / 1000000000000) (65213495524 / 1000000000000), orderedInterval (54191598237 / 1000000000000) (54191598238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (286350032805221 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23148137504 / 1000000000000) (23148137505 / 1000000000000), orderedInterval (35220214067 / 1000000000000) (35220214068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (191268551289739 / 800000000000) 2 (IntervalRat.scale (385 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46208490582 / 1000000000000) (46208490583 / 1000000000000), orderedInterval (22870694997 / 1000000000000) (22870694998 / 1000000000000)))) (orderedInterval (19861185652 / 1000000000000) (19861185764 / 1000000000000))) = true
  rfl'

theorem compactCertificate320_chunkChecks2 :
    compactCertificate320.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate320.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate320_chunkChecks2_0
    compactCertificate320_chunkChecks2_1 compactCertificate320_chunkChecks2_2

theorem compactCertificate320_chunkChecks3_0 :
    compactCertificate320.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (385 / 2) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-57337914709 / 1000000000000) (-57337914519 / 1000000000000), orderedInterval (4561209593 / 1000000000000) (4561209783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (113435702988377 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62631278793 / 1000000000000) (-62631278792 / 1000000000000), orderedInterval (-23591611313 / 1000000000000) (-23591611312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (36682775662841 / 160000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34584955806 / 1000000000000) (-34584955805 / 1000000000000), orderedInterval (-39681826380 / 1000000000000) (-39681826379 / 1000000000000)))) (orderedInterval (2079142163 / 1000000000000) (2079142260 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (33100255219339 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-120064024356 / 1000000000000) (-120064024355 / 1000000000000), orderedInterval (-29695905531 / 1000000000000) (-29695905530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (88911941455183 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-69778121861 / 1000000000000) (-69778116601 / 1000000000000), orderedInterval (29623737063 / 1000000000000) (29623742323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (241413216886611 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (37589499533 / 1000000000000) (37589499534 / 1000000000000), orderedInterval (26332262962 / 1000000000000) (26332262963 / 1000000000000)))) (orderedInterval (6961642535 / 1000000000000) (6961642627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (177823882910443 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-621371224 / 1000000000000) (-621371221 / 1000000000000), orderedInterval (-53511846921 / 1000000000000) (-53511846919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (304704254278039 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-40853568354 / 1000000000000) (-40853568208 / 1000000000000), orderedInterval (-1504446925 / 1000000000000) (-1504446780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (224443774594501 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-46971794437 / 1000000000000) (-46971793394 / 1000000000000), orderedInterval (8007960759 / 1000000000000) (8007961802 / 1000000000000)))) (orderedInterval (-945448990 / 1000000000000) (-945448816 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate320_chunkChecks3_1 :
    compactCertificate320.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (344354468534923 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28379058150 / 1000000000000) (-28379058149 / 1000000000000), orderedInterval (-25921149866 / 1000000000000) (-25921149865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (198813145105267 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45457245318 / 1000000000000) (-45457245317 / 1000000000000), orderedInterval (-22164249719 / 1000000000000) (-22164249718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (352797414826703 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35168725244 / 1000000000000) (35168749984 / 1000000000000), orderedInterval (-14418760784 / 1000000000000) (-14418736045 / 1000000000000)))) (orderedInterval (-23079809896 / 1000000000000) (-23079766773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (329629108608107 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-37575298054 / 1000000000000) (-37575298051 / 1000000000000), orderedInterval (-11493605984 / 1000000000000) (-11493605980 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (235238885674331 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-21326532303 / 1000000000000) (-21326531034 / 1000000000000), orderedInterval (41390782489 / 1000000000000) (41390783757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (266735824365549 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (40662668757 / 1000000000000) (40662668759 / 1000000000000), orderedInterval (15936207264 / 1000000000000) (15936207266 / 1000000000000)))) (orderedInterval (-15577409179 / 1000000000000) (-15577408644 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (222376521748381 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35831554646 / 1000000000000) (35831611624 / 1000000000000), orderedInterval (-31787311744 / 1000000000000) (-31787254766 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (196476400968001 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49518053304 / 1000000000000) (49518053307 / 1000000000000), orderedInterval (11735789819 / 1000000000000) (11735789822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (56946519036099 / 160000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-41935775197 / 1000000000000) (-41935774142 / 1000000000000), orderedInterval (5542543676 / 1000000000000) (5542544732 / 1000000000000)))) (orderedInterval (1564373269 / 1000000000000) (1564375490 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate320_chunkChecks3_2 :
    compactCertificate320.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (157517068584953 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13474113485 / 1000000000000) (13474113601 / 1000000000000), orderedInterval (-55276693979 / 1000000000000) (-55276693863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (133528963493233 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57367684124 / 1000000000000) (-57367684123 / 1000000000000), orderedInterval (-22698630589 / 1000000000000) (-22698630588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (83556225405499 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-78064104304 / 1000000000000) (-78064104277 / 1000000000000), orderedInterval (-709187371 / 1000000000000) (-709187343 / 1000000000000)))) (orderedInterval (-10293982135 / 1000000000000) (-10293982073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (44936815918533 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41997553893 / 1000000000000) (41997553894 / 1000000000000), orderedInterval (97453146474 / 1000000000000) (97453146475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (122012196674599 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (38490705109 / 1000000000000) (38490720215 / 1000000000000), orderedInterval (-52016558515 / 1000000000000) (-52016543409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (166597223415623 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54922655939 / 1000000000000) (54922656290 / 1000000000000), orderedInterval (-6499122669 / 1000000000000) (-6499122318 / 1000000000000)))) (orderedInterval (-1201506424 / 1000000000000) (-1201506197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (70443774594501 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65213495523 / 1000000000000) (65213495524 / 1000000000000), orderedInterval (54191598237 / 1000000000000) (54191598238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (286350032805221 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23148137504 / 1000000000000) (23148137505 / 1000000000000), orderedInterval (35220214067 / 1000000000000) (35220214068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (191268551289739 / 800000000000) 3 (IntervalRat.scale (385 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46208490582 / 1000000000000) (46208490583 / 1000000000000), orderedInterval (22870694997 / 1000000000000) (22870694998 / 1000000000000)))) (orderedInterval (26517881877 / 1000000000000) (26517882049 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate320_chunkChecks3 :
    compactCertificate320.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate320.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate320_chunkChecks3_0
    compactCertificate320_chunkChecks3_1 compactCertificate320_chunkChecks3_2

theorem compactCertificate320_chunkChecks4_0 :
    compactCertificate320.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (385 / 2) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-57337914709 / 1000000000000) (-57337914519 / 1000000000000), orderedInterval (4561209593 / 1000000000000) (4561209783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (113435702988377 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62631278793 / 1000000000000) (-62631278792 / 1000000000000), orderedInterval (-23591611313 / 1000000000000) (-23591611312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (36682775662841 / 160000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34584955806 / 1000000000000) (-34584955805 / 1000000000000), orderedInterval (-39681826380 / 1000000000000) (-39681826379 / 1000000000000)))) (orderedInterval (-27002939225 / 1000000000000) (-27002939125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (33100255219339 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-120064024356 / 1000000000000) (-120064024355 / 1000000000000), orderedInterval (-29695905531 / 1000000000000) (-29695905530 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (88911941455183 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-69778121861 / 1000000000000) (-69778116601 / 1000000000000), orderedInterval (29623737063 / 1000000000000) (29623742323 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (241413216886611 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (37589499533 / 1000000000000) (37589499534 / 1000000000000), orderedInterval (26332262962 / 1000000000000) (26332262963 / 1000000000000)))) (orderedInterval (-16489851623 / 1000000000000) (-16489851516 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (177823882910443 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-621371224 / 1000000000000) (-621371221 / 1000000000000), orderedInterval (-53511846921 / 1000000000000) (-53511846919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (304704254278039 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-40853568354 / 1000000000000) (-40853568208 / 1000000000000), orderedInterval (-1504446925 / 1000000000000) (-1504446780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (224443774594501 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-46971794437 / 1000000000000) (-46971793394 / 1000000000000), orderedInterval (8007960759 / 1000000000000) (8007961802 / 1000000000000)))) (orderedInterval (14200124267 / 1000000000000) (14200124564 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate320_chunkChecks4_1 :
    compactCertificate320.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (344354468534923 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-28379058150 / 1000000000000) (-28379058149 / 1000000000000), orderedInterval (-25921149866 / 1000000000000) (-25921149865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (198813145105267 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45457245318 / 1000000000000) (-45457245317 / 1000000000000), orderedInterval (-22164249719 / 1000000000000) (-22164249718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (352797414826703 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (35168725244 / 1000000000000) (35168749984 / 1000000000000), orderedInterval (-14418760784 / 1000000000000) (-14418736045 / 1000000000000)))) (orderedInterval (254650353286 / 1000000000000) (254650452247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (329629108608107 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-37575298054 / 1000000000000) (-37575298051 / 1000000000000), orderedInterval (-11493605984 / 1000000000000) (-11493605980 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (235238885674331 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-21326532303 / 1000000000000) (-21326531034 / 1000000000000), orderedInterval (41390782489 / 1000000000000) (41390783757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (266735824365549 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (40662668757 / 1000000000000) (40662668759 / 1000000000000), orderedInterval (15936207264 / 1000000000000) (15936207266 / 1000000000000)))) (orderedInterval (1568906712 / 1000000000000) (1568907553 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (222376521748381 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (35831554646 / 1000000000000) (35831611624 / 1000000000000), orderedInterval (-31787311744 / 1000000000000) (-31787254766 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (196476400968001 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (49518053304 / 1000000000000) (49518053307 / 1000000000000), orderedInterval (11735789819 / 1000000000000) (11735789822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (56946519036099 / 160000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-41935775197 / 1000000000000) (-41935774142 / 1000000000000), orderedInterval (5542543676 / 1000000000000) (5542544732 / 1000000000000)))) (orderedInterval (-18272494334 / 1000000000000) (-18272491037 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate320_chunkChecks4_2 :
    compactCertificate320.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (157517068584953 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (13474113485 / 1000000000000) (13474113601 / 1000000000000), orderedInterval (-55276693979 / 1000000000000) (-55276693863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (133528963493233 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-57367684124 / 1000000000000) (-57367684123 / 1000000000000), orderedInterval (-22698630589 / 1000000000000) (-22698630588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (83556225405499 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-78064104304 / 1000000000000) (-78064104277 / 1000000000000), orderedInterval (-709187371 / 1000000000000) (-709187343 / 1000000000000)))) (orderedInterval (-636066130 / 1000000000000) (-636066068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (44936815918533 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41997553893 / 1000000000000) (41997553894 / 1000000000000), orderedInterval (97453146474 / 1000000000000) (97453146475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (122012196674599 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (38490705109 / 1000000000000) (38490720215 / 1000000000000), orderedInterval (-52016558515 / 1000000000000) (-52016543409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (166597223415623 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (54922655939 / 1000000000000) (54922656290 / 1000000000000), orderedInterval (-6499122669 / 1000000000000) (-6499122318 / 1000000000000)))) (orderedInterval (-6101930822 / 1000000000000) (-6101930625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (70443774594501 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65213495523 / 1000000000000) (65213495524 / 1000000000000), orderedInterval (54191598237 / 1000000000000) (54191598238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (286350032805221 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23148137504 / 1000000000000) (23148137505 / 1000000000000), orderedInterval (35220214067 / 1000000000000) (35220214068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (191268551289739 / 800000000000) 4 (IntervalRat.scale (385 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (46208490582 / 1000000000000) (46208490583 / 1000000000000), orderedInterval (22870694997 / 1000000000000) (22870694998 / 1000000000000)))) (orderedInterval (-43412694157 / 1000000000000) (-43412693881 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate320_chunkChecks4 :
    compactCertificate320.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate320.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate320_chunkChecks4_0
    compactCertificate320_chunkChecks4_1 compactCertificate320_chunkChecks4_2

theorem compactCertificate320_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate320.chunkCheck r b = true :=
  compactCertificate320.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate320_chunkChecks0
    · exact compactCertificate320_chunkChecks1
    · exact compactCertificate320_chunkChecks2
    · exact compactCertificate320_chunkChecks3
    · exact compactCertificate320_chunkChecks4)

theorem compactCertificate320_coefficient0 :
    compactCertificate320.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate320_coefficient1 :
    compactCertificate320.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate320_coefficient2 :
    compactCertificate320.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate320_coefficient3 :
    compactCertificate320.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate320_coefficient4 :
    compactCertificate320.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate320_coefficients : ∀ r : Fin 5,
    compactCertificate320.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate320_coefficient0
  · exact compactCertificate320_coefficient1
  · exact compactCertificate320_coefficient2
  · exact compactCertificate320_coefficient3
  · exact compactCertificate320_coefficient4

theorem compactCertificate320_lower : (1 : ℚ) ≤ compactCertificate320.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate320, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate320_proves {t : ℝ} (ht : t ∈ compactCertificate320.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate320.proves compactCertificate320_states compactCertificate320_chunks
    compactCertificate320_coefficients compactCertificate320_lower ht

end Erdos232
