/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate441 : CompactCertificate where
  left := 312
  right := 313
  center := 625 / 2
  grid := fun i =>
    match i.val with
    | 0 => 100
    | 1 => 73
    | 2 => 119
    | 3 => 21
    | 4 => 57
    | 5 => 156
    | 6 => 115
    | 7 => 197
    | 8 => 145
    | 9 => 223
    | 10 => 128
    | 11 => 228
    | 12 => 213
    | 13 => 152
    | 14 => 172
    | 15 => 144
    | 16 => 127
    | 17 => 184
    | 18 => 102
    | 19 => 86
    | 20 => 54
    | 21 => 29
    | 22 => 79
    | 23 => 108
    | 24 => 46
    | 25 => 185
    | _ => 124
  point := fun i =>
    match i.val with
    | 0 => 625 / 2
    | 1 => 1473190947901 / 6400000000
    | 2 => 476399683933 / 1280000000
    | 3 => 429873444407 / 6400000000
    | 4 => 1154700538379 / 6400000000
    | 5 => 3135236582943 / 6400000000
    | 6 => 2309401076759 / 6400000000
    | 7 => 3957198107507 / 6400000000
    | 8 => 2914854215513 / 6400000000
    | 9 => 4472135954999 / 6400000000
    | 10 => 2581988897471 / 6400000000
    | 11 => 4581784608139 / 6400000000
    | 12 => 4280897514391 / 6400000000
    | 13 => 3055050463303 / 6400000000
    | 14 => 3464101615137 / 6400000000
    | 15 => 2888006775953 / 6400000000
    | 16 => 2551641571013 / 6400000000
    | 17 => 739565182287 / 1280000000
    | 18 => 2045676215389 / 6400000000
    | 19 => 1734142383029 / 6400000000
    | 20 => 1085145784487 / 6400000000
    | 21 => 583595011929 / 6400000000
    | 22 => 1584573982787 / 6400000000
    | 23 => 2163600304099 / 6400000000
    | 24 => 914854215513 / 6400000000
    | 25 => 3718831594873 / 6400000000
    | _ => 2484007159607 / 6400000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-34622001314 / 1000000000000) (-34621938804 / 1000000000000), orderedInterval (29012260602 / 1000000000000) (29012323111 / 1000000000000))
    | 1 => (orderedInterval (-52482352104 / 1000000000000) (-52482351898 / 1000000000000), orderedInterval (3471184358 / 1000000000000) (3471184564 / 1000000000000))
    | 2 => (orderedInterval (31802529243 / 1000000000000) (31802578496 / 1000000000000), orderedInterval (-26482863284 / 1000000000000) (-26482814032 / 1000000000000))
    | 3 => (orderedInterval (-89400574697 / 1000000000000) (-89400570071 / 1000000000000), orderedInterval (39206583662 / 1000000000000) (39206588288 / 1000000000000))
    | 4 => (orderedInterval (-50166751054 / 1000000000000) (-50166713630 / 1000000000000), orderedInterval (31947778584 / 1000000000000) (31947816008 / 1000000000000))
    | 5 => (orderedInterval (19677473963 / 1000000000000) (19677473964 / 1000000000000), orderedInterval (30184844032 / 1000000000000) (30184844033 / 1000000000000))
    | 6 => (orderedInterval (-14237474130 / 1000000000000) (-14237474129 / 1000000000000), orderedInterval (-39496700248 / 1000000000000) (-39496700247 / 1000000000000))
    | 7 => (orderedInterval (-6489469933 / 1000000000000) (-6489469932 / 1000000000000), orderedInterval (-31419201795 / 1000000000000) (-31419201794 / 1000000000000))
    | 8 => (orderedInterval (-24089993599 / 1000000000000) (-24089993598 / 1000000000000), orderedInterval (-28564926769 / 1000000000000) (-28564926768 / 1000000000000))
    | 9 => (orderedInterval (25699187688 / 1000000000000) (25699227471 / 1000000000000), orderedInterval (-15848969222 / 1000000000000) (-15848929439 / 1000000000000))
    | 10 => (orderedInterval (34350201014 / 1000000000000) (34350272624 / 1000000000000), orderedInterval (-19993946066 / 1000000000000) (-19993874457 / 1000000000000))
    | 11 => (orderedInterval (11775631177 / 1000000000000) (11775631178 / 1000000000000), orderedInterval (27388633941 / 1000000000000) (27388633942 / 1000000000000))
    | 12 => (orderedInterval (-15227507617 / 1000000000000) (-15227507616 / 1000000000000), orderedInterval (-26819166445 / 1000000000000) (-26819166444 / 1000000000000))
    | 13 => (orderedInterval (21060726580 / 1000000000000) (21060726581 / 1000000000000), orderedInterval (29812409169 / 1000000000000) (29812409170 / 1000000000000))
    | 14 => (orderedInterval (34022079718 / 1000000000000) (34022082666 / 1000000000000), orderedInterval (-4351824662 / 1000000000000) (-4351821714 / 1000000000000))
    | 15 => (orderedInterval (-12990905509 / 1000000000000) (-12990905415 / 1000000000000), orderedInterval (35256775891 / 1000000000000) (35256775985 / 1000000000000))
    | 16 => (orderedInterval (-19045750371 / 1000000000000) (-19045750370 / 1000000000000), orderedInterval (-35104777774 / 1000000000000) (-35104777773 / 1000000000000))
    | 17 => (orderedInterval (16419308707 / 1000000000000) (16419308708 / 1000000000000), orderedInterval (28834258790 / 1000000000000) (28834258791 / 1000000000000))
    | 18 => (orderedInterval (-916376032 / 1000000000000) (-916376029 / 1000000000000), orderedInterval (44620480713 / 1000000000000) (44620480715 / 1000000000000))
    | 19 => (orderedInterval (48471364050 / 1000000000000) (48471364159 / 1000000000000), orderedInterval (59865593 / 1000000000000) (59865702 / 1000000000000))
    | 20 => (orderedInterval (39130789753 / 1000000000000) (39130789754 / 1000000000000), orderedInterval (47038147883 / 1000000000000) (47038147884 / 1000000000000))
    | 21 => (orderedInterval (-63569309832 / 1000000000000) (-63569309831 / 1000000000000), orderedInterval (-53877109475 / 1000000000000) (-53877109474 / 1000000000000))
    | 22 => (orderedInterval (-9514758545 / 1000000000000) (-9514758544 / 1000000000000), orderedInterval (-49787849179 / 1000000000000) (-49787849178 / 1000000000000))
    | 23 => (orderedInterval (-18657485494 / 1000000000000) (-18657484829 / 1000000000000), orderedInterval (39207200206 / 1000000000000) (39207200871 / 1000000000000))
    | 24 => (orderedInterval (-47064385647 / 1000000000000) (-47064326296 / 1000000000000), orderedInterval (47477543616 / 1000000000000) (47477602967 / 1000000000000))
    | 25 => (orderedInterval (-20241215520 / 1000000000000) (-20241215519 / 1000000000000), orderedInterval (-26172222593 / 1000000000000) (-26172222592 / 1000000000000))
    | _ => (orderedInterval (-24390316783 / 1000000000000) (-24390311847 / 1000000000000), orderedInterval (32363327808 / 1000000000000) (32363332744 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12345774355 / 1000000000000) (-12345746663 / 1000000000000)
      | 1 => orderedInterval (-2260607451 / 1000000000000) (-2260605996 / 1000000000000)
      | 2 => orderedInterval (-382046408 / 1000000000000) (-382046390 / 1000000000000)
      | 3 => orderedInterval (-347399910 / 1000000000000) (-347387411 / 1000000000000)
      | 4 => orderedInterval (2094294816 / 1000000000000) (2094294869 / 1000000000000)
      | 5 => orderedInterval (1360309459 / 1000000000000) (1360309490 / 1000000000000)
      | 6 => orderedInterval (-1323042052 / 1000000000000) (-1323041967 / 1000000000000)
      | 7 => orderedInterval (2819563293 / 1000000000000) (2819563382 / 1000000000000)
      | _ => orderedInterval (5940220819 / 1000000000000) (5940222190 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9672403520 / 1000000000000) (9672431765 / 1000000000000)
      | 1 => orderedInterval (-2781806933 / 1000000000000) (-2781806090 / 1000000000000)
      | 2 => orderedInterval (911301893 / 1000000000000) (911301924 / 1000000000000)
      | 3 => orderedInterval (13304158116 / 1000000000000) (13304181029 / 1000000000000)
      | 4 => orderedInterval (5380800729 / 1000000000000) (5380800816 / 1000000000000)
      | 5 => orderedInterval (4515935333 / 1000000000000) (4515935378 / 1000000000000)
      | 6 => orderedInterval (-6469490226 / 1000000000000) (-6469490148 / 1000000000000)
      | 7 => orderedInterval (-2065382435 / 1000000000000) (-2065382346 / 1000000000000)
      | _ => orderedInterval (-3449377319 / 1000000000000) (-3449375883 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11310127038 / 1000000000000) (11310156035 / 1000000000000)
      | 1 => orderedInterval (4012258783 / 1000000000000) (4012259303 / 1000000000000)
      | 2 => orderedInterval (450145394 / 1000000000000) (450145449 / 1000000000000)
      | 3 => orderedInterval (9762478982 / 1000000000000) (9762523793 / 1000000000000)
      | 4 => orderedInterval (-5407160352 / 1000000000000) (-5407160207 / 1000000000000)
      | 5 => orderedInterval (-2912865563 / 1000000000000) (-2912865496 / 1000000000000)
      | 6 => orderedInterval (1554970527 / 1000000000000) (1554970602 / 1000000000000)
      | 7 => orderedInterval (-1902222112 / 1000000000000) (-1902222019 / 1000000000000)
      | _ => orderedInterval (-12685529597 / 1000000000000) (-12685527909 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8923079750 / 1000000000000) (-8923049965 / 1000000000000)
      | 1 => orderedInterval (8033264913 / 1000000000000) (8033265267 / 1000000000000)
      | 2 => orderedInterval (-5370812379 / 1000000000000) (-5370812280 / 1000000000000)
      | 3 => orderedInterval (-75140565998 / 1000000000000) (-75140474200 / 1000000000000)
      | 4 => orderedInterval (-14893156507 / 1000000000000) (-14893156259 / 1000000000000)
      | 5 => orderedInterval (-10054613036 / 1000000000000) (-10054612933 / 1000000000000)
      | 6 => orderedInterval (7387112716 / 1000000000000) (7387112788 / 1000000000000)
      | 7 => orderedInterval (3223731703 / 1000000000000) (3223731802 / 1000000000000)
      | _ => orderedInterval (-2049511154 / 1000000000000) (-2049509063 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10054723908 / 1000000000000) (-10054693088 / 1000000000000)
      | 1 => orderedInterval (-8700491564 / 1000000000000) (-8700491274 / 1000000000000)
      | 2 => orderedInterval (475275825 / 1000000000000) (475276008 / 1000000000000)
      | 3 => orderedInterval (-60503338104 / 1000000000000) (-60503143383 / 1000000000000)
      | 4 => orderedInterval (15158987049 / 1000000000000) (15158987479 / 1000000000000)
      | 5 => orderedInterval (7212586534 / 1000000000000) (7212586697 / 1000000000000)
      | 6 => orderedInterval (-1327161835 / 1000000000000) (-1327161764 / 1000000000000)
      | 7 => orderedInterval (2031264231 / 1000000000000) (2031264338 / 1000000000000)
      | _ => orderedInterval (30585873185 / 1000000000000) (30585875861 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-4444481789 / 1000000000000) (-4444438496 / 1000000000000)
    | 1 => orderedInterval (19018542678 / 1000000000000) (19018596445 / 1000000000000)
    | 2 => orderedInterval (4182203100 / 1000000000000) (4182279551 / 1000000000000)
    | 3 => orderedInterval (-97787629492 / 1000000000000) (-97787504843 / 1000000000000)
    | _ => orderedInterval (-25121728587 / 1000000000000) (-25121499126 / 1000000000000)

theorem compactCertificate441_stateChecks0 :
    compactCertificate441.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (625 / 2)) (orderedInterval (-34622001314 / 1000000000000) (-34621938804 / 1000000000000), orderedInterval (29012260602 / 1000000000000) (29012323111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (1473190947901 / 6400000000)) (orderedInterval (-52482352104 / 1000000000000) (-52482351898 / 1000000000000), orderedInterval (3471184358 / 1000000000000) (3471184564 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (476399683933 / 1280000000)) (orderedInterval (31802529243 / 1000000000000) (31802578496 / 1000000000000), orderedInterval (-26482863284 / 1000000000000) (-26482814032 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_stateChecks1 :
    compactCertificate441.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (429873444407 / 6400000000)) (orderedInterval (-89400574697 / 1000000000000) (-89400570071 / 1000000000000), orderedInterval (39206583662 / 1000000000000) (39206588288 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (1154700538379 / 6400000000)) (orderedInterval (-50166751054 / 1000000000000) (-50166713630 / 1000000000000), orderedInterval (31947778584 / 1000000000000) (31947816008 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (3135236582943 / 6400000000)) (orderedInterval (19677473963 / 1000000000000) (19677473964 / 1000000000000), orderedInterval (30184844032 / 1000000000000) (30184844033 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_stateChecks2 :
    compactCertificate441.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (2309401076759 / 6400000000)) (orderedInterval (-14237474130 / 1000000000000) (-14237474129 / 1000000000000), orderedInterval (-39496700248 / 1000000000000) (-39496700247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (3957198107507 / 6400000000)) (orderedInterval (-6489469933 / 1000000000000) (-6489469932 / 1000000000000), orderedInterval (-31419201795 / 1000000000000) (-31419201794 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (2914854215513 / 6400000000)) (orderedInterval (-24089993599 / 1000000000000) (-24089993598 / 1000000000000), orderedInterval (-28564926769 / 1000000000000) (-28564926768 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_stateChecks3 :
    compactCertificate441.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (4472135954999 / 6400000000)) (orderedInterval (25699187688 / 1000000000000) (25699227471 / 1000000000000), orderedInterval (-15848969222 / 1000000000000) (-15848929439 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (2581988897471 / 6400000000)) (orderedInterval (34350201014 / 1000000000000) (34350272624 / 1000000000000), orderedInterval (-19993946066 / 1000000000000) (-19993874457 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (4581784608139 / 6400000000)) (orderedInterval (11775631177 / 1000000000000) (11775631178 / 1000000000000), orderedInterval (27388633941 / 1000000000000) (27388633942 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_stateChecks4 :
    compactCertificate441.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (4280897514391 / 6400000000)) (orderedInterval (-15227507617 / 1000000000000) (-15227507616 / 1000000000000), orderedInterval (-26819166445 / 1000000000000) (-26819166444 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (3055050463303 / 6400000000)) (orderedInterval (21060726580 / 1000000000000) (21060726581 / 1000000000000), orderedInterval (29812409169 / 1000000000000) (29812409170 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (3464101615137 / 6400000000)) (orderedInterval (34022079718 / 1000000000000) (34022082666 / 1000000000000), orderedInterval (-4351824662 / 1000000000000) (-4351821714 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_stateChecks5 :
    compactCertificate441.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (2888006775953 / 6400000000)) (orderedInterval (-12990905509 / 1000000000000) (-12990905415 / 1000000000000), orderedInterval (35256775891 / 1000000000000) (35256775985 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (2551641571013 / 6400000000)) (orderedInterval (-19045750371 / 1000000000000) (-19045750370 / 1000000000000), orderedInterval (-35104777774 / 1000000000000) (-35104777773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (739565182287 / 1280000000)) (orderedInterval (16419308707 / 1000000000000) (16419308708 / 1000000000000), orderedInterval (28834258790 / 1000000000000) (28834258791 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_stateChecks6 :
    compactCertificate441.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (2045676215389 / 6400000000)) (orderedInterval (-916376032 / 1000000000000) (-916376029 / 1000000000000), orderedInterval (44620480713 / 1000000000000) (44620480715 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1734142383029 / 6400000000)) (orderedInterval (48471364050 / 1000000000000) (48471364159 / 1000000000000), orderedInterval (59865593 / 1000000000000) (59865702 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1085145784487 / 6400000000)) (orderedInterval (39130789753 / 1000000000000) (39130789754 / 1000000000000), orderedInterval (47038147883 / 1000000000000) (47038147884 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_stateChecks7 :
    compactCertificate441.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (583595011929 / 6400000000)) (orderedInterval (-63569309832 / 1000000000000) (-63569309831 / 1000000000000), orderedInterval (-53877109475 / 1000000000000) (-53877109474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (1584573982787 / 6400000000)) (orderedInterval (-9514758545 / 1000000000000) (-9514758544 / 1000000000000), orderedInterval (-49787849179 / 1000000000000) (-49787849178 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (2163600304099 / 6400000000)) (orderedInterval (-18657485494 / 1000000000000) (-18657484829 / 1000000000000), orderedInterval (39207200206 / 1000000000000) (39207200871 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_stateChecks8 :
    compactCertificate441.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (914854215513 / 6400000000)) (orderedInterval (-47064385647 / 1000000000000) (-47064326296 / 1000000000000), orderedInterval (47477543616 / 1000000000000) (47477602967 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (3718831594873 / 6400000000)) (orderedInterval (-20241215520 / 1000000000000) (-20241215519 / 1000000000000), orderedInterval (-26172222593 / 1000000000000) (-26172222592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (2484007159607 / 6400000000)) (orderedInterval (-24390316783 / 1000000000000) (-24390311847 / 1000000000000), orderedInterval (32363327808 / 1000000000000) (32363332744 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_states : ∀ j,
    BesselStateValid (compactCertificate441.point j) (compactCertificate441.state j) :=
  compactCertificate441.statesValid_of_checks3 compactCertificate441_stateChecks0
    compactCertificate441_stateChecks1 compactCertificate441_stateChecks2
    compactCertificate441_stateChecks3 compactCertificate441_stateChecks4
    compactCertificate441_stateChecks5 compactCertificate441_stateChecks6
    compactCertificate441_stateChecks7 compactCertificate441_stateChecks8

theorem compactCertificate441_chunkChecks0_0 :
    compactCertificate441.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (625 / 2) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34622001314 / 1000000000000) (-34621938804 / 1000000000000), orderedInterval (29012260602 / 1000000000000) (29012323111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1473190947901 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52482352104 / 1000000000000) (-52482351898 / 1000000000000), orderedInterval (3471184358 / 1000000000000) (3471184564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (476399683933 / 1280000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31802529243 / 1000000000000) (31802578496 / 1000000000000), orderedInterval (-26482863284 / 1000000000000) (-26482814032 / 1000000000000)))) (orderedInterval (-12345774355 / 1000000000000) (-12345746663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (429873444407 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89400574697 / 1000000000000) (-89400570071 / 1000000000000), orderedInterval (39206583662 / 1000000000000) (39206588288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1154700538379 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50166751054 / 1000000000000) (-50166713630 / 1000000000000), orderedInterval (31947778584 / 1000000000000) (31947816008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3135236582943 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19677473963 / 1000000000000) (19677473964 / 1000000000000), orderedInterval (30184844032 / 1000000000000) (30184844033 / 1000000000000)))) (orderedInterval (-2260607451 / 1000000000000) (-2260605996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2309401076759 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14237474130 / 1000000000000) (-14237474129 / 1000000000000), orderedInterval (-39496700248 / 1000000000000) (-39496700247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3957198107507 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6489469933 / 1000000000000) (-6489469932 / 1000000000000), orderedInterval (-31419201795 / 1000000000000) (-31419201794 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2914854215513 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24089993599 / 1000000000000) (-24089993598 / 1000000000000), orderedInterval (-28564926769 / 1000000000000) (-28564926768 / 1000000000000)))) (orderedInterval (-382046408 / 1000000000000) (-382046390 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_chunkChecks0_1 :
    compactCertificate441.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4472135954999 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25699187688 / 1000000000000) (25699227471 / 1000000000000), orderedInterval (-15848969222 / 1000000000000) (-15848929439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2581988897471 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34350201014 / 1000000000000) (34350272624 / 1000000000000), orderedInterval (-19993946066 / 1000000000000) (-19993874457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4581784608139 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11775631177 / 1000000000000) (11775631178 / 1000000000000), orderedInterval (27388633941 / 1000000000000) (27388633942 / 1000000000000)))) (orderedInterval (-347399910 / 1000000000000) (-347387411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4280897514391 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15227507617 / 1000000000000) (-15227507616 / 1000000000000), orderedInterval (-26819166445 / 1000000000000) (-26819166444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (3055050463303 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21060726580 / 1000000000000) (21060726581 / 1000000000000), orderedInterval (29812409169 / 1000000000000) (29812409170 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3464101615137 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34022079718 / 1000000000000) (34022082666 / 1000000000000), orderedInterval (-4351824662 / 1000000000000) (-4351821714 / 1000000000000)))) (orderedInterval (2094294816 / 1000000000000) (2094294869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2888006775953 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12990905509 / 1000000000000) (-12990905415 / 1000000000000), orderedInterval (35256775891 / 1000000000000) (35256775985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2551641571013 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19045750371 / 1000000000000) (-19045750370 / 1000000000000), orderedInterval (-35104777774 / 1000000000000) (-35104777773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (739565182287 / 1280000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16419308707 / 1000000000000) (16419308708 / 1000000000000), orderedInterval (28834258790 / 1000000000000) (28834258791 / 1000000000000)))) (orderedInterval (1360309459 / 1000000000000) (1360309490 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_chunkChecks0_2 :
    compactCertificate441.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2045676215389 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-916376032 / 1000000000000) (-916376029 / 1000000000000), orderedInterval (44620480713 / 1000000000000) (44620480715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1734142383029 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (48471364050 / 1000000000000) (48471364159 / 1000000000000), orderedInterval (59865593 / 1000000000000) (59865702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1085145784487 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (39130789753 / 1000000000000) (39130789754 / 1000000000000), orderedInterval (47038147883 / 1000000000000) (47038147884 / 1000000000000)))) (orderedInterval (-1323042052 / 1000000000000) (-1323041967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (583595011929 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63569309832 / 1000000000000) (-63569309831 / 1000000000000), orderedInterval (-53877109475 / 1000000000000) (-53877109474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1584573982787 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9514758545 / 1000000000000) (-9514758544 / 1000000000000), orderedInterval (-49787849179 / 1000000000000) (-49787849178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2163600304099 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-18657485494 / 1000000000000) (-18657484829 / 1000000000000), orderedInterval (39207200206 / 1000000000000) (39207200871 / 1000000000000)))) (orderedInterval (2819563293 / 1000000000000) (2819563382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (914854215513 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47064385647 / 1000000000000) (-47064326296 / 1000000000000), orderedInterval (47477543616 / 1000000000000) (47477602967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3718831594873 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20241215520 / 1000000000000) (-20241215519 / 1000000000000), orderedInterval (-26172222593 / 1000000000000) (-26172222592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2484007159607 / 6400000000) 0 (IntervalRat.scale (625 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24390316783 / 1000000000000) (-24390311847 / 1000000000000), orderedInterval (32363327808 / 1000000000000) (32363332744 / 1000000000000)))) (orderedInterval (5940220819 / 1000000000000) (5940222190 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_chunkChecks0 :
    compactCertificate441.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate441.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate441_chunkChecks0_0
    compactCertificate441_chunkChecks0_1 compactCertificate441_chunkChecks0_2

theorem compactCertificate441_chunkChecks1_0 :
    compactCertificate441.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (625 / 2) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34622001314 / 1000000000000) (-34621938804 / 1000000000000), orderedInterval (29012260602 / 1000000000000) (29012323111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1473190947901 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52482352104 / 1000000000000) (-52482351898 / 1000000000000), orderedInterval (3471184358 / 1000000000000) (3471184564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (476399683933 / 1280000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31802529243 / 1000000000000) (31802578496 / 1000000000000), orderedInterval (-26482863284 / 1000000000000) (-26482814032 / 1000000000000)))) (orderedInterval (9672403520 / 1000000000000) (9672431765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (429873444407 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89400574697 / 1000000000000) (-89400570071 / 1000000000000), orderedInterval (39206583662 / 1000000000000) (39206588288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1154700538379 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50166751054 / 1000000000000) (-50166713630 / 1000000000000), orderedInterval (31947778584 / 1000000000000) (31947816008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3135236582943 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19677473963 / 1000000000000) (19677473964 / 1000000000000), orderedInterval (30184844032 / 1000000000000) (30184844033 / 1000000000000)))) (orderedInterval (-2781806933 / 1000000000000) (-2781806090 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2309401076759 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14237474130 / 1000000000000) (-14237474129 / 1000000000000), orderedInterval (-39496700248 / 1000000000000) (-39496700247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3957198107507 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6489469933 / 1000000000000) (-6489469932 / 1000000000000), orderedInterval (-31419201795 / 1000000000000) (-31419201794 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2914854215513 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24089993599 / 1000000000000) (-24089993598 / 1000000000000), orderedInterval (-28564926769 / 1000000000000) (-28564926768 / 1000000000000)))) (orderedInterval (911301893 / 1000000000000) (911301924 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_chunkChecks1_1 :
    compactCertificate441.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4472135954999 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25699187688 / 1000000000000) (25699227471 / 1000000000000), orderedInterval (-15848969222 / 1000000000000) (-15848929439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2581988897471 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34350201014 / 1000000000000) (34350272624 / 1000000000000), orderedInterval (-19993946066 / 1000000000000) (-19993874457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4581784608139 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11775631177 / 1000000000000) (11775631178 / 1000000000000), orderedInterval (27388633941 / 1000000000000) (27388633942 / 1000000000000)))) (orderedInterval (13304158116 / 1000000000000) (13304181029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4280897514391 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15227507617 / 1000000000000) (-15227507616 / 1000000000000), orderedInterval (-26819166445 / 1000000000000) (-26819166444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (3055050463303 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21060726580 / 1000000000000) (21060726581 / 1000000000000), orderedInterval (29812409169 / 1000000000000) (29812409170 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3464101615137 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34022079718 / 1000000000000) (34022082666 / 1000000000000), orderedInterval (-4351824662 / 1000000000000) (-4351821714 / 1000000000000)))) (orderedInterval (5380800729 / 1000000000000) (5380800816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2888006775953 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12990905509 / 1000000000000) (-12990905415 / 1000000000000), orderedInterval (35256775891 / 1000000000000) (35256775985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2551641571013 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19045750371 / 1000000000000) (-19045750370 / 1000000000000), orderedInterval (-35104777774 / 1000000000000) (-35104777773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (739565182287 / 1280000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16419308707 / 1000000000000) (16419308708 / 1000000000000), orderedInterval (28834258790 / 1000000000000) (28834258791 / 1000000000000)))) (orderedInterval (4515935333 / 1000000000000) (4515935378 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_chunkChecks1_2 :
    compactCertificate441.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2045676215389 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-916376032 / 1000000000000) (-916376029 / 1000000000000), orderedInterval (44620480713 / 1000000000000) (44620480715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1734142383029 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (48471364050 / 1000000000000) (48471364159 / 1000000000000), orderedInterval (59865593 / 1000000000000) (59865702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1085145784487 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (39130789753 / 1000000000000) (39130789754 / 1000000000000), orderedInterval (47038147883 / 1000000000000) (47038147884 / 1000000000000)))) (orderedInterval (-6469490226 / 1000000000000) (-6469490148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (583595011929 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63569309832 / 1000000000000) (-63569309831 / 1000000000000), orderedInterval (-53877109475 / 1000000000000) (-53877109474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1584573982787 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9514758545 / 1000000000000) (-9514758544 / 1000000000000), orderedInterval (-49787849179 / 1000000000000) (-49787849178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2163600304099 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-18657485494 / 1000000000000) (-18657484829 / 1000000000000), orderedInterval (39207200206 / 1000000000000) (39207200871 / 1000000000000)))) (orderedInterval (-2065382435 / 1000000000000) (-2065382346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (914854215513 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47064385647 / 1000000000000) (-47064326296 / 1000000000000), orderedInterval (47477543616 / 1000000000000) (47477602967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3718831594873 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20241215520 / 1000000000000) (-20241215519 / 1000000000000), orderedInterval (-26172222593 / 1000000000000) (-26172222592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2484007159607 / 6400000000) 1 (IntervalRat.scale (625 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24390316783 / 1000000000000) (-24390311847 / 1000000000000), orderedInterval (32363327808 / 1000000000000) (32363332744 / 1000000000000)))) (orderedInterval (-3449377319 / 1000000000000) (-3449375883 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_chunkChecks1 :
    compactCertificate441.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate441.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate441_chunkChecks1_0
    compactCertificate441_chunkChecks1_1 compactCertificate441_chunkChecks1_2

theorem compactCertificate441_chunkChecks2_0 :
    compactCertificate441.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (625 / 2) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34622001314 / 1000000000000) (-34621938804 / 1000000000000), orderedInterval (29012260602 / 1000000000000) (29012323111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1473190947901 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52482352104 / 1000000000000) (-52482351898 / 1000000000000), orderedInterval (3471184358 / 1000000000000) (3471184564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (476399683933 / 1280000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31802529243 / 1000000000000) (31802578496 / 1000000000000), orderedInterval (-26482863284 / 1000000000000) (-26482814032 / 1000000000000)))) (orderedInterval (11310127038 / 1000000000000) (11310156035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (429873444407 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89400574697 / 1000000000000) (-89400570071 / 1000000000000), orderedInterval (39206583662 / 1000000000000) (39206588288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1154700538379 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50166751054 / 1000000000000) (-50166713630 / 1000000000000), orderedInterval (31947778584 / 1000000000000) (31947816008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3135236582943 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19677473963 / 1000000000000) (19677473964 / 1000000000000), orderedInterval (30184844032 / 1000000000000) (30184844033 / 1000000000000)))) (orderedInterval (4012258783 / 1000000000000) (4012259303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2309401076759 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14237474130 / 1000000000000) (-14237474129 / 1000000000000), orderedInterval (-39496700248 / 1000000000000) (-39496700247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3957198107507 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6489469933 / 1000000000000) (-6489469932 / 1000000000000), orderedInterval (-31419201795 / 1000000000000) (-31419201794 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2914854215513 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24089993599 / 1000000000000) (-24089993598 / 1000000000000), orderedInterval (-28564926769 / 1000000000000) (-28564926768 / 1000000000000)))) (orderedInterval (450145394 / 1000000000000) (450145449 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_chunkChecks2_1 :
    compactCertificate441.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4472135954999 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25699187688 / 1000000000000) (25699227471 / 1000000000000), orderedInterval (-15848969222 / 1000000000000) (-15848929439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2581988897471 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34350201014 / 1000000000000) (34350272624 / 1000000000000), orderedInterval (-19993946066 / 1000000000000) (-19993874457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4581784608139 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11775631177 / 1000000000000) (11775631178 / 1000000000000), orderedInterval (27388633941 / 1000000000000) (27388633942 / 1000000000000)))) (orderedInterval (9762478982 / 1000000000000) (9762523793 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4280897514391 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15227507617 / 1000000000000) (-15227507616 / 1000000000000), orderedInterval (-26819166445 / 1000000000000) (-26819166444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (3055050463303 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21060726580 / 1000000000000) (21060726581 / 1000000000000), orderedInterval (29812409169 / 1000000000000) (29812409170 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3464101615137 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34022079718 / 1000000000000) (34022082666 / 1000000000000), orderedInterval (-4351824662 / 1000000000000) (-4351821714 / 1000000000000)))) (orderedInterval (-5407160352 / 1000000000000) (-5407160207 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2888006775953 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12990905509 / 1000000000000) (-12990905415 / 1000000000000), orderedInterval (35256775891 / 1000000000000) (35256775985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2551641571013 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19045750371 / 1000000000000) (-19045750370 / 1000000000000), orderedInterval (-35104777774 / 1000000000000) (-35104777773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (739565182287 / 1280000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16419308707 / 1000000000000) (16419308708 / 1000000000000), orderedInterval (28834258790 / 1000000000000) (28834258791 / 1000000000000)))) (orderedInterval (-2912865563 / 1000000000000) (-2912865496 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_chunkChecks2_2 :
    compactCertificate441.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2045676215389 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-916376032 / 1000000000000) (-916376029 / 1000000000000), orderedInterval (44620480713 / 1000000000000) (44620480715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1734142383029 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (48471364050 / 1000000000000) (48471364159 / 1000000000000), orderedInterval (59865593 / 1000000000000) (59865702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1085145784487 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (39130789753 / 1000000000000) (39130789754 / 1000000000000), orderedInterval (47038147883 / 1000000000000) (47038147884 / 1000000000000)))) (orderedInterval (1554970527 / 1000000000000) (1554970602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (583595011929 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63569309832 / 1000000000000) (-63569309831 / 1000000000000), orderedInterval (-53877109475 / 1000000000000) (-53877109474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1584573982787 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9514758545 / 1000000000000) (-9514758544 / 1000000000000), orderedInterval (-49787849179 / 1000000000000) (-49787849178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2163600304099 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-18657485494 / 1000000000000) (-18657484829 / 1000000000000), orderedInterval (39207200206 / 1000000000000) (39207200871 / 1000000000000)))) (orderedInterval (-1902222112 / 1000000000000) (-1902222019 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (914854215513 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47064385647 / 1000000000000) (-47064326296 / 1000000000000), orderedInterval (47477543616 / 1000000000000) (47477602967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3718831594873 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20241215520 / 1000000000000) (-20241215519 / 1000000000000), orderedInterval (-26172222593 / 1000000000000) (-26172222592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2484007159607 / 6400000000) 2 (IntervalRat.scale (625 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24390316783 / 1000000000000) (-24390311847 / 1000000000000), orderedInterval (32363327808 / 1000000000000) (32363332744 / 1000000000000)))) (orderedInterval (-12685529597 / 1000000000000) (-12685527909 / 1000000000000))) = true
  rfl'

theorem compactCertificate441_chunkChecks2 :
    compactCertificate441.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate441.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate441_chunkChecks2_0
    compactCertificate441_chunkChecks2_1 compactCertificate441_chunkChecks2_2

theorem compactCertificate441_chunkChecks3_0 :
    compactCertificate441.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (625 / 2) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34622001314 / 1000000000000) (-34621938804 / 1000000000000), orderedInterval (29012260602 / 1000000000000) (29012323111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1473190947901 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52482352104 / 1000000000000) (-52482351898 / 1000000000000), orderedInterval (3471184358 / 1000000000000) (3471184564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (476399683933 / 1280000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31802529243 / 1000000000000) (31802578496 / 1000000000000), orderedInterval (-26482863284 / 1000000000000) (-26482814032 / 1000000000000)))) (orderedInterval (-8923079750 / 1000000000000) (-8923049965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (429873444407 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89400574697 / 1000000000000) (-89400570071 / 1000000000000), orderedInterval (39206583662 / 1000000000000) (39206588288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1154700538379 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50166751054 / 1000000000000) (-50166713630 / 1000000000000), orderedInterval (31947778584 / 1000000000000) (31947816008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3135236582943 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19677473963 / 1000000000000) (19677473964 / 1000000000000), orderedInterval (30184844032 / 1000000000000) (30184844033 / 1000000000000)))) (orderedInterval (8033264913 / 1000000000000) (8033265267 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2309401076759 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14237474130 / 1000000000000) (-14237474129 / 1000000000000), orderedInterval (-39496700248 / 1000000000000) (-39496700247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3957198107507 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6489469933 / 1000000000000) (-6489469932 / 1000000000000), orderedInterval (-31419201795 / 1000000000000) (-31419201794 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2914854215513 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24089993599 / 1000000000000) (-24089993598 / 1000000000000), orderedInterval (-28564926769 / 1000000000000) (-28564926768 / 1000000000000)))) (orderedInterval (-5370812379 / 1000000000000) (-5370812280 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate441_chunkChecks3_1 :
    compactCertificate441.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4472135954999 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25699187688 / 1000000000000) (25699227471 / 1000000000000), orderedInterval (-15848969222 / 1000000000000) (-15848929439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2581988897471 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34350201014 / 1000000000000) (34350272624 / 1000000000000), orderedInterval (-19993946066 / 1000000000000) (-19993874457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4581784608139 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11775631177 / 1000000000000) (11775631178 / 1000000000000), orderedInterval (27388633941 / 1000000000000) (27388633942 / 1000000000000)))) (orderedInterval (-75140565998 / 1000000000000) (-75140474200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4280897514391 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15227507617 / 1000000000000) (-15227507616 / 1000000000000), orderedInterval (-26819166445 / 1000000000000) (-26819166444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (3055050463303 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21060726580 / 1000000000000) (21060726581 / 1000000000000), orderedInterval (29812409169 / 1000000000000) (29812409170 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3464101615137 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34022079718 / 1000000000000) (34022082666 / 1000000000000), orderedInterval (-4351824662 / 1000000000000) (-4351821714 / 1000000000000)))) (orderedInterval (-14893156507 / 1000000000000) (-14893156259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2888006775953 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12990905509 / 1000000000000) (-12990905415 / 1000000000000), orderedInterval (35256775891 / 1000000000000) (35256775985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2551641571013 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19045750371 / 1000000000000) (-19045750370 / 1000000000000), orderedInterval (-35104777774 / 1000000000000) (-35104777773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (739565182287 / 1280000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16419308707 / 1000000000000) (16419308708 / 1000000000000), orderedInterval (28834258790 / 1000000000000) (28834258791 / 1000000000000)))) (orderedInterval (-10054613036 / 1000000000000) (-10054612933 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate441_chunkChecks3_2 :
    compactCertificate441.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2045676215389 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-916376032 / 1000000000000) (-916376029 / 1000000000000), orderedInterval (44620480713 / 1000000000000) (44620480715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1734142383029 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (48471364050 / 1000000000000) (48471364159 / 1000000000000), orderedInterval (59865593 / 1000000000000) (59865702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1085145784487 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (39130789753 / 1000000000000) (39130789754 / 1000000000000), orderedInterval (47038147883 / 1000000000000) (47038147884 / 1000000000000)))) (orderedInterval (7387112716 / 1000000000000) (7387112788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (583595011929 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63569309832 / 1000000000000) (-63569309831 / 1000000000000), orderedInterval (-53877109475 / 1000000000000) (-53877109474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1584573982787 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9514758545 / 1000000000000) (-9514758544 / 1000000000000), orderedInterval (-49787849179 / 1000000000000) (-49787849178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2163600304099 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-18657485494 / 1000000000000) (-18657484829 / 1000000000000), orderedInterval (39207200206 / 1000000000000) (39207200871 / 1000000000000)))) (orderedInterval (3223731703 / 1000000000000) (3223731802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (914854215513 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47064385647 / 1000000000000) (-47064326296 / 1000000000000), orderedInterval (47477543616 / 1000000000000) (47477602967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3718831594873 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20241215520 / 1000000000000) (-20241215519 / 1000000000000), orderedInterval (-26172222593 / 1000000000000) (-26172222592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2484007159607 / 6400000000) 3 (IntervalRat.scale (625 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24390316783 / 1000000000000) (-24390311847 / 1000000000000), orderedInterval (32363327808 / 1000000000000) (32363332744 / 1000000000000)))) (orderedInterval (-2049511154 / 1000000000000) (-2049509063 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate441_chunkChecks3 :
    compactCertificate441.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate441.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate441_chunkChecks3_0
    compactCertificate441_chunkChecks3_1 compactCertificate441_chunkChecks3_2

theorem compactCertificate441_chunkChecks4_0 :
    compactCertificate441.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (625 / 2) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34622001314 / 1000000000000) (-34621938804 / 1000000000000), orderedInterval (29012260602 / 1000000000000) (29012323111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1473190947901 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-52482352104 / 1000000000000) (-52482351898 / 1000000000000), orderedInterval (3471184358 / 1000000000000) (3471184564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (476399683933 / 1280000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31802529243 / 1000000000000) (31802578496 / 1000000000000), orderedInterval (-26482863284 / 1000000000000) (-26482814032 / 1000000000000)))) (orderedInterval (-10054723908 / 1000000000000) (-10054693088 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (429873444407 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89400574697 / 1000000000000) (-89400570071 / 1000000000000), orderedInterval (39206583662 / 1000000000000) (39206588288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1154700538379 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-50166751054 / 1000000000000) (-50166713630 / 1000000000000), orderedInterval (31947778584 / 1000000000000) (31947816008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3135236582943 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19677473963 / 1000000000000) (19677473964 / 1000000000000), orderedInterval (30184844032 / 1000000000000) (30184844033 / 1000000000000)))) (orderedInterval (-8700491564 / 1000000000000) (-8700491274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2309401076759 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14237474130 / 1000000000000) (-14237474129 / 1000000000000), orderedInterval (-39496700248 / 1000000000000) (-39496700247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3957198107507 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-6489469933 / 1000000000000) (-6489469932 / 1000000000000), orderedInterval (-31419201795 / 1000000000000) (-31419201794 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2914854215513 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24089993599 / 1000000000000) (-24089993598 / 1000000000000), orderedInterval (-28564926769 / 1000000000000) (-28564926768 / 1000000000000)))) (orderedInterval (475275825 / 1000000000000) (475276008 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate441_chunkChecks4_1 :
    compactCertificate441.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4472135954999 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25699187688 / 1000000000000) (25699227471 / 1000000000000), orderedInterval (-15848969222 / 1000000000000) (-15848929439 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2581988897471 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34350201014 / 1000000000000) (34350272624 / 1000000000000), orderedInterval (-19993946066 / 1000000000000) (-19993874457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4581784608139 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11775631177 / 1000000000000) (11775631178 / 1000000000000), orderedInterval (27388633941 / 1000000000000) (27388633942 / 1000000000000)))) (orderedInterval (-60503338104 / 1000000000000) (-60503143383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4280897514391 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15227507617 / 1000000000000) (-15227507616 / 1000000000000), orderedInterval (-26819166445 / 1000000000000) (-26819166444 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (3055050463303 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21060726580 / 1000000000000) (21060726581 / 1000000000000), orderedInterval (29812409169 / 1000000000000) (29812409170 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3464101615137 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (34022079718 / 1000000000000) (34022082666 / 1000000000000), orderedInterval (-4351824662 / 1000000000000) (-4351821714 / 1000000000000)))) (orderedInterval (15158987049 / 1000000000000) (15158987479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2888006775953 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12990905509 / 1000000000000) (-12990905415 / 1000000000000), orderedInterval (35256775891 / 1000000000000) (35256775985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2551641571013 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19045750371 / 1000000000000) (-19045750370 / 1000000000000), orderedInterval (-35104777774 / 1000000000000) (-35104777773 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (739565182287 / 1280000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16419308707 / 1000000000000) (16419308708 / 1000000000000), orderedInterval (28834258790 / 1000000000000) (28834258791 / 1000000000000)))) (orderedInterval (7212586534 / 1000000000000) (7212586697 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate441_chunkChecks4_2 :
    compactCertificate441.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2045676215389 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-916376032 / 1000000000000) (-916376029 / 1000000000000), orderedInterval (44620480713 / 1000000000000) (44620480715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1734142383029 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (48471364050 / 1000000000000) (48471364159 / 1000000000000), orderedInterval (59865593 / 1000000000000) (59865702 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1085145784487 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (39130789753 / 1000000000000) (39130789754 / 1000000000000), orderedInterval (47038147883 / 1000000000000) (47038147884 / 1000000000000)))) (orderedInterval (-1327161835 / 1000000000000) (-1327161764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (583595011929 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-63569309832 / 1000000000000) (-63569309831 / 1000000000000), orderedInterval (-53877109475 / 1000000000000) (-53877109474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1584573982787 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9514758545 / 1000000000000) (-9514758544 / 1000000000000), orderedInterval (-49787849179 / 1000000000000) (-49787849178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2163600304099 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-18657485494 / 1000000000000) (-18657484829 / 1000000000000), orderedInterval (39207200206 / 1000000000000) (39207200871 / 1000000000000)))) (orderedInterval (2031264231 / 1000000000000) (2031264338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (914854215513 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-47064385647 / 1000000000000) (-47064326296 / 1000000000000), orderedInterval (47477543616 / 1000000000000) (47477602967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3718831594873 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20241215520 / 1000000000000) (-20241215519 / 1000000000000), orderedInterval (-26172222593 / 1000000000000) (-26172222592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2484007159607 / 6400000000) 4 (IntervalRat.scale (625 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24390316783 / 1000000000000) (-24390311847 / 1000000000000), orderedInterval (32363327808 / 1000000000000) (32363332744 / 1000000000000)))) (orderedInterval (30585873185 / 1000000000000) (30585875861 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate441_chunkChecks4 :
    compactCertificate441.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate441.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate441_chunkChecks4_0
    compactCertificate441_chunkChecks4_1 compactCertificate441_chunkChecks4_2

theorem compactCertificate441_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate441.chunkCheck r b = true :=
  compactCertificate441.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate441_chunkChecks0
    · exact compactCertificate441_chunkChecks1
    · exact compactCertificate441_chunkChecks2
    · exact compactCertificate441_chunkChecks3
    · exact compactCertificate441_chunkChecks4)

theorem compactCertificate441_coefficient0 :
    compactCertificate441.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate441_coefficient1 :
    compactCertificate441.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate441_coefficient2 :
    compactCertificate441.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate441_coefficient3 :
    compactCertificate441.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate441_coefficient4 :
    compactCertificate441.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate441_coefficients : ∀ r : Fin 5,
    compactCertificate441.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate441_coefficient0
  · exact compactCertificate441_coefficient1
  · exact compactCertificate441_coefficient2
  · exact compactCertificate441_coefficient3
  · exact compactCertificate441_coefficient4

theorem compactCertificate441_lower : (1 : ℚ) ≤ compactCertificate441.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate441, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate441_proves {t : ℝ} (ht : t ∈ compactCertificate441.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate441.proves compactCertificate441_states compactCertificate441_chunks
    compactCertificate441_coefficients compactCertificate441_lower ht

end Erdos232
