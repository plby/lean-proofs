/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate375 : CompactCertificate where
  left := 246
  right := 247
  center := 493 / 2
  grid := fun i =>
    match i.val with
    | 0 => 79
    | 1 => 58
    | 2 => 93
    | 3 => 17
    | 4 => 45
    | 5 => 123
    | 6 => 91
    | 7 => 155
    | 8 => 114
    | 9 => 176
    | 10 => 101
    | 11 => 180
    | 12 => 168
    | 13 => 120
    | 14 => 136
    | 15 => 113
    | 16 => 100
    | 17 => 145
    | 18 => 80
    | 19 => 68
    | 20 => 43
    | 21 => 23
    | 22 => 62
    | 23 => 85
    | 24 => 36
    | 25 => 146
    | _ => 98
  point := fun i =>
    match i.val with
    | 0 => 493 / 2
    | 1 => 726283137315193 / 4000000000000
    | 2 => 234865044178969 / 800000000000
    | 3 => 211927608092651 / 4000000000000
    | 4 => 569267365420847 / 4000000000000
    | 5 => 1545671635390899 / 4000000000000
    | 6 => 1138534730842187 / 4000000000000
    | 7 => 1950898667000951 / 4000000000000
    | 8 => 1437023128247909 / 4000000000000
    | 9 => 2204763025814507 / 4000000000000
    | 10 => 1272920526453203 / 4000000000000
    | 11 => 2258819811812527 / 4000000000000
    | 12 => 2110482474594763 / 4000000000000
    | 13 => 1506139878408379 / 4000000000000
    | 14 => 1707802096262541 / 4000000000000
    | 15 => 1423787340544829 / 4000000000000
    | 16 => 1257959294509409 / 4000000000000
    | 17 => 364605634867491 / 800000000000
    | 18 => 1008518374186777 / 4000000000000
    | 19 => 854932194833297 / 4000000000000
    | 20 => 534976871752091 / 4000000000000
    | 21 => 287712340880997 / 4000000000000
    | 22 => 781194973513991 / 4000000000000
    | 23 => 1066654949920807 / 4000000000000
    | 24 => 451023128247909 / 4000000000000
    | 25 => 1833383976272389 / 4000000000000
    | _ => 1224615529686251 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (39837613953 / 1000000000000) (39837718035 / 1000000000000), orderedInterval (-31633906992 / 1000000000000) (-31633802910 / 1000000000000))
    | 1 => (orderedInterval (8445656436 / 1000000000000) (8445656437 / 1000000000000), orderedInterval (58584448935 / 1000000000000) (58584448936 / 1000000000000))
    | 2 => (orderedInterval (-37699405743 / 1000000000000) (-37699300523 / 1000000000000), orderedInterval (27399462248 / 1000000000000) (27399567468 / 1000000000000))
    | 3 => (orderedInterval (-38395253715 / 1000000000000) (-38395253714 / 1000000000000), orderedInterval (-102311955166 / 1000000000000) (-102311955165 / 1000000000000))
    | 4 => (orderedInterval (-66039665301 / 1000000000000) (-66039664901 / 1000000000000), orderedInterval (10814695700 / 1000000000000) (10814696100 / 1000000000000))
    | 5 => (orderedInterval (-28749383307 / 1000000000000) (-28749383306 / 1000000000000), orderedInterval (-28615257267 / 1000000000000) (-28615257266 / 1000000000000))
    | 6 => (orderedInterval (21261747521 / 1000000000000) (21261748716 / 1000000000000), orderedInterval (-42281503237 / 1000000000000) (-42281502041 / 1000000000000))
    | 7 => (orderedInterval (-36127608309 / 1000000000000) (-36127607867 / 1000000000000), orderedInterval (-246535348 / 1000000000000) (-246534906 / 1000000000000))
    | 8 => (orderedInterval (39845108160 / 1000000000000) (39845117486 / 1000000000000), orderedInterval (-13635488316 / 1000000000000) (-13635478990 / 1000000000000))
    | 9 => (orderedInterval (-27532504325 / 1000000000000) (-27532464367 / 1000000000000), orderedInterval (19948610767 / 1000000000000) (19948650724 / 1000000000000))
    | 10 => (orderedInterval (-44267322699 / 1000000000000) (-44267321712 / 1000000000000), orderedInterval (6465101194 / 1000000000000) (6465102181 / 1000000000000))
    | 11 => (orderedInterval (115908082 / 1000000000000) (115908083 / 1000000000000), orderedInterval (33575727611 / 1000000000000) (33575727612 / 1000000000000))
    | 12 => (orderedInterval (20132282670 / 1000000000000) (20132282671 / 1000000000000), orderedInterval (28287768889 / 1000000000000) (28287768890 / 1000000000000))
    | 13 => (orderedInterval (13282039424 / 1000000000000) (13282039425 / 1000000000000), orderedInterval (38896637102 / 1000000000000) (38896637103 / 1000000000000))
    | 14 => (orderedInterval (17798120730 / 1000000000000) (17798120731 / 1000000000000), orderedInterval (34247408392 / 1000000000000) (34247408393 / 1000000000000))
    | 15 => (orderedInterval (-41743219975 / 1000000000000) (-41743218457 / 1000000000000), orderedInterval (6842945724 / 1000000000000) (6842947241 / 1000000000000))
    | 16 => (orderedInterval (40409976535 / 1000000000000) (40409976536 / 1000000000000), orderedInterval (19717713222 / 1000000000000) (19717713223 / 1000000000000))
    | 17 => (orderedInterval (-31674239367 / 1000000000000) (-31674239366 / 1000000000000), orderedInterval (-19804162793 / 1000000000000) (-19804162792 / 1000000000000))
    | 18 => (orderedInterval (50242369761 / 1000000000000) (50242369886 / 1000000000000), orderedInterval (-918023373 / 1000000000000) (-918023248 / 1000000000000))
    | 19 => (orderedInterval (42394591884 / 1000000000000) (42394591885 / 1000000000000), orderedInterval (34270450507 / 1000000000000) (34270450508 / 1000000000000))
    | 20 => (orderedInterval (36636248550 / 1000000000000) (36636256169 / 1000000000000), orderedInterval (-58598741800 / 1000000000000) (-58598734181 / 1000000000000))
    | 21 => (orderedInterval (-41353187503 / 1000000000000) (-41353187502 / 1000000000000), orderedInterval (-84215963848 / 1000000000000) (-84215963847 / 1000000000000))
    | 22 => (orderedInterval (55085312499 / 1000000000000) (55085312500 / 1000000000000), orderedInterval (14869701109 / 1000000000000) (14869701111 / 1000000000000))
    | 23 => (orderedInterval (-19623623946 / 1000000000000) (-19623623945 / 1000000000000), orderedInterval (-44709899119 / 1000000000000) (-44709899118 / 1000000000000))
    | 24 => (orderedInterval (32190784975 / 1000000000000) (32190784976 / 1000000000000), orderedInterval (67752721345 / 1000000000000) (67752721346 / 1000000000000))
    | 25 => (orderedInterval (16498296431 / 1000000000000) (16498296432 / 1000000000000), orderedInterval (33399915897 / 1000000000000) (33399915898 / 1000000000000))
    | _ => (orderedInterval (-36749889797 / 1000000000000) (-36749780283 / 1000000000000), orderedInterval (27057364285 / 1000000000000) (27057473800 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13656688594 / 1000000000000) (13656736040 / 1000000000000)
      | 1 => orderedInterval (49121118 / 1000000000000) (49121163 / 1000000000000)
      | 2 => orderedInterval (2077297616 / 1000000000000) (2077297869 / 1000000000000)
      | 3 => orderedInterval (1628819123 / 1000000000000) (1628826394 / 1000000000000)
      | 4 => orderedInterval (802469126 / 1000000000000) (802469156 / 1000000000000)
      | 5 => orderedInterval (-3605551257 / 1000000000000) (-3605551215 / 1000000000000)
      | 6 => orderedInterval (-9240204279 / 1000000000000) (-9240203949 / 1000000000000)
      | 7 => orderedInterval (1017810912 / 1000000000000) (1017810942 / 1000000000000)
      | _ => orderedInterval (5746299571 / 1000000000000) (5746320188 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10221544458 / 1000000000000) (-10221495829 / 1000000000000)
      | 1 => orderedInterval (3655481813 / 1000000000000) (3655481855 / 1000000000000)
      | 2 => orderedInterval (-465239184 / 1000000000000) (-465238804 / 1000000000000)
      | 3 => orderedInterval (3626757113 / 1000000000000) (3626773287 / 1000000000000)
      | 4 => orderedInterval (4225236733 / 1000000000000) (4225236781 / 1000000000000)
      | 5 => orderedInterval (-2263023067 / 1000000000000) (-2263023007 / 1000000000000)
      | 6 => orderedInterval (-2566791121 / 1000000000000) (-2566790908 / 1000000000000)
      | 7 => orderedInterval (3893292085 / 1000000000000) (3893292112 / 1000000000000)
      | _ => orderedInterval (-11173852817 / 1000000000000) (-11173827200 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12653495948 / 1000000000000) (-12653445715 / 1000000000000)
      | 1 => orderedInterval (-4252781198 / 1000000000000) (-4252781146 / 1000000000000)
      | 2 => orderedInterval (-6405968251 / 1000000000000) (-6405967674 / 1000000000000)
      | 3 => orderedInterval (-19095748618 / 1000000000000) (-19095712496 / 1000000000000)
      | 4 => orderedInterval (-1012419744 / 1000000000000) (-1012419664 / 1000000000000)
      | 5 => orderedInterval (7550781422 / 1000000000000) (7550781510 / 1000000000000)
      | 6 => orderedInterval (9867796033 / 1000000000000) (9867796183 / 1000000000000)
      | 7 => orderedInterval (-1056382144 / 1000000000000) (-1056382117 / 1000000000000)
      | _ => orderedInterval (-5988414393 / 1000000000000) (-5988382451 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (9655232950 / 1000000000000) (9655284863 / 1000000000000)
      | 1 => orderedInterval (-7906251309 / 1000000000000) (-7906251236 / 1000000000000)
      | 2 => orderedInterval (987247924 / 1000000000000) (987248807 / 1000000000000)
      | 3 => orderedInterval (-18708786760 / 1000000000000) (-18708706126 / 1000000000000)
      | 4 => orderedInterval (-7197120094 / 1000000000000) (-7197119960 / 1000000000000)
      | 5 => orderedInterval (5279572076 / 1000000000000) (5279572208 / 1000000000000)
      | 6 => orderedInterval (1372006462 / 1000000000000) (1372006577 / 1000000000000)
      | 7 => orderedInterval (-4204555935 / 1000000000000) (-4204555907 / 1000000000000)
      | _ => orderedInterval (27190018289 / 1000000000000) (27190058003 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (11283637481 / 1000000000000) (11283691607 / 1000000000000)
      | 1 => orderedInterval (12139354396 / 1000000000000) (12139354506 / 1000000000000)
      | 2 => orderedInterval (21414783259 / 1000000000000) (21414784636 / 1000000000000)
      | 3 => orderedInterval (113799297037 / 1000000000000) (113799477501 / 1000000000000)
      | 4 => orderedInterval (-1543019113 / 1000000000000) (-1543018880 / 1000000000000)
      | 5 => orderedInterval (-17742676679 / 1000000000000) (-17742676478 / 1000000000000)
      | 6 => orderedInterval (-10056643428 / 1000000000000) (-10056643331 / 1000000000000)
      | 7 => orderedInterval (1606966216 / 1000000000000) (1606966245 / 1000000000000)
      | _ => orderedInterval (141367586 / 1000000000000) (141417150 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (12132750524 / 1000000000000) (12132826588 / 1000000000000)
    | 1 => orderedInterval (-11289682903 / 1000000000000) (-11289591713 / 1000000000000)
    | 2 => orderedInterval (-33046632841 / 1000000000000) (-33046513570 / 1000000000000)
    | 3 => orderedInterval (6467363603 / 1000000000000) (6467537229 / 1000000000000)
    | _ => orderedInterval (131043066755 / 1000000000000) (131043352956 / 1000000000000)

theorem compactCertificate375_stateChecks0 :
    compactCertificate375.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (493 / 2)) (orderedInterval (39837613953 / 1000000000000) (39837718035 / 1000000000000), orderedInterval (-31633906992 / 1000000000000) (-31633802910 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (726283137315193 / 4000000000000)) (orderedInterval (8445656436 / 1000000000000) (8445656437 / 1000000000000), orderedInterval (58584448935 / 1000000000000) (58584448936 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (234865044178969 / 800000000000)) (orderedInterval (-37699405743 / 1000000000000) (-37699300523 / 1000000000000), orderedInterval (27399462248 / 1000000000000) (27399567468 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_stateChecks1 :
    compactCertificate375.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (211927608092651 / 4000000000000)) (orderedInterval (-38395253715 / 1000000000000) (-38395253714 / 1000000000000), orderedInterval (-102311955166 / 1000000000000) (-102311955165 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (569267365420847 / 4000000000000)) (orderedInterval (-66039665301 / 1000000000000) (-66039664901 / 1000000000000), orderedInterval (10814695700 / 1000000000000) (10814696100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1545671635390899 / 4000000000000)) (orderedInterval (-28749383307 / 1000000000000) (-28749383306 / 1000000000000), orderedInterval (-28615257267 / 1000000000000) (-28615257266 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_stateChecks2 :
    compactCertificate375.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1138534730842187 / 4000000000000)) (orderedInterval (21261747521 / 1000000000000) (21261748716 / 1000000000000), orderedInterval (-42281503237 / 1000000000000) (-42281502041 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1950898667000951 / 4000000000000)) (orderedInterval (-36127608309 / 1000000000000) (-36127607867 / 1000000000000), orderedInterval (-246535348 / 1000000000000) (-246534906 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1437023128247909 / 4000000000000)) (orderedInterval (39845108160 / 1000000000000) (39845117486 / 1000000000000), orderedInterval (-13635488316 / 1000000000000) (-13635478990 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_stateChecks3 :
    compactCertificate375.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2204763025814507 / 4000000000000)) (orderedInterval (-27532504325 / 1000000000000) (-27532464367 / 1000000000000), orderedInterval (19948610767 / 1000000000000) (19948650724 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1272920526453203 / 4000000000000)) (orderedInterval (-44267322699 / 1000000000000) (-44267321712 / 1000000000000), orderedInterval (6465101194 / 1000000000000) (6465102181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2258819811812527 / 4000000000000)) (orderedInterval (115908082 / 1000000000000) (115908083 / 1000000000000), orderedInterval (33575727611 / 1000000000000) (33575727612 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_stateChecks4 :
    compactCertificate375.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2110482474594763 / 4000000000000)) (orderedInterval (20132282670 / 1000000000000) (20132282671 / 1000000000000), orderedInterval (28287768889 / 1000000000000) (28287768890 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1506139878408379 / 4000000000000)) (orderedInterval (13282039424 / 1000000000000) (13282039425 / 1000000000000), orderedInterval (38896637102 / 1000000000000) (38896637103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1707802096262541 / 4000000000000)) (orderedInterval (17798120730 / 1000000000000) (17798120731 / 1000000000000), orderedInterval (34247408392 / 1000000000000) (34247408393 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_stateChecks5 :
    compactCertificate375.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1423787340544829 / 4000000000000)) (orderedInterval (-41743219975 / 1000000000000) (-41743218457 / 1000000000000), orderedInterval (6842945724 / 1000000000000) (6842947241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1257959294509409 / 4000000000000)) (orderedInterval (40409976535 / 1000000000000) (40409976536 / 1000000000000), orderedInterval (19717713222 / 1000000000000) (19717713223 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (364605634867491 / 800000000000)) (orderedInterval (-31674239367 / 1000000000000) (-31674239366 / 1000000000000), orderedInterval (-19804162793 / 1000000000000) (-19804162792 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_stateChecks6 :
    compactCertificate375.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1008518374186777 / 4000000000000)) (orderedInterval (50242369761 / 1000000000000) (50242369886 / 1000000000000), orderedInterval (-918023373 / 1000000000000) (-918023248 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (854932194833297 / 4000000000000)) (orderedInterval (42394591884 / 1000000000000) (42394591885 / 1000000000000), orderedInterval (34270450507 / 1000000000000) (34270450508 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (534976871752091 / 4000000000000)) (orderedInterval (36636248550 / 1000000000000) (36636256169 / 1000000000000), orderedInterval (-58598741800 / 1000000000000) (-58598734181 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_stateChecks7 :
    compactCertificate375.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (287712340880997 / 4000000000000)) (orderedInterval (-41353187503 / 1000000000000) (-41353187502 / 1000000000000), orderedInterval (-84215963848 / 1000000000000) (-84215963847 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (781194973513991 / 4000000000000)) (orderedInterval (55085312499 / 1000000000000) (55085312500 / 1000000000000), orderedInterval (14869701109 / 1000000000000) (14869701111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1066654949920807 / 4000000000000)) (orderedInterval (-19623623946 / 1000000000000) (-19623623945 / 1000000000000), orderedInterval (-44709899119 / 1000000000000) (-44709899118 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_stateChecks8 :
    compactCertificate375.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (451023128247909 / 4000000000000)) (orderedInterval (32190784975 / 1000000000000) (32190784976 / 1000000000000), orderedInterval (67752721345 / 1000000000000) (67752721346 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1833383976272389 / 4000000000000)) (orderedInterval (16498296431 / 1000000000000) (16498296432 / 1000000000000), orderedInterval (33399915897 / 1000000000000) (33399915898 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1224615529686251 / 4000000000000)) (orderedInterval (-36749889797 / 1000000000000) (-36749780283 / 1000000000000), orderedInterval (27057364285 / 1000000000000) (27057473800 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_states : ∀ j,
    BesselStateValid (compactCertificate375.point j) (compactCertificate375.state j) :=
  compactCertificate375.statesValid_of_checks3 compactCertificate375_stateChecks0
    compactCertificate375_stateChecks1 compactCertificate375_stateChecks2
    compactCertificate375_stateChecks3 compactCertificate375_stateChecks4
    compactCertificate375_stateChecks5 compactCertificate375_stateChecks6
    compactCertificate375_stateChecks7 compactCertificate375_stateChecks8

theorem compactCertificate375_chunkChecks0_0 :
    compactCertificate375.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (493 / 2) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39837613953 / 1000000000000) (39837718035 / 1000000000000), orderedInterval (-31633906992 / 1000000000000) (-31633802910 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (726283137315193 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8445656436 / 1000000000000) (8445656437 / 1000000000000), orderedInterval (58584448935 / 1000000000000) (58584448936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (234865044178969 / 800000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37699405743 / 1000000000000) (-37699300523 / 1000000000000), orderedInterval (27399462248 / 1000000000000) (27399567468 / 1000000000000)))) (orderedInterval (13656688594 / 1000000000000) (13656736040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (211927608092651 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38395253715 / 1000000000000) (-38395253714 / 1000000000000), orderedInterval (-102311955166 / 1000000000000) (-102311955165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (569267365420847 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-66039665301 / 1000000000000) (-66039664901 / 1000000000000), orderedInterval (10814695700 / 1000000000000) (10814696100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1545671635390899 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28749383307 / 1000000000000) (-28749383306 / 1000000000000), orderedInterval (-28615257267 / 1000000000000) (-28615257266 / 1000000000000)))) (orderedInterval (49121118 / 1000000000000) (49121163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1138534730842187 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21261747521 / 1000000000000) (21261748716 / 1000000000000), orderedInterval (-42281503237 / 1000000000000) (-42281502041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1950898667000951 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-36127608309 / 1000000000000) (-36127607867 / 1000000000000), orderedInterval (-246535348 / 1000000000000) (-246534906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1437023128247909 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39845108160 / 1000000000000) (39845117486 / 1000000000000), orderedInterval (-13635488316 / 1000000000000) (-13635478990 / 1000000000000)))) (orderedInterval (2077297616 / 1000000000000) (2077297869 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_chunkChecks0_1 :
    compactCertificate375.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2204763025814507 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27532504325 / 1000000000000) (-27532464367 / 1000000000000), orderedInterval (19948610767 / 1000000000000) (19948650724 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1272920526453203 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-44267322699 / 1000000000000) (-44267321712 / 1000000000000), orderedInterval (6465101194 / 1000000000000) (6465102181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2258819811812527 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (115908082 / 1000000000000) (115908083 / 1000000000000), orderedInterval (33575727611 / 1000000000000) (33575727612 / 1000000000000)))) (orderedInterval (1628819123 / 1000000000000) (1628826394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2110482474594763 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20132282670 / 1000000000000) (20132282671 / 1000000000000), orderedInterval (28287768889 / 1000000000000) (28287768890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1506139878408379 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13282039424 / 1000000000000) (13282039425 / 1000000000000), orderedInterval (38896637102 / 1000000000000) (38896637103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1707802096262541 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17798120730 / 1000000000000) (17798120731 / 1000000000000), orderedInterval (34247408392 / 1000000000000) (34247408393 / 1000000000000)))) (orderedInterval (802469126 / 1000000000000) (802469156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1423787340544829 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41743219975 / 1000000000000) (-41743218457 / 1000000000000), orderedInterval (6842945724 / 1000000000000) (6842947241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1257959294509409 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (40409976535 / 1000000000000) (40409976536 / 1000000000000), orderedInterval (19717713222 / 1000000000000) (19717713223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (364605634867491 / 800000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31674239367 / 1000000000000) (-31674239366 / 1000000000000), orderedInterval (-19804162793 / 1000000000000) (-19804162792 / 1000000000000)))) (orderedInterval (-3605551257 / 1000000000000) (-3605551215 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_chunkChecks0_2 :
    compactCertificate375.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1008518374186777 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50242369761 / 1000000000000) (50242369886 / 1000000000000), orderedInterval (-918023373 / 1000000000000) (-918023248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (854932194833297 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42394591884 / 1000000000000) (42394591885 / 1000000000000), orderedInterval (34270450507 / 1000000000000) (34270450508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (534976871752091 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36636248550 / 1000000000000) (36636256169 / 1000000000000), orderedInterval (-58598741800 / 1000000000000) (-58598734181 / 1000000000000)))) (orderedInterval (-9240204279 / 1000000000000) (-9240203949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (287712340880997 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41353187503 / 1000000000000) (-41353187502 / 1000000000000), orderedInterval (-84215963848 / 1000000000000) (-84215963847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (781194973513991 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (55085312499 / 1000000000000) (55085312500 / 1000000000000), orderedInterval (14869701109 / 1000000000000) (14869701111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1066654949920807 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19623623946 / 1000000000000) (-19623623945 / 1000000000000), orderedInterval (-44709899119 / 1000000000000) (-44709899118 / 1000000000000)))) (orderedInterval (1017810912 / 1000000000000) (1017810942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (451023128247909 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32190784975 / 1000000000000) (32190784976 / 1000000000000), orderedInterval (67752721345 / 1000000000000) (67752721346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1833383976272389 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16498296431 / 1000000000000) (16498296432 / 1000000000000), orderedInterval (33399915897 / 1000000000000) (33399915898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1224615529686251 / 4000000000000) 0 (IntervalRat.scale (493 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36749889797 / 1000000000000) (-36749780283 / 1000000000000), orderedInterval (27057364285 / 1000000000000) (27057473800 / 1000000000000)))) (orderedInterval (5746299571 / 1000000000000) (5746320188 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_chunkChecks0 :
    compactCertificate375.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate375.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate375_chunkChecks0_0
    compactCertificate375_chunkChecks0_1 compactCertificate375_chunkChecks0_2

theorem compactCertificate375_chunkChecks1_0 :
    compactCertificate375.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (493 / 2) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39837613953 / 1000000000000) (39837718035 / 1000000000000), orderedInterval (-31633906992 / 1000000000000) (-31633802910 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (726283137315193 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8445656436 / 1000000000000) (8445656437 / 1000000000000), orderedInterval (58584448935 / 1000000000000) (58584448936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (234865044178969 / 800000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37699405743 / 1000000000000) (-37699300523 / 1000000000000), orderedInterval (27399462248 / 1000000000000) (27399567468 / 1000000000000)))) (orderedInterval (-10221544458 / 1000000000000) (-10221495829 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (211927608092651 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38395253715 / 1000000000000) (-38395253714 / 1000000000000), orderedInterval (-102311955166 / 1000000000000) (-102311955165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (569267365420847 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-66039665301 / 1000000000000) (-66039664901 / 1000000000000), orderedInterval (10814695700 / 1000000000000) (10814696100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1545671635390899 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28749383307 / 1000000000000) (-28749383306 / 1000000000000), orderedInterval (-28615257267 / 1000000000000) (-28615257266 / 1000000000000)))) (orderedInterval (3655481813 / 1000000000000) (3655481855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1138534730842187 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21261747521 / 1000000000000) (21261748716 / 1000000000000), orderedInterval (-42281503237 / 1000000000000) (-42281502041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1950898667000951 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-36127608309 / 1000000000000) (-36127607867 / 1000000000000), orderedInterval (-246535348 / 1000000000000) (-246534906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1437023128247909 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39845108160 / 1000000000000) (39845117486 / 1000000000000), orderedInterval (-13635488316 / 1000000000000) (-13635478990 / 1000000000000)))) (orderedInterval (-465239184 / 1000000000000) (-465238804 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_chunkChecks1_1 :
    compactCertificate375.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2204763025814507 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27532504325 / 1000000000000) (-27532464367 / 1000000000000), orderedInterval (19948610767 / 1000000000000) (19948650724 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1272920526453203 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-44267322699 / 1000000000000) (-44267321712 / 1000000000000), orderedInterval (6465101194 / 1000000000000) (6465102181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2258819811812527 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (115908082 / 1000000000000) (115908083 / 1000000000000), orderedInterval (33575727611 / 1000000000000) (33575727612 / 1000000000000)))) (orderedInterval (3626757113 / 1000000000000) (3626773287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2110482474594763 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20132282670 / 1000000000000) (20132282671 / 1000000000000), orderedInterval (28287768889 / 1000000000000) (28287768890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1506139878408379 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13282039424 / 1000000000000) (13282039425 / 1000000000000), orderedInterval (38896637102 / 1000000000000) (38896637103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1707802096262541 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17798120730 / 1000000000000) (17798120731 / 1000000000000), orderedInterval (34247408392 / 1000000000000) (34247408393 / 1000000000000)))) (orderedInterval (4225236733 / 1000000000000) (4225236781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1423787340544829 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41743219975 / 1000000000000) (-41743218457 / 1000000000000), orderedInterval (6842945724 / 1000000000000) (6842947241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1257959294509409 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (40409976535 / 1000000000000) (40409976536 / 1000000000000), orderedInterval (19717713222 / 1000000000000) (19717713223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (364605634867491 / 800000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31674239367 / 1000000000000) (-31674239366 / 1000000000000), orderedInterval (-19804162793 / 1000000000000) (-19804162792 / 1000000000000)))) (orderedInterval (-2263023067 / 1000000000000) (-2263023007 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_chunkChecks1_2 :
    compactCertificate375.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1008518374186777 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50242369761 / 1000000000000) (50242369886 / 1000000000000), orderedInterval (-918023373 / 1000000000000) (-918023248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (854932194833297 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42394591884 / 1000000000000) (42394591885 / 1000000000000), orderedInterval (34270450507 / 1000000000000) (34270450508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (534976871752091 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36636248550 / 1000000000000) (36636256169 / 1000000000000), orderedInterval (-58598741800 / 1000000000000) (-58598734181 / 1000000000000)))) (orderedInterval (-2566791121 / 1000000000000) (-2566790908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (287712340880997 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41353187503 / 1000000000000) (-41353187502 / 1000000000000), orderedInterval (-84215963848 / 1000000000000) (-84215963847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (781194973513991 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (55085312499 / 1000000000000) (55085312500 / 1000000000000), orderedInterval (14869701109 / 1000000000000) (14869701111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1066654949920807 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19623623946 / 1000000000000) (-19623623945 / 1000000000000), orderedInterval (-44709899119 / 1000000000000) (-44709899118 / 1000000000000)))) (orderedInterval (3893292085 / 1000000000000) (3893292112 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (451023128247909 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32190784975 / 1000000000000) (32190784976 / 1000000000000), orderedInterval (67752721345 / 1000000000000) (67752721346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1833383976272389 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16498296431 / 1000000000000) (16498296432 / 1000000000000), orderedInterval (33399915897 / 1000000000000) (33399915898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1224615529686251 / 4000000000000) 1 (IntervalRat.scale (493 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36749889797 / 1000000000000) (-36749780283 / 1000000000000), orderedInterval (27057364285 / 1000000000000) (27057473800 / 1000000000000)))) (orderedInterval (-11173852817 / 1000000000000) (-11173827200 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_chunkChecks1 :
    compactCertificate375.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate375.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate375_chunkChecks1_0
    compactCertificate375_chunkChecks1_1 compactCertificate375_chunkChecks1_2

theorem compactCertificate375_chunkChecks2_0 :
    compactCertificate375.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (493 / 2) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39837613953 / 1000000000000) (39837718035 / 1000000000000), orderedInterval (-31633906992 / 1000000000000) (-31633802910 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (726283137315193 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8445656436 / 1000000000000) (8445656437 / 1000000000000), orderedInterval (58584448935 / 1000000000000) (58584448936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (234865044178969 / 800000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37699405743 / 1000000000000) (-37699300523 / 1000000000000), orderedInterval (27399462248 / 1000000000000) (27399567468 / 1000000000000)))) (orderedInterval (-12653495948 / 1000000000000) (-12653445715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (211927608092651 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38395253715 / 1000000000000) (-38395253714 / 1000000000000), orderedInterval (-102311955166 / 1000000000000) (-102311955165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (569267365420847 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-66039665301 / 1000000000000) (-66039664901 / 1000000000000), orderedInterval (10814695700 / 1000000000000) (10814696100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1545671635390899 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28749383307 / 1000000000000) (-28749383306 / 1000000000000), orderedInterval (-28615257267 / 1000000000000) (-28615257266 / 1000000000000)))) (orderedInterval (-4252781198 / 1000000000000) (-4252781146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1138534730842187 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21261747521 / 1000000000000) (21261748716 / 1000000000000), orderedInterval (-42281503237 / 1000000000000) (-42281502041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1950898667000951 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-36127608309 / 1000000000000) (-36127607867 / 1000000000000), orderedInterval (-246535348 / 1000000000000) (-246534906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1437023128247909 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39845108160 / 1000000000000) (39845117486 / 1000000000000), orderedInterval (-13635488316 / 1000000000000) (-13635478990 / 1000000000000)))) (orderedInterval (-6405968251 / 1000000000000) (-6405967674 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_chunkChecks2_1 :
    compactCertificate375.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2204763025814507 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27532504325 / 1000000000000) (-27532464367 / 1000000000000), orderedInterval (19948610767 / 1000000000000) (19948650724 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1272920526453203 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-44267322699 / 1000000000000) (-44267321712 / 1000000000000), orderedInterval (6465101194 / 1000000000000) (6465102181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2258819811812527 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (115908082 / 1000000000000) (115908083 / 1000000000000), orderedInterval (33575727611 / 1000000000000) (33575727612 / 1000000000000)))) (orderedInterval (-19095748618 / 1000000000000) (-19095712496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2110482474594763 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20132282670 / 1000000000000) (20132282671 / 1000000000000), orderedInterval (28287768889 / 1000000000000) (28287768890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1506139878408379 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13282039424 / 1000000000000) (13282039425 / 1000000000000), orderedInterval (38896637102 / 1000000000000) (38896637103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1707802096262541 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17798120730 / 1000000000000) (17798120731 / 1000000000000), orderedInterval (34247408392 / 1000000000000) (34247408393 / 1000000000000)))) (orderedInterval (-1012419744 / 1000000000000) (-1012419664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1423787340544829 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41743219975 / 1000000000000) (-41743218457 / 1000000000000), orderedInterval (6842945724 / 1000000000000) (6842947241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1257959294509409 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (40409976535 / 1000000000000) (40409976536 / 1000000000000), orderedInterval (19717713222 / 1000000000000) (19717713223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (364605634867491 / 800000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31674239367 / 1000000000000) (-31674239366 / 1000000000000), orderedInterval (-19804162793 / 1000000000000) (-19804162792 / 1000000000000)))) (orderedInterval (7550781422 / 1000000000000) (7550781510 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_chunkChecks2_2 :
    compactCertificate375.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1008518374186777 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50242369761 / 1000000000000) (50242369886 / 1000000000000), orderedInterval (-918023373 / 1000000000000) (-918023248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (854932194833297 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42394591884 / 1000000000000) (42394591885 / 1000000000000), orderedInterval (34270450507 / 1000000000000) (34270450508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (534976871752091 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36636248550 / 1000000000000) (36636256169 / 1000000000000), orderedInterval (-58598741800 / 1000000000000) (-58598734181 / 1000000000000)))) (orderedInterval (9867796033 / 1000000000000) (9867796183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (287712340880997 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41353187503 / 1000000000000) (-41353187502 / 1000000000000), orderedInterval (-84215963848 / 1000000000000) (-84215963847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (781194973513991 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (55085312499 / 1000000000000) (55085312500 / 1000000000000), orderedInterval (14869701109 / 1000000000000) (14869701111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1066654949920807 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19623623946 / 1000000000000) (-19623623945 / 1000000000000), orderedInterval (-44709899119 / 1000000000000) (-44709899118 / 1000000000000)))) (orderedInterval (-1056382144 / 1000000000000) (-1056382117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (451023128247909 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32190784975 / 1000000000000) (32190784976 / 1000000000000), orderedInterval (67752721345 / 1000000000000) (67752721346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1833383976272389 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16498296431 / 1000000000000) (16498296432 / 1000000000000), orderedInterval (33399915897 / 1000000000000) (33399915898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1224615529686251 / 4000000000000) 2 (IntervalRat.scale (493 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36749889797 / 1000000000000) (-36749780283 / 1000000000000), orderedInterval (27057364285 / 1000000000000) (27057473800 / 1000000000000)))) (orderedInterval (-5988414393 / 1000000000000) (-5988382451 / 1000000000000))) = true
  rfl'

theorem compactCertificate375_chunkChecks2 :
    compactCertificate375.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate375.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate375_chunkChecks2_0
    compactCertificate375_chunkChecks2_1 compactCertificate375_chunkChecks2_2

theorem compactCertificate375_chunkChecks3_0 :
    compactCertificate375.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (493 / 2) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39837613953 / 1000000000000) (39837718035 / 1000000000000), orderedInterval (-31633906992 / 1000000000000) (-31633802910 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (726283137315193 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8445656436 / 1000000000000) (8445656437 / 1000000000000), orderedInterval (58584448935 / 1000000000000) (58584448936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (234865044178969 / 800000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37699405743 / 1000000000000) (-37699300523 / 1000000000000), orderedInterval (27399462248 / 1000000000000) (27399567468 / 1000000000000)))) (orderedInterval (9655232950 / 1000000000000) (9655284863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (211927608092651 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38395253715 / 1000000000000) (-38395253714 / 1000000000000), orderedInterval (-102311955166 / 1000000000000) (-102311955165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (569267365420847 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-66039665301 / 1000000000000) (-66039664901 / 1000000000000), orderedInterval (10814695700 / 1000000000000) (10814696100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1545671635390899 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28749383307 / 1000000000000) (-28749383306 / 1000000000000), orderedInterval (-28615257267 / 1000000000000) (-28615257266 / 1000000000000)))) (orderedInterval (-7906251309 / 1000000000000) (-7906251236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1138534730842187 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21261747521 / 1000000000000) (21261748716 / 1000000000000), orderedInterval (-42281503237 / 1000000000000) (-42281502041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1950898667000951 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-36127608309 / 1000000000000) (-36127607867 / 1000000000000), orderedInterval (-246535348 / 1000000000000) (-246534906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1437023128247909 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39845108160 / 1000000000000) (39845117486 / 1000000000000), orderedInterval (-13635488316 / 1000000000000) (-13635478990 / 1000000000000)))) (orderedInterval (987247924 / 1000000000000) (987248807 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate375_chunkChecks3_1 :
    compactCertificate375.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2204763025814507 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27532504325 / 1000000000000) (-27532464367 / 1000000000000), orderedInterval (19948610767 / 1000000000000) (19948650724 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1272920526453203 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-44267322699 / 1000000000000) (-44267321712 / 1000000000000), orderedInterval (6465101194 / 1000000000000) (6465102181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2258819811812527 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (115908082 / 1000000000000) (115908083 / 1000000000000), orderedInterval (33575727611 / 1000000000000) (33575727612 / 1000000000000)))) (orderedInterval (-18708786760 / 1000000000000) (-18708706126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2110482474594763 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20132282670 / 1000000000000) (20132282671 / 1000000000000), orderedInterval (28287768889 / 1000000000000) (28287768890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1506139878408379 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13282039424 / 1000000000000) (13282039425 / 1000000000000), orderedInterval (38896637102 / 1000000000000) (38896637103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1707802096262541 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17798120730 / 1000000000000) (17798120731 / 1000000000000), orderedInterval (34247408392 / 1000000000000) (34247408393 / 1000000000000)))) (orderedInterval (-7197120094 / 1000000000000) (-7197119960 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1423787340544829 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41743219975 / 1000000000000) (-41743218457 / 1000000000000), orderedInterval (6842945724 / 1000000000000) (6842947241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1257959294509409 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (40409976535 / 1000000000000) (40409976536 / 1000000000000), orderedInterval (19717713222 / 1000000000000) (19717713223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (364605634867491 / 800000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31674239367 / 1000000000000) (-31674239366 / 1000000000000), orderedInterval (-19804162793 / 1000000000000) (-19804162792 / 1000000000000)))) (orderedInterval (5279572076 / 1000000000000) (5279572208 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate375_chunkChecks3_2 :
    compactCertificate375.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1008518374186777 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50242369761 / 1000000000000) (50242369886 / 1000000000000), orderedInterval (-918023373 / 1000000000000) (-918023248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (854932194833297 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42394591884 / 1000000000000) (42394591885 / 1000000000000), orderedInterval (34270450507 / 1000000000000) (34270450508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (534976871752091 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36636248550 / 1000000000000) (36636256169 / 1000000000000), orderedInterval (-58598741800 / 1000000000000) (-58598734181 / 1000000000000)))) (orderedInterval (1372006462 / 1000000000000) (1372006577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (287712340880997 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41353187503 / 1000000000000) (-41353187502 / 1000000000000), orderedInterval (-84215963848 / 1000000000000) (-84215963847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (781194973513991 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (55085312499 / 1000000000000) (55085312500 / 1000000000000), orderedInterval (14869701109 / 1000000000000) (14869701111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1066654949920807 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19623623946 / 1000000000000) (-19623623945 / 1000000000000), orderedInterval (-44709899119 / 1000000000000) (-44709899118 / 1000000000000)))) (orderedInterval (-4204555935 / 1000000000000) (-4204555907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (451023128247909 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32190784975 / 1000000000000) (32190784976 / 1000000000000), orderedInterval (67752721345 / 1000000000000) (67752721346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1833383976272389 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16498296431 / 1000000000000) (16498296432 / 1000000000000), orderedInterval (33399915897 / 1000000000000) (33399915898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1224615529686251 / 4000000000000) 3 (IntervalRat.scale (493 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36749889797 / 1000000000000) (-36749780283 / 1000000000000), orderedInterval (27057364285 / 1000000000000) (27057473800 / 1000000000000)))) (orderedInterval (27190018289 / 1000000000000) (27190058003 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate375_chunkChecks3 :
    compactCertificate375.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate375.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate375_chunkChecks3_0
    compactCertificate375_chunkChecks3_1 compactCertificate375_chunkChecks3_2

theorem compactCertificate375_chunkChecks4_0 :
    compactCertificate375.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (493 / 2) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (39837613953 / 1000000000000) (39837718035 / 1000000000000), orderedInterval (-31633906992 / 1000000000000) (-31633802910 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (726283137315193 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8445656436 / 1000000000000) (8445656437 / 1000000000000), orderedInterval (58584448935 / 1000000000000) (58584448936 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (234865044178969 / 800000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37699405743 / 1000000000000) (-37699300523 / 1000000000000), orderedInterval (27399462248 / 1000000000000) (27399567468 / 1000000000000)))) (orderedInterval (11283637481 / 1000000000000) (11283691607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (211927608092651 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38395253715 / 1000000000000) (-38395253714 / 1000000000000), orderedInterval (-102311955166 / 1000000000000) (-102311955165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (569267365420847 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-66039665301 / 1000000000000) (-66039664901 / 1000000000000), orderedInterval (10814695700 / 1000000000000) (10814696100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1545671635390899 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28749383307 / 1000000000000) (-28749383306 / 1000000000000), orderedInterval (-28615257267 / 1000000000000) (-28615257266 / 1000000000000)))) (orderedInterval (12139354396 / 1000000000000) (12139354506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1138534730842187 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (21261747521 / 1000000000000) (21261748716 / 1000000000000), orderedInterval (-42281503237 / 1000000000000) (-42281502041 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1950898667000951 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-36127608309 / 1000000000000) (-36127607867 / 1000000000000), orderedInterval (-246535348 / 1000000000000) (-246534906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1437023128247909 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (39845108160 / 1000000000000) (39845117486 / 1000000000000), orderedInterval (-13635488316 / 1000000000000) (-13635478990 / 1000000000000)))) (orderedInterval (21414783259 / 1000000000000) (21414784636 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate375_chunkChecks4_1 :
    compactCertificate375.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2204763025814507 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-27532504325 / 1000000000000) (-27532464367 / 1000000000000), orderedInterval (19948610767 / 1000000000000) (19948650724 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1272920526453203 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-44267322699 / 1000000000000) (-44267321712 / 1000000000000), orderedInterval (6465101194 / 1000000000000) (6465102181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2258819811812527 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (115908082 / 1000000000000) (115908083 / 1000000000000), orderedInterval (33575727611 / 1000000000000) (33575727612 / 1000000000000)))) (orderedInterval (113799297037 / 1000000000000) (113799477501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2110482474594763 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20132282670 / 1000000000000) (20132282671 / 1000000000000), orderedInterval (28287768889 / 1000000000000) (28287768890 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1506139878408379 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (13282039424 / 1000000000000) (13282039425 / 1000000000000), orderedInterval (38896637102 / 1000000000000) (38896637103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1707802096262541 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (17798120730 / 1000000000000) (17798120731 / 1000000000000), orderedInterval (34247408392 / 1000000000000) (34247408393 / 1000000000000)))) (orderedInterval (-1543019113 / 1000000000000) (-1543018880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1423787340544829 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-41743219975 / 1000000000000) (-41743218457 / 1000000000000), orderedInterval (6842945724 / 1000000000000) (6842947241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1257959294509409 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (40409976535 / 1000000000000) (40409976536 / 1000000000000), orderedInterval (19717713222 / 1000000000000) (19717713223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (364605634867491 / 800000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31674239367 / 1000000000000) (-31674239366 / 1000000000000), orderedInterval (-19804162793 / 1000000000000) (-19804162792 / 1000000000000)))) (orderedInterval (-17742676679 / 1000000000000) (-17742676478 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate375_chunkChecks4_2 :
    compactCertificate375.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1008518374186777 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50242369761 / 1000000000000) (50242369886 / 1000000000000), orderedInterval (-918023373 / 1000000000000) (-918023248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (854932194833297 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42394591884 / 1000000000000) (42394591885 / 1000000000000), orderedInterval (34270450507 / 1000000000000) (34270450508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (534976871752091 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36636248550 / 1000000000000) (36636256169 / 1000000000000), orderedInterval (-58598741800 / 1000000000000) (-58598734181 / 1000000000000)))) (orderedInterval (-10056643428 / 1000000000000) (-10056643331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (287712340880997 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41353187503 / 1000000000000) (-41353187502 / 1000000000000), orderedInterval (-84215963848 / 1000000000000) (-84215963847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (781194973513991 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (55085312499 / 1000000000000) (55085312500 / 1000000000000), orderedInterval (14869701109 / 1000000000000) (14869701111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1066654949920807 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19623623946 / 1000000000000) (-19623623945 / 1000000000000), orderedInterval (-44709899119 / 1000000000000) (-44709899118 / 1000000000000)))) (orderedInterval (1606966216 / 1000000000000) (1606966245 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (451023128247909 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32190784975 / 1000000000000) (32190784976 / 1000000000000), orderedInterval (67752721345 / 1000000000000) (67752721346 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1833383976272389 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (16498296431 / 1000000000000) (16498296432 / 1000000000000), orderedInterval (33399915897 / 1000000000000) (33399915898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1224615529686251 / 4000000000000) 4 (IntervalRat.scale (493 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36749889797 / 1000000000000) (-36749780283 / 1000000000000), orderedInterval (27057364285 / 1000000000000) (27057473800 / 1000000000000)))) (orderedInterval (141367586 / 1000000000000) (141417150 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate375_chunkChecks4 :
    compactCertificate375.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate375.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate375_chunkChecks4_0
    compactCertificate375_chunkChecks4_1 compactCertificate375_chunkChecks4_2

theorem compactCertificate375_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate375.chunkCheck r b = true :=
  compactCertificate375.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate375_chunkChecks0
    · exact compactCertificate375_chunkChecks1
    · exact compactCertificate375_chunkChecks2
    · exact compactCertificate375_chunkChecks3
    · exact compactCertificate375_chunkChecks4)

theorem compactCertificate375_coefficient0 :
    compactCertificate375.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate375_coefficient1 :
    compactCertificate375.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate375_coefficient2 :
    compactCertificate375.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate375_coefficient3 :
    compactCertificate375.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate375_coefficient4 :
    compactCertificate375.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate375_coefficients : ∀ r : Fin 5,
    compactCertificate375.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate375_coefficient0
  · exact compactCertificate375_coefficient1
  · exact compactCertificate375_coefficient2
  · exact compactCertificate375_coefficient3
  · exact compactCertificate375_coefficient4

theorem compactCertificate375_lower : (1 : ℚ) ≤ compactCertificate375.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate375, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate375_proves {t : ℝ} (ht : t ∈ compactCertificate375.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate375.proves compactCertificate375_states compactCertificate375_chunks
    compactCertificate375_coefficients compactCertificate375_lower ht

end Erdos232
