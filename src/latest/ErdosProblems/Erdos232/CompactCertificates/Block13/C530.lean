/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate530 : CompactCertificate where
  left := 401
  right := 402
  center := 803 / 2
  grid := fun i =>
    match i.val with
    | 0 => 128
    | 1 => 94
    | 2 => 152
    | 3 => 27
    | 4 => 74
    | 5 => 200
    | 6 => 148
    | 7 => 253
    | 8 => 186
    | 9 => 286
    | 10 => 165
    | 11 => 293
    | 12 => 274
    | 13 => 195
    | 14 => 221
    | 15 => 185
    | 16 => 163
    | 17 => 236
    | 18 => 131
    | 19 => 111
    | 20 => 69
    | 21 => 37
    | 22 => 101
    | 23 => 138
    | 24 => 58
    | 25 => 238
    | _ => 159
  point := fun i =>
    match i.val with
    | 0 => 803 / 2
    | 1 => 1182972331164503 / 4000000000000
    | 2 => 382548946198199 / 800000000000
    | 3 => 345188375858821 / 4000000000000
    | 4 => 927224532318337 / 4000000000000
    | 5 => 2517594976103229 / 4000000000000
    | 6 => 1854449064637477 / 4000000000000
    | 7 => 3177630080328121 / 4000000000000
    | 8 => 2340627935056939 / 4000000000000
    | 9 => 3591125171864197 / 4000000000000
    | 10 => 2073337084669213 / 4000000000000
    | 11 => 3679173040335617 / 4000000000000
    | 12 => 3437560704055973 / 4000000000000
    | 13 => 2453205522032309 / 4000000000000
    | 14 => 2781673596955011 / 4000000000000
    | 15 => 2319069441090259 / 4000000000000
    | 16 => 2048968181523439 / 4000000000000
    | 17 => 593870841376461 / 800000000000
    | 18 => 1642678000957367 / 4000000000000
    | 19 => 1392516333572287 / 4000000000000
    | 20 => 871372064943061 / 4000000000000
    | 21 => 468626794578987 / 4000000000000
    | 22 => 1272412908177961 / 4000000000000
    | 23 => 1737371044191497 / 4000000000000
    | 24 => 734627935056939 / 4000000000000
    | 25 => 2986221770683019 / 4000000000000
    | _ => 1994657749164421 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (6392227154 / 1000000000000) (6392227155 / 1000000000000), orderedInterval (39295271205 / 1000000000000) (39295271206 / 1000000000000))
    | 1 => (orderedInterval (43544260720 / 1000000000000) (43544260722 / 1000000000000), orderedInterval (15942182672 / 1000000000000) (15942182673 / 1000000000000))
    | 2 => (orderedInterval (36218022945 / 1000000000000) (36218023035 / 1000000000000), orderedInterval (4386615907 / 1000000000000) (4386615997 / 1000000000000))
    | 3 => (orderedInterval (-66392029924 / 1000000000000) (-66391957494 / 1000000000000), orderedInterval (54874522976 / 1000000000000) (54874595406 / 1000000000000))
    | 4 => (orderedInterval (5916292836 / 1000000000000) (5916292837 / 1000000000000), orderedInterval (52057857980 / 1000000000000) (52057857982 / 1000000000000))
    | 5 => (orderedInterval (30433337376 / 1000000000000) (30433362574 / 1000000000000), orderedInterval (-9259112973 / 1000000000000) (-9259087775 / 1000000000000))
    | 6 => (orderedInterval (-19630979603 / 1000000000000) (-19630978387 / 1000000000000), orderedInterval (31450422682 / 1000000000000) (31450423897 / 1000000000000))
    | 7 => (orderedInterval (-10232062421 / 1000000000000) (-10232062420 / 1000000000000), orderedInterval (-26388291162 / 1000000000000) (-26388291161 / 1000000000000))
    | 8 => (orderedInterval (32963673817 / 1000000000000) (32963675171 / 1000000000000), orderedInterval (-1186935836 / 1000000000000) (-1186934482 / 1000000000000))
    | 9 => (orderedInterval (1890477472 / 1000000000000) (1890477473 / 1000000000000), orderedInterval (26560754484 / 1000000000000) (26560754485 / 1000000000000))
    | 10 => (orderedInterval (-24058268965 / 1000000000000) (-24058268964 / 1000000000000), orderedInterval (-25460176605 / 1000000000000) (-25460176604 / 1000000000000))
    | 11 => (orderedInterval (-2413683873 / 1000000000000) (-2413683872 / 1000000000000), orderedInterval (-26196164489 / 1000000000000) (-26196164488 / 1000000000000))
    | 12 => (orderedInterval (-15835422672 / 1000000000000) (-15835422456 / 1000000000000), orderedInterval (22145614482 / 1000000000000) (22145614699 / 1000000000000))
    | 13 => (orderedInterval (-32073698089 / 1000000000000) (-32073697761 / 1000000000000), orderedInterval (-3023222262 / 1000000000000) (-3023221934 / 1000000000000))
    | 14 => (orderedInterval (-28515830243 / 1000000000000) (-28515778476 / 1000000000000), orderedInterval (10134686145 / 1000000000000) (10134737912 / 1000000000000))
    | 15 => (orderedInterval (19844981897 / 1000000000000) (19844983520 / 1000000000000), orderedInterval (-26554589058 / 1000000000000) (-26554587436 / 1000000000000))
    | 16 => (orderedInterval (-28626390619 / 1000000000000) (-28626390618 / 1000000000000), orderedInterval (-20547286380 / 1000000000000) (-20547286379 / 1000000000000))
    | 17 => (orderedInterval (29009708007 / 1000000000000) (29009717596 / 1000000000000), orderedInterval (-4022444106 / 1000000000000) (-4022434518 / 1000000000000))
    | 18 => (orderedInterval (3697281833 / 1000000000000) (3697281836 / 1000000000000), orderedInterval (-39203111501 / 1000000000000) (-39203111499 / 1000000000000))
    | 19 => (orderedInterval (-8384127758 / 1000000000000) (-8384127757 / 1000000000000), orderedInterval (-41921202787 / 1000000000000) (-41921202786 / 1000000000000))
    | 20 => (orderedInterval (-51845494300 / 1000000000000) (-51845491444 / 1000000000000), orderedInterval (15429678364 / 1000000000000) (15429681220 / 1000000000000))
    | 21 => (orderedInterval (-73080221648 / 1000000000000) (-73080221410 / 1000000000000), orderedInterval (9963330683 / 1000000000000) (9963330921 / 1000000000000))
    | 22 => (orderedInterval (-44729709333 / 1000000000000) (-44729709134 / 1000000000000), orderedInterval (811900865 / 1000000000000) (811901063 / 1000000000000))
    | 23 => (orderedInterval (38278834966 / 1000000000000) (38278835397 / 1000000000000), orderedInterval (-705930682 / 1000000000000) (-705930250 / 1000000000000))
    | 24 => (orderedInterval (46564216177 / 1000000000000) (46564301970 / 1000000000000), orderedInterval (-36156221335 / 1000000000000) (-36156135541 / 1000000000000))
    | 25 => (orderedInterval (-10242688253 / 1000000000000) (-10242688242 / 1000000000000), orderedInterval (27353345533 / 1000000000000) (27353345544 / 1000000000000))
    | _ => (orderedInterval (2272591391 / 1000000000000) (2272591393 / 1000000000000), orderedInterval (-35660175431 / 1000000000000) (-35660175429 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5064717966 / 1000000000000) (5064718000 / 1000000000000)
      | 1 => orderedInterval (-1227176996 / 1000000000000) (-1227174370 / 1000000000000)
      | 2 => orderedInterval (1112264691 / 1000000000000) (1112264747 / 1000000000000)
      | 3 => orderedInterval (-2461554240 / 1000000000000) (-2461554080 / 1000000000000)
      | 4 => orderedInterval (-2602796331 / 1000000000000) (-2602795986 / 1000000000000)
      | 5 => orderedInterval (2610119606 / 1000000000000) (2610119909 / 1000000000000)
      | 6 => orderedInterval (-1804470327 / 1000000000000) (-1804470132 / 1000000000000)
      | 7 => orderedInterval (-569435137 / 1000000000000) (-569435047 / 1000000000000)
      | _ => orderedInterval (688078906 / 1000000000000) (688079536 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15991268335 / 1000000000000) (15991268373 / 1000000000000)
      | 1 => orderedInterval (2001266303 / 1000000000000) (2001269335 / 1000000000000)
      | 2 => orderedInterval (1568614665 / 1000000000000) (1568614753 / 1000000000000)
      | 3 => orderedInterval (-21519641693 / 1000000000000) (-21519641362 / 1000000000000)
      | 4 => orderedInterval (-1381272990 / 1000000000000) (-1381272403 / 1000000000000)
      | 5 => orderedInterval (866962735 / 1000000000000) (866963272 / 1000000000000)
      | 6 => orderedInterval (8741313617 / 1000000000000) (8741313761 / 1000000000000)
      | 7 => orderedInterval (-9749494 / 1000000000000) (-9749409 / 1000000000000)
      | _ => orderedInterval (4070094027 / 1000000000000) (4070094422 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-5808346563 / 1000000000000) (-5808346519 / 1000000000000)
      | 1 => orderedInterval (5206365514 / 1000000000000) (5206370036 / 1000000000000)
      | 2 => orderedInterval (-2931621475 / 1000000000000) (-2931621335 / 1000000000000)
      | 3 => orderedInterval (6504793999 / 1000000000000) (6504794708 / 1000000000000)
      | 4 => orderedInterval (5337718639 / 1000000000000) (5337719645 / 1000000000000)
      | 5 => orderedInterval (-5685637000 / 1000000000000) (-5685636037 / 1000000000000)
      | 6 => orderedInterval (736816880 / 1000000000000) (736816997 / 1000000000000)
      | 7 => orderedInterval (2681353207 / 1000000000000) (2681353292 / 1000000000000)
      | _ => orderedInterval (-2293830702 / 1000000000000) (-2293830359 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16054946331 / 1000000000000) (-16054946280 / 1000000000000)
      | 1 => orderedInterval (-2908530718 / 1000000000000) (-2908523685 / 1000000000000)
      | 2 => orderedInterval (-6208453979 / 1000000000000) (-6208453750 / 1000000000000)
      | 3 => orderedInterval (101581467498 / 1000000000000) (101581469051 / 1000000000000)
      | 4 => orderedInterval (5192761147 / 1000000000000) (5192762878 / 1000000000000)
      | 5 => orderedInterval (-853463302 / 1000000000000) (-853461564 / 1000000000000)
      | 6 => orderedInterval (-8336373588 / 1000000000000) (-8336373486 / 1000000000000)
      | 7 => orderedInterval (-61440862 / 1000000000000) (-61440773 / 1000000000000)
      | _ => orderedInterval (1522256856 / 1000000000000) (1522257268 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (7009349814 / 1000000000000) (7009349875 / 1000000000000)
      | 1 => orderedInterval (-13025185427 / 1000000000000) (-13025174398 / 1000000000000)
      | 2 => orderedInterval (8462166907 / 1000000000000) (8462167290 / 1000000000000)
      | 3 => orderedInterval (-23305989470 / 1000000000000) (-23305986022 / 1000000000000)
      | 4 => orderedInterval (-9239293340 / 1000000000000) (-9239290346 / 1000000000000)
      | 5 => orderedInterval (14020849725 / 1000000000000) (14020852886 / 1000000000000)
      | 6 => orderedInterval (-483571874 / 1000000000000) (-483571780 / 1000000000000)
      | 7 => orderedInterval (-3607911715 / 1000000000000) (-3607911620 / 1000000000000)
      | _ => orderedInterval (8956821621 / 1000000000000) (8956822227 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (809748138 / 1000000000000) (809752577 / 1000000000000)
    | 1 => orderedInterval (10328855505 / 1000000000000) (10328860742 / 1000000000000)
    | 2 => orderedInterval (3747612499 / 1000000000000) (3747620428 / 1000000000000)
    | 3 => orderedInterval (73873276721 / 1000000000000) (73873289659 / 1000000000000)
    | _ => orderedInterval (-11212763759 / 1000000000000) (-11212741888 / 1000000000000)

theorem compactCertificate530_stateChecks0 :
    compactCertificate530.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (803 / 2)) (orderedInterval (6392227154 / 1000000000000) (6392227155 / 1000000000000), orderedInterval (39295271205 / 1000000000000) (39295271206 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1182972331164503 / 4000000000000)) (orderedInterval (43544260720 / 1000000000000) (43544260722 / 1000000000000), orderedInterval (15942182672 / 1000000000000) (15942182673 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (382548946198199 / 800000000000)) (orderedInterval (36218022945 / 1000000000000) (36218023035 / 1000000000000), orderedInterval (4386615907 / 1000000000000) (4386615997 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_stateChecks1 :
    compactCertificate530.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (345188375858821 / 4000000000000)) (orderedInterval (-66392029924 / 1000000000000) (-66391957494 / 1000000000000), orderedInterval (54874522976 / 1000000000000) (54874595406 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (927224532318337 / 4000000000000)) (orderedInterval (5916292836 / 1000000000000) (5916292837 / 1000000000000), orderedInterval (52057857980 / 1000000000000) (52057857982 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2517594976103229 / 4000000000000)) (orderedInterval (30433337376 / 1000000000000) (30433362574 / 1000000000000), orderedInterval (-9259112973 / 1000000000000) (-9259087775 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_stateChecks2 :
    compactCertificate530.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1854449064637477 / 4000000000000)) (orderedInterval (-19630979603 / 1000000000000) (-19630978387 / 1000000000000), orderedInterval (31450422682 / 1000000000000) (31450423897 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (3177630080328121 / 4000000000000)) (orderedInterval (-10232062421 / 1000000000000) (-10232062420 / 1000000000000), orderedInterval (-26388291162 / 1000000000000) (-26388291161 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2340627935056939 / 4000000000000)) (orderedInterval (32963673817 / 1000000000000) (32963675171 / 1000000000000), orderedInterval (-1186935836 / 1000000000000) (-1186934482 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_stateChecks3 :
    compactCertificate530.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 286 12 (3591125171864197 / 4000000000000)) (orderedInterval (1890477472 / 1000000000000) (1890477473 / 1000000000000), orderedInterval (26560754484 / 1000000000000) (26560754485 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2073337084669213 / 4000000000000)) (orderedInterval (-24058268965 / 1000000000000) (-24058268964 / 1000000000000), orderedInterval (-25460176605 / 1000000000000) (-25460176604 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 293 12 (3679173040335617 / 4000000000000)) (orderedInterval (-2413683873 / 1000000000000) (-2413683872 / 1000000000000), orderedInterval (-26196164489 / 1000000000000) (-26196164488 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_stateChecks4 :
    compactCertificate530.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (3437560704055973 / 4000000000000)) (orderedInterval (-15835422672 / 1000000000000) (-15835422456 / 1000000000000), orderedInterval (22145614482 / 1000000000000) (22145614699 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2453205522032309 / 4000000000000)) (orderedInterval (-32073698089 / 1000000000000) (-32073697761 / 1000000000000), orderedInterval (-3023222262 / 1000000000000) (-3023221934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2781673596955011 / 4000000000000)) (orderedInterval (-28515830243 / 1000000000000) (-28515778476 / 1000000000000), orderedInterval (10134686145 / 1000000000000) (10134737912 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_stateChecks5 :
    compactCertificate530.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2319069441090259 / 4000000000000)) (orderedInterval (19844981897 / 1000000000000) (19844983520 / 1000000000000), orderedInterval (-26554589058 / 1000000000000) (-26554587436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2048968181523439 / 4000000000000)) (orderedInterval (-28626390619 / 1000000000000) (-28626390618 / 1000000000000), orderedInterval (-20547286380 / 1000000000000) (-20547286379 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (593870841376461 / 800000000000)) (orderedInterval (29009708007 / 1000000000000) (29009717596 / 1000000000000), orderedInterval (-4022444106 / 1000000000000) (-4022434518 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_stateChecks6 :
    compactCertificate530.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1642678000957367 / 4000000000000)) (orderedInterval (3697281833 / 1000000000000) (3697281836 / 1000000000000), orderedInterval (-39203111501 / 1000000000000) (-39203111499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1392516333572287 / 4000000000000)) (orderedInterval (-8384127758 / 1000000000000) (-8384127757 / 1000000000000), orderedInterval (-41921202787 / 1000000000000) (-41921202786 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (871372064943061 / 4000000000000)) (orderedInterval (-51845494300 / 1000000000000) (-51845491444 / 1000000000000), orderedInterval (15429678364 / 1000000000000) (15429681220 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_stateChecks7 :
    compactCertificate530.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (468626794578987 / 4000000000000)) (orderedInterval (-73080221648 / 1000000000000) (-73080221410 / 1000000000000), orderedInterval (9963330683 / 1000000000000) (9963330921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1272412908177961 / 4000000000000)) (orderedInterval (-44729709333 / 1000000000000) (-44729709134 / 1000000000000), orderedInterval (811900865 / 1000000000000) (811901063 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1737371044191497 / 4000000000000)) (orderedInterval (38278834966 / 1000000000000) (38278835397 / 1000000000000), orderedInterval (-705930682 / 1000000000000) (-705930250 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_stateChecks8 :
    compactCertificate530.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (734627935056939 / 4000000000000)) (orderedInterval (46564216177 / 1000000000000) (46564301970 / 1000000000000), orderedInterval (-36156221335 / 1000000000000) (-36156135541 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (2986221770683019 / 4000000000000)) (orderedInterval (-10242688253 / 1000000000000) (-10242688242 / 1000000000000), orderedInterval (27353345533 / 1000000000000) (27353345544 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1994657749164421 / 4000000000000)) (orderedInterval (2272591391 / 1000000000000) (2272591393 / 1000000000000), orderedInterval (-35660175431 / 1000000000000) (-35660175429 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_states : ∀ j,
    BesselStateValid (compactCertificate530.point j) (compactCertificate530.state j) :=
  compactCertificate530.statesValid_of_checks3 compactCertificate530_stateChecks0
    compactCertificate530_stateChecks1 compactCertificate530_stateChecks2
    compactCertificate530_stateChecks3 compactCertificate530_stateChecks4
    compactCertificate530_stateChecks5 compactCertificate530_stateChecks6
    compactCertificate530_stateChecks7 compactCertificate530_stateChecks8

theorem compactCertificate530_chunkChecks0_0 :
    compactCertificate530.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (803 / 2) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6392227154 / 1000000000000) (6392227155 / 1000000000000), orderedInterval (39295271205 / 1000000000000) (39295271206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1182972331164503 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43544260720 / 1000000000000) (43544260722 / 1000000000000), orderedInterval (15942182672 / 1000000000000) (15942182673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (382548946198199 / 800000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36218022945 / 1000000000000) (36218023035 / 1000000000000), orderedInterval (4386615907 / 1000000000000) (4386615997 / 1000000000000)))) (orderedInterval (5064717966 / 1000000000000) (5064718000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (345188375858821 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66392029924 / 1000000000000) (-66391957494 / 1000000000000), orderedInterval (54874522976 / 1000000000000) (54874595406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (927224532318337 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (5916292836 / 1000000000000) (5916292837 / 1000000000000), orderedInterval (52057857980 / 1000000000000) (52057857982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2517594976103229 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30433337376 / 1000000000000) (30433362574 / 1000000000000), orderedInterval (-9259112973 / 1000000000000) (-9259087775 / 1000000000000)))) (orderedInterval (-1227176996 / 1000000000000) (-1227174370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1854449064637477 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19630979603 / 1000000000000) (-19630978387 / 1000000000000), orderedInterval (31450422682 / 1000000000000) (31450423897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3177630080328121 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10232062421 / 1000000000000) (-10232062420 / 1000000000000), orderedInterval (-26388291162 / 1000000000000) (-26388291161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2340627935056939 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32963673817 / 1000000000000) (32963675171 / 1000000000000), orderedInterval (-1186935836 / 1000000000000) (-1186934482 / 1000000000000)))) (orderedInterval (1112264691 / 1000000000000) (1112264747 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_chunkChecks0_1 :
    compactCertificate530.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3591125171864197 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1890477472 / 1000000000000) (1890477473 / 1000000000000), orderedInterval (26560754484 / 1000000000000) (26560754485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2073337084669213 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24058268965 / 1000000000000) (-24058268964 / 1000000000000), orderedInterval (-25460176605 / 1000000000000) (-25460176604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3679173040335617 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2413683873 / 1000000000000) (-2413683872 / 1000000000000), orderedInterval (-26196164489 / 1000000000000) (-26196164488 / 1000000000000)))) (orderedInterval (-2461554240 / 1000000000000) (-2461554080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3437560704055973 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15835422672 / 1000000000000) (-15835422456 / 1000000000000), orderedInterval (22145614482 / 1000000000000) (22145614699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2453205522032309 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32073698089 / 1000000000000) (-32073697761 / 1000000000000), orderedInterval (-3023222262 / 1000000000000) (-3023221934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2781673596955011 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28515830243 / 1000000000000) (-28515778476 / 1000000000000), orderedInterval (10134686145 / 1000000000000) (10134737912 / 1000000000000)))) (orderedInterval (-2602796331 / 1000000000000) (-2602795986 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2319069441090259 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19844981897 / 1000000000000) (19844983520 / 1000000000000), orderedInterval (-26554589058 / 1000000000000) (-26554587436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2048968181523439 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28626390619 / 1000000000000) (-28626390618 / 1000000000000), orderedInterval (-20547286380 / 1000000000000) (-20547286379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (593870841376461 / 800000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29009708007 / 1000000000000) (29009717596 / 1000000000000), orderedInterval (-4022444106 / 1000000000000) (-4022434518 / 1000000000000)))) (orderedInterval (2610119606 / 1000000000000) (2610119909 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_chunkChecks0_2 :
    compactCertificate530.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1642678000957367 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3697281833 / 1000000000000) (3697281836 / 1000000000000), orderedInterval (-39203111501 / 1000000000000) (-39203111499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1392516333572287 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8384127758 / 1000000000000) (-8384127757 / 1000000000000), orderedInterval (-41921202787 / 1000000000000) (-41921202786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (871372064943061 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51845494300 / 1000000000000) (-51845491444 / 1000000000000), orderedInterval (15429678364 / 1000000000000) (15429681220 / 1000000000000)))) (orderedInterval (-1804470327 / 1000000000000) (-1804470132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (468626794578987 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73080221648 / 1000000000000) (-73080221410 / 1000000000000), orderedInterval (9963330683 / 1000000000000) (9963330921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1272412908177961 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44729709333 / 1000000000000) (-44729709134 / 1000000000000), orderedInterval (811900865 / 1000000000000) (811901063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1737371044191497 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38278834966 / 1000000000000) (38278835397 / 1000000000000), orderedInterval (-705930682 / 1000000000000) (-705930250 / 1000000000000)))) (orderedInterval (-569435137 / 1000000000000) (-569435047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (734627935056939 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46564216177 / 1000000000000) (46564301970 / 1000000000000), orderedInterval (-36156221335 / 1000000000000) (-36156135541 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2986221770683019 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10242688253 / 1000000000000) (-10242688242 / 1000000000000), orderedInterval (27353345533 / 1000000000000) (27353345544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1994657749164421 / 4000000000000) 0 (IntervalRat.scale (803 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2272591391 / 1000000000000) (2272591393 / 1000000000000), orderedInterval (-35660175431 / 1000000000000) (-35660175429 / 1000000000000)))) (orderedInterval (688078906 / 1000000000000) (688079536 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_chunkChecks0 :
    compactCertificate530.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate530.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate530_chunkChecks0_0
    compactCertificate530_chunkChecks0_1 compactCertificate530_chunkChecks0_2

theorem compactCertificate530_chunkChecks1_0 :
    compactCertificate530.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (803 / 2) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6392227154 / 1000000000000) (6392227155 / 1000000000000), orderedInterval (39295271205 / 1000000000000) (39295271206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1182972331164503 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43544260720 / 1000000000000) (43544260722 / 1000000000000), orderedInterval (15942182672 / 1000000000000) (15942182673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (382548946198199 / 800000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36218022945 / 1000000000000) (36218023035 / 1000000000000), orderedInterval (4386615907 / 1000000000000) (4386615997 / 1000000000000)))) (orderedInterval (15991268335 / 1000000000000) (15991268373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (345188375858821 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66392029924 / 1000000000000) (-66391957494 / 1000000000000), orderedInterval (54874522976 / 1000000000000) (54874595406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (927224532318337 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (5916292836 / 1000000000000) (5916292837 / 1000000000000), orderedInterval (52057857980 / 1000000000000) (52057857982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2517594976103229 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30433337376 / 1000000000000) (30433362574 / 1000000000000), orderedInterval (-9259112973 / 1000000000000) (-9259087775 / 1000000000000)))) (orderedInterval (2001266303 / 1000000000000) (2001269335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1854449064637477 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19630979603 / 1000000000000) (-19630978387 / 1000000000000), orderedInterval (31450422682 / 1000000000000) (31450423897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3177630080328121 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10232062421 / 1000000000000) (-10232062420 / 1000000000000), orderedInterval (-26388291162 / 1000000000000) (-26388291161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2340627935056939 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32963673817 / 1000000000000) (32963675171 / 1000000000000), orderedInterval (-1186935836 / 1000000000000) (-1186934482 / 1000000000000)))) (orderedInterval (1568614665 / 1000000000000) (1568614753 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_chunkChecks1_1 :
    compactCertificate530.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3591125171864197 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1890477472 / 1000000000000) (1890477473 / 1000000000000), orderedInterval (26560754484 / 1000000000000) (26560754485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2073337084669213 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24058268965 / 1000000000000) (-24058268964 / 1000000000000), orderedInterval (-25460176605 / 1000000000000) (-25460176604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3679173040335617 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2413683873 / 1000000000000) (-2413683872 / 1000000000000), orderedInterval (-26196164489 / 1000000000000) (-26196164488 / 1000000000000)))) (orderedInterval (-21519641693 / 1000000000000) (-21519641362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3437560704055973 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15835422672 / 1000000000000) (-15835422456 / 1000000000000), orderedInterval (22145614482 / 1000000000000) (22145614699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2453205522032309 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32073698089 / 1000000000000) (-32073697761 / 1000000000000), orderedInterval (-3023222262 / 1000000000000) (-3023221934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2781673596955011 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28515830243 / 1000000000000) (-28515778476 / 1000000000000), orderedInterval (10134686145 / 1000000000000) (10134737912 / 1000000000000)))) (orderedInterval (-1381272990 / 1000000000000) (-1381272403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2319069441090259 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19844981897 / 1000000000000) (19844983520 / 1000000000000), orderedInterval (-26554589058 / 1000000000000) (-26554587436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2048968181523439 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28626390619 / 1000000000000) (-28626390618 / 1000000000000), orderedInterval (-20547286380 / 1000000000000) (-20547286379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (593870841376461 / 800000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29009708007 / 1000000000000) (29009717596 / 1000000000000), orderedInterval (-4022444106 / 1000000000000) (-4022434518 / 1000000000000)))) (orderedInterval (866962735 / 1000000000000) (866963272 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_chunkChecks1_2 :
    compactCertificate530.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1642678000957367 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3697281833 / 1000000000000) (3697281836 / 1000000000000), orderedInterval (-39203111501 / 1000000000000) (-39203111499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1392516333572287 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8384127758 / 1000000000000) (-8384127757 / 1000000000000), orderedInterval (-41921202787 / 1000000000000) (-41921202786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (871372064943061 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51845494300 / 1000000000000) (-51845491444 / 1000000000000), orderedInterval (15429678364 / 1000000000000) (15429681220 / 1000000000000)))) (orderedInterval (8741313617 / 1000000000000) (8741313761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (468626794578987 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73080221648 / 1000000000000) (-73080221410 / 1000000000000), orderedInterval (9963330683 / 1000000000000) (9963330921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1272412908177961 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44729709333 / 1000000000000) (-44729709134 / 1000000000000), orderedInterval (811900865 / 1000000000000) (811901063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1737371044191497 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38278834966 / 1000000000000) (38278835397 / 1000000000000), orderedInterval (-705930682 / 1000000000000) (-705930250 / 1000000000000)))) (orderedInterval (-9749494 / 1000000000000) (-9749409 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (734627935056939 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46564216177 / 1000000000000) (46564301970 / 1000000000000), orderedInterval (-36156221335 / 1000000000000) (-36156135541 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2986221770683019 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10242688253 / 1000000000000) (-10242688242 / 1000000000000), orderedInterval (27353345533 / 1000000000000) (27353345544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1994657749164421 / 4000000000000) 1 (IntervalRat.scale (803 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2272591391 / 1000000000000) (2272591393 / 1000000000000), orderedInterval (-35660175431 / 1000000000000) (-35660175429 / 1000000000000)))) (orderedInterval (4070094027 / 1000000000000) (4070094422 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_chunkChecks1 :
    compactCertificate530.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate530.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate530_chunkChecks1_0
    compactCertificate530_chunkChecks1_1 compactCertificate530_chunkChecks1_2

theorem compactCertificate530_chunkChecks2_0 :
    compactCertificate530.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (803 / 2) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6392227154 / 1000000000000) (6392227155 / 1000000000000), orderedInterval (39295271205 / 1000000000000) (39295271206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1182972331164503 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43544260720 / 1000000000000) (43544260722 / 1000000000000), orderedInterval (15942182672 / 1000000000000) (15942182673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (382548946198199 / 800000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36218022945 / 1000000000000) (36218023035 / 1000000000000), orderedInterval (4386615907 / 1000000000000) (4386615997 / 1000000000000)))) (orderedInterval (-5808346563 / 1000000000000) (-5808346519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (345188375858821 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66392029924 / 1000000000000) (-66391957494 / 1000000000000), orderedInterval (54874522976 / 1000000000000) (54874595406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (927224532318337 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (5916292836 / 1000000000000) (5916292837 / 1000000000000), orderedInterval (52057857980 / 1000000000000) (52057857982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2517594976103229 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30433337376 / 1000000000000) (30433362574 / 1000000000000), orderedInterval (-9259112973 / 1000000000000) (-9259087775 / 1000000000000)))) (orderedInterval (5206365514 / 1000000000000) (5206370036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1854449064637477 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19630979603 / 1000000000000) (-19630978387 / 1000000000000), orderedInterval (31450422682 / 1000000000000) (31450423897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3177630080328121 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10232062421 / 1000000000000) (-10232062420 / 1000000000000), orderedInterval (-26388291162 / 1000000000000) (-26388291161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2340627935056939 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32963673817 / 1000000000000) (32963675171 / 1000000000000), orderedInterval (-1186935836 / 1000000000000) (-1186934482 / 1000000000000)))) (orderedInterval (-2931621475 / 1000000000000) (-2931621335 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_chunkChecks2_1 :
    compactCertificate530.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3591125171864197 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1890477472 / 1000000000000) (1890477473 / 1000000000000), orderedInterval (26560754484 / 1000000000000) (26560754485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2073337084669213 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24058268965 / 1000000000000) (-24058268964 / 1000000000000), orderedInterval (-25460176605 / 1000000000000) (-25460176604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3679173040335617 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2413683873 / 1000000000000) (-2413683872 / 1000000000000), orderedInterval (-26196164489 / 1000000000000) (-26196164488 / 1000000000000)))) (orderedInterval (6504793999 / 1000000000000) (6504794708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3437560704055973 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15835422672 / 1000000000000) (-15835422456 / 1000000000000), orderedInterval (22145614482 / 1000000000000) (22145614699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2453205522032309 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32073698089 / 1000000000000) (-32073697761 / 1000000000000), orderedInterval (-3023222262 / 1000000000000) (-3023221934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2781673596955011 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28515830243 / 1000000000000) (-28515778476 / 1000000000000), orderedInterval (10134686145 / 1000000000000) (10134737912 / 1000000000000)))) (orderedInterval (5337718639 / 1000000000000) (5337719645 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2319069441090259 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19844981897 / 1000000000000) (19844983520 / 1000000000000), orderedInterval (-26554589058 / 1000000000000) (-26554587436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2048968181523439 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28626390619 / 1000000000000) (-28626390618 / 1000000000000), orderedInterval (-20547286380 / 1000000000000) (-20547286379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (593870841376461 / 800000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29009708007 / 1000000000000) (29009717596 / 1000000000000), orderedInterval (-4022444106 / 1000000000000) (-4022434518 / 1000000000000)))) (orderedInterval (-5685637000 / 1000000000000) (-5685636037 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_chunkChecks2_2 :
    compactCertificate530.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1642678000957367 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3697281833 / 1000000000000) (3697281836 / 1000000000000), orderedInterval (-39203111501 / 1000000000000) (-39203111499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1392516333572287 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8384127758 / 1000000000000) (-8384127757 / 1000000000000), orderedInterval (-41921202787 / 1000000000000) (-41921202786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (871372064943061 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51845494300 / 1000000000000) (-51845491444 / 1000000000000), orderedInterval (15429678364 / 1000000000000) (15429681220 / 1000000000000)))) (orderedInterval (736816880 / 1000000000000) (736816997 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (468626794578987 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73080221648 / 1000000000000) (-73080221410 / 1000000000000), orderedInterval (9963330683 / 1000000000000) (9963330921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1272412908177961 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44729709333 / 1000000000000) (-44729709134 / 1000000000000), orderedInterval (811900865 / 1000000000000) (811901063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1737371044191497 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38278834966 / 1000000000000) (38278835397 / 1000000000000), orderedInterval (-705930682 / 1000000000000) (-705930250 / 1000000000000)))) (orderedInterval (2681353207 / 1000000000000) (2681353292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (734627935056939 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46564216177 / 1000000000000) (46564301970 / 1000000000000), orderedInterval (-36156221335 / 1000000000000) (-36156135541 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2986221770683019 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10242688253 / 1000000000000) (-10242688242 / 1000000000000), orderedInterval (27353345533 / 1000000000000) (27353345544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1994657749164421 / 4000000000000) 2 (IntervalRat.scale (803 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2272591391 / 1000000000000) (2272591393 / 1000000000000), orderedInterval (-35660175431 / 1000000000000) (-35660175429 / 1000000000000)))) (orderedInterval (-2293830702 / 1000000000000) (-2293830359 / 1000000000000))) = true
  rfl'

theorem compactCertificate530_chunkChecks2 :
    compactCertificate530.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate530.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate530_chunkChecks2_0
    compactCertificate530_chunkChecks2_1 compactCertificate530_chunkChecks2_2

theorem compactCertificate530_chunkChecks3_0 :
    compactCertificate530.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (803 / 2) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6392227154 / 1000000000000) (6392227155 / 1000000000000), orderedInterval (39295271205 / 1000000000000) (39295271206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1182972331164503 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43544260720 / 1000000000000) (43544260722 / 1000000000000), orderedInterval (15942182672 / 1000000000000) (15942182673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (382548946198199 / 800000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36218022945 / 1000000000000) (36218023035 / 1000000000000), orderedInterval (4386615907 / 1000000000000) (4386615997 / 1000000000000)))) (orderedInterval (-16054946331 / 1000000000000) (-16054946280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (345188375858821 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66392029924 / 1000000000000) (-66391957494 / 1000000000000), orderedInterval (54874522976 / 1000000000000) (54874595406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (927224532318337 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (5916292836 / 1000000000000) (5916292837 / 1000000000000), orderedInterval (52057857980 / 1000000000000) (52057857982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2517594976103229 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30433337376 / 1000000000000) (30433362574 / 1000000000000), orderedInterval (-9259112973 / 1000000000000) (-9259087775 / 1000000000000)))) (orderedInterval (-2908530718 / 1000000000000) (-2908523685 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1854449064637477 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19630979603 / 1000000000000) (-19630978387 / 1000000000000), orderedInterval (31450422682 / 1000000000000) (31450423897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3177630080328121 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10232062421 / 1000000000000) (-10232062420 / 1000000000000), orderedInterval (-26388291162 / 1000000000000) (-26388291161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2340627935056939 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32963673817 / 1000000000000) (32963675171 / 1000000000000), orderedInterval (-1186935836 / 1000000000000) (-1186934482 / 1000000000000)))) (orderedInterval (-6208453979 / 1000000000000) (-6208453750 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate530_chunkChecks3_1 :
    compactCertificate530.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3591125171864197 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1890477472 / 1000000000000) (1890477473 / 1000000000000), orderedInterval (26560754484 / 1000000000000) (26560754485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2073337084669213 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24058268965 / 1000000000000) (-24058268964 / 1000000000000), orderedInterval (-25460176605 / 1000000000000) (-25460176604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3679173040335617 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2413683873 / 1000000000000) (-2413683872 / 1000000000000), orderedInterval (-26196164489 / 1000000000000) (-26196164488 / 1000000000000)))) (orderedInterval (101581467498 / 1000000000000) (101581469051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3437560704055973 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15835422672 / 1000000000000) (-15835422456 / 1000000000000), orderedInterval (22145614482 / 1000000000000) (22145614699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2453205522032309 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32073698089 / 1000000000000) (-32073697761 / 1000000000000), orderedInterval (-3023222262 / 1000000000000) (-3023221934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2781673596955011 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28515830243 / 1000000000000) (-28515778476 / 1000000000000), orderedInterval (10134686145 / 1000000000000) (10134737912 / 1000000000000)))) (orderedInterval (5192761147 / 1000000000000) (5192762878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2319069441090259 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19844981897 / 1000000000000) (19844983520 / 1000000000000), orderedInterval (-26554589058 / 1000000000000) (-26554587436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2048968181523439 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28626390619 / 1000000000000) (-28626390618 / 1000000000000), orderedInterval (-20547286380 / 1000000000000) (-20547286379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (593870841376461 / 800000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29009708007 / 1000000000000) (29009717596 / 1000000000000), orderedInterval (-4022444106 / 1000000000000) (-4022434518 / 1000000000000)))) (orderedInterval (-853463302 / 1000000000000) (-853461564 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate530_chunkChecks3_2 :
    compactCertificate530.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1642678000957367 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3697281833 / 1000000000000) (3697281836 / 1000000000000), orderedInterval (-39203111501 / 1000000000000) (-39203111499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1392516333572287 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8384127758 / 1000000000000) (-8384127757 / 1000000000000), orderedInterval (-41921202787 / 1000000000000) (-41921202786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (871372064943061 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51845494300 / 1000000000000) (-51845491444 / 1000000000000), orderedInterval (15429678364 / 1000000000000) (15429681220 / 1000000000000)))) (orderedInterval (-8336373588 / 1000000000000) (-8336373486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (468626794578987 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73080221648 / 1000000000000) (-73080221410 / 1000000000000), orderedInterval (9963330683 / 1000000000000) (9963330921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1272412908177961 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44729709333 / 1000000000000) (-44729709134 / 1000000000000), orderedInterval (811900865 / 1000000000000) (811901063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1737371044191497 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38278834966 / 1000000000000) (38278835397 / 1000000000000), orderedInterval (-705930682 / 1000000000000) (-705930250 / 1000000000000)))) (orderedInterval (-61440862 / 1000000000000) (-61440773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (734627935056939 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46564216177 / 1000000000000) (46564301970 / 1000000000000), orderedInterval (-36156221335 / 1000000000000) (-36156135541 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2986221770683019 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10242688253 / 1000000000000) (-10242688242 / 1000000000000), orderedInterval (27353345533 / 1000000000000) (27353345544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1994657749164421 / 4000000000000) 3 (IntervalRat.scale (803 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2272591391 / 1000000000000) (2272591393 / 1000000000000), orderedInterval (-35660175431 / 1000000000000) (-35660175429 / 1000000000000)))) (orderedInterval (1522256856 / 1000000000000) (1522257268 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate530_chunkChecks3 :
    compactCertificate530.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate530.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate530_chunkChecks3_0
    compactCertificate530_chunkChecks3_1 compactCertificate530_chunkChecks3_2

theorem compactCertificate530_chunkChecks4_0 :
    compactCertificate530.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (803 / 2) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6392227154 / 1000000000000) (6392227155 / 1000000000000), orderedInterval (39295271205 / 1000000000000) (39295271206 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1182972331164503 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43544260720 / 1000000000000) (43544260722 / 1000000000000), orderedInterval (15942182672 / 1000000000000) (15942182673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (382548946198199 / 800000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (36218022945 / 1000000000000) (36218023035 / 1000000000000), orderedInterval (4386615907 / 1000000000000) (4386615997 / 1000000000000)))) (orderedInterval (7009349814 / 1000000000000) (7009349875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (345188375858821 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66392029924 / 1000000000000) (-66391957494 / 1000000000000), orderedInterval (54874522976 / 1000000000000) (54874595406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (927224532318337 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (5916292836 / 1000000000000) (5916292837 / 1000000000000), orderedInterval (52057857980 / 1000000000000) (52057857982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2517594976103229 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30433337376 / 1000000000000) (30433362574 / 1000000000000), orderedInterval (-9259112973 / 1000000000000) (-9259087775 / 1000000000000)))) (orderedInterval (-13025185427 / 1000000000000) (-13025174398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1854449064637477 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-19630979603 / 1000000000000) (-19630978387 / 1000000000000), orderedInterval (31450422682 / 1000000000000) (31450423897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3177630080328121 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10232062421 / 1000000000000) (-10232062420 / 1000000000000), orderedInterval (-26388291162 / 1000000000000) (-26388291161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2340627935056939 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32963673817 / 1000000000000) (32963675171 / 1000000000000), orderedInterval (-1186935836 / 1000000000000) (-1186934482 / 1000000000000)))) (orderedInterval (8462166907 / 1000000000000) (8462167290 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate530_chunkChecks4_1 :
    compactCertificate530.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3591125171864197 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (1890477472 / 1000000000000) (1890477473 / 1000000000000), orderedInterval (26560754484 / 1000000000000) (26560754485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2073337084669213 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24058268965 / 1000000000000) (-24058268964 / 1000000000000), orderedInterval (-25460176605 / 1000000000000) (-25460176604 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3679173040335617 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2413683873 / 1000000000000) (-2413683872 / 1000000000000), orderedInterval (-26196164489 / 1000000000000) (-26196164488 / 1000000000000)))) (orderedInterval (-23305989470 / 1000000000000) (-23305986022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3437560704055973 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15835422672 / 1000000000000) (-15835422456 / 1000000000000), orderedInterval (22145614482 / 1000000000000) (22145614699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2453205522032309 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32073698089 / 1000000000000) (-32073697761 / 1000000000000), orderedInterval (-3023222262 / 1000000000000) (-3023221934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2781673596955011 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28515830243 / 1000000000000) (-28515778476 / 1000000000000), orderedInterval (10134686145 / 1000000000000) (10134737912 / 1000000000000)))) (orderedInterval (-9239293340 / 1000000000000) (-9239290346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2319069441090259 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19844981897 / 1000000000000) (19844983520 / 1000000000000), orderedInterval (-26554589058 / 1000000000000) (-26554587436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2048968181523439 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-28626390619 / 1000000000000) (-28626390618 / 1000000000000), orderedInterval (-20547286380 / 1000000000000) (-20547286379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (593870841376461 / 800000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29009708007 / 1000000000000) (29009717596 / 1000000000000), orderedInterval (-4022444106 / 1000000000000) (-4022434518 / 1000000000000)))) (orderedInterval (14020849725 / 1000000000000) (14020852886 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate530_chunkChecks4_2 :
    compactCertificate530.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1642678000957367 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (3697281833 / 1000000000000) (3697281836 / 1000000000000), orderedInterval (-39203111501 / 1000000000000) (-39203111499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1392516333572287 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8384127758 / 1000000000000) (-8384127757 / 1000000000000), orderedInterval (-41921202787 / 1000000000000) (-41921202786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (871372064943061 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51845494300 / 1000000000000) (-51845491444 / 1000000000000), orderedInterval (15429678364 / 1000000000000) (15429681220 / 1000000000000)))) (orderedInterval (-483571874 / 1000000000000) (-483571780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (468626794578987 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73080221648 / 1000000000000) (-73080221410 / 1000000000000), orderedInterval (9963330683 / 1000000000000) (9963330921 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1272412908177961 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-44729709333 / 1000000000000) (-44729709134 / 1000000000000), orderedInterval (811900865 / 1000000000000) (811901063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1737371044191497 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38278834966 / 1000000000000) (38278835397 / 1000000000000), orderedInterval (-705930682 / 1000000000000) (-705930250 / 1000000000000)))) (orderedInterval (-3607911715 / 1000000000000) (-3607911620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (734627935056939 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46564216177 / 1000000000000) (46564301970 / 1000000000000), orderedInterval (-36156221335 / 1000000000000) (-36156135541 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2986221770683019 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-10242688253 / 1000000000000) (-10242688242 / 1000000000000), orderedInterval (27353345533 / 1000000000000) (27353345544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1994657749164421 / 4000000000000) 4 (IntervalRat.scale (803 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2272591391 / 1000000000000) (2272591393 / 1000000000000), orderedInterval (-35660175431 / 1000000000000) (-35660175429 / 1000000000000)))) (orderedInterval (8956821621 / 1000000000000) (8956822227 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate530_chunkChecks4 :
    compactCertificate530.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate530.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate530_chunkChecks4_0
    compactCertificate530_chunkChecks4_1 compactCertificate530_chunkChecks4_2

theorem compactCertificate530_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate530.chunkCheck r b = true :=
  compactCertificate530.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate530_chunkChecks0
    · exact compactCertificate530_chunkChecks1
    · exact compactCertificate530_chunkChecks2
    · exact compactCertificate530_chunkChecks3
    · exact compactCertificate530_chunkChecks4)

theorem compactCertificate530_coefficient0 :
    compactCertificate530.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate530_coefficient1 :
    compactCertificate530.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate530_coefficient2 :
    compactCertificate530.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate530_coefficient3 :
    compactCertificate530.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate530_coefficient4 :
    compactCertificate530.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate530_coefficients : ∀ r : Fin 5,
    compactCertificate530.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate530_coefficient0
  · exact compactCertificate530_coefficient1
  · exact compactCertificate530_coefficient2
  · exact compactCertificate530_coefficient3
  · exact compactCertificate530_coefficient4

theorem compactCertificate530_lower : (1 : ℚ) ≤ compactCertificate530.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate530, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate530_proves {t : ℝ} (ht : t ∈ compactCertificate530.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate530.proves compactCertificate530_states compactCertificate530_chunks
    compactCertificate530_coefficients compactCertificate530_lower ht

end Erdos232
