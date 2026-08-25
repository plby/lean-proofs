/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate620 : CompactCertificate where
  left := 491
  right := 492
  center := 983 / 2
  grid := fun i =>
    match i.val with
    | 0 => 157
    | 1 => 115
    | 2 => 186
    | 3 => 34
    | 4 => 90
    | 5 => 245
    | 6 => 181
    | 7 => 310
    | 8 => 228
    | 9 => 350
    | 10 => 202
    | 11 => 359
    | 12 => 335
    | 13 => 239
    | 14 => 271
    | 15 => 226
    | 16 => 200
    | 17 => 289
    | 18 => 160
    | 19 => 136
    | 20 => 85
    | 21 => 46
    | 22 => 124
    | 23 => 169
    | 24 => 72
    | 25 => 291
    | _ => 194
  point := fun i =>
    match i.val with
    | 0 => 983 / 2
    | 1 => 1448146701786683 / 4000000000000
    | 2 => 468300889306139 / 800000000000
    | 3 => 422565595852081 / 4000000000000
    | 4 => 1135070629226557 / 4000000000000
    | 5 => 3081937561032969 / 4000000000000
    | 6 => 2270141258454097 / 4000000000000
    | 7 => 3889925739679381 / 4000000000000
    | 8 => 2865301693849279 / 4000000000000
    | 9 => 4396109643764017 / 4000000000000
    | 10 => 2538095086213993 / 4000000000000
    | 11 => 4503894269800637 / 4000000000000
    | 12 => 4208122256646353 / 4000000000000
    | 13 => 3003114605426849 / 4000000000000
    | 14 => 3405211887679671 / 4000000000000
    | 15 => 2838910660761799 / 4000000000000
    | 16 => 2508263664305779 / 4000000000000
    | 17 => 726992574188121 / 800000000000
    | 18 => 2010899719727387 / 4000000000000
    | 19 => 1704661962517507 / 4000000000000
    | 20 => 1066698306150721 / 4000000000000
    | 21 => 573673896726207 / 4000000000000
    | 22 => 1557636225079621 / 4000000000000
    | 23 => 2126819098929317 / 4000000000000
    | 24 => 899301693849279 / 4000000000000
    | 25 => 3655611457760159 / 4000000000000
    | _ => 2441779037893681 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (29167462067 / 1000000000000) (29167514567 / 1000000000000), orderedInterval (-21113253226 / 1000000000000) (-21113200726 / 1000000000000))
    | 1 => (orderedInterval (-41911968712 / 1000000000000) (-41911968574 / 1000000000000), orderedInterval (-1293121033 / 1000000000000) (-1293120895 / 1000000000000))
    | 2 => (orderedInterval (31917552799 / 1000000000000) (31917566690 / 1000000000000), orderedInterval (-8322372674 / 1000000000000) (-8322358783 / 1000000000000))
    | 3 => (orderedInterval (-29408288890 / 1000000000000) (-29408287510 / 1000000000000), orderedInterval (71982309829 / 1000000000000) (71982311209 / 1000000000000))
    | 4 => (orderedInterval (46024562055 / 1000000000000) (46024564465 / 1000000000000), orderedInterval (-11269965170 / 1000000000000) (-11269962760 / 1000000000000))
    | 5 => (orderedInterval (-28743651802 / 1000000000000) (-28743648902 / 1000000000000), orderedInterval (266707645 / 1000000000000) (266710545 / 1000000000000))
    | 6 => (orderedInterval (10146176734 / 1000000000000) (10146176754 / 1000000000000), orderedInterval (-31927312912 / 1000000000000) (-31927312891 / 1000000000000))
    | 7 => (orderedInterval (-15012037368 / 1000000000000) (-15012037261 / 1000000000000), orderedInterval (20726625995 / 1000000000000) (20726626103 / 1000000000000))
    | 8 => (orderedInterval (21948971091 / 1000000000000) (21948971092 / 1000000000000), orderedInterval (20158238423 / 1000000000000) (20158238424 / 1000000000000))
    | 9 => (orderedInterval (6077192441 / 1000000000000) (6077192442 / 1000000000000), orderedInterval (23285111763 / 1000000000000) (23285111764 / 1000000000000))
    | 10 => (orderedInterval (20580832434 / 1000000000000) (20580832435 / 1000000000000), orderedInterval (24061420450 / 1000000000000) (24061420451 / 1000000000000))
    | 11 => (orderedInterval (20891210144 / 1000000000000) (20891218632 / 1000000000000), orderedInterval (-11364988122 / 1000000000000) (-11364979633 / 1000000000000))
    | 12 => (orderedInterval (-9177071728 / 1000000000000) (-9177071727 / 1000000000000), orderedInterval (-22819216069 / 1000000000000) (-22819216068 / 1000000000000))
    | 13 => (orderedInterval (-19271762324 / 1000000000000) (-19271762323 / 1000000000000), orderedInterval (-21817081301 / 1000000000000) (-21817081300 / 1000000000000))
    | 14 => (orderedInterval (-17961991475 / 1000000000000) (-17961991474 / 1000000000000), orderedInterval (-20609464401 / 1000000000000) (-20609464400 / 1000000000000))
    | 15 => (orderedInterval (14697798312 / 1000000000000) (14697798313 / 1000000000000), orderedInterval (26084979653 / 1000000000000) (26084979654 / 1000000000000))
    | 16 => (orderedInterval (-14356748094 / 1000000000000) (-14356747960 / 1000000000000), orderedInterval (28456478445 / 1000000000000) (28456478578 / 1000000000000))
    | 17 => (orderedInterval (-26451815195 / 1000000000000) (-26451807184 / 1000000000000), orderedInterval (938229295 / 1000000000000) (938237306 / 1000000000000))
    | 18 => (orderedInterval (26857837619 / 1000000000000) (26857837620 / 1000000000000), orderedInterval (23318408248 / 1000000000000) (23318408249 / 1000000000000))
    | 19 => (orderedInterval (-11643425091 / 1000000000000) (-11643425034 / 1000000000000), orderedInterval (36868291120 / 1000000000000) (36868291177 / 1000000000000))
    | 20 => (orderedInterval (-20107065059 / 1000000000000) (-20107065058 / 1000000000000), orderedInterval (-44492762495 / 1000000000000) (-44492762494 / 1000000000000))
    | 21 => (orderedInterval (-20341060563 / 1000000000000) (-20341060138 / 1000000000000), orderedInterval (63515060860 / 1000000000000) (63515061285 / 1000000000000))
    | 22 => (orderedInterval (24037490715 / 1000000000000) (24037490716 / 1000000000000), orderedInterval (32481210585 / 1000000000000) (32481210586 / 1000000000000))
    | 23 => (orderedInterval (-34600541844 / 1000000000000) (-34600541275 / 1000000000000), orderedInterval (-314067642 / 1000000000000) (-314067073 / 1000000000000))
    | 24 => (orderedInterval (-29357742234 / 1000000000000) (-29357736106 / 1000000000000), orderedInterval (44447086176 / 1000000000000) (44447092304 / 1000000000000))
    | 25 => (orderedInterval (-12296818072 / 1000000000000) (-12296818071 / 1000000000000), orderedInterval (-23346706666 / 1000000000000) (-23346706665 / 1000000000000))
    | _ => (orderedInterval (31711363687 / 1000000000000) (31711372033 / 1000000000000), orderedInterval (-6130682020 / 1000000000000) (-6130673674 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13043381026 / 1000000000000) (13043402686 / 1000000000000)
      | 1 => orderedInterval (4042871840 / 1000000000000) (4042872209 / 1000000000000)
      | 2 => orderedInterval (993494604 / 1000000000000) (993494636 / 1000000000000)
      | 3 => orderedInterval (3414835118 / 1000000000000) (3414836520 / 1000000000000)
      | 4 => orderedInterval (-1565820620 / 1000000000000) (-1565820561 / 1000000000000)
      | 5 => orderedInterval (314043326 / 1000000000000) (314043586 / 1000000000000)
      | 6 => orderedInterval (-4289938913 / 1000000000000) (-4289938786 / 1000000000000)
      | 7 => orderedInterval (2482011176 / 1000000000000) (2482011286 / 1000000000000)
      | _ => orderedInterval (-5125889926 / 1000000000000) (-5125888187 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-8959073901 / 1000000000000) (-8959052082 / 1000000000000)
      | 1 => orderedInterval (-435150596 / 1000000000000) (-435150152 / 1000000000000)
      | 2 => orderedInterval (-554866314 / 1000000000000) (-554866259 / 1000000000000)
      | 3 => orderedInterval (-10651335036 / 1000000000000) (-10651331867 / 1000000000000)
      | 4 => orderedInterval (-2088996580 / 1000000000000) (-2088996485 / 1000000000000)
      | 5 => orderedInterval (-1598256490 / 1000000000000) (-1598256032 / 1000000000000)
      | 6 => orderedInterval (-6408845752 / 1000000000000) (-6408845635 / 1000000000000)
      | 7 => orderedInterval (-900018994 / 1000000000000) (-900018892 / 1000000000000)
      | _ => orderedInterval (5084963512 / 1000000000000) (5084965665 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13987611801 / 1000000000000) (-13987589746 / 1000000000000)
      | 1 => orderedInterval (-5595447555 / 1000000000000) (-5595446924 / 1000000000000)
      | 2 => orderedInterval (-2938324986 / 1000000000000) (-2938324888 / 1000000000000)
      | 3 => orderedInterval (-12706680214 / 1000000000000) (-12706673009 / 1000000000000)
      | 4 => orderedInterval (3224765594 / 1000000000000) (3224765751 / 1000000000000)
      | 5 => orderedInterval (627269871 / 1000000000000) (627270687 / 1000000000000)
      | 6 => orderedInterval (4203039288 / 1000000000000) (4203039399 / 1000000000000)
      | 7 => orderedInterval (-2791148997 / 1000000000000) (-2791148892 / 1000000000000)
      | _ => orderedInterval (5744003354 / 1000000000000) (5744006064 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (9226819487 / 1000000000000) (9226841770 / 1000000000000)
      | 1 => orderedInterval (171368007 / 1000000000000) (171368958 / 1000000000000)
      | 2 => orderedInterval (3449701623 / 1000000000000) (3449701805 / 1000000000000)
      | 3 => orderedInterval (61872799213 / 1000000000000) (61872815632 / 1000000000000)
      | 4 => orderedInterval (2764932981 / 1000000000000) (2764933248 / 1000000000000)
      | 5 => orderedInterval (2321726292 / 1000000000000) (2321727762 / 1000000000000)
      | 6 => orderedInterval (5572843078 / 1000000000000) (5572843186 / 1000000000000)
      | 7 => orderedInterval (370824455 / 1000000000000) (370824565 / 1000000000000)
      | _ => orderedInterval (-14458796847 / 1000000000000) (-14458793402 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15176936404 / 1000000000000) (15176959004 / 1000000000000)
      | 1 => orderedInterval (12526515051 / 1000000000000) (12526516523 / 1000000000000)
      | 2 => orderedInterval (9475737351 / 1000000000000) (9475737689 / 1000000000000)
      | 3 => orderedInterval (58786673893 / 1000000000000) (58786711401 / 1000000000000)
      | 4 => orderedInterval (-5637511237 / 1000000000000) (-5637510773 / 1000000000000)
      | 5 => orderedInterval (-5009321905 / 1000000000000) (-5009319235 / 1000000000000)
      | 6 => orderedInterval (-4407207882 / 1000000000000) (-4407207776 / 1000000000000)
      | 7 => orderedInterval (3418108719 / 1000000000000) (3418108836 / 1000000000000)
      | _ => orderedInterval (-2141298052 / 1000000000000) (-2141293612 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (13308987631 / 1000000000000) (13309013389 / 1000000000000)
    | 1 => orderedInterval (-26511580151 / 1000000000000) (-26511551739 / 1000000000000)
    | 2 => orderedInterval (-24220135446 / 1000000000000) (-24220101558 / 1000000000000)
    | 3 => orderedInterval (71292218289 / 1000000000000) (71292263524 / 1000000000000)
    | _ => orderedInterval (82188632342 / 1000000000000) (82188702057 / 1000000000000)

theorem compactCertificate620_stateChecks0 :
    compactCertificate620.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (983 / 2)) (orderedInterval (29167462067 / 1000000000000) (29167514567 / 1000000000000), orderedInterval (-21113253226 / 1000000000000) (-21113200726 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1448146701786683 / 4000000000000)) (orderedInterval (-41911968712 / 1000000000000) (-41911968574 / 1000000000000), orderedInterval (-1293121033 / 1000000000000) (-1293120895 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (468300889306139 / 800000000000)) (orderedInterval (31917552799 / 1000000000000) (31917566690 / 1000000000000), orderedInterval (-8322372674 / 1000000000000) (-8322358783 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_stateChecks1 :
    compactCertificate620.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (422565595852081 / 4000000000000)) (orderedInterval (-29408288890 / 1000000000000) (-29408287510 / 1000000000000), orderedInterval (71982309829 / 1000000000000) (71982311209 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1135070629226557 / 4000000000000)) (orderedInterval (46024562055 / 1000000000000) (46024564465 / 1000000000000), orderedInterval (-11269965170 / 1000000000000) (-11269962760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3081937561032969 / 4000000000000)) (orderedInterval (-28743651802 / 1000000000000) (-28743648902 / 1000000000000), orderedInterval (266707645 / 1000000000000) (266710545 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_stateChecks2 :
    compactCertificate620.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2270141258454097 / 4000000000000)) (orderedInterval (10146176734 / 1000000000000) (10146176754 / 1000000000000), orderedInterval (-31927312912 / 1000000000000) (-31927312891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 310 12 (3889925739679381 / 4000000000000)) (orderedInterval (-15012037368 / 1000000000000) (-15012037261 / 1000000000000), orderedInterval (20726625995 / 1000000000000) (20726626103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2865301693849279 / 4000000000000)) (orderedInterval (21948971091 / 1000000000000) (21948971092 / 1000000000000), orderedInterval (20158238423 / 1000000000000) (20158238424 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_stateChecks3 :
    compactCertificate620.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 350 12 (4396109643764017 / 4000000000000)) (orderedInterval (6077192441 / 1000000000000) (6077192442 / 1000000000000), orderedInterval (23285111763 / 1000000000000) (23285111764 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2538095086213993 / 4000000000000)) (orderedInterval (20580832434 / 1000000000000) (20580832435 / 1000000000000), orderedInterval (24061420450 / 1000000000000) (24061420451 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 359 12 (4503894269800637 / 4000000000000)) (orderedInterval (20891210144 / 1000000000000) (20891218632 / 1000000000000), orderedInterval (-11364988122 / 1000000000000) (-11364979633 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_stateChecks4 :
    compactCertificate620.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 335 12 (4208122256646353 / 4000000000000)) (orderedInterval (-9177071728 / 1000000000000) (-9177071727 / 1000000000000), orderedInterval (-22819216069 / 1000000000000) (-22819216068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (3003114605426849 / 4000000000000)) (orderedInterval (-19271762324 / 1000000000000) (-19271762323 / 1000000000000), orderedInterval (-21817081301 / 1000000000000) (-21817081300 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 271 12 (3405211887679671 / 4000000000000)) (orderedInterval (-17961991475 / 1000000000000) (-17961991474 / 1000000000000), orderedInterval (-20609464401 / 1000000000000) (-20609464400 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_stateChecks5 :
    compactCertificate620.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2838910660761799 / 4000000000000)) (orderedInterval (14697798312 / 1000000000000) (14697798313 / 1000000000000), orderedInterval (26084979653 / 1000000000000) (26084979654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2508263664305779 / 4000000000000)) (orderedInterval (-14356748094 / 1000000000000) (-14356747960 / 1000000000000), orderedInterval (28456478445 / 1000000000000) (28456478578 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (726992574188121 / 800000000000)) (orderedInterval (-26451815195 / 1000000000000) (-26451807184 / 1000000000000), orderedInterval (938229295 / 1000000000000) (938237306 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_stateChecks6 :
    compactCertificate620.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2010899719727387 / 4000000000000)) (orderedInterval (26857837619 / 1000000000000) (26857837620 / 1000000000000), orderedInterval (23318408248 / 1000000000000) (23318408249 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1704661962517507 / 4000000000000)) (orderedInterval (-11643425091 / 1000000000000) (-11643425034 / 1000000000000), orderedInterval (36868291120 / 1000000000000) (36868291177 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1066698306150721 / 4000000000000)) (orderedInterval (-20107065059 / 1000000000000) (-20107065058 / 1000000000000), orderedInterval (-44492762495 / 1000000000000) (-44492762494 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_stateChecks7 :
    compactCertificate620.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (573673896726207 / 4000000000000)) (orderedInterval (-20341060563 / 1000000000000) (-20341060138 / 1000000000000), orderedInterval (63515060860 / 1000000000000) (63515061285 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1557636225079621 / 4000000000000)) (orderedInterval (24037490715 / 1000000000000) (24037490716 / 1000000000000), orderedInterval (32481210585 / 1000000000000) (32481210586 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2126819098929317 / 4000000000000)) (orderedInterval (-34600541844 / 1000000000000) (-34600541275 / 1000000000000), orderedInterval (-314067642 / 1000000000000) (-314067073 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_stateChecks8 :
    compactCertificate620.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (899301693849279 / 4000000000000)) (orderedInterval (-29357742234 / 1000000000000) (-29357736106 / 1000000000000), orderedInterval (44447086176 / 1000000000000) (44447092304 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 291 12 (3655611457760159 / 4000000000000)) (orderedInterval (-12296818072 / 1000000000000) (-12296818071 / 1000000000000), orderedInterval (-23346706666 / 1000000000000) (-23346706665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2441779037893681 / 4000000000000)) (orderedInterval (31711363687 / 1000000000000) (31711372033 / 1000000000000), orderedInterval (-6130682020 / 1000000000000) (-6130673674 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_states : ∀ j,
    BesselStateValid (compactCertificate620.point j) (compactCertificate620.state j) :=
  compactCertificate620.statesValid_of_checks3 compactCertificate620_stateChecks0
    compactCertificate620_stateChecks1 compactCertificate620_stateChecks2
    compactCertificate620_stateChecks3 compactCertificate620_stateChecks4
    compactCertificate620_stateChecks5 compactCertificate620_stateChecks6
    compactCertificate620_stateChecks7 compactCertificate620_stateChecks8

theorem compactCertificate620_chunkChecks0_0 :
    compactCertificate620.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (983 / 2) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29167462067 / 1000000000000) (29167514567 / 1000000000000), orderedInterval (-21113253226 / 1000000000000) (-21113200726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1448146701786683 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41911968712 / 1000000000000) (-41911968574 / 1000000000000), orderedInterval (-1293121033 / 1000000000000) (-1293120895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (468300889306139 / 800000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31917552799 / 1000000000000) (31917566690 / 1000000000000), orderedInterval (-8322372674 / 1000000000000) (-8322358783 / 1000000000000)))) (orderedInterval (13043381026 / 1000000000000) (13043402686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (422565595852081 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29408288890 / 1000000000000) (-29408287510 / 1000000000000), orderedInterval (71982309829 / 1000000000000) (71982311209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1135070629226557 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46024562055 / 1000000000000) (46024564465 / 1000000000000), orderedInterval (-11269965170 / 1000000000000) (-11269962760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3081937561032969 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28743651802 / 1000000000000) (-28743648902 / 1000000000000), orderedInterval (266707645 / 1000000000000) (266710545 / 1000000000000)))) (orderedInterval (4042871840 / 1000000000000) (4042872209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2270141258454097 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10146176734 / 1000000000000) (10146176754 / 1000000000000), orderedInterval (-31927312912 / 1000000000000) (-31927312891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3889925739679381 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15012037368 / 1000000000000) (-15012037261 / 1000000000000), orderedInterval (20726625995 / 1000000000000) (20726626103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2865301693849279 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21948971091 / 1000000000000) (21948971092 / 1000000000000), orderedInterval (20158238423 / 1000000000000) (20158238424 / 1000000000000)))) (orderedInterval (993494604 / 1000000000000) (993494636 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_chunkChecks0_1 :
    compactCertificate620.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4396109643764017 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6077192441 / 1000000000000) (6077192442 / 1000000000000), orderedInterval (23285111763 / 1000000000000) (23285111764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2538095086213993 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (20580832434 / 1000000000000) (20580832435 / 1000000000000), orderedInterval (24061420450 / 1000000000000) (24061420451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4503894269800637 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20891210144 / 1000000000000) (20891218632 / 1000000000000), orderedInterval (-11364988122 / 1000000000000) (-11364979633 / 1000000000000)))) (orderedInterval (3414835118 / 1000000000000) (3414836520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4208122256646353 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9177071728 / 1000000000000) (-9177071727 / 1000000000000), orderedInterval (-22819216069 / 1000000000000) (-22819216068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (3003114605426849 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19271762324 / 1000000000000) (-19271762323 / 1000000000000), orderedInterval (-21817081301 / 1000000000000) (-21817081300 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3405211887679671 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17961991475 / 1000000000000) (-17961991474 / 1000000000000), orderedInterval (-20609464401 / 1000000000000) (-20609464400 / 1000000000000)))) (orderedInterval (-1565820620 / 1000000000000) (-1565820561 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2838910660761799 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14697798312 / 1000000000000) (14697798313 / 1000000000000), orderedInterval (26084979653 / 1000000000000) (26084979654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2508263664305779 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14356748094 / 1000000000000) (-14356747960 / 1000000000000), orderedInterval (28456478445 / 1000000000000) (28456478578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (726992574188121 / 800000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26451815195 / 1000000000000) (-26451807184 / 1000000000000), orderedInterval (938229295 / 1000000000000) (938237306 / 1000000000000)))) (orderedInterval (314043326 / 1000000000000) (314043586 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_chunkChecks0_2 :
    compactCertificate620.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2010899719727387 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26857837619 / 1000000000000) (26857837620 / 1000000000000), orderedInterval (23318408248 / 1000000000000) (23318408249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1704661962517507 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11643425091 / 1000000000000) (-11643425034 / 1000000000000), orderedInterval (36868291120 / 1000000000000) (36868291177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1066698306150721 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20107065059 / 1000000000000) (-20107065058 / 1000000000000), orderedInterval (-44492762495 / 1000000000000) (-44492762494 / 1000000000000)))) (orderedInterval (-4289938913 / 1000000000000) (-4289938786 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (573673896726207 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20341060563 / 1000000000000) (-20341060138 / 1000000000000), orderedInterval (63515060860 / 1000000000000) (63515061285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1557636225079621 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24037490715 / 1000000000000) (24037490716 / 1000000000000), orderedInterval (32481210585 / 1000000000000) (32481210586 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2126819098929317 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34600541844 / 1000000000000) (-34600541275 / 1000000000000), orderedInterval (-314067642 / 1000000000000) (-314067073 / 1000000000000)))) (orderedInterval (2482011176 / 1000000000000) (2482011286 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (899301693849279 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29357742234 / 1000000000000) (-29357736106 / 1000000000000), orderedInterval (44447086176 / 1000000000000) (44447092304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3655611457760159 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12296818072 / 1000000000000) (-12296818071 / 1000000000000), orderedInterval (-23346706666 / 1000000000000) (-23346706665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2441779037893681 / 4000000000000) 0 (IntervalRat.scale (983 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31711363687 / 1000000000000) (31711372033 / 1000000000000), orderedInterval (-6130682020 / 1000000000000) (-6130673674 / 1000000000000)))) (orderedInterval (-5125889926 / 1000000000000) (-5125888187 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_chunkChecks0 :
    compactCertificate620.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate620.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate620_chunkChecks0_0
    compactCertificate620_chunkChecks0_1 compactCertificate620_chunkChecks0_2

theorem compactCertificate620_chunkChecks1_0 :
    compactCertificate620.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (983 / 2) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29167462067 / 1000000000000) (29167514567 / 1000000000000), orderedInterval (-21113253226 / 1000000000000) (-21113200726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1448146701786683 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41911968712 / 1000000000000) (-41911968574 / 1000000000000), orderedInterval (-1293121033 / 1000000000000) (-1293120895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (468300889306139 / 800000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31917552799 / 1000000000000) (31917566690 / 1000000000000), orderedInterval (-8322372674 / 1000000000000) (-8322358783 / 1000000000000)))) (orderedInterval (-8959073901 / 1000000000000) (-8959052082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (422565595852081 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29408288890 / 1000000000000) (-29408287510 / 1000000000000), orderedInterval (71982309829 / 1000000000000) (71982311209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1135070629226557 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46024562055 / 1000000000000) (46024564465 / 1000000000000), orderedInterval (-11269965170 / 1000000000000) (-11269962760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3081937561032969 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28743651802 / 1000000000000) (-28743648902 / 1000000000000), orderedInterval (266707645 / 1000000000000) (266710545 / 1000000000000)))) (orderedInterval (-435150596 / 1000000000000) (-435150152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2270141258454097 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10146176734 / 1000000000000) (10146176754 / 1000000000000), orderedInterval (-31927312912 / 1000000000000) (-31927312891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3889925739679381 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15012037368 / 1000000000000) (-15012037261 / 1000000000000), orderedInterval (20726625995 / 1000000000000) (20726626103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2865301693849279 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21948971091 / 1000000000000) (21948971092 / 1000000000000), orderedInterval (20158238423 / 1000000000000) (20158238424 / 1000000000000)))) (orderedInterval (-554866314 / 1000000000000) (-554866259 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_chunkChecks1_1 :
    compactCertificate620.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4396109643764017 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6077192441 / 1000000000000) (6077192442 / 1000000000000), orderedInterval (23285111763 / 1000000000000) (23285111764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2538095086213993 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (20580832434 / 1000000000000) (20580832435 / 1000000000000), orderedInterval (24061420450 / 1000000000000) (24061420451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4503894269800637 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20891210144 / 1000000000000) (20891218632 / 1000000000000), orderedInterval (-11364988122 / 1000000000000) (-11364979633 / 1000000000000)))) (orderedInterval (-10651335036 / 1000000000000) (-10651331867 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4208122256646353 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9177071728 / 1000000000000) (-9177071727 / 1000000000000), orderedInterval (-22819216069 / 1000000000000) (-22819216068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (3003114605426849 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19271762324 / 1000000000000) (-19271762323 / 1000000000000), orderedInterval (-21817081301 / 1000000000000) (-21817081300 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3405211887679671 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17961991475 / 1000000000000) (-17961991474 / 1000000000000), orderedInterval (-20609464401 / 1000000000000) (-20609464400 / 1000000000000)))) (orderedInterval (-2088996580 / 1000000000000) (-2088996485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2838910660761799 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14697798312 / 1000000000000) (14697798313 / 1000000000000), orderedInterval (26084979653 / 1000000000000) (26084979654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2508263664305779 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14356748094 / 1000000000000) (-14356747960 / 1000000000000), orderedInterval (28456478445 / 1000000000000) (28456478578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (726992574188121 / 800000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26451815195 / 1000000000000) (-26451807184 / 1000000000000), orderedInterval (938229295 / 1000000000000) (938237306 / 1000000000000)))) (orderedInterval (-1598256490 / 1000000000000) (-1598256032 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_chunkChecks1_2 :
    compactCertificate620.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2010899719727387 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26857837619 / 1000000000000) (26857837620 / 1000000000000), orderedInterval (23318408248 / 1000000000000) (23318408249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1704661962517507 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11643425091 / 1000000000000) (-11643425034 / 1000000000000), orderedInterval (36868291120 / 1000000000000) (36868291177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1066698306150721 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20107065059 / 1000000000000) (-20107065058 / 1000000000000), orderedInterval (-44492762495 / 1000000000000) (-44492762494 / 1000000000000)))) (orderedInterval (-6408845752 / 1000000000000) (-6408845635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (573673896726207 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20341060563 / 1000000000000) (-20341060138 / 1000000000000), orderedInterval (63515060860 / 1000000000000) (63515061285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1557636225079621 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24037490715 / 1000000000000) (24037490716 / 1000000000000), orderedInterval (32481210585 / 1000000000000) (32481210586 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2126819098929317 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34600541844 / 1000000000000) (-34600541275 / 1000000000000), orderedInterval (-314067642 / 1000000000000) (-314067073 / 1000000000000)))) (orderedInterval (-900018994 / 1000000000000) (-900018892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (899301693849279 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29357742234 / 1000000000000) (-29357736106 / 1000000000000), orderedInterval (44447086176 / 1000000000000) (44447092304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3655611457760159 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12296818072 / 1000000000000) (-12296818071 / 1000000000000), orderedInterval (-23346706666 / 1000000000000) (-23346706665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2441779037893681 / 4000000000000) 1 (IntervalRat.scale (983 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31711363687 / 1000000000000) (31711372033 / 1000000000000), orderedInterval (-6130682020 / 1000000000000) (-6130673674 / 1000000000000)))) (orderedInterval (5084963512 / 1000000000000) (5084965665 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_chunkChecks1 :
    compactCertificate620.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate620.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate620_chunkChecks1_0
    compactCertificate620_chunkChecks1_1 compactCertificate620_chunkChecks1_2

theorem compactCertificate620_chunkChecks2_0 :
    compactCertificate620.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (983 / 2) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29167462067 / 1000000000000) (29167514567 / 1000000000000), orderedInterval (-21113253226 / 1000000000000) (-21113200726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1448146701786683 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41911968712 / 1000000000000) (-41911968574 / 1000000000000), orderedInterval (-1293121033 / 1000000000000) (-1293120895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (468300889306139 / 800000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31917552799 / 1000000000000) (31917566690 / 1000000000000), orderedInterval (-8322372674 / 1000000000000) (-8322358783 / 1000000000000)))) (orderedInterval (-13987611801 / 1000000000000) (-13987589746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (422565595852081 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29408288890 / 1000000000000) (-29408287510 / 1000000000000), orderedInterval (71982309829 / 1000000000000) (71982311209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1135070629226557 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46024562055 / 1000000000000) (46024564465 / 1000000000000), orderedInterval (-11269965170 / 1000000000000) (-11269962760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3081937561032969 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28743651802 / 1000000000000) (-28743648902 / 1000000000000), orderedInterval (266707645 / 1000000000000) (266710545 / 1000000000000)))) (orderedInterval (-5595447555 / 1000000000000) (-5595446924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2270141258454097 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10146176734 / 1000000000000) (10146176754 / 1000000000000), orderedInterval (-31927312912 / 1000000000000) (-31927312891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3889925739679381 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15012037368 / 1000000000000) (-15012037261 / 1000000000000), orderedInterval (20726625995 / 1000000000000) (20726626103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2865301693849279 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21948971091 / 1000000000000) (21948971092 / 1000000000000), orderedInterval (20158238423 / 1000000000000) (20158238424 / 1000000000000)))) (orderedInterval (-2938324986 / 1000000000000) (-2938324888 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_chunkChecks2_1 :
    compactCertificate620.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4396109643764017 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6077192441 / 1000000000000) (6077192442 / 1000000000000), orderedInterval (23285111763 / 1000000000000) (23285111764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2538095086213993 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (20580832434 / 1000000000000) (20580832435 / 1000000000000), orderedInterval (24061420450 / 1000000000000) (24061420451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4503894269800637 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20891210144 / 1000000000000) (20891218632 / 1000000000000), orderedInterval (-11364988122 / 1000000000000) (-11364979633 / 1000000000000)))) (orderedInterval (-12706680214 / 1000000000000) (-12706673009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4208122256646353 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9177071728 / 1000000000000) (-9177071727 / 1000000000000), orderedInterval (-22819216069 / 1000000000000) (-22819216068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (3003114605426849 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19271762324 / 1000000000000) (-19271762323 / 1000000000000), orderedInterval (-21817081301 / 1000000000000) (-21817081300 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3405211887679671 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17961991475 / 1000000000000) (-17961991474 / 1000000000000), orderedInterval (-20609464401 / 1000000000000) (-20609464400 / 1000000000000)))) (orderedInterval (3224765594 / 1000000000000) (3224765751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2838910660761799 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14697798312 / 1000000000000) (14697798313 / 1000000000000), orderedInterval (26084979653 / 1000000000000) (26084979654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2508263664305779 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14356748094 / 1000000000000) (-14356747960 / 1000000000000), orderedInterval (28456478445 / 1000000000000) (28456478578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (726992574188121 / 800000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26451815195 / 1000000000000) (-26451807184 / 1000000000000), orderedInterval (938229295 / 1000000000000) (938237306 / 1000000000000)))) (orderedInterval (627269871 / 1000000000000) (627270687 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_chunkChecks2_2 :
    compactCertificate620.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2010899719727387 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26857837619 / 1000000000000) (26857837620 / 1000000000000), orderedInterval (23318408248 / 1000000000000) (23318408249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1704661962517507 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11643425091 / 1000000000000) (-11643425034 / 1000000000000), orderedInterval (36868291120 / 1000000000000) (36868291177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1066698306150721 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20107065059 / 1000000000000) (-20107065058 / 1000000000000), orderedInterval (-44492762495 / 1000000000000) (-44492762494 / 1000000000000)))) (orderedInterval (4203039288 / 1000000000000) (4203039399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (573673896726207 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20341060563 / 1000000000000) (-20341060138 / 1000000000000), orderedInterval (63515060860 / 1000000000000) (63515061285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1557636225079621 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24037490715 / 1000000000000) (24037490716 / 1000000000000), orderedInterval (32481210585 / 1000000000000) (32481210586 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2126819098929317 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34600541844 / 1000000000000) (-34600541275 / 1000000000000), orderedInterval (-314067642 / 1000000000000) (-314067073 / 1000000000000)))) (orderedInterval (-2791148997 / 1000000000000) (-2791148892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (899301693849279 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29357742234 / 1000000000000) (-29357736106 / 1000000000000), orderedInterval (44447086176 / 1000000000000) (44447092304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3655611457760159 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12296818072 / 1000000000000) (-12296818071 / 1000000000000), orderedInterval (-23346706666 / 1000000000000) (-23346706665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2441779037893681 / 4000000000000) 2 (IntervalRat.scale (983 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31711363687 / 1000000000000) (31711372033 / 1000000000000), orderedInterval (-6130682020 / 1000000000000) (-6130673674 / 1000000000000)))) (orderedInterval (5744003354 / 1000000000000) (5744006064 / 1000000000000))) = true
  rfl'

theorem compactCertificate620_chunkChecks2 :
    compactCertificate620.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate620.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate620_chunkChecks2_0
    compactCertificate620_chunkChecks2_1 compactCertificate620_chunkChecks2_2

theorem compactCertificate620_chunkChecks3_0 :
    compactCertificate620.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (983 / 2) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29167462067 / 1000000000000) (29167514567 / 1000000000000), orderedInterval (-21113253226 / 1000000000000) (-21113200726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1448146701786683 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41911968712 / 1000000000000) (-41911968574 / 1000000000000), orderedInterval (-1293121033 / 1000000000000) (-1293120895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (468300889306139 / 800000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31917552799 / 1000000000000) (31917566690 / 1000000000000), orderedInterval (-8322372674 / 1000000000000) (-8322358783 / 1000000000000)))) (orderedInterval (9226819487 / 1000000000000) (9226841770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (422565595852081 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29408288890 / 1000000000000) (-29408287510 / 1000000000000), orderedInterval (71982309829 / 1000000000000) (71982311209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1135070629226557 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46024562055 / 1000000000000) (46024564465 / 1000000000000), orderedInterval (-11269965170 / 1000000000000) (-11269962760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3081937561032969 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28743651802 / 1000000000000) (-28743648902 / 1000000000000), orderedInterval (266707645 / 1000000000000) (266710545 / 1000000000000)))) (orderedInterval (171368007 / 1000000000000) (171368958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2270141258454097 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10146176734 / 1000000000000) (10146176754 / 1000000000000), orderedInterval (-31927312912 / 1000000000000) (-31927312891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3889925739679381 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15012037368 / 1000000000000) (-15012037261 / 1000000000000), orderedInterval (20726625995 / 1000000000000) (20726626103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2865301693849279 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21948971091 / 1000000000000) (21948971092 / 1000000000000), orderedInterval (20158238423 / 1000000000000) (20158238424 / 1000000000000)))) (orderedInterval (3449701623 / 1000000000000) (3449701805 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate620_chunkChecks3_1 :
    compactCertificate620.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4396109643764017 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6077192441 / 1000000000000) (6077192442 / 1000000000000), orderedInterval (23285111763 / 1000000000000) (23285111764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2538095086213993 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (20580832434 / 1000000000000) (20580832435 / 1000000000000), orderedInterval (24061420450 / 1000000000000) (24061420451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4503894269800637 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20891210144 / 1000000000000) (20891218632 / 1000000000000), orderedInterval (-11364988122 / 1000000000000) (-11364979633 / 1000000000000)))) (orderedInterval (61872799213 / 1000000000000) (61872815632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4208122256646353 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9177071728 / 1000000000000) (-9177071727 / 1000000000000), orderedInterval (-22819216069 / 1000000000000) (-22819216068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (3003114605426849 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19271762324 / 1000000000000) (-19271762323 / 1000000000000), orderedInterval (-21817081301 / 1000000000000) (-21817081300 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3405211887679671 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17961991475 / 1000000000000) (-17961991474 / 1000000000000), orderedInterval (-20609464401 / 1000000000000) (-20609464400 / 1000000000000)))) (orderedInterval (2764932981 / 1000000000000) (2764933248 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2838910660761799 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14697798312 / 1000000000000) (14697798313 / 1000000000000), orderedInterval (26084979653 / 1000000000000) (26084979654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2508263664305779 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14356748094 / 1000000000000) (-14356747960 / 1000000000000), orderedInterval (28456478445 / 1000000000000) (28456478578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (726992574188121 / 800000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26451815195 / 1000000000000) (-26451807184 / 1000000000000), orderedInterval (938229295 / 1000000000000) (938237306 / 1000000000000)))) (orderedInterval (2321726292 / 1000000000000) (2321727762 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate620_chunkChecks3_2 :
    compactCertificate620.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2010899719727387 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26857837619 / 1000000000000) (26857837620 / 1000000000000), orderedInterval (23318408248 / 1000000000000) (23318408249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1704661962517507 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11643425091 / 1000000000000) (-11643425034 / 1000000000000), orderedInterval (36868291120 / 1000000000000) (36868291177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1066698306150721 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20107065059 / 1000000000000) (-20107065058 / 1000000000000), orderedInterval (-44492762495 / 1000000000000) (-44492762494 / 1000000000000)))) (orderedInterval (5572843078 / 1000000000000) (5572843186 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (573673896726207 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20341060563 / 1000000000000) (-20341060138 / 1000000000000), orderedInterval (63515060860 / 1000000000000) (63515061285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1557636225079621 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24037490715 / 1000000000000) (24037490716 / 1000000000000), orderedInterval (32481210585 / 1000000000000) (32481210586 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2126819098929317 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34600541844 / 1000000000000) (-34600541275 / 1000000000000), orderedInterval (-314067642 / 1000000000000) (-314067073 / 1000000000000)))) (orderedInterval (370824455 / 1000000000000) (370824565 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (899301693849279 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29357742234 / 1000000000000) (-29357736106 / 1000000000000), orderedInterval (44447086176 / 1000000000000) (44447092304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3655611457760159 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12296818072 / 1000000000000) (-12296818071 / 1000000000000), orderedInterval (-23346706666 / 1000000000000) (-23346706665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2441779037893681 / 4000000000000) 3 (IntervalRat.scale (983 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31711363687 / 1000000000000) (31711372033 / 1000000000000), orderedInterval (-6130682020 / 1000000000000) (-6130673674 / 1000000000000)))) (orderedInterval (-14458796847 / 1000000000000) (-14458793402 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate620_chunkChecks3 :
    compactCertificate620.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate620.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate620_chunkChecks3_0
    compactCertificate620_chunkChecks3_1 compactCertificate620_chunkChecks3_2

theorem compactCertificate620_chunkChecks4_0 :
    compactCertificate620.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (983 / 2) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29167462067 / 1000000000000) (29167514567 / 1000000000000), orderedInterval (-21113253226 / 1000000000000) (-21113200726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1448146701786683 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-41911968712 / 1000000000000) (-41911968574 / 1000000000000), orderedInterval (-1293121033 / 1000000000000) (-1293120895 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (468300889306139 / 800000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31917552799 / 1000000000000) (31917566690 / 1000000000000), orderedInterval (-8322372674 / 1000000000000) (-8322358783 / 1000000000000)))) (orderedInterval (15176936404 / 1000000000000) (15176959004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (422565595852081 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-29408288890 / 1000000000000) (-29408287510 / 1000000000000), orderedInterval (71982309829 / 1000000000000) (71982311209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1135070629226557 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46024562055 / 1000000000000) (46024564465 / 1000000000000), orderedInterval (-11269965170 / 1000000000000) (-11269962760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3081937561032969 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28743651802 / 1000000000000) (-28743648902 / 1000000000000), orderedInterval (266707645 / 1000000000000) (266710545 / 1000000000000)))) (orderedInterval (12526515051 / 1000000000000) (12526516523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2270141258454097 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10146176734 / 1000000000000) (10146176754 / 1000000000000), orderedInterval (-31927312912 / 1000000000000) (-31927312891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3889925739679381 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15012037368 / 1000000000000) (-15012037261 / 1000000000000), orderedInterval (20726625995 / 1000000000000) (20726626103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2865301693849279 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (21948971091 / 1000000000000) (21948971092 / 1000000000000), orderedInterval (20158238423 / 1000000000000) (20158238424 / 1000000000000)))) (orderedInterval (9475737351 / 1000000000000) (9475737689 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate620_chunkChecks4_1 :
    compactCertificate620.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4396109643764017 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6077192441 / 1000000000000) (6077192442 / 1000000000000), orderedInterval (23285111763 / 1000000000000) (23285111764 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2538095086213993 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (20580832434 / 1000000000000) (20580832435 / 1000000000000), orderedInterval (24061420450 / 1000000000000) (24061420451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4503894269800637 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (20891210144 / 1000000000000) (20891218632 / 1000000000000), orderedInterval (-11364988122 / 1000000000000) (-11364979633 / 1000000000000)))) (orderedInterval (58786673893 / 1000000000000) (58786711401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4208122256646353 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-9177071728 / 1000000000000) (-9177071727 / 1000000000000), orderedInterval (-22819216069 / 1000000000000) (-22819216068 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (3003114605426849 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19271762324 / 1000000000000) (-19271762323 / 1000000000000), orderedInterval (-21817081301 / 1000000000000) (-21817081300 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3405211887679671 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17961991475 / 1000000000000) (-17961991474 / 1000000000000), orderedInterval (-20609464401 / 1000000000000) (-20609464400 / 1000000000000)))) (orderedInterval (-5637511237 / 1000000000000) (-5637510773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2838910660761799 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14697798312 / 1000000000000) (14697798313 / 1000000000000), orderedInterval (26084979653 / 1000000000000) (26084979654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2508263664305779 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14356748094 / 1000000000000) (-14356747960 / 1000000000000), orderedInterval (28456478445 / 1000000000000) (28456478578 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (726992574188121 / 800000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26451815195 / 1000000000000) (-26451807184 / 1000000000000), orderedInterval (938229295 / 1000000000000) (938237306 / 1000000000000)))) (orderedInterval (-5009321905 / 1000000000000) (-5009319235 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate620_chunkChecks4_2 :
    compactCertificate620.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2010899719727387 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26857837619 / 1000000000000) (26857837620 / 1000000000000), orderedInterval (23318408248 / 1000000000000) (23318408249 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1704661962517507 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-11643425091 / 1000000000000) (-11643425034 / 1000000000000), orderedInterval (36868291120 / 1000000000000) (36868291177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1066698306150721 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20107065059 / 1000000000000) (-20107065058 / 1000000000000), orderedInterval (-44492762495 / 1000000000000) (-44492762494 / 1000000000000)))) (orderedInterval (-4407207882 / 1000000000000) (-4407207776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (573673896726207 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-20341060563 / 1000000000000) (-20341060138 / 1000000000000), orderedInterval (63515060860 / 1000000000000) (63515061285 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1557636225079621 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (24037490715 / 1000000000000) (24037490716 / 1000000000000), orderedInterval (32481210585 / 1000000000000) (32481210586 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2126819098929317 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-34600541844 / 1000000000000) (-34600541275 / 1000000000000), orderedInterval (-314067642 / 1000000000000) (-314067073 / 1000000000000)))) (orderedInterval (3418108719 / 1000000000000) (3418108836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (899301693849279 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-29357742234 / 1000000000000) (-29357736106 / 1000000000000), orderedInterval (44447086176 / 1000000000000) (44447092304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3655611457760159 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12296818072 / 1000000000000) (-12296818071 / 1000000000000), orderedInterval (-23346706666 / 1000000000000) (-23346706665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2441779037893681 / 4000000000000) 4 (IntervalRat.scale (983 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31711363687 / 1000000000000) (31711372033 / 1000000000000), orderedInterval (-6130682020 / 1000000000000) (-6130673674 / 1000000000000)))) (orderedInterval (-2141298052 / 1000000000000) (-2141293612 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate620_chunkChecks4 :
    compactCertificate620.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate620.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate620_chunkChecks4_0
    compactCertificate620_chunkChecks4_1 compactCertificate620_chunkChecks4_2

theorem compactCertificate620_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate620.chunkCheck r b = true :=
  compactCertificate620.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate620_chunkChecks0
    · exact compactCertificate620_chunkChecks1
    · exact compactCertificate620_chunkChecks2
    · exact compactCertificate620_chunkChecks3
    · exact compactCertificate620_chunkChecks4)

theorem compactCertificate620_coefficient0 :
    compactCertificate620.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate620_coefficient1 :
    compactCertificate620.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate620_coefficient2 :
    compactCertificate620.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate620_coefficient3 :
    compactCertificate620.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate620_coefficient4 :
    compactCertificate620.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate620_coefficients : ∀ r : Fin 5,
    compactCertificate620.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate620_coefficient0
  · exact compactCertificate620_coefficient1
  · exact compactCertificate620_coefficient2
  · exact compactCertificate620_coefficient3
  · exact compactCertificate620_coefficient4

theorem compactCertificate620_lower : (1 : ℚ) ≤ compactCertificate620.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate620, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate620_proves {t : ℝ} (ht : t ∈ compactCertificate620.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate620.proves compactCertificate620_states compactCertificate620_chunks
    compactCertificate620_coefficients compactCertificate620_lower ht

end Erdos232
