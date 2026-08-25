/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate332 : CompactCertificate where
  left := 204
  right := 205
  center := 409 / 2
  grid := fun i =>
    match i.val with
    | 0 => 65
    | 1 => 48
    | 2 => 78
    | 3 => 14
    | 4 => 38
    | 5 => 102
    | 6 => 75
    | 7 => 129
    | 8 => 95
    | 9 => 146
    | 10 => 84
    | 11 => 149
    | 12 => 139
    | 13 => 99
    | 14 => 113
    | 15 => 94
    | 16 => 83
    | 17 => 120
    | 18 => 67
    | 19 => 56
    | 20 => 35
    | 21 => 19
    | 22 => 52
    | 23 => 70
    | 24 => 30
    | 25 => 121
    | _ => 81
  point := fun i =>
    match i.val with
    | 0 => 409 / 2
    | 1 => 602535097691509 / 4000000000000
    | 2 => 194847470728597 / 800000000000
    | 3 => 175818238762463 / 4000000000000
    | 4 => 472272520197011 / 4000000000000
    | 5 => 1282311762423687 / 4000000000000
    | 6 => 944545040394431 / 4000000000000
    | 7 => 1618494025970363 / 4000000000000
    | 8 => 1192175374144817 / 4000000000000
    | 9 => 1829103605594591 / 4000000000000
    | 10 => 1056033459065639 / 4000000000000
    | 11 => 1873949904728851 / 4000000000000
    | 12 => 1750887083385919 / 4000000000000
    | 13 => 1249515639490927 / 4000000000000
    | 14 => 1416817560591033 / 4000000000000
    | 15 => 1181194771364777 / 4000000000000
    | 16 => 1043621402544317 / 4000000000000
    | 17 => 302482159555383 / 800000000000
    | 18 => 836681572094101 / 4000000000000
    | 19 => 709264234658861 / 4000000000000
    | 20 => 443824625855183 / 4000000000000
    | 21 => 238690359878961 / 4000000000000
    | 22 => 648090758959883 / 4000000000000
    | 23 => 884912524376491 / 4000000000000
    | 24 => 374175374144817 / 4000000000000
    | 25 => 1521002122303057 / 4000000000000
    | _ => 1015958928279263 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-49241762090 / 1000000000000) (-49241762089 / 1000000000000), orderedInterval (-26115054473 / 1000000000000) (-26115054472 / 1000000000000))
    | 1 => (orderedInterval (37873097989 / 1000000000000) (37873097990 / 1000000000000), orderedInterval (52712826350 / 1000000000000) (52712826351 / 1000000000000))
    | 2 => (orderedInterval (-32936074384 / 1000000000000) (-32936056783 / 1000000000000), orderedInterval (39170474848 / 1000000000000) (39170492448 / 1000000000000))
    | 3 => (orderedInterval (82454320892 / 1000000000000) (82454320893 / 1000000000000), orderedInterval (86725910478 / 1000000000000) (86725910479 / 1000000000000))
    | 4 => (orderedInterval (-36997634040 / 1000000000000) (-36997628082 / 1000000000000), orderedInterval (63585126781 / 1000000000000) (63585132739 / 1000000000000))
    | 5 => (orderedInterval (35467722556 / 1000000000000) (35467722557 / 1000000000000), orderedInterval (26924122551 / 1000000000000) (26924122552 / 1000000000000))
    | 6 => (orderedInterval (-50053915850 / 1000000000000) (-50053915848 / 1000000000000), orderedInterval (-13699272853 / 1000000000000) (-13699272852 / 1000000000000))
    | 7 => (orderedInterval (-5658503406 / 1000000000000) (-5658503405 / 1000000000000), orderedInterval (-39252984576 / 1000000000000) (-39252984575 / 1000000000000))
    | 8 => (orderedInterval (-17036264574 / 1000000000000) (-17036264573 / 1000000000000), orderedInterval (-42933747390 / 1000000000000) (-42933747389 / 1000000000000))
    | 9 => (orderedInterval (-21420829803 / 1000000000000) (-21420827486 / 1000000000000), orderedInterval (30574181328 / 1000000000000) (30574183645 / 1000000000000))
    | 10 => (orderedInterval (38450654125 / 1000000000000) (38450654126 / 1000000000000), orderedInterval (30470727734 / 1000000000000) (30470727735 / 1000000000000))
    | 11 => (orderedInterval (-34017429193 / 1000000000000) (-34017429191 / 1000000000000), orderedInterval (-14165708100 / 1000000000000) (-14165708099 / 1000000000000))
    | 12 => (orderedInterval (-36906100441 / 1000000000000) (-36906093841 / 1000000000000), orderedInterval (9651150802 / 1000000000000) (9651157403 / 1000000000000))
    | 13 => (orderedInterval (-37873658565 / 1000000000000) (-37873585000 / 1000000000000), orderedInterval (24628053168 / 1000000000000) (24628126733 / 1000000000000))
    | 14 => (orderedInterval (446597789 / 1000000000000) (446597790 / 1000000000000), orderedInterval (-42393148079 / 1000000000000) (-42393148077 / 1000000000000))
    | 15 => (orderedInterval (32454014973 / 1000000000000) (32454014974 / 1000000000000), orderedInterval (33150278580 / 1000000000000) (33150278581 / 1000000000000))
    | 16 => (orderedInterval (-39834700727 / 1000000000000) (-39834700726 / 1000000000000), orderedInterval (-29133870538 / 1000000000000) (-29133870537 / 1000000000000))
    | 17 => (orderedInterval (38873919871 / 1000000000000) (38873929866 / 1000000000000), orderedInterval (-13186807096 / 1000000000000) (-13186797101 / 1000000000000))
    | 18 => (orderedInterval (27961438968 / 1000000000000) (27961442781 / 1000000000000), orderedInterval (-47624261779 / 1000000000000) (-47624257967 / 1000000000000))
    | 19 => (orderedInterval (49427364578 / 1000000000000) (49427415290 / 1000000000000), orderedInterval (-34010312525 / 1000000000000) (-34010261814 / 1000000000000))
    | 20 => (orderedInterval (-74020381977 / 1000000000000) (-74020381322 / 1000000000000), orderedInterval (16411784511 / 1000000000000) (16411785165 / 1000000000000))
    | 21 => (orderedInterval (-71577128597 / 1000000000000) (-71577128596 / 1000000000000), orderedInterval (-73866899775 / 1000000000000) (-73866899774 / 1000000000000))
    | 22 => (orderedInterval (-33057207880 / 1000000000000) (-33057201576 / 1000000000000), orderedInterval (53360162911 / 1000000000000) (53360169214 / 1000000000000))
    | 23 => (orderedInterval (46265701159 / 1000000000000) (46265734177 / 1000000000000), orderedInterval (-27254933919 / 1000000000000) (-27254900901 / 1000000000000))
    | 24 => (orderedInterval (6602941771 / 1000000000000) (6602941773 / 1000000000000), orderedInterval (82196535475 / 1000000000000) (82196535477 / 1000000000000))
    | 25 => (orderedInterval (-32124818374 / 1000000000000) (-32124818373 / 1000000000000), orderedInterval (-25299563914 / 1000000000000) (-25299563913 / 1000000000000))
    | _ => (orderedInterval (-15064318234 / 1000000000000) (-15064318233 / 1000000000000), orderedInterval (-47714964067 / 1000000000000) (-47714964066 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-21097533286 / 1000000000000) (-21097532238 / 1000000000000)
      | 1 => orderedInterval (-4766806815 / 1000000000000) (-4766806572 / 1000000000000)
      | 2 => orderedInterval (-237202024 / 1000000000000) (-237202011 / 1000000000000)
      | 3 => orderedInterval (1819321438 / 1000000000000) (1819321932 / 1000000000000)
      | 4 => orderedInterval (-2917432868 / 1000000000000) (-2917425768 / 1000000000000)
      | 5 => orderedInterval (3649701697 / 1000000000000) (3649701974 / 1000000000000)
      | 6 => orderedInterval (-9678166519 / 1000000000000) (-9678162966 / 1000000000000)
      | 7 => orderedInterval (-1474109375 / 1000000000000) (-1474106677 / 1000000000000)
      | _ => orderedInterval (5481287683 / 1000000000000) (5481287741 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-7251698672 / 1000000000000) (-7251697425 / 1000000000000)
      | 1 => orderedInterval (-1862320921 / 1000000000000) (-1862320767 / 1000000000000)
      | 2 => orderedInterval (883266350 / 1000000000000) (883266371 / 1000000000000)
      | 3 => orderedInterval (-13846475329 / 1000000000000) (-13846474240 / 1000000000000)
      | 4 => orderedInterval (3556098579 / 1000000000000) (3556109500 / 1000000000000)
      | 5 => orderedInterval (2055612756 / 1000000000000) (2055613259 / 1000000000000)
      | 6 => orderedInterval (9747651000 / 1000000000000) (9747654172 / 1000000000000)
      | 7 => orderedInterval (1698525451 / 1000000000000) (1698528324 / 1000000000000)
      | _ => orderedInterval (15175146821 / 1000000000000) (15175146902 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (22103225827 / 1000000000000) (22103227317 / 1000000000000)
      | 1 => orderedInterval (6696842947 / 1000000000000) (6696843060 / 1000000000000)
      | 2 => orderedInterval (186977155 / 1000000000000) (186977192 / 1000000000000)
      | 3 => orderedInterval (1667536039 / 1000000000000) (1667538465 / 1000000000000)
      | 4 => orderedInterval (5293546512 / 1000000000000) (5293563409 / 1000000000000)
      | 5 => orderedInterval (-7904559837 / 1000000000000) (-7904558917 / 1000000000000)
      | 6 => orderedInterval (7442355714 / 1000000000000) (7442358577 / 1000000000000)
      | 7 => orderedInterval (3557954703 / 1000000000000) (3557957790 / 1000000000000)
      | _ => orderedInterval (-13483795967 / 1000000000000) (-13483795848 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (6163311839 / 1000000000000) (6163313614 / 1000000000000)
      | 1 => orderedInterval (6903175872 / 1000000000000) (6903175973 / 1000000000000)
      | 2 => orderedInterval (-6166849967 / 1000000000000) (-6166849902 / 1000000000000)
      | 3 => orderedInterval (80084132762 / 1000000000000) (80084138166 / 1000000000000)
      | 4 => orderedInterval (-7732679283 / 1000000000000) (-7732653127 / 1000000000000)
      | 5 => orderedInterval (-2442219874 / 1000000000000) (-2442218187 / 1000000000000)
      | 6 => orderedInterval (-9524832671 / 1000000000000) (-9524830086 / 1000000000000)
      | 7 => orderedInterval (-2093636524 / 1000000000000) (-2093633211 / 1000000000000)
      | _ => orderedInterval (-30372880006 / 1000000000000) (-30372879823 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-23362374453 / 1000000000000) (-23362372332 / 1000000000000)
      | 1 => orderedInterval (-15445884852 / 1000000000000) (-15445884737 / 1000000000000)
      | 2 => orderedInterval (877544763 / 1000000000000) (877544884 / 1000000000000)
      | 3 => orderedInterval (-30908189044 / 1000000000000) (-30908176945 / 1000000000000)
      | 4 => orderedInterval (-5458343526 / 1000000000000) (-5458302704 / 1000000000000)
      | 5 => orderedInterval (19324250660 / 1000000000000) (19324253770 / 1000000000000)
      | 6 => orderedInterval (-6590215217 / 1000000000000) (-6590212857 / 1000000000000)
      | 7 => orderedInterval (-4530550199 / 1000000000000) (-4530546621 / 1000000000000)
      | _ => orderedInterval (38283526362 / 1000000000000) (38283526655 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-29220940069 / 1000000000000) (-29220924585 / 1000000000000)
    | 1 => orderedInterval (10155806035 / 1000000000000) (10155826096 / 1000000000000)
    | 2 => orderedInterval (25560083093 / 1000000000000) (25560111045 / 1000000000000)
    | 3 => orderedInterval (34817522148 / 1000000000000) (34817563417 / 1000000000000)
    | _ => orderedInterval (-27810235506 / 1000000000000) (-27810170887 / 1000000000000)

theorem compactCertificate332_stateChecks0 :
    compactCertificate332.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (409 / 2)) (orderedInterval (-49241762090 / 1000000000000) (-49241762089 / 1000000000000), orderedInterval (-26115054473 / 1000000000000) (-26115054472 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (602535097691509 / 4000000000000)) (orderedInterval (37873097989 / 1000000000000) (37873097990 / 1000000000000), orderedInterval (52712826350 / 1000000000000) (52712826351 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (194847470728597 / 800000000000)) (orderedInterval (-32936074384 / 1000000000000) (-32936056783 / 1000000000000), orderedInterval (39170474848 / 1000000000000) (39170492448 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_stateChecks1 :
    compactCertificate332.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (175818238762463 / 4000000000000)) (orderedInterval (82454320892 / 1000000000000) (82454320893 / 1000000000000), orderedInterval (86725910478 / 1000000000000) (86725910479 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (472272520197011 / 4000000000000)) (orderedInterval (-36997634040 / 1000000000000) (-36997628082 / 1000000000000), orderedInterval (63585126781 / 1000000000000) (63585132739 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1282311762423687 / 4000000000000)) (orderedInterval (35467722556 / 1000000000000) (35467722557 / 1000000000000), orderedInterval (26924122551 / 1000000000000) (26924122552 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_stateChecks2 :
    compactCertificate332.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (944545040394431 / 4000000000000)) (orderedInterval (-50053915850 / 1000000000000) (-50053915848 / 1000000000000), orderedInterval (-13699272853 / 1000000000000) (-13699272852 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1618494025970363 / 4000000000000)) (orderedInterval (-5658503406 / 1000000000000) (-5658503405 / 1000000000000), orderedInterval (-39252984576 / 1000000000000) (-39252984575 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1192175374144817 / 4000000000000)) (orderedInterval (-17036264574 / 1000000000000) (-17036264573 / 1000000000000), orderedInterval (-42933747390 / 1000000000000) (-42933747389 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_stateChecks3 :
    compactCertificate332.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1829103605594591 / 4000000000000)) (orderedInterval (-21420829803 / 1000000000000) (-21420827486 / 1000000000000), orderedInterval (30574181328 / 1000000000000) (30574183645 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1056033459065639 / 4000000000000)) (orderedInterval (38450654125 / 1000000000000) (38450654126 / 1000000000000), orderedInterval (30470727734 / 1000000000000) (30470727735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1873949904728851 / 4000000000000)) (orderedInterval (-34017429193 / 1000000000000) (-34017429191 / 1000000000000), orderedInterval (-14165708100 / 1000000000000) (-14165708099 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_stateChecks4 :
    compactCertificate332.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1750887083385919 / 4000000000000)) (orderedInterval (-36906100441 / 1000000000000) (-36906093841 / 1000000000000), orderedInterval (9651150802 / 1000000000000) (9651157403 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1249515639490927 / 4000000000000)) (orderedInterval (-37873658565 / 1000000000000) (-37873585000 / 1000000000000), orderedInterval (24628053168 / 1000000000000) (24628126733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1416817560591033 / 4000000000000)) (orderedInterval (446597789 / 1000000000000) (446597790 / 1000000000000), orderedInterval (-42393148079 / 1000000000000) (-42393148077 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_stateChecks5 :
    compactCertificate332.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1181194771364777 / 4000000000000)) (orderedInterval (32454014973 / 1000000000000) (32454014974 / 1000000000000), orderedInterval (33150278580 / 1000000000000) (33150278581 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1043621402544317 / 4000000000000)) (orderedInterval (-39834700727 / 1000000000000) (-39834700726 / 1000000000000), orderedInterval (-29133870538 / 1000000000000) (-29133870537 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (302482159555383 / 800000000000)) (orderedInterval (38873919871 / 1000000000000) (38873929866 / 1000000000000), orderedInterval (-13186807096 / 1000000000000) (-13186797101 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_stateChecks6 :
    compactCertificate332.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (836681572094101 / 4000000000000)) (orderedInterval (27961438968 / 1000000000000) (27961442781 / 1000000000000), orderedInterval (-47624261779 / 1000000000000) (-47624257967 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (709264234658861 / 4000000000000)) (orderedInterval (49427364578 / 1000000000000) (49427415290 / 1000000000000), orderedInterval (-34010312525 / 1000000000000) (-34010261814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (443824625855183 / 4000000000000)) (orderedInterval (-74020381977 / 1000000000000) (-74020381322 / 1000000000000), orderedInterval (16411784511 / 1000000000000) (16411785165 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_stateChecks7 :
    compactCertificate332.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (238690359878961 / 4000000000000)) (orderedInterval (-71577128597 / 1000000000000) (-71577128596 / 1000000000000), orderedInterval (-73866899775 / 1000000000000) (-73866899774 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (648090758959883 / 4000000000000)) (orderedInterval (-33057207880 / 1000000000000) (-33057201576 / 1000000000000), orderedInterval (53360162911 / 1000000000000) (53360169214 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (884912524376491 / 4000000000000)) (orderedInterval (46265701159 / 1000000000000) (46265734177 / 1000000000000), orderedInterval (-27254933919 / 1000000000000) (-27254900901 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_stateChecks8 :
    compactCertificate332.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (374175374144817 / 4000000000000)) (orderedInterval (6602941771 / 1000000000000) (6602941773 / 1000000000000), orderedInterval (82196535475 / 1000000000000) (82196535477 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1521002122303057 / 4000000000000)) (orderedInterval (-32124818374 / 1000000000000) (-32124818373 / 1000000000000), orderedInterval (-25299563914 / 1000000000000) (-25299563913 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1015958928279263 / 4000000000000)) (orderedInterval (-15064318234 / 1000000000000) (-15064318233 / 1000000000000), orderedInterval (-47714964067 / 1000000000000) (-47714964066 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_states : ∀ j,
    BesselStateValid (compactCertificate332.point j) (compactCertificate332.state j) :=
  compactCertificate332.statesValid_of_checks3 compactCertificate332_stateChecks0
    compactCertificate332_stateChecks1 compactCertificate332_stateChecks2
    compactCertificate332_stateChecks3 compactCertificate332_stateChecks4
    compactCertificate332_stateChecks5 compactCertificate332_stateChecks6
    compactCertificate332_stateChecks7 compactCertificate332_stateChecks8

theorem compactCertificate332_chunkChecks0_0 :
    compactCertificate332.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (409 / 2) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49241762090 / 1000000000000) (-49241762089 / 1000000000000), orderedInterval (-26115054473 / 1000000000000) (-26115054472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (602535097691509 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37873097989 / 1000000000000) (37873097990 / 1000000000000), orderedInterval (52712826350 / 1000000000000) (52712826351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (194847470728597 / 800000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32936074384 / 1000000000000) (-32936056783 / 1000000000000), orderedInterval (39170474848 / 1000000000000) (39170492448 / 1000000000000)))) (orderedInterval (-21097533286 / 1000000000000) (-21097532238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (175818238762463 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (82454320892 / 1000000000000) (82454320893 / 1000000000000), orderedInterval (86725910478 / 1000000000000) (86725910479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (472272520197011 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-36997634040 / 1000000000000) (-36997628082 / 1000000000000), orderedInterval (63585126781 / 1000000000000) (63585132739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1282311762423687 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (35467722556 / 1000000000000) (35467722557 / 1000000000000), orderedInterval (26924122551 / 1000000000000) (26924122552 / 1000000000000)))) (orderedInterval (-4766806815 / 1000000000000) (-4766806572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (944545040394431 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50053915850 / 1000000000000) (-50053915848 / 1000000000000), orderedInterval (-13699272853 / 1000000000000) (-13699272852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1618494025970363 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5658503406 / 1000000000000) (-5658503405 / 1000000000000), orderedInterval (-39252984576 / 1000000000000) (-39252984575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1192175374144817 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17036264574 / 1000000000000) (-17036264573 / 1000000000000), orderedInterval (-42933747390 / 1000000000000) (-42933747389 / 1000000000000)))) (orderedInterval (-237202024 / 1000000000000) (-237202011 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_chunkChecks0_1 :
    compactCertificate332.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1829103605594591 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21420829803 / 1000000000000) (-21420827486 / 1000000000000), orderedInterval (30574181328 / 1000000000000) (30574183645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1056033459065639 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38450654125 / 1000000000000) (38450654126 / 1000000000000), orderedInterval (30470727734 / 1000000000000) (30470727735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1873949904728851 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34017429193 / 1000000000000) (-34017429191 / 1000000000000), orderedInterval (-14165708100 / 1000000000000) (-14165708099 / 1000000000000)))) (orderedInterval (1819321438 / 1000000000000) (1819321932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1750887083385919 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36906100441 / 1000000000000) (-36906093841 / 1000000000000), orderedInterval (9651150802 / 1000000000000) (9651157403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1249515639490927 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37873658565 / 1000000000000) (-37873585000 / 1000000000000), orderedInterval (24628053168 / 1000000000000) (24628126733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1416817560591033 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (446597789 / 1000000000000) (446597790 / 1000000000000), orderedInterval (-42393148079 / 1000000000000) (-42393148077 / 1000000000000)))) (orderedInterval (-2917432868 / 1000000000000) (-2917425768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1181194771364777 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32454014973 / 1000000000000) (32454014974 / 1000000000000), orderedInterval (33150278580 / 1000000000000) (33150278581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1043621402544317 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39834700727 / 1000000000000) (-39834700726 / 1000000000000), orderedInterval (-29133870538 / 1000000000000) (-29133870537 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (302482159555383 / 800000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38873919871 / 1000000000000) (38873929866 / 1000000000000), orderedInterval (-13186807096 / 1000000000000) (-13186797101 / 1000000000000)))) (orderedInterval (3649701697 / 1000000000000) (3649701974 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_chunkChecks0_2 :
    compactCertificate332.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (836681572094101 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27961438968 / 1000000000000) (27961442781 / 1000000000000), orderedInterval (-47624261779 / 1000000000000) (-47624257967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (709264234658861 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (49427364578 / 1000000000000) (49427415290 / 1000000000000), orderedInterval (-34010312525 / 1000000000000) (-34010261814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (443824625855183 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-74020381977 / 1000000000000) (-74020381322 / 1000000000000), orderedInterval (16411784511 / 1000000000000) (16411785165 / 1000000000000)))) (orderedInterval (-9678166519 / 1000000000000) (-9678162966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (238690359878961 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-71577128597 / 1000000000000) (-71577128596 / 1000000000000), orderedInterval (-73866899775 / 1000000000000) (-73866899774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (648090758959883 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33057207880 / 1000000000000) (-33057201576 / 1000000000000), orderedInterval (53360162911 / 1000000000000) (53360169214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (884912524376491 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (46265701159 / 1000000000000) (46265734177 / 1000000000000), orderedInterval (-27254933919 / 1000000000000) (-27254900901 / 1000000000000)))) (orderedInterval (-1474109375 / 1000000000000) (-1474106677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (374175374144817 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (6602941771 / 1000000000000) (6602941773 / 1000000000000), orderedInterval (82196535475 / 1000000000000) (82196535477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1521002122303057 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32124818374 / 1000000000000) (-32124818373 / 1000000000000), orderedInterval (-25299563914 / 1000000000000) (-25299563913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1015958928279263 / 4000000000000) 0 (IntervalRat.scale (409 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15064318234 / 1000000000000) (-15064318233 / 1000000000000), orderedInterval (-47714964067 / 1000000000000) (-47714964066 / 1000000000000)))) (orderedInterval (5481287683 / 1000000000000) (5481287741 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_chunkChecks0 :
    compactCertificate332.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate332.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate332_chunkChecks0_0
    compactCertificate332_chunkChecks0_1 compactCertificate332_chunkChecks0_2

theorem compactCertificate332_chunkChecks1_0 :
    compactCertificate332.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (409 / 2) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49241762090 / 1000000000000) (-49241762089 / 1000000000000), orderedInterval (-26115054473 / 1000000000000) (-26115054472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (602535097691509 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37873097989 / 1000000000000) (37873097990 / 1000000000000), orderedInterval (52712826350 / 1000000000000) (52712826351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (194847470728597 / 800000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32936074384 / 1000000000000) (-32936056783 / 1000000000000), orderedInterval (39170474848 / 1000000000000) (39170492448 / 1000000000000)))) (orderedInterval (-7251698672 / 1000000000000) (-7251697425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (175818238762463 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (82454320892 / 1000000000000) (82454320893 / 1000000000000), orderedInterval (86725910478 / 1000000000000) (86725910479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (472272520197011 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-36997634040 / 1000000000000) (-36997628082 / 1000000000000), orderedInterval (63585126781 / 1000000000000) (63585132739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1282311762423687 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (35467722556 / 1000000000000) (35467722557 / 1000000000000), orderedInterval (26924122551 / 1000000000000) (26924122552 / 1000000000000)))) (orderedInterval (-1862320921 / 1000000000000) (-1862320767 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (944545040394431 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50053915850 / 1000000000000) (-50053915848 / 1000000000000), orderedInterval (-13699272853 / 1000000000000) (-13699272852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1618494025970363 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5658503406 / 1000000000000) (-5658503405 / 1000000000000), orderedInterval (-39252984576 / 1000000000000) (-39252984575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1192175374144817 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17036264574 / 1000000000000) (-17036264573 / 1000000000000), orderedInterval (-42933747390 / 1000000000000) (-42933747389 / 1000000000000)))) (orderedInterval (883266350 / 1000000000000) (883266371 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_chunkChecks1_1 :
    compactCertificate332.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1829103605594591 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21420829803 / 1000000000000) (-21420827486 / 1000000000000), orderedInterval (30574181328 / 1000000000000) (30574183645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1056033459065639 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38450654125 / 1000000000000) (38450654126 / 1000000000000), orderedInterval (30470727734 / 1000000000000) (30470727735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1873949904728851 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34017429193 / 1000000000000) (-34017429191 / 1000000000000), orderedInterval (-14165708100 / 1000000000000) (-14165708099 / 1000000000000)))) (orderedInterval (-13846475329 / 1000000000000) (-13846474240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1750887083385919 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36906100441 / 1000000000000) (-36906093841 / 1000000000000), orderedInterval (9651150802 / 1000000000000) (9651157403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1249515639490927 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37873658565 / 1000000000000) (-37873585000 / 1000000000000), orderedInterval (24628053168 / 1000000000000) (24628126733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1416817560591033 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (446597789 / 1000000000000) (446597790 / 1000000000000), orderedInterval (-42393148079 / 1000000000000) (-42393148077 / 1000000000000)))) (orderedInterval (3556098579 / 1000000000000) (3556109500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1181194771364777 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32454014973 / 1000000000000) (32454014974 / 1000000000000), orderedInterval (33150278580 / 1000000000000) (33150278581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1043621402544317 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39834700727 / 1000000000000) (-39834700726 / 1000000000000), orderedInterval (-29133870538 / 1000000000000) (-29133870537 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (302482159555383 / 800000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38873919871 / 1000000000000) (38873929866 / 1000000000000), orderedInterval (-13186807096 / 1000000000000) (-13186797101 / 1000000000000)))) (orderedInterval (2055612756 / 1000000000000) (2055613259 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_chunkChecks1_2 :
    compactCertificate332.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (836681572094101 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27961438968 / 1000000000000) (27961442781 / 1000000000000), orderedInterval (-47624261779 / 1000000000000) (-47624257967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (709264234658861 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (49427364578 / 1000000000000) (49427415290 / 1000000000000), orderedInterval (-34010312525 / 1000000000000) (-34010261814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (443824625855183 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-74020381977 / 1000000000000) (-74020381322 / 1000000000000), orderedInterval (16411784511 / 1000000000000) (16411785165 / 1000000000000)))) (orderedInterval (9747651000 / 1000000000000) (9747654172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (238690359878961 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-71577128597 / 1000000000000) (-71577128596 / 1000000000000), orderedInterval (-73866899775 / 1000000000000) (-73866899774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (648090758959883 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33057207880 / 1000000000000) (-33057201576 / 1000000000000), orderedInterval (53360162911 / 1000000000000) (53360169214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (884912524376491 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (46265701159 / 1000000000000) (46265734177 / 1000000000000), orderedInterval (-27254933919 / 1000000000000) (-27254900901 / 1000000000000)))) (orderedInterval (1698525451 / 1000000000000) (1698528324 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (374175374144817 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (6602941771 / 1000000000000) (6602941773 / 1000000000000), orderedInterval (82196535475 / 1000000000000) (82196535477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1521002122303057 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32124818374 / 1000000000000) (-32124818373 / 1000000000000), orderedInterval (-25299563914 / 1000000000000) (-25299563913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1015958928279263 / 4000000000000) 1 (IntervalRat.scale (409 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15064318234 / 1000000000000) (-15064318233 / 1000000000000), orderedInterval (-47714964067 / 1000000000000) (-47714964066 / 1000000000000)))) (orderedInterval (15175146821 / 1000000000000) (15175146902 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_chunkChecks1 :
    compactCertificate332.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate332.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate332_chunkChecks1_0
    compactCertificate332_chunkChecks1_1 compactCertificate332_chunkChecks1_2

theorem compactCertificate332_chunkChecks2_0 :
    compactCertificate332.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (409 / 2) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49241762090 / 1000000000000) (-49241762089 / 1000000000000), orderedInterval (-26115054473 / 1000000000000) (-26115054472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (602535097691509 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37873097989 / 1000000000000) (37873097990 / 1000000000000), orderedInterval (52712826350 / 1000000000000) (52712826351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (194847470728597 / 800000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32936074384 / 1000000000000) (-32936056783 / 1000000000000), orderedInterval (39170474848 / 1000000000000) (39170492448 / 1000000000000)))) (orderedInterval (22103225827 / 1000000000000) (22103227317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (175818238762463 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (82454320892 / 1000000000000) (82454320893 / 1000000000000), orderedInterval (86725910478 / 1000000000000) (86725910479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (472272520197011 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-36997634040 / 1000000000000) (-36997628082 / 1000000000000), orderedInterval (63585126781 / 1000000000000) (63585132739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1282311762423687 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (35467722556 / 1000000000000) (35467722557 / 1000000000000), orderedInterval (26924122551 / 1000000000000) (26924122552 / 1000000000000)))) (orderedInterval (6696842947 / 1000000000000) (6696843060 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (944545040394431 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50053915850 / 1000000000000) (-50053915848 / 1000000000000), orderedInterval (-13699272853 / 1000000000000) (-13699272852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1618494025970363 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5658503406 / 1000000000000) (-5658503405 / 1000000000000), orderedInterval (-39252984576 / 1000000000000) (-39252984575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1192175374144817 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17036264574 / 1000000000000) (-17036264573 / 1000000000000), orderedInterval (-42933747390 / 1000000000000) (-42933747389 / 1000000000000)))) (orderedInterval (186977155 / 1000000000000) (186977192 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_chunkChecks2_1 :
    compactCertificate332.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1829103605594591 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21420829803 / 1000000000000) (-21420827486 / 1000000000000), orderedInterval (30574181328 / 1000000000000) (30574183645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1056033459065639 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38450654125 / 1000000000000) (38450654126 / 1000000000000), orderedInterval (30470727734 / 1000000000000) (30470727735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1873949904728851 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34017429193 / 1000000000000) (-34017429191 / 1000000000000), orderedInterval (-14165708100 / 1000000000000) (-14165708099 / 1000000000000)))) (orderedInterval (1667536039 / 1000000000000) (1667538465 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1750887083385919 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36906100441 / 1000000000000) (-36906093841 / 1000000000000), orderedInterval (9651150802 / 1000000000000) (9651157403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1249515639490927 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37873658565 / 1000000000000) (-37873585000 / 1000000000000), orderedInterval (24628053168 / 1000000000000) (24628126733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1416817560591033 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (446597789 / 1000000000000) (446597790 / 1000000000000), orderedInterval (-42393148079 / 1000000000000) (-42393148077 / 1000000000000)))) (orderedInterval (5293546512 / 1000000000000) (5293563409 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1181194771364777 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32454014973 / 1000000000000) (32454014974 / 1000000000000), orderedInterval (33150278580 / 1000000000000) (33150278581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1043621402544317 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39834700727 / 1000000000000) (-39834700726 / 1000000000000), orderedInterval (-29133870538 / 1000000000000) (-29133870537 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (302482159555383 / 800000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38873919871 / 1000000000000) (38873929866 / 1000000000000), orderedInterval (-13186807096 / 1000000000000) (-13186797101 / 1000000000000)))) (orderedInterval (-7904559837 / 1000000000000) (-7904558917 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_chunkChecks2_2 :
    compactCertificate332.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (836681572094101 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27961438968 / 1000000000000) (27961442781 / 1000000000000), orderedInterval (-47624261779 / 1000000000000) (-47624257967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (709264234658861 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (49427364578 / 1000000000000) (49427415290 / 1000000000000), orderedInterval (-34010312525 / 1000000000000) (-34010261814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (443824625855183 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-74020381977 / 1000000000000) (-74020381322 / 1000000000000), orderedInterval (16411784511 / 1000000000000) (16411785165 / 1000000000000)))) (orderedInterval (7442355714 / 1000000000000) (7442358577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (238690359878961 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-71577128597 / 1000000000000) (-71577128596 / 1000000000000), orderedInterval (-73866899775 / 1000000000000) (-73866899774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (648090758959883 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33057207880 / 1000000000000) (-33057201576 / 1000000000000), orderedInterval (53360162911 / 1000000000000) (53360169214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (884912524376491 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (46265701159 / 1000000000000) (46265734177 / 1000000000000), orderedInterval (-27254933919 / 1000000000000) (-27254900901 / 1000000000000)))) (orderedInterval (3557954703 / 1000000000000) (3557957790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (374175374144817 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (6602941771 / 1000000000000) (6602941773 / 1000000000000), orderedInterval (82196535475 / 1000000000000) (82196535477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1521002122303057 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32124818374 / 1000000000000) (-32124818373 / 1000000000000), orderedInterval (-25299563914 / 1000000000000) (-25299563913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1015958928279263 / 4000000000000) 2 (IntervalRat.scale (409 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15064318234 / 1000000000000) (-15064318233 / 1000000000000), orderedInterval (-47714964067 / 1000000000000) (-47714964066 / 1000000000000)))) (orderedInterval (-13483795967 / 1000000000000) (-13483795848 / 1000000000000))) = true
  rfl'

theorem compactCertificate332_chunkChecks2 :
    compactCertificate332.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate332.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate332_chunkChecks2_0
    compactCertificate332_chunkChecks2_1 compactCertificate332_chunkChecks2_2

theorem compactCertificate332_chunkChecks3_0 :
    compactCertificate332.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (409 / 2) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49241762090 / 1000000000000) (-49241762089 / 1000000000000), orderedInterval (-26115054473 / 1000000000000) (-26115054472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (602535097691509 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37873097989 / 1000000000000) (37873097990 / 1000000000000), orderedInterval (52712826350 / 1000000000000) (52712826351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (194847470728597 / 800000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32936074384 / 1000000000000) (-32936056783 / 1000000000000), orderedInterval (39170474848 / 1000000000000) (39170492448 / 1000000000000)))) (orderedInterval (6163311839 / 1000000000000) (6163313614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (175818238762463 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (82454320892 / 1000000000000) (82454320893 / 1000000000000), orderedInterval (86725910478 / 1000000000000) (86725910479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (472272520197011 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-36997634040 / 1000000000000) (-36997628082 / 1000000000000), orderedInterval (63585126781 / 1000000000000) (63585132739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1282311762423687 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (35467722556 / 1000000000000) (35467722557 / 1000000000000), orderedInterval (26924122551 / 1000000000000) (26924122552 / 1000000000000)))) (orderedInterval (6903175872 / 1000000000000) (6903175973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (944545040394431 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50053915850 / 1000000000000) (-50053915848 / 1000000000000), orderedInterval (-13699272853 / 1000000000000) (-13699272852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1618494025970363 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5658503406 / 1000000000000) (-5658503405 / 1000000000000), orderedInterval (-39252984576 / 1000000000000) (-39252984575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1192175374144817 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17036264574 / 1000000000000) (-17036264573 / 1000000000000), orderedInterval (-42933747390 / 1000000000000) (-42933747389 / 1000000000000)))) (orderedInterval (-6166849967 / 1000000000000) (-6166849902 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate332_chunkChecks3_1 :
    compactCertificate332.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1829103605594591 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21420829803 / 1000000000000) (-21420827486 / 1000000000000), orderedInterval (30574181328 / 1000000000000) (30574183645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1056033459065639 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38450654125 / 1000000000000) (38450654126 / 1000000000000), orderedInterval (30470727734 / 1000000000000) (30470727735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1873949904728851 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34017429193 / 1000000000000) (-34017429191 / 1000000000000), orderedInterval (-14165708100 / 1000000000000) (-14165708099 / 1000000000000)))) (orderedInterval (80084132762 / 1000000000000) (80084138166 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1750887083385919 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36906100441 / 1000000000000) (-36906093841 / 1000000000000), orderedInterval (9651150802 / 1000000000000) (9651157403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1249515639490927 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37873658565 / 1000000000000) (-37873585000 / 1000000000000), orderedInterval (24628053168 / 1000000000000) (24628126733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1416817560591033 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (446597789 / 1000000000000) (446597790 / 1000000000000), orderedInterval (-42393148079 / 1000000000000) (-42393148077 / 1000000000000)))) (orderedInterval (-7732679283 / 1000000000000) (-7732653127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1181194771364777 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32454014973 / 1000000000000) (32454014974 / 1000000000000), orderedInterval (33150278580 / 1000000000000) (33150278581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1043621402544317 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39834700727 / 1000000000000) (-39834700726 / 1000000000000), orderedInterval (-29133870538 / 1000000000000) (-29133870537 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (302482159555383 / 800000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38873919871 / 1000000000000) (38873929866 / 1000000000000), orderedInterval (-13186807096 / 1000000000000) (-13186797101 / 1000000000000)))) (orderedInterval (-2442219874 / 1000000000000) (-2442218187 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate332_chunkChecks3_2 :
    compactCertificate332.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (836681572094101 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27961438968 / 1000000000000) (27961442781 / 1000000000000), orderedInterval (-47624261779 / 1000000000000) (-47624257967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (709264234658861 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (49427364578 / 1000000000000) (49427415290 / 1000000000000), orderedInterval (-34010312525 / 1000000000000) (-34010261814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (443824625855183 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-74020381977 / 1000000000000) (-74020381322 / 1000000000000), orderedInterval (16411784511 / 1000000000000) (16411785165 / 1000000000000)))) (orderedInterval (-9524832671 / 1000000000000) (-9524830086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (238690359878961 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-71577128597 / 1000000000000) (-71577128596 / 1000000000000), orderedInterval (-73866899775 / 1000000000000) (-73866899774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (648090758959883 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33057207880 / 1000000000000) (-33057201576 / 1000000000000), orderedInterval (53360162911 / 1000000000000) (53360169214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (884912524376491 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (46265701159 / 1000000000000) (46265734177 / 1000000000000), orderedInterval (-27254933919 / 1000000000000) (-27254900901 / 1000000000000)))) (orderedInterval (-2093636524 / 1000000000000) (-2093633211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (374175374144817 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (6602941771 / 1000000000000) (6602941773 / 1000000000000), orderedInterval (82196535475 / 1000000000000) (82196535477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1521002122303057 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32124818374 / 1000000000000) (-32124818373 / 1000000000000), orderedInterval (-25299563914 / 1000000000000) (-25299563913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1015958928279263 / 4000000000000) 3 (IntervalRat.scale (409 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15064318234 / 1000000000000) (-15064318233 / 1000000000000), orderedInterval (-47714964067 / 1000000000000) (-47714964066 / 1000000000000)))) (orderedInterval (-30372880006 / 1000000000000) (-30372879823 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate332_chunkChecks3 :
    compactCertificate332.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate332.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate332_chunkChecks3_0
    compactCertificate332_chunkChecks3_1 compactCertificate332_chunkChecks3_2

theorem compactCertificate332_chunkChecks4_0 :
    compactCertificate332.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (409 / 2) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49241762090 / 1000000000000) (-49241762089 / 1000000000000), orderedInterval (-26115054473 / 1000000000000) (-26115054472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (602535097691509 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (37873097989 / 1000000000000) (37873097990 / 1000000000000), orderedInterval (52712826350 / 1000000000000) (52712826351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (194847470728597 / 800000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32936074384 / 1000000000000) (-32936056783 / 1000000000000), orderedInterval (39170474848 / 1000000000000) (39170492448 / 1000000000000)))) (orderedInterval (-23362374453 / 1000000000000) (-23362372332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (175818238762463 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (82454320892 / 1000000000000) (82454320893 / 1000000000000), orderedInterval (86725910478 / 1000000000000) (86725910479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (472272520197011 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-36997634040 / 1000000000000) (-36997628082 / 1000000000000), orderedInterval (63585126781 / 1000000000000) (63585132739 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1282311762423687 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (35467722556 / 1000000000000) (35467722557 / 1000000000000), orderedInterval (26924122551 / 1000000000000) (26924122552 / 1000000000000)))) (orderedInterval (-15445884852 / 1000000000000) (-15445884737 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (944545040394431 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50053915850 / 1000000000000) (-50053915848 / 1000000000000), orderedInterval (-13699272853 / 1000000000000) (-13699272852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1618494025970363 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5658503406 / 1000000000000) (-5658503405 / 1000000000000), orderedInterval (-39252984576 / 1000000000000) (-39252984575 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1192175374144817 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17036264574 / 1000000000000) (-17036264573 / 1000000000000), orderedInterval (-42933747390 / 1000000000000) (-42933747389 / 1000000000000)))) (orderedInterval (877544763 / 1000000000000) (877544884 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate332_chunkChecks4_1 :
    compactCertificate332.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1829103605594591 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21420829803 / 1000000000000) (-21420827486 / 1000000000000), orderedInterval (30574181328 / 1000000000000) (30574183645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1056033459065639 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (38450654125 / 1000000000000) (38450654126 / 1000000000000), orderedInterval (30470727734 / 1000000000000) (30470727735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1873949904728851 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34017429193 / 1000000000000) (-34017429191 / 1000000000000), orderedInterval (-14165708100 / 1000000000000) (-14165708099 / 1000000000000)))) (orderedInterval (-30908189044 / 1000000000000) (-30908176945 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1750887083385919 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-36906100441 / 1000000000000) (-36906093841 / 1000000000000), orderedInterval (9651150802 / 1000000000000) (9651157403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1249515639490927 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37873658565 / 1000000000000) (-37873585000 / 1000000000000), orderedInterval (24628053168 / 1000000000000) (24628126733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1416817560591033 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (446597789 / 1000000000000) (446597790 / 1000000000000), orderedInterval (-42393148079 / 1000000000000) (-42393148077 / 1000000000000)))) (orderedInterval (-5458343526 / 1000000000000) (-5458302704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1181194771364777 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32454014973 / 1000000000000) (32454014974 / 1000000000000), orderedInterval (33150278580 / 1000000000000) (33150278581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1043621402544317 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39834700727 / 1000000000000) (-39834700726 / 1000000000000), orderedInterval (-29133870538 / 1000000000000) (-29133870537 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (302482159555383 / 800000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (38873919871 / 1000000000000) (38873929866 / 1000000000000), orderedInterval (-13186807096 / 1000000000000) (-13186797101 / 1000000000000)))) (orderedInterval (19324250660 / 1000000000000) (19324253770 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate332_chunkChecks4_2 :
    compactCertificate332.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (836681572094101 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27961438968 / 1000000000000) (27961442781 / 1000000000000), orderedInterval (-47624261779 / 1000000000000) (-47624257967 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (709264234658861 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (49427364578 / 1000000000000) (49427415290 / 1000000000000), orderedInterval (-34010312525 / 1000000000000) (-34010261814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (443824625855183 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-74020381977 / 1000000000000) (-74020381322 / 1000000000000), orderedInterval (16411784511 / 1000000000000) (16411785165 / 1000000000000)))) (orderedInterval (-6590215217 / 1000000000000) (-6590212857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (238690359878961 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-71577128597 / 1000000000000) (-71577128596 / 1000000000000), orderedInterval (-73866899775 / 1000000000000) (-73866899774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (648090758959883 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33057207880 / 1000000000000) (-33057201576 / 1000000000000), orderedInterval (53360162911 / 1000000000000) (53360169214 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (884912524376491 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (46265701159 / 1000000000000) (46265734177 / 1000000000000), orderedInterval (-27254933919 / 1000000000000) (-27254900901 / 1000000000000)))) (orderedInterval (-4530550199 / 1000000000000) (-4530546621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (374175374144817 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (6602941771 / 1000000000000) (6602941773 / 1000000000000), orderedInterval (82196535475 / 1000000000000) (82196535477 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1521002122303057 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32124818374 / 1000000000000) (-32124818373 / 1000000000000), orderedInterval (-25299563914 / 1000000000000) (-25299563913 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1015958928279263 / 4000000000000) 4 (IntervalRat.scale (409 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-15064318234 / 1000000000000) (-15064318233 / 1000000000000), orderedInterval (-47714964067 / 1000000000000) (-47714964066 / 1000000000000)))) (orderedInterval (38283526362 / 1000000000000) (38283526655 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate332_chunkChecks4 :
    compactCertificate332.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate332.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate332_chunkChecks4_0
    compactCertificate332_chunkChecks4_1 compactCertificate332_chunkChecks4_2

theorem compactCertificate332_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate332.chunkCheck r b = true :=
  compactCertificate332.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate332_chunkChecks0
    · exact compactCertificate332_chunkChecks1
    · exact compactCertificate332_chunkChecks2
    · exact compactCertificate332_chunkChecks3
    · exact compactCertificate332_chunkChecks4)

theorem compactCertificate332_coefficient0 :
    compactCertificate332.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate332_coefficient1 :
    compactCertificate332.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate332_coefficient2 :
    compactCertificate332.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate332_coefficient3 :
    compactCertificate332.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate332_coefficient4 :
    compactCertificate332.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate332_coefficients : ∀ r : Fin 5,
    compactCertificate332.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate332_coefficient0
  · exact compactCertificate332_coefficient1
  · exact compactCertificate332_coefficient2
  · exact compactCertificate332_coefficient3
  · exact compactCertificate332_coefficient4

theorem compactCertificate332_lower : (1 : ℚ) ≤ compactCertificate332.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate332, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate332_proves {t : ℝ} (ht : t ∈ compactCertificate332.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate332.proves compactCertificate332_states compactCertificate332_chunks
    compactCertificate332_coefficients compactCertificate332_lower ht

end Erdos232
