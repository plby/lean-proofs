/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate413 : CompactCertificate where
  left := 284
  right := 285
  center := 569 / 2
  grid := fun i =>
    match i.val with
    | 0 => 91
    | 1 => 67
    | 2 => 108
    | 3 => 19
    | 4 => 52
    | 5 => 142
    | 6 => 105
    | 7 => 179
    | 8 => 132
    | 9 => 203
    | 10 => 117
    | 11 => 208
    | 12 => 194
    | 13 => 138
    | 14 => 157
    | 15 => 131
    | 16 => 116
    | 17 => 168
    | 18 => 93
    | 19 => 79
    | 20 => 49
    | 21 => 26
    | 22 => 72
    | 23 => 98
    | 24 => 41
    | 25 => 168
    | _ => 113
  point := fun i =>
    match i.val with
    | 0 => 569 / 2
    | 1 => 838245649355669 / 4000000000000
    | 2 => 271071420157877 / 800000000000
    | 3 => 244597989867583 / 4000000000000
    | 4 => 657024606337651 / 4000000000000
    | 5 => 1783949615694567 / 4000000000000
    | 6 => 1314049212675871 / 4000000000000
    | 7 => 2251645723171483 / 4000000000000
    | 8 => 1658552048626897 / 4000000000000
    | 9 => 2544645358394431 / 4000000000000
    | 10 => 1469151682660999 / 4000000000000
    | 11 => 2607035442031091 / 4000000000000
    | 12 => 2435830685688479 / 4000000000000
    | 13 => 1738323713619407 / 4000000000000
    | 14 => 1971073819012953 / 4000000000000
    | 15 => 1643275855517257 / 4000000000000
    | 16 => 1451884053906397 / 4000000000000
    | 17 => 420812588721303 / 800000000000
    | 18 => 1163989766556341 / 4000000000000
    | 19 => 986727015943501 / 4000000000000
    | 20 => 617447951373103 / 4000000000000
    | 21 => 332065561787601 / 4000000000000
    | 22 => 901622596205803 / 4000000000000
    | 23 => 1231088573032331 / 4000000000000
    | 24 => 520552048626897 / 4000000000000
    | 25 => 2116015177482737 / 4000000000000
    | _ => 1413400073816383 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (26708822683 / 1000000000000) (26708827947 / 1000000000000), orderedInterval (-39089473496 / 1000000000000) (-39089468232 / 1000000000000))
    | 1 => (orderedInterval (7718113733 / 1000000000000) (7718113758 / 1000000000000), orderedInterval (-54592276499 / 1000000000000) (-54592276474 / 1000000000000))
    | 2 => (orderedInterval (14139963225 / 1000000000000) (14139963226 / 1000000000000), orderedInterval (40953373731 / 1000000000000) (40953373732 / 1000000000000))
    | 3 => (orderedInterval (-79861050975 / 1000000000000) (-79860993923 / 1000000000000), orderedInterval (64158934724 / 1000000000000) (64158991776 / 1000000000000))
    | 4 => (orderedInterval (61898369860 / 1000000000000) (61898370095 / 1000000000000), orderedInterval (-6847889889 / 1000000000000) (-6847889654 / 1000000000000))
    | 5 => (orderedInterval (23353950064 / 1000000000000) (23353950065 / 1000000000000), orderedInterval (29672843558 / 1000000000000) (29672843559 / 1000000000000))
    | 6 => (orderedInterval (23751947048 / 1000000000000) (23751950054 / 1000000000000), orderedInterval (-37100056830 / 1000000000000) (-37100053824 / 1000000000000))
    | 7 => (orderedInterval (-32824224231 / 1000000000000) (-32824224190 / 1000000000000), orderedInterval (-7285977771 / 1000000000000) (-7285977731 / 1000000000000))
    | 8 => (orderedInterval (26214356293 / 1000000000000) (26214356294 / 1000000000000), orderedInterval (29091754519 / 1000000000000) (29091754520 / 1000000000000))
    | 9 => (orderedInterval (22621592815 / 1000000000000) (22621599207 / 1000000000000), orderedInterval (-22130765661 / 1000000000000) (-22130759269 / 1000000000000))
    | 10 => (orderedInterval (-20201957134 / 1000000000000) (-20201957133 / 1000000000000), orderedInterval (-36375530565 / 1000000000000) (-36375530564 / 1000000000000))
    | 11 => (orderedInterval (-24620934774 / 1000000000000) (-24620917093 / 1000000000000), orderedInterval (19269382304 / 1000000000000) (19269399985 / 1000000000000))
    | 12 => (orderedInterval (8745374424 / 1000000000000) (8745374425 / 1000000000000), orderedInterval (31120685582 / 1000000000000) (31120685583 / 1000000000000))
    | 13 => (orderedInterval (37031993884 / 1000000000000) (37032000428 / 1000000000000), orderedInterval (-9713976084 / 1000000000000) (-9713969540 / 1000000000000))
    | 14 => (orderedInterval (-11427714315 / 1000000000000) (-11427714314 / 1000000000000), orderedInterval (-34066735622 / 1000000000000) (-34066735621 / 1000000000000))
    | 15 => (orderedInterval (-2180519842 / 1000000000000) (-2180519841 / 1000000000000), orderedInterval (-39302336537 / 1000000000000) (-39302336536 / 1000000000000))
    | 16 => (orderedInterval (-25963394476 / 1000000000000) (-25963387368 / 1000000000000), orderedInterval (32896318954 / 1000000000000) (32896326063 / 1000000000000))
    | 17 => (orderedInterval (-29020711517 / 1000000000000) (-29020646659 / 1000000000000), orderedInterval (19212636636 / 1000000000000) (19212701495 / 1000000000000))
    | 18 => (orderedInterval (17596647747 / 1000000000000) (17596648177 / 1000000000000), orderedInterval (-43367013336 / 1000000000000) (-43367012905 / 1000000000000))
    | 19 => (orderedInterval (33465749968 / 1000000000000) (33465770766 / 1000000000000), orderedInterval (-38287949909 / 1000000000000) (-38287929111 / 1000000000000))
    | 20 => (orderedInterval (-60051794165 / 1000000000000) (-60051794164 / 1000000000000), orderedInterval (-22564357144 / 1000000000000) (-22564357143 / 1000000000000))
    | 21 => (orderedInterval (74743213921 / 1000000000000) (74743234357 / 1000000000000), orderedInterval (-46078995400 / 1000000000000) (-46078974963 / 1000000000000))
    | 22 => (orderedInterval (-222057387 / 1000000000000) (-222057384 / 1000000000000), orderedInterval (53144513015 / 1000000000000) (53144513018 / 1000000000000))
    | 23 => (orderedInterval (28635115419 / 1000000000000) (28635115420 / 1000000000000), orderedInterval (35287716953 / 1000000000000) (35287716954 / 1000000000000))
    | 24 => (orderedInterval (-59759919361 / 1000000000000) (-59759894334 / 1000000000000), orderedInterval (36569902619 / 1000000000000) (36569927646 / 1000000000000))
    | 25 => (orderedInterval (31523851999 / 1000000000000) (31523906276 / 1000000000000), orderedInterval (-14510016743 / 1000000000000) (-14509962466 / 1000000000000))
    | _ => (orderedInterval (32302902159 / 1000000000000) (32302950222 / 1000000000000), orderedInterval (-27580976045 / 1000000000000) (-27580927981 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11488109314 / 1000000000000) (11488111421 / 1000000000000)
      | 1 => orderedInterval (1466228777 / 1000000000000) (1466229440 / 1000000000000)
      | 2 => orderedInterval (1645979666 / 1000000000000) (1645979684 / 1000000000000)
      | 3 => orderedInterval (-9016394829 / 1000000000000) (-9016391066 / 1000000000000)
      | 4 => orderedInterval (3401801278 / 1000000000000) (3401801932 / 1000000000000)
      | 5 => orderedInterval (717573599 / 1000000000000) (717575694 / 1000000000000)
      | 6 => orderedInterval (-6662734670 / 1000000000000) (-6662733352 / 1000000000000)
      | 7 => orderedInterval (-3569667687 / 1000000000000) (-3569667275 / 1000000000000)
      | _ => orderedInterval (-8987244786 / 1000000000000) (-8987231119 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-13006202504 / 1000000000000) (-13006200394 / 1000000000000)
      | 1 => orderedInterval (-3600750923 / 1000000000000) (-3600750745 / 1000000000000)
      | 2 => orderedInterval (1469350863 / 1000000000000) (1469350894 / 1000000000000)
      | 3 => orderedInterval (11588990042 / 1000000000000) (11588998574 / 1000000000000)
      | 4 => orderedInterval (-2307111798 / 1000000000000) (-2307110798 / 1000000000000)
      | 5 => orderedInterval (-2147638560 / 1000000000000) (-2147634931 / 1000000000000)
      | 6 => orderedInterval (8572876101 / 1000000000000) (8572877258 / 1000000000000)
      | 7 => orderedInterval (-3632601350 / 1000000000000) (-3632601209 / 1000000000000)
      | _ => orderedInterval (8724327874 / 1000000000000) (8724347470 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11756730954 / 1000000000000) (-11756728834 / 1000000000000)
      | 1 => orderedInterval (3299169060 / 1000000000000) (3299169146 / 1000000000000)
      | 2 => orderedInterval (-5314400204 / 1000000000000) (-5314400149 / 1000000000000)
      | 3 => orderedInterval (40920549989 / 1000000000000) (40920569389 / 1000000000000)
      | 4 => orderedInterval (-7613036281 / 1000000000000) (-7613034742 / 1000000000000)
      | 5 => orderedInterval (181667762 / 1000000000000) (181674173 / 1000000000000)
      | 6 => orderedInterval (4912995702 / 1000000000000) (4912996727 / 1000000000000)
      | 7 => orderedInterval (2695397777 / 1000000000000) (2695397841 / 1000000000000)
      | _ => orderedInterval (18266159961 / 1000000000000) (18266189411 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11678194963 / 1000000000000) (11678197087 / 1000000000000)
      | 1 => orderedInterval (8169569190 / 1000000000000) (8169569279 / 1000000000000)
      | 2 => orderedInterval (-3898599214 / 1000000000000) (-3898599114 / 1000000000000)
      | 3 => orderedInterval (-71244127926 / 1000000000000) (-71244083844 / 1000000000000)
      | 4 => orderedInterval (7914494351 / 1000000000000) (7914496716 / 1000000000000)
      | 5 => orderedInterval (2166129495 / 1000000000000) (2166140949 / 1000000000000)
      | 6 => orderedInterval (-8732578652 / 1000000000000) (-8732577746 / 1000000000000)
      | 7 => orderedInterval (3992809593 / 1000000000000) (3992809635 / 1000000000000)
      | _ => orderedInterval (-17593047331 / 1000000000000) (-17593001280 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12194897071 / 1000000000000) (12194899208 / 1000000000000)
      | 1 => orderedInterval (-9830433914 / 1000000000000) (-9830433787 / 1000000000000)
      | 2 => orderedInterval (18402365159 / 1000000000000) (18402365345 / 1000000000000)
      | 3 => orderedInterval (-200548514921 / 1000000000000) (-200548414558 / 1000000000000)
      | 4 => orderedInterval (16216406346 / 1000000000000) (16216409999 / 1000000000000)
      | 5 => orderedInterval (-4871349826 / 1000000000000) (-4871329119 / 1000000000000)
      | 6 => orderedInterval (-4258135515 / 1000000000000) (-4258134708 / 1000000000000)
      | 7 => orderedInterval (-3041690852 / 1000000000000) (-3041690815 / 1000000000000)
      | _ => orderedInterval (-44988623443 / 1000000000000) (-44988548438 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9516349338 / 1000000000000) (-9516324641 / 1000000000000)
    | 1 => orderedInterval (5661239745 / 1000000000000) (5661276119 / 1000000000000)
    | 2 => orderedInterval (45591772812 / 1000000000000) (45591832962 / 1000000000000)
    | 3 => orderedInterval (-67547155531 / 1000000000000) (-67547048318 / 1000000000000)
    | _ => orderedInterval (-220725079895 / 1000000000000) (-220724876873 / 1000000000000)

theorem compactCertificate413_stateChecks0 :
    compactCertificate413.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (569 / 2)) (orderedInterval (26708822683 / 1000000000000) (26708827947 / 1000000000000), orderedInterval (-39089473496 / 1000000000000) (-39089468232 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (838245649355669 / 4000000000000)) (orderedInterval (7718113733 / 1000000000000) (7718113758 / 1000000000000), orderedInterval (-54592276499 / 1000000000000) (-54592276474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (271071420157877 / 800000000000)) (orderedInterval (14139963225 / 1000000000000) (14139963226 / 1000000000000), orderedInterval (40953373731 / 1000000000000) (40953373732 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_stateChecks1 :
    compactCertificate413.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (244597989867583 / 4000000000000)) (orderedInterval (-79861050975 / 1000000000000) (-79860993923 / 1000000000000), orderedInterval (64158934724 / 1000000000000) (64158991776 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (657024606337651 / 4000000000000)) (orderedInterval (61898369860 / 1000000000000) (61898370095 / 1000000000000), orderedInterval (-6847889889 / 1000000000000) (-6847889654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1783949615694567 / 4000000000000)) (orderedInterval (23353950064 / 1000000000000) (23353950065 / 1000000000000), orderedInterval (29672843558 / 1000000000000) (29672843559 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_stateChecks2 :
    compactCertificate413.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1314049212675871 / 4000000000000)) (orderedInterval (23751947048 / 1000000000000) (23751950054 / 1000000000000), orderedInterval (-37100056830 / 1000000000000) (-37100053824 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2251645723171483 / 4000000000000)) (orderedInterval (-32824224231 / 1000000000000) (-32824224190 / 1000000000000), orderedInterval (-7285977771 / 1000000000000) (-7285977731 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1658552048626897 / 4000000000000)) (orderedInterval (26214356293 / 1000000000000) (26214356294 / 1000000000000), orderedInterval (29091754519 / 1000000000000) (29091754520 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_stateChecks3 :
    compactCertificate413.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2544645358394431 / 4000000000000)) (orderedInterval (22621592815 / 1000000000000) (22621599207 / 1000000000000), orderedInterval (-22130765661 / 1000000000000) (-22130759269 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1469151682660999 / 4000000000000)) (orderedInterval (-20201957134 / 1000000000000) (-20201957133 / 1000000000000), orderedInterval (-36375530565 / 1000000000000) (-36375530564 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2607035442031091 / 4000000000000)) (orderedInterval (-24620934774 / 1000000000000) (-24620917093 / 1000000000000), orderedInterval (19269382304 / 1000000000000) (19269399985 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_stateChecks4 :
    compactCertificate413.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2435830685688479 / 4000000000000)) (orderedInterval (8745374424 / 1000000000000) (8745374425 / 1000000000000), orderedInterval (31120685582 / 1000000000000) (31120685583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1738323713619407 / 4000000000000)) (orderedInterval (37031993884 / 1000000000000) (37032000428 / 1000000000000), orderedInterval (-9713976084 / 1000000000000) (-9713969540 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1971073819012953 / 4000000000000)) (orderedInterval (-11427714315 / 1000000000000) (-11427714314 / 1000000000000), orderedInterval (-34066735622 / 1000000000000) (-34066735621 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_stateChecks5 :
    compactCertificate413.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1643275855517257 / 4000000000000)) (orderedInterval (-2180519842 / 1000000000000) (-2180519841 / 1000000000000), orderedInterval (-39302336537 / 1000000000000) (-39302336536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1451884053906397 / 4000000000000)) (orderedInterval (-25963394476 / 1000000000000) (-25963387368 / 1000000000000), orderedInterval (32896318954 / 1000000000000) (32896326063 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (420812588721303 / 800000000000)) (orderedInterval (-29020711517 / 1000000000000) (-29020646659 / 1000000000000), orderedInterval (19212636636 / 1000000000000) (19212701495 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_stateChecks6 :
    compactCertificate413.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1163989766556341 / 4000000000000)) (orderedInterval (17596647747 / 1000000000000) (17596648177 / 1000000000000), orderedInterval (-43367013336 / 1000000000000) (-43367012905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (986727015943501 / 4000000000000)) (orderedInterval (33465749968 / 1000000000000) (33465770766 / 1000000000000), orderedInterval (-38287949909 / 1000000000000) (-38287929111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (617447951373103 / 4000000000000)) (orderedInterval (-60051794165 / 1000000000000) (-60051794164 / 1000000000000), orderedInterval (-22564357144 / 1000000000000) (-22564357143 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_stateChecks7 :
    compactCertificate413.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (332065561787601 / 4000000000000)) (orderedInterval (74743213921 / 1000000000000) (74743234357 / 1000000000000), orderedInterval (-46078995400 / 1000000000000) (-46078974963 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (901622596205803 / 4000000000000)) (orderedInterval (-222057387 / 1000000000000) (-222057384 / 1000000000000), orderedInterval (53144513015 / 1000000000000) (53144513018 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1231088573032331 / 4000000000000)) (orderedInterval (28635115419 / 1000000000000) (28635115420 / 1000000000000), orderedInterval (35287716953 / 1000000000000) (35287716954 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_stateChecks8 :
    compactCertificate413.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (520552048626897 / 4000000000000)) (orderedInterval (-59759919361 / 1000000000000) (-59759894334 / 1000000000000), orderedInterval (36569902619 / 1000000000000) (36569927646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2116015177482737 / 4000000000000)) (orderedInterval (31523851999 / 1000000000000) (31523906276 / 1000000000000), orderedInterval (-14510016743 / 1000000000000) (-14509962466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1413400073816383 / 4000000000000)) (orderedInterval (32302902159 / 1000000000000) (32302950222 / 1000000000000), orderedInterval (-27580976045 / 1000000000000) (-27580927981 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_states : ∀ j,
    BesselStateValid (compactCertificate413.point j) (compactCertificate413.state j) :=
  compactCertificate413.statesValid_of_checks3 compactCertificate413_stateChecks0
    compactCertificate413_stateChecks1 compactCertificate413_stateChecks2
    compactCertificate413_stateChecks3 compactCertificate413_stateChecks4
    compactCertificate413_stateChecks5 compactCertificate413_stateChecks6
    compactCertificate413_stateChecks7 compactCertificate413_stateChecks8

theorem compactCertificate413_chunkChecks0_0 :
    compactCertificate413.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (569 / 2) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26708822683 / 1000000000000) (26708827947 / 1000000000000), orderedInterval (-39089473496 / 1000000000000) (-39089468232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (838245649355669 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7718113733 / 1000000000000) (7718113758 / 1000000000000), orderedInterval (-54592276499 / 1000000000000) (-54592276474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (271071420157877 / 800000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14139963225 / 1000000000000) (14139963226 / 1000000000000), orderedInterval (40953373731 / 1000000000000) (40953373732 / 1000000000000)))) (orderedInterval (11488109314 / 1000000000000) (11488111421 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (244597989867583 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79861050975 / 1000000000000) (-79860993923 / 1000000000000), orderedInterval (64158934724 / 1000000000000) (64158991776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (657024606337651 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61898369860 / 1000000000000) (61898370095 / 1000000000000), orderedInterval (-6847889889 / 1000000000000) (-6847889654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1783949615694567 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23353950064 / 1000000000000) (23353950065 / 1000000000000), orderedInterval (29672843558 / 1000000000000) (29672843559 / 1000000000000)))) (orderedInterval (1466228777 / 1000000000000) (1466229440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1314049212675871 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23751947048 / 1000000000000) (23751950054 / 1000000000000), orderedInterval (-37100056830 / 1000000000000) (-37100053824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2251645723171483 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32824224231 / 1000000000000) (-32824224190 / 1000000000000), orderedInterval (-7285977771 / 1000000000000) (-7285977731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1658552048626897 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26214356293 / 1000000000000) (26214356294 / 1000000000000), orderedInterval (29091754519 / 1000000000000) (29091754520 / 1000000000000)))) (orderedInterval (1645979666 / 1000000000000) (1645979684 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_chunkChecks0_1 :
    compactCertificate413.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2544645358394431 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22621592815 / 1000000000000) (22621599207 / 1000000000000), orderedInterval (-22130765661 / 1000000000000) (-22130759269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1469151682660999 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20201957134 / 1000000000000) (-20201957133 / 1000000000000), orderedInterval (-36375530565 / 1000000000000) (-36375530564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2607035442031091 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24620934774 / 1000000000000) (-24620917093 / 1000000000000), orderedInterval (19269382304 / 1000000000000) (19269399985 / 1000000000000)))) (orderedInterval (-9016394829 / 1000000000000) (-9016391066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2435830685688479 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8745374424 / 1000000000000) (8745374425 / 1000000000000), orderedInterval (31120685582 / 1000000000000) (31120685583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1738323713619407 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37031993884 / 1000000000000) (37032000428 / 1000000000000), orderedInterval (-9713976084 / 1000000000000) (-9713969540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1971073819012953 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11427714315 / 1000000000000) (-11427714314 / 1000000000000), orderedInterval (-34066735622 / 1000000000000) (-34066735621 / 1000000000000)))) (orderedInterval (3401801278 / 1000000000000) (3401801932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1643275855517257 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2180519842 / 1000000000000) (-2180519841 / 1000000000000), orderedInterval (-39302336537 / 1000000000000) (-39302336536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1451884053906397 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25963394476 / 1000000000000) (-25963387368 / 1000000000000), orderedInterval (32896318954 / 1000000000000) (32896326063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (420812588721303 / 800000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29020711517 / 1000000000000) (-29020646659 / 1000000000000), orderedInterval (19212636636 / 1000000000000) (19212701495 / 1000000000000)))) (orderedInterval (717573599 / 1000000000000) (717575694 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_chunkChecks0_2 :
    compactCertificate413.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1163989766556341 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (17596647747 / 1000000000000) (17596648177 / 1000000000000), orderedInterval (-43367013336 / 1000000000000) (-43367012905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (986727015943501 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33465749968 / 1000000000000) (33465770766 / 1000000000000), orderedInterval (-38287949909 / 1000000000000) (-38287929111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (617447951373103 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60051794165 / 1000000000000) (-60051794164 / 1000000000000), orderedInterval (-22564357144 / 1000000000000) (-22564357143 / 1000000000000)))) (orderedInterval (-6662734670 / 1000000000000) (-6662733352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (332065561787601 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74743213921 / 1000000000000) (74743234357 / 1000000000000), orderedInterval (-46078995400 / 1000000000000) (-46078974963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (901622596205803 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-222057387 / 1000000000000) (-222057384 / 1000000000000), orderedInterval (53144513015 / 1000000000000) (53144513018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1231088573032331 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28635115419 / 1000000000000) (28635115420 / 1000000000000), orderedInterval (35287716953 / 1000000000000) (35287716954 / 1000000000000)))) (orderedInterval (-3569667687 / 1000000000000) (-3569667275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (520552048626897 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-59759919361 / 1000000000000) (-59759894334 / 1000000000000), orderedInterval (36569902619 / 1000000000000) (36569927646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2116015177482737 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31523851999 / 1000000000000) (31523906276 / 1000000000000), orderedInterval (-14510016743 / 1000000000000) (-14509962466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1413400073816383 / 4000000000000) 0 (IntervalRat.scale (569 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32302902159 / 1000000000000) (32302950222 / 1000000000000), orderedInterval (-27580976045 / 1000000000000) (-27580927981 / 1000000000000)))) (orderedInterval (-8987244786 / 1000000000000) (-8987231119 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_chunkChecks0 :
    compactCertificate413.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate413.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate413_chunkChecks0_0
    compactCertificate413_chunkChecks0_1 compactCertificate413_chunkChecks0_2

theorem compactCertificate413_chunkChecks1_0 :
    compactCertificate413.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (569 / 2) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26708822683 / 1000000000000) (26708827947 / 1000000000000), orderedInterval (-39089473496 / 1000000000000) (-39089468232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (838245649355669 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7718113733 / 1000000000000) (7718113758 / 1000000000000), orderedInterval (-54592276499 / 1000000000000) (-54592276474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (271071420157877 / 800000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14139963225 / 1000000000000) (14139963226 / 1000000000000), orderedInterval (40953373731 / 1000000000000) (40953373732 / 1000000000000)))) (orderedInterval (-13006202504 / 1000000000000) (-13006200394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (244597989867583 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79861050975 / 1000000000000) (-79860993923 / 1000000000000), orderedInterval (64158934724 / 1000000000000) (64158991776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (657024606337651 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61898369860 / 1000000000000) (61898370095 / 1000000000000), orderedInterval (-6847889889 / 1000000000000) (-6847889654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1783949615694567 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23353950064 / 1000000000000) (23353950065 / 1000000000000), orderedInterval (29672843558 / 1000000000000) (29672843559 / 1000000000000)))) (orderedInterval (-3600750923 / 1000000000000) (-3600750745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1314049212675871 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23751947048 / 1000000000000) (23751950054 / 1000000000000), orderedInterval (-37100056830 / 1000000000000) (-37100053824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2251645723171483 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32824224231 / 1000000000000) (-32824224190 / 1000000000000), orderedInterval (-7285977771 / 1000000000000) (-7285977731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1658552048626897 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26214356293 / 1000000000000) (26214356294 / 1000000000000), orderedInterval (29091754519 / 1000000000000) (29091754520 / 1000000000000)))) (orderedInterval (1469350863 / 1000000000000) (1469350894 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_chunkChecks1_1 :
    compactCertificate413.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2544645358394431 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22621592815 / 1000000000000) (22621599207 / 1000000000000), orderedInterval (-22130765661 / 1000000000000) (-22130759269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1469151682660999 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20201957134 / 1000000000000) (-20201957133 / 1000000000000), orderedInterval (-36375530565 / 1000000000000) (-36375530564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2607035442031091 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24620934774 / 1000000000000) (-24620917093 / 1000000000000), orderedInterval (19269382304 / 1000000000000) (19269399985 / 1000000000000)))) (orderedInterval (11588990042 / 1000000000000) (11588998574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2435830685688479 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8745374424 / 1000000000000) (8745374425 / 1000000000000), orderedInterval (31120685582 / 1000000000000) (31120685583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1738323713619407 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37031993884 / 1000000000000) (37032000428 / 1000000000000), orderedInterval (-9713976084 / 1000000000000) (-9713969540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1971073819012953 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11427714315 / 1000000000000) (-11427714314 / 1000000000000), orderedInterval (-34066735622 / 1000000000000) (-34066735621 / 1000000000000)))) (orderedInterval (-2307111798 / 1000000000000) (-2307110798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1643275855517257 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2180519842 / 1000000000000) (-2180519841 / 1000000000000), orderedInterval (-39302336537 / 1000000000000) (-39302336536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1451884053906397 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25963394476 / 1000000000000) (-25963387368 / 1000000000000), orderedInterval (32896318954 / 1000000000000) (32896326063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (420812588721303 / 800000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29020711517 / 1000000000000) (-29020646659 / 1000000000000), orderedInterval (19212636636 / 1000000000000) (19212701495 / 1000000000000)))) (orderedInterval (-2147638560 / 1000000000000) (-2147634931 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_chunkChecks1_2 :
    compactCertificate413.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1163989766556341 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (17596647747 / 1000000000000) (17596648177 / 1000000000000), orderedInterval (-43367013336 / 1000000000000) (-43367012905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (986727015943501 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33465749968 / 1000000000000) (33465770766 / 1000000000000), orderedInterval (-38287949909 / 1000000000000) (-38287929111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (617447951373103 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60051794165 / 1000000000000) (-60051794164 / 1000000000000), orderedInterval (-22564357144 / 1000000000000) (-22564357143 / 1000000000000)))) (orderedInterval (8572876101 / 1000000000000) (8572877258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (332065561787601 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74743213921 / 1000000000000) (74743234357 / 1000000000000), orderedInterval (-46078995400 / 1000000000000) (-46078974963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (901622596205803 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-222057387 / 1000000000000) (-222057384 / 1000000000000), orderedInterval (53144513015 / 1000000000000) (53144513018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1231088573032331 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28635115419 / 1000000000000) (28635115420 / 1000000000000), orderedInterval (35287716953 / 1000000000000) (35287716954 / 1000000000000)))) (orderedInterval (-3632601350 / 1000000000000) (-3632601209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (520552048626897 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-59759919361 / 1000000000000) (-59759894334 / 1000000000000), orderedInterval (36569902619 / 1000000000000) (36569927646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2116015177482737 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31523851999 / 1000000000000) (31523906276 / 1000000000000), orderedInterval (-14510016743 / 1000000000000) (-14509962466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1413400073816383 / 4000000000000) 1 (IntervalRat.scale (569 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32302902159 / 1000000000000) (32302950222 / 1000000000000), orderedInterval (-27580976045 / 1000000000000) (-27580927981 / 1000000000000)))) (orderedInterval (8724327874 / 1000000000000) (8724347470 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_chunkChecks1 :
    compactCertificate413.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate413.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate413_chunkChecks1_0
    compactCertificate413_chunkChecks1_1 compactCertificate413_chunkChecks1_2

theorem compactCertificate413_chunkChecks2_0 :
    compactCertificate413.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (569 / 2) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26708822683 / 1000000000000) (26708827947 / 1000000000000), orderedInterval (-39089473496 / 1000000000000) (-39089468232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (838245649355669 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7718113733 / 1000000000000) (7718113758 / 1000000000000), orderedInterval (-54592276499 / 1000000000000) (-54592276474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (271071420157877 / 800000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14139963225 / 1000000000000) (14139963226 / 1000000000000), orderedInterval (40953373731 / 1000000000000) (40953373732 / 1000000000000)))) (orderedInterval (-11756730954 / 1000000000000) (-11756728834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (244597989867583 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79861050975 / 1000000000000) (-79860993923 / 1000000000000), orderedInterval (64158934724 / 1000000000000) (64158991776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (657024606337651 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61898369860 / 1000000000000) (61898370095 / 1000000000000), orderedInterval (-6847889889 / 1000000000000) (-6847889654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1783949615694567 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23353950064 / 1000000000000) (23353950065 / 1000000000000), orderedInterval (29672843558 / 1000000000000) (29672843559 / 1000000000000)))) (orderedInterval (3299169060 / 1000000000000) (3299169146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1314049212675871 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23751947048 / 1000000000000) (23751950054 / 1000000000000), orderedInterval (-37100056830 / 1000000000000) (-37100053824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2251645723171483 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32824224231 / 1000000000000) (-32824224190 / 1000000000000), orderedInterval (-7285977771 / 1000000000000) (-7285977731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1658552048626897 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26214356293 / 1000000000000) (26214356294 / 1000000000000), orderedInterval (29091754519 / 1000000000000) (29091754520 / 1000000000000)))) (orderedInterval (-5314400204 / 1000000000000) (-5314400149 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_chunkChecks2_1 :
    compactCertificate413.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2544645358394431 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22621592815 / 1000000000000) (22621599207 / 1000000000000), orderedInterval (-22130765661 / 1000000000000) (-22130759269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1469151682660999 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20201957134 / 1000000000000) (-20201957133 / 1000000000000), orderedInterval (-36375530565 / 1000000000000) (-36375530564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2607035442031091 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24620934774 / 1000000000000) (-24620917093 / 1000000000000), orderedInterval (19269382304 / 1000000000000) (19269399985 / 1000000000000)))) (orderedInterval (40920549989 / 1000000000000) (40920569389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2435830685688479 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8745374424 / 1000000000000) (8745374425 / 1000000000000), orderedInterval (31120685582 / 1000000000000) (31120685583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1738323713619407 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37031993884 / 1000000000000) (37032000428 / 1000000000000), orderedInterval (-9713976084 / 1000000000000) (-9713969540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1971073819012953 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11427714315 / 1000000000000) (-11427714314 / 1000000000000), orderedInterval (-34066735622 / 1000000000000) (-34066735621 / 1000000000000)))) (orderedInterval (-7613036281 / 1000000000000) (-7613034742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1643275855517257 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2180519842 / 1000000000000) (-2180519841 / 1000000000000), orderedInterval (-39302336537 / 1000000000000) (-39302336536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1451884053906397 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25963394476 / 1000000000000) (-25963387368 / 1000000000000), orderedInterval (32896318954 / 1000000000000) (32896326063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (420812588721303 / 800000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29020711517 / 1000000000000) (-29020646659 / 1000000000000), orderedInterval (19212636636 / 1000000000000) (19212701495 / 1000000000000)))) (orderedInterval (181667762 / 1000000000000) (181674173 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_chunkChecks2_2 :
    compactCertificate413.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1163989766556341 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (17596647747 / 1000000000000) (17596648177 / 1000000000000), orderedInterval (-43367013336 / 1000000000000) (-43367012905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (986727015943501 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33465749968 / 1000000000000) (33465770766 / 1000000000000), orderedInterval (-38287949909 / 1000000000000) (-38287929111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (617447951373103 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60051794165 / 1000000000000) (-60051794164 / 1000000000000), orderedInterval (-22564357144 / 1000000000000) (-22564357143 / 1000000000000)))) (orderedInterval (4912995702 / 1000000000000) (4912996727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (332065561787601 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74743213921 / 1000000000000) (74743234357 / 1000000000000), orderedInterval (-46078995400 / 1000000000000) (-46078974963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (901622596205803 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-222057387 / 1000000000000) (-222057384 / 1000000000000), orderedInterval (53144513015 / 1000000000000) (53144513018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1231088573032331 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28635115419 / 1000000000000) (28635115420 / 1000000000000), orderedInterval (35287716953 / 1000000000000) (35287716954 / 1000000000000)))) (orderedInterval (2695397777 / 1000000000000) (2695397841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (520552048626897 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-59759919361 / 1000000000000) (-59759894334 / 1000000000000), orderedInterval (36569902619 / 1000000000000) (36569927646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2116015177482737 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31523851999 / 1000000000000) (31523906276 / 1000000000000), orderedInterval (-14510016743 / 1000000000000) (-14509962466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1413400073816383 / 4000000000000) 2 (IntervalRat.scale (569 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32302902159 / 1000000000000) (32302950222 / 1000000000000), orderedInterval (-27580976045 / 1000000000000) (-27580927981 / 1000000000000)))) (orderedInterval (18266159961 / 1000000000000) (18266189411 / 1000000000000))) = true
  rfl'

theorem compactCertificate413_chunkChecks2 :
    compactCertificate413.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate413.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate413_chunkChecks2_0
    compactCertificate413_chunkChecks2_1 compactCertificate413_chunkChecks2_2

theorem compactCertificate413_chunkChecks3_0 :
    compactCertificate413.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (569 / 2) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26708822683 / 1000000000000) (26708827947 / 1000000000000), orderedInterval (-39089473496 / 1000000000000) (-39089468232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (838245649355669 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7718113733 / 1000000000000) (7718113758 / 1000000000000), orderedInterval (-54592276499 / 1000000000000) (-54592276474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (271071420157877 / 800000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14139963225 / 1000000000000) (14139963226 / 1000000000000), orderedInterval (40953373731 / 1000000000000) (40953373732 / 1000000000000)))) (orderedInterval (11678194963 / 1000000000000) (11678197087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (244597989867583 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79861050975 / 1000000000000) (-79860993923 / 1000000000000), orderedInterval (64158934724 / 1000000000000) (64158991776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (657024606337651 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61898369860 / 1000000000000) (61898370095 / 1000000000000), orderedInterval (-6847889889 / 1000000000000) (-6847889654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1783949615694567 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23353950064 / 1000000000000) (23353950065 / 1000000000000), orderedInterval (29672843558 / 1000000000000) (29672843559 / 1000000000000)))) (orderedInterval (8169569190 / 1000000000000) (8169569279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1314049212675871 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23751947048 / 1000000000000) (23751950054 / 1000000000000), orderedInterval (-37100056830 / 1000000000000) (-37100053824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2251645723171483 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32824224231 / 1000000000000) (-32824224190 / 1000000000000), orderedInterval (-7285977771 / 1000000000000) (-7285977731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1658552048626897 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26214356293 / 1000000000000) (26214356294 / 1000000000000), orderedInterval (29091754519 / 1000000000000) (29091754520 / 1000000000000)))) (orderedInterval (-3898599214 / 1000000000000) (-3898599114 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate413_chunkChecks3_1 :
    compactCertificate413.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2544645358394431 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22621592815 / 1000000000000) (22621599207 / 1000000000000), orderedInterval (-22130765661 / 1000000000000) (-22130759269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1469151682660999 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20201957134 / 1000000000000) (-20201957133 / 1000000000000), orderedInterval (-36375530565 / 1000000000000) (-36375530564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2607035442031091 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24620934774 / 1000000000000) (-24620917093 / 1000000000000), orderedInterval (19269382304 / 1000000000000) (19269399985 / 1000000000000)))) (orderedInterval (-71244127926 / 1000000000000) (-71244083844 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2435830685688479 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8745374424 / 1000000000000) (8745374425 / 1000000000000), orderedInterval (31120685582 / 1000000000000) (31120685583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1738323713619407 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37031993884 / 1000000000000) (37032000428 / 1000000000000), orderedInterval (-9713976084 / 1000000000000) (-9713969540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1971073819012953 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11427714315 / 1000000000000) (-11427714314 / 1000000000000), orderedInterval (-34066735622 / 1000000000000) (-34066735621 / 1000000000000)))) (orderedInterval (7914494351 / 1000000000000) (7914496716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1643275855517257 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2180519842 / 1000000000000) (-2180519841 / 1000000000000), orderedInterval (-39302336537 / 1000000000000) (-39302336536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1451884053906397 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25963394476 / 1000000000000) (-25963387368 / 1000000000000), orderedInterval (32896318954 / 1000000000000) (32896326063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (420812588721303 / 800000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29020711517 / 1000000000000) (-29020646659 / 1000000000000), orderedInterval (19212636636 / 1000000000000) (19212701495 / 1000000000000)))) (orderedInterval (2166129495 / 1000000000000) (2166140949 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate413_chunkChecks3_2 :
    compactCertificate413.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1163989766556341 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (17596647747 / 1000000000000) (17596648177 / 1000000000000), orderedInterval (-43367013336 / 1000000000000) (-43367012905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (986727015943501 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33465749968 / 1000000000000) (33465770766 / 1000000000000), orderedInterval (-38287949909 / 1000000000000) (-38287929111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (617447951373103 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60051794165 / 1000000000000) (-60051794164 / 1000000000000), orderedInterval (-22564357144 / 1000000000000) (-22564357143 / 1000000000000)))) (orderedInterval (-8732578652 / 1000000000000) (-8732577746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (332065561787601 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74743213921 / 1000000000000) (74743234357 / 1000000000000), orderedInterval (-46078995400 / 1000000000000) (-46078974963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (901622596205803 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-222057387 / 1000000000000) (-222057384 / 1000000000000), orderedInterval (53144513015 / 1000000000000) (53144513018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1231088573032331 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28635115419 / 1000000000000) (28635115420 / 1000000000000), orderedInterval (35287716953 / 1000000000000) (35287716954 / 1000000000000)))) (orderedInterval (3992809593 / 1000000000000) (3992809635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (520552048626897 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-59759919361 / 1000000000000) (-59759894334 / 1000000000000), orderedInterval (36569902619 / 1000000000000) (36569927646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2116015177482737 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31523851999 / 1000000000000) (31523906276 / 1000000000000), orderedInterval (-14510016743 / 1000000000000) (-14509962466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1413400073816383 / 4000000000000) 3 (IntervalRat.scale (569 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32302902159 / 1000000000000) (32302950222 / 1000000000000), orderedInterval (-27580976045 / 1000000000000) (-27580927981 / 1000000000000)))) (orderedInterval (-17593047331 / 1000000000000) (-17593001280 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate413_chunkChecks3 :
    compactCertificate413.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate413.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate413_chunkChecks3_0
    compactCertificate413_chunkChecks3_1 compactCertificate413_chunkChecks3_2

theorem compactCertificate413_chunkChecks4_0 :
    compactCertificate413.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (569 / 2) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (26708822683 / 1000000000000) (26708827947 / 1000000000000), orderedInterval (-39089473496 / 1000000000000) (-39089468232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (838245649355669 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (7718113733 / 1000000000000) (7718113758 / 1000000000000), orderedInterval (-54592276499 / 1000000000000) (-54592276474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (271071420157877 / 800000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (14139963225 / 1000000000000) (14139963226 / 1000000000000), orderedInterval (40953373731 / 1000000000000) (40953373732 / 1000000000000)))) (orderedInterval (12194897071 / 1000000000000) (12194899208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (244597989867583 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-79861050975 / 1000000000000) (-79860993923 / 1000000000000), orderedInterval (64158934724 / 1000000000000) (64158991776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (657024606337651 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61898369860 / 1000000000000) (61898370095 / 1000000000000), orderedInterval (-6847889889 / 1000000000000) (-6847889654 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1783949615694567 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (23353950064 / 1000000000000) (23353950065 / 1000000000000), orderedInterval (29672843558 / 1000000000000) (29672843559 / 1000000000000)))) (orderedInterval (-9830433914 / 1000000000000) (-9830433787 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1314049212675871 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23751947048 / 1000000000000) (23751950054 / 1000000000000), orderedInterval (-37100056830 / 1000000000000) (-37100053824 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2251645723171483 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32824224231 / 1000000000000) (-32824224190 / 1000000000000), orderedInterval (-7285977771 / 1000000000000) (-7285977731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1658552048626897 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (26214356293 / 1000000000000) (26214356294 / 1000000000000), orderedInterval (29091754519 / 1000000000000) (29091754520 / 1000000000000)))) (orderedInterval (18402365159 / 1000000000000) (18402365345 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate413_chunkChecks4_1 :
    compactCertificate413.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2544645358394431 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22621592815 / 1000000000000) (22621599207 / 1000000000000), orderedInterval (-22130765661 / 1000000000000) (-22130759269 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1469151682660999 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20201957134 / 1000000000000) (-20201957133 / 1000000000000), orderedInterval (-36375530565 / 1000000000000) (-36375530564 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2607035442031091 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24620934774 / 1000000000000) (-24620917093 / 1000000000000), orderedInterval (19269382304 / 1000000000000) (19269399985 / 1000000000000)))) (orderedInterval (-200548514921 / 1000000000000) (-200548414558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2435830685688479 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (8745374424 / 1000000000000) (8745374425 / 1000000000000), orderedInterval (31120685582 / 1000000000000) (31120685583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1738323713619407 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (37031993884 / 1000000000000) (37032000428 / 1000000000000), orderedInterval (-9713976084 / 1000000000000) (-9713969540 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1971073819012953 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-11427714315 / 1000000000000) (-11427714314 / 1000000000000), orderedInterval (-34066735622 / 1000000000000) (-34066735621 / 1000000000000)))) (orderedInterval (16216406346 / 1000000000000) (16216409999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1643275855517257 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-2180519842 / 1000000000000) (-2180519841 / 1000000000000), orderedInterval (-39302336537 / 1000000000000) (-39302336536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1451884053906397 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25963394476 / 1000000000000) (-25963387368 / 1000000000000), orderedInterval (32896318954 / 1000000000000) (32896326063 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (420812588721303 / 800000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29020711517 / 1000000000000) (-29020646659 / 1000000000000), orderedInterval (19212636636 / 1000000000000) (19212701495 / 1000000000000)))) (orderedInterval (-4871349826 / 1000000000000) (-4871329119 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate413_chunkChecks4_2 :
    compactCertificate413.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1163989766556341 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (17596647747 / 1000000000000) (17596648177 / 1000000000000), orderedInterval (-43367013336 / 1000000000000) (-43367012905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (986727015943501 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33465749968 / 1000000000000) (33465770766 / 1000000000000), orderedInterval (-38287949909 / 1000000000000) (-38287929111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (617447951373103 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-60051794165 / 1000000000000) (-60051794164 / 1000000000000), orderedInterval (-22564357144 / 1000000000000) (-22564357143 / 1000000000000)))) (orderedInterval (-4258135515 / 1000000000000) (-4258134708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (332065561787601 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74743213921 / 1000000000000) (74743234357 / 1000000000000), orderedInterval (-46078995400 / 1000000000000) (-46078974963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (901622596205803 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-222057387 / 1000000000000) (-222057384 / 1000000000000), orderedInterval (53144513015 / 1000000000000) (53144513018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1231088573032331 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (28635115419 / 1000000000000) (28635115420 / 1000000000000), orderedInterval (35287716953 / 1000000000000) (35287716954 / 1000000000000)))) (orderedInterval (-3041690852 / 1000000000000) (-3041690815 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (520552048626897 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-59759919361 / 1000000000000) (-59759894334 / 1000000000000), orderedInterval (36569902619 / 1000000000000) (36569927646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2116015177482737 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31523851999 / 1000000000000) (31523906276 / 1000000000000), orderedInterval (-14510016743 / 1000000000000) (-14509962466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1413400073816383 / 4000000000000) 4 (IntervalRat.scale (569 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32302902159 / 1000000000000) (32302950222 / 1000000000000), orderedInterval (-27580976045 / 1000000000000) (-27580927981 / 1000000000000)))) (orderedInterval (-44988623443 / 1000000000000) (-44988548438 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate413_chunkChecks4 :
    compactCertificate413.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate413.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate413_chunkChecks4_0
    compactCertificate413_chunkChecks4_1 compactCertificate413_chunkChecks4_2

theorem compactCertificate413_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate413.chunkCheck r b = true :=
  compactCertificate413.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate413_chunkChecks0
    · exact compactCertificate413_chunkChecks1
    · exact compactCertificate413_chunkChecks2
    · exact compactCertificate413_chunkChecks3
    · exact compactCertificate413_chunkChecks4)

theorem compactCertificate413_coefficient0 :
    compactCertificate413.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate413_coefficient1 :
    compactCertificate413.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate413_coefficient2 :
    compactCertificate413.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate413_coefficient3 :
    compactCertificate413.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate413_coefficient4 :
    compactCertificate413.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate413_coefficients : ∀ r : Fin 5,
    compactCertificate413.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate413_coefficient0
  · exact compactCertificate413_coefficient1
  · exact compactCertificate413_coefficient2
  · exact compactCertificate413_coefficient3
  · exact compactCertificate413_coefficient4

theorem compactCertificate413_lower : (1 : ℚ) ≤ compactCertificate413.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate413, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate413_proves {t : ℝ} (ht : t ∈ compactCertificate413.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate413.proves compactCertificate413_states compactCertificate413_chunks
    compactCertificate413_coefficients compactCertificate413_lower ht

end Erdos232
