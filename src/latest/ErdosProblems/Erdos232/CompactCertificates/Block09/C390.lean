/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate390 : CompactCertificate where
  left := 261
  right := 262
  center := 523 / 2
  grid := fun i =>
    match i.val with
    | 0 => 83
    | 1 => 61
    | 2 => 99
    | 3 => 18
    | 4 => 48
    | 5 => 131
    | 6 => 96
    | 7 => 165
    | 8 => 121
    | 9 => 186
    | 10 => 108
    | 11 => 191
    | 12 => 178
    | 13 => 127
    | 14 => 144
    | 15 => 120
    | 16 => 106
    | 17 => 154
    | 18 => 85
    | 19 => 72
    | 20 => 45
    | 21 => 24
    | 22 => 66
    | 23 => 90
    | 24 => 38
    | 25 => 155
    | _ => 103
  point := fun i =>
    match i.val with
    | 0 => 523 / 2
    | 1 => 770478865752223 / 4000000000000
    | 2 => 249157034696959 / 800000000000
    | 3 => 224823811424861 / 4000000000000
    | 4 => 603908381572217 / 4000000000000
    | 5 => 1639728732879189 / 4000000000000
    | 6 => 1207816763144957 / 4000000000000
    | 7 => 2069614610226161 / 4000000000000
    | 8 => 1524468754713299 / 4000000000000
    | 9 => 2338927104464477 / 4000000000000
    | 10 => 1350380193377333 / 4000000000000
    | 11 => 2396273350056697 / 4000000000000
    | 12 => 2238909400026493 / 4000000000000
    | 13 => 1597791392307469 / 4000000000000
    | 14 => 1811725144716651 / 4000000000000
    | 15 => 1510427543823419 / 4000000000000
    | 16 => 1334508541639799 / 4000000000000
    | 17 => 386792590336101 / 800000000000
    | 18 => 1069888660648447 / 4000000000000
    | 19 => 906956466324167 / 4000000000000
    | 20 => 567531245286701 / 4000000000000
    | 21 => 305220191238867 / 4000000000000
    | 22 => 828732192997601 / 4000000000000
    | 23 => 1131562959043777 / 4000000000000
    | 24 => 478468754713299 / 4000000000000
    | 25 => 1944948924118579 / 4000000000000
    | _ => 1299135744474461 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-49304786720 / 1000000000000) (-49304786658 / 1000000000000), orderedInterval (-1783494552 / 1000000000000) (-1783494490 / 1000000000000))
    | 1 => (orderedInterval (-56383027268 / 1000000000000) (-56383026397 / 1000000000000), orderedInterval (11371519302 / 1000000000000) (11371520174 / 1000000000000))
    | 2 => (orderedInterval (-42357992849 / 1000000000000) (-42357992848 / 1000000000000), orderedInterval (-15739403402 / 1000000000000) (-15739403400 / 1000000000000))
    | 3 => (orderedInterval (45374513160 / 1000000000000) (45374513161 / 1000000000000), orderedInterval (95866802166 / 1000000000000) (95866802167 / 1000000000000))
    | 4 => (orderedInterval (53388367728 / 1000000000000) (53388367729 / 1000000000000), orderedInterval (36787210705 / 1000000000000) (36787210706 / 1000000000000))
    | 5 => (orderedInterval (29116525528 / 1000000000000) (29116552936 / 1000000000000), orderedInterval (-26591412402 / 1000000000000) (-26591384995 / 1000000000000))
    | 6 => (orderedInterval (41840910627 / 1000000000000) (41840910628 / 1000000000000), orderedInterval (18842844616 / 1000000000000) (18842844617 / 1000000000000))
    | 7 => (orderedInterval (6071950180 / 1000000000000) (6071950184 / 1000000000000), orderedInterval (-34553576351 / 1000000000000) (-34553576347 / 1000000000000))
    | 8 => (orderedInterval (-40065979516 / 1000000000000) (-40065976837 / 1000000000000), orderedInterval (8122278350 / 1000000000000) (8122281029 / 1000000000000))
    | 9 => (orderedInterval (30517452669 / 1000000000000) (30517452672 / 1000000000000), orderedInterval (12520733670 / 1000000000000) (12520733673 / 1000000000000))
    | 10 => (orderedInterval (-34335775770 / 1000000000000) (-34335698308 / 1000000000000), orderedInterval (26636642282 / 1000000000000) (26636719743 / 1000000000000))
    | 11 => (orderedInterval (6178016880 / 1000000000000) (6178016883 / 1000000000000), orderedInterval (-32013210153 / 1000000000000) (-32013210150 / 1000000000000))
    | 12 => (orderedInterval (32576140354 / 1000000000000) (32576140375 / 1000000000000), orderedInterval (8698412097 / 1000000000000) (8698412118 / 1000000000000))
    | 13 => (orderedInterval (-37893530131 / 1000000000000) (-37893530128 / 1000000000000), orderedInterval (-12515560305 / 1000000000000) (-12515560302 / 1000000000000))
    | 14 => (orderedInterval (36382664613 / 1000000000000) (36382664625 / 1000000000000), orderedInterval (9007257253 / 1000000000000) (9007257265 / 1000000000000))
    | 15 => (orderedInterval (40468467461 / 1000000000000) (40468467482 / 1000000000000), orderedInterval (6891512364 / 1000000000000) (6891512385 / 1000000000000))
    | 16 => (orderedInterval (43071612024 / 1000000000000) (43071612039 / 1000000000000), orderedInterval (7216359637 / 1000000000000) (7216359653 / 1000000000000))
    | 17 => (orderedInterval (16453383801 / 1000000000000) (16453383802 / 1000000000000), orderedInterval (32324940926 / 1000000000000) (32324940927 / 1000000000000))
    | 18 => (orderedInterval (-45844222819 / 1000000000000) (-45844222818 / 1000000000000), orderedInterval (-16600784223 / 1000000000000) (-16600784222 / 1000000000000))
    | 19 => (orderedInterval (51450111397 / 1000000000000) (51450111399 / 1000000000000), orderedInterval (12559317792 / 1000000000000) (12559317794 / 1000000000000))
    | 20 => (orderedInterval (-64464999624 / 1000000000000) (-64464999623 / 1000000000000), orderedInterval (-17971201080 / 1000000000000) (-17971201078 / 1000000000000))
    | 21 => (orderedInterval (90684989508 / 1000000000000) (90684989663 / 1000000000000), orderedInterval (-11509662156 / 1000000000000) (-11509662001 / 1000000000000))
    | 22 => (orderedInterval (32331024220 / 1000000000000) (32331024221 / 1000000000000), orderedInterval (44949171119 / 1000000000000) (44949171120 / 1000000000000))
    | 23 => (orderedInterval (38094342032 / 1000000000000) (38094342033 / 1000000000000), orderedInterval (28203303835 / 1000000000000) (28203303836 / 1000000000000))
    | 24 => (orderedInterval (62202532771 / 1000000000000) (62202532772 / 1000000000000), orderedInterval (37857798422 / 1000000000000) (37857798423 / 1000000000000))
    | 25 => (orderedInterval (-2729682795 / 1000000000000) (-2729682794 / 1000000000000), orderedInterval (-36078041797 / 1000000000000) (-36078041796 / 1000000000000))
    | _ => (orderedInterval (-40531162970 / 1000000000000) (-40531144811 / 1000000000000), orderedInterval (17876908606 / 1000000000000) (17876926765 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-22553687192 / 1000000000000) (-22553687141 / 1000000000000)
      | 1 => orderedInterval (-612864087 / 1000000000000) (-612862106 / 1000000000000)
      | 2 => orderedInterval (-1155598920 / 1000000000000) (-1155598840 / 1000000000000)
      | 3 => orderedInterval (-7088339859 / 1000000000000) (-7088334015 / 1000000000000)
      | 4 => orderedInterval (-4355537931 / 1000000000000) (-4355537899 / 1000000000000)
      | 5 => orderedInterval (-1576257119 / 1000000000000) (-1576257092 / 1000000000000)
      | 6 => orderedInterval (2319395131 / 1000000000000) (2319395197 / 1000000000000)
      | 7 => orderedInterval (-5327505772 / 1000000000000) (-5327505737 / 1000000000000)
      | _ => orderedInterval (8201896200 / 1000000000000) (8201899680 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-1728878969 / 1000000000000) (-1728878917 / 1000000000000)
      | 1 => orderedInterval (3515305716 / 1000000000000) (3515308806 / 1000000000000)
      | 2 => orderedInterval (2394824704 / 1000000000000) (2394824825 / 1000000000000)
      | 3 => orderedInterval (-12852461650 / 1000000000000) (-12852454023 / 1000000000000)
      | 4 => orderedInterval (-2222908878 / 1000000000000) (-2222908826 / 1000000000000)
      | 5 => orderedInterval (1118287296 / 1000000000000) (1118287334 / 1000000000000)
      | 6 => orderedInterval (1781160273 / 1000000000000) (1781160335 / 1000000000000)
      | 7 => orderedInterval (-3084202078 / 1000000000000) (-3084202048 / 1000000000000)
      | _ => orderedInterval (1399246375 / 1000000000000) (1399250709 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (23360153384 / 1000000000000) (23360153437 / 1000000000000)
      | 1 => orderedInterval (4446119361 / 1000000000000) (4446124211 / 1000000000000)
      | 2 => orderedInterval (2780821677 / 1000000000000) (2780821862 / 1000000000000)
      | 3 => orderedInterval (26792874809 / 1000000000000) (26792884869 / 1000000000000)
      | 4 => orderedInterval (11616325982 / 1000000000000) (11616326069 / 1000000000000)
      | 5 => orderedInterval (1593266885 / 1000000000000) (1593266941 / 1000000000000)
      | 6 => orderedInterval (-4868439768 / 1000000000000) (-4868439709 / 1000000000000)
      | 7 => orderedInterval (4031471494 / 1000000000000) (4031471523 / 1000000000000)
      | _ => orderedInterval (-12582891879 / 1000000000000) (-12582886456 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (2135557422 / 1000000000000) (2135557478 / 1000000000000)
      | 1 => orderedInterval (-7547417787 / 1000000000000) (-7547410188 / 1000000000000)
      | 2 => orderedInterval (-8873666513 / 1000000000000) (-8873666228 / 1000000000000)
      | 3 => orderedInterval (75239971686 / 1000000000000) (75239985091 / 1000000000000)
      | 4 => orderedInterval (5950630423 / 1000000000000) (5950630571 / 1000000000000)
      | 5 => orderedInterval (-4619202437 / 1000000000000) (-4619202351 / 1000000000000)
      | 6 => orderedInterval (-2264903498 / 1000000000000) (-2264903441 / 1000000000000)
      | 7 => orderedInterval (3222883199 / 1000000000000) (3222883229 / 1000000000000)
      | _ => orderedInterval (-12427681925 / 1000000000000) (-12427675145 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-24714611511 / 1000000000000) (-24714611451 / 1000000000000)
      | 1 => orderedInterval (-12226602376 / 1000000000000) (-12226590438 / 1000000000000)
      | 2 => orderedInterval (-7171232494 / 1000000000000) (-7171232046 / 1000000000000)
      | 3 => orderedInterval (-119016471271 / 1000000000000) (-119016452969 / 1000000000000)
      | 4 => orderedInterval (-33556000209 / 1000000000000) (-33555999952 / 1000000000000)
      | 5 => orderedInterval (459616887 / 1000000000000) (459617023 / 1000000000000)
      | 6 => orderedInterval (6212467961 / 1000000000000) (6212468017 / 1000000000000)
      | 7 => orderedInterval (-4324253080 / 1000000000000) (-4324253049 / 1000000000000)
      | _ => orderedInterval (20863092033 / 1000000000000) (20863100563 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-32148499549 / 1000000000000) (-32148487953 / 1000000000000)
    | 1 => orderedInterval (-9679627211 / 1000000000000) (-9679611805 / 1000000000000)
    | 2 => orderedInterval (57169701945 / 1000000000000) (57169722747 / 1000000000000)
    | 3 => orderedInterval (50816170570 / 1000000000000) (50816199016 / 1000000000000)
    | _ => orderedInterval (-173473994060 / 1000000000000) (-173473954302 / 1000000000000)

theorem compactCertificate390_stateChecks0 :
    compactCertificate390.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (523 / 2)) (orderedInterval (-49304786720 / 1000000000000) (-49304786658 / 1000000000000), orderedInterval (-1783494552 / 1000000000000) (-1783494490 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (770478865752223 / 4000000000000)) (orderedInterval (-56383027268 / 1000000000000) (-56383026397 / 1000000000000), orderedInterval (11371519302 / 1000000000000) (11371520174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (249157034696959 / 800000000000)) (orderedInterval (-42357992849 / 1000000000000) (-42357992848 / 1000000000000), orderedInterval (-15739403402 / 1000000000000) (-15739403400 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_stateChecks1 :
    compactCertificate390.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (224823811424861 / 4000000000000)) (orderedInterval (45374513160 / 1000000000000) (45374513161 / 1000000000000), orderedInterval (95866802166 / 1000000000000) (95866802167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (603908381572217 / 4000000000000)) (orderedInterval (53388367728 / 1000000000000) (53388367729 / 1000000000000), orderedInterval (36787210705 / 1000000000000) (36787210706 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1639728732879189 / 4000000000000)) (orderedInterval (29116525528 / 1000000000000) (29116552936 / 1000000000000), orderedInterval (-26591412402 / 1000000000000) (-26591384995 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_stateChecks2 :
    compactCertificate390.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1207816763144957 / 4000000000000)) (orderedInterval (41840910627 / 1000000000000) (41840910628 / 1000000000000), orderedInterval (18842844616 / 1000000000000) (18842844617 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2069614610226161 / 4000000000000)) (orderedInterval (6071950180 / 1000000000000) (6071950184 / 1000000000000), orderedInterval (-34553576351 / 1000000000000) (-34553576347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1524468754713299 / 4000000000000)) (orderedInterval (-40065979516 / 1000000000000) (-40065976837 / 1000000000000), orderedInterval (8122278350 / 1000000000000) (8122281029 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_stateChecks3 :
    compactCertificate390.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2338927104464477 / 4000000000000)) (orderedInterval (30517452669 / 1000000000000) (30517452672 / 1000000000000), orderedInterval (12520733670 / 1000000000000) (12520733673 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1350380193377333 / 4000000000000)) (orderedInterval (-34335775770 / 1000000000000) (-34335698308 / 1000000000000), orderedInterval (26636642282 / 1000000000000) (26636719743 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2396273350056697 / 4000000000000)) (orderedInterval (6178016880 / 1000000000000) (6178016883 / 1000000000000), orderedInterval (-32013210153 / 1000000000000) (-32013210150 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_stateChecks4 :
    compactCertificate390.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2238909400026493 / 4000000000000)) (orderedInterval (32576140354 / 1000000000000) (32576140375 / 1000000000000), orderedInterval (8698412097 / 1000000000000) (8698412118 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1597791392307469 / 4000000000000)) (orderedInterval (-37893530131 / 1000000000000) (-37893530128 / 1000000000000), orderedInterval (-12515560305 / 1000000000000) (-12515560302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1811725144716651 / 4000000000000)) (orderedInterval (36382664613 / 1000000000000) (36382664625 / 1000000000000), orderedInterval (9007257253 / 1000000000000) (9007257265 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_stateChecks5 :
    compactCertificate390.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1510427543823419 / 4000000000000)) (orderedInterval (40468467461 / 1000000000000) (40468467482 / 1000000000000), orderedInterval (6891512364 / 1000000000000) (6891512385 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1334508541639799 / 4000000000000)) (orderedInterval (43071612024 / 1000000000000) (43071612039 / 1000000000000), orderedInterval (7216359637 / 1000000000000) (7216359653 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (386792590336101 / 800000000000)) (orderedInterval (16453383801 / 1000000000000) (16453383802 / 1000000000000), orderedInterval (32324940926 / 1000000000000) (32324940927 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_stateChecks6 :
    compactCertificate390.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1069888660648447 / 4000000000000)) (orderedInterval (-45844222819 / 1000000000000) (-45844222818 / 1000000000000), orderedInterval (-16600784223 / 1000000000000) (-16600784222 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (906956466324167 / 4000000000000)) (orderedInterval (51450111397 / 1000000000000) (51450111399 / 1000000000000), orderedInterval (12559317792 / 1000000000000) (12559317794 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (567531245286701 / 4000000000000)) (orderedInterval (-64464999624 / 1000000000000) (-64464999623 / 1000000000000), orderedInterval (-17971201080 / 1000000000000) (-17971201078 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_stateChecks7 :
    compactCertificate390.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (305220191238867 / 4000000000000)) (orderedInterval (90684989508 / 1000000000000) (90684989663 / 1000000000000), orderedInterval (-11509662156 / 1000000000000) (-11509662001 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (828732192997601 / 4000000000000)) (orderedInterval (32331024220 / 1000000000000) (32331024221 / 1000000000000), orderedInterval (44949171119 / 1000000000000) (44949171120 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1131562959043777 / 4000000000000)) (orderedInterval (38094342032 / 1000000000000) (38094342033 / 1000000000000), orderedInterval (28203303835 / 1000000000000) (28203303836 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_stateChecks8 :
    compactCertificate390.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (478468754713299 / 4000000000000)) (orderedInterval (62202532771 / 1000000000000) (62202532772 / 1000000000000), orderedInterval (37857798422 / 1000000000000) (37857798423 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1944948924118579 / 4000000000000)) (orderedInterval (-2729682795 / 1000000000000) (-2729682794 / 1000000000000), orderedInterval (-36078041797 / 1000000000000) (-36078041796 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1299135744474461 / 4000000000000)) (orderedInterval (-40531162970 / 1000000000000) (-40531144811 / 1000000000000), orderedInterval (17876908606 / 1000000000000) (17876926765 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_states : ∀ j,
    BesselStateValid (compactCertificate390.point j) (compactCertificate390.state j) :=
  compactCertificate390.statesValid_of_checks3 compactCertificate390_stateChecks0
    compactCertificate390_stateChecks1 compactCertificate390_stateChecks2
    compactCertificate390_stateChecks3 compactCertificate390_stateChecks4
    compactCertificate390_stateChecks5 compactCertificate390_stateChecks6
    compactCertificate390_stateChecks7 compactCertificate390_stateChecks8

theorem compactCertificate390_chunkChecks0_0 :
    compactCertificate390.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (523 / 2) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49304786720 / 1000000000000) (-49304786658 / 1000000000000), orderedInterval (-1783494552 / 1000000000000) (-1783494490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (770478865752223 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-56383027268 / 1000000000000) (-56383026397 / 1000000000000), orderedInterval (11371519302 / 1000000000000) (11371520174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (249157034696959 / 800000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-42357992849 / 1000000000000) (-42357992848 / 1000000000000), orderedInterval (-15739403402 / 1000000000000) (-15739403400 / 1000000000000)))) (orderedInterval (-22553687192 / 1000000000000) (-22553687141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (224823811424861 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (45374513160 / 1000000000000) (45374513161 / 1000000000000), orderedInterval (95866802166 / 1000000000000) (95866802167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (603908381572217 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53388367728 / 1000000000000) (53388367729 / 1000000000000), orderedInterval (36787210705 / 1000000000000) (36787210706 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1639728732879189 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29116525528 / 1000000000000) (29116552936 / 1000000000000), orderedInterval (-26591412402 / 1000000000000) (-26591384995 / 1000000000000)))) (orderedInterval (-612864087 / 1000000000000) (-612862106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1207816763144957 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41840910627 / 1000000000000) (41840910628 / 1000000000000), orderedInterval (18842844616 / 1000000000000) (18842844617 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2069614610226161 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6071950180 / 1000000000000) (6071950184 / 1000000000000), orderedInterval (-34553576351 / 1000000000000) (-34553576347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1524468754713299 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-40065979516 / 1000000000000) (-40065976837 / 1000000000000), orderedInterval (8122278350 / 1000000000000) (8122281029 / 1000000000000)))) (orderedInterval (-1155598920 / 1000000000000) (-1155598840 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_chunkChecks0_1 :
    compactCertificate390.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2338927104464477 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30517452669 / 1000000000000) (30517452672 / 1000000000000), orderedInterval (12520733670 / 1000000000000) (12520733673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1350380193377333 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34335775770 / 1000000000000) (-34335698308 / 1000000000000), orderedInterval (26636642282 / 1000000000000) (26636719743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2396273350056697 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6178016880 / 1000000000000) (6178016883 / 1000000000000), orderedInterval (-32013210153 / 1000000000000) (-32013210150 / 1000000000000)))) (orderedInterval (-7088339859 / 1000000000000) (-7088334015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2238909400026493 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32576140354 / 1000000000000) (32576140375 / 1000000000000), orderedInterval (8698412097 / 1000000000000) (8698412118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1597791392307469 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37893530131 / 1000000000000) (-37893530128 / 1000000000000), orderedInterval (-12515560305 / 1000000000000) (-12515560302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1811725144716651 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36382664613 / 1000000000000) (36382664625 / 1000000000000), orderedInterval (9007257253 / 1000000000000) (9007257265 / 1000000000000)))) (orderedInterval (-4355537931 / 1000000000000) (-4355537899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1510427543823419 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (40468467461 / 1000000000000) (40468467482 / 1000000000000), orderedInterval (6891512364 / 1000000000000) (6891512385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1334508541639799 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43071612024 / 1000000000000) (43071612039 / 1000000000000), orderedInterval (7216359637 / 1000000000000) (7216359653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (386792590336101 / 800000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16453383801 / 1000000000000) (16453383802 / 1000000000000), orderedInterval (32324940926 / 1000000000000) (32324940927 / 1000000000000)))) (orderedInterval (-1576257119 / 1000000000000) (-1576257092 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_chunkChecks0_2 :
    compactCertificate390.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1069888660648447 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45844222819 / 1000000000000) (-45844222818 / 1000000000000), orderedInterval (-16600784223 / 1000000000000) (-16600784222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (906956466324167 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51450111397 / 1000000000000) (51450111399 / 1000000000000), orderedInterval (12559317792 / 1000000000000) (12559317794 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (567531245286701 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-64464999624 / 1000000000000) (-64464999623 / 1000000000000), orderedInterval (-17971201080 / 1000000000000) (-17971201078 / 1000000000000)))) (orderedInterval (2319395131 / 1000000000000) (2319395197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (305220191238867 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90684989508 / 1000000000000) (90684989663 / 1000000000000), orderedInterval (-11509662156 / 1000000000000) (-11509662001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (828732192997601 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32331024220 / 1000000000000) (32331024221 / 1000000000000), orderedInterval (44949171119 / 1000000000000) (44949171120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1131562959043777 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38094342032 / 1000000000000) (38094342033 / 1000000000000), orderedInterval (28203303835 / 1000000000000) (28203303836 / 1000000000000)))) (orderedInterval (-5327505772 / 1000000000000) (-5327505737 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (478468754713299 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62202532771 / 1000000000000) (62202532772 / 1000000000000), orderedInterval (37857798422 / 1000000000000) (37857798423 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1944948924118579 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2729682795 / 1000000000000) (-2729682794 / 1000000000000), orderedInterval (-36078041797 / 1000000000000) (-36078041796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1299135744474461 / 4000000000000) 0 (IntervalRat.scale (523 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40531162970 / 1000000000000) (-40531144811 / 1000000000000), orderedInterval (17876908606 / 1000000000000) (17876926765 / 1000000000000)))) (orderedInterval (8201896200 / 1000000000000) (8201899680 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_chunkChecks0 :
    compactCertificate390.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate390.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate390_chunkChecks0_0
    compactCertificate390_chunkChecks0_1 compactCertificate390_chunkChecks0_2

theorem compactCertificate390_chunkChecks1_0 :
    compactCertificate390.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (523 / 2) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49304786720 / 1000000000000) (-49304786658 / 1000000000000), orderedInterval (-1783494552 / 1000000000000) (-1783494490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (770478865752223 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-56383027268 / 1000000000000) (-56383026397 / 1000000000000), orderedInterval (11371519302 / 1000000000000) (11371520174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (249157034696959 / 800000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-42357992849 / 1000000000000) (-42357992848 / 1000000000000), orderedInterval (-15739403402 / 1000000000000) (-15739403400 / 1000000000000)))) (orderedInterval (-1728878969 / 1000000000000) (-1728878917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (224823811424861 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (45374513160 / 1000000000000) (45374513161 / 1000000000000), orderedInterval (95866802166 / 1000000000000) (95866802167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (603908381572217 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53388367728 / 1000000000000) (53388367729 / 1000000000000), orderedInterval (36787210705 / 1000000000000) (36787210706 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1639728732879189 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29116525528 / 1000000000000) (29116552936 / 1000000000000), orderedInterval (-26591412402 / 1000000000000) (-26591384995 / 1000000000000)))) (orderedInterval (3515305716 / 1000000000000) (3515308806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1207816763144957 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41840910627 / 1000000000000) (41840910628 / 1000000000000), orderedInterval (18842844616 / 1000000000000) (18842844617 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2069614610226161 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6071950180 / 1000000000000) (6071950184 / 1000000000000), orderedInterval (-34553576351 / 1000000000000) (-34553576347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1524468754713299 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-40065979516 / 1000000000000) (-40065976837 / 1000000000000), orderedInterval (8122278350 / 1000000000000) (8122281029 / 1000000000000)))) (orderedInterval (2394824704 / 1000000000000) (2394824825 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_chunkChecks1_1 :
    compactCertificate390.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2338927104464477 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30517452669 / 1000000000000) (30517452672 / 1000000000000), orderedInterval (12520733670 / 1000000000000) (12520733673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1350380193377333 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34335775770 / 1000000000000) (-34335698308 / 1000000000000), orderedInterval (26636642282 / 1000000000000) (26636719743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2396273350056697 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6178016880 / 1000000000000) (6178016883 / 1000000000000), orderedInterval (-32013210153 / 1000000000000) (-32013210150 / 1000000000000)))) (orderedInterval (-12852461650 / 1000000000000) (-12852454023 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2238909400026493 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32576140354 / 1000000000000) (32576140375 / 1000000000000), orderedInterval (8698412097 / 1000000000000) (8698412118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1597791392307469 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37893530131 / 1000000000000) (-37893530128 / 1000000000000), orderedInterval (-12515560305 / 1000000000000) (-12515560302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1811725144716651 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36382664613 / 1000000000000) (36382664625 / 1000000000000), orderedInterval (9007257253 / 1000000000000) (9007257265 / 1000000000000)))) (orderedInterval (-2222908878 / 1000000000000) (-2222908826 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1510427543823419 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (40468467461 / 1000000000000) (40468467482 / 1000000000000), orderedInterval (6891512364 / 1000000000000) (6891512385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1334508541639799 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43071612024 / 1000000000000) (43071612039 / 1000000000000), orderedInterval (7216359637 / 1000000000000) (7216359653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (386792590336101 / 800000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16453383801 / 1000000000000) (16453383802 / 1000000000000), orderedInterval (32324940926 / 1000000000000) (32324940927 / 1000000000000)))) (orderedInterval (1118287296 / 1000000000000) (1118287334 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_chunkChecks1_2 :
    compactCertificate390.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1069888660648447 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45844222819 / 1000000000000) (-45844222818 / 1000000000000), orderedInterval (-16600784223 / 1000000000000) (-16600784222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (906956466324167 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51450111397 / 1000000000000) (51450111399 / 1000000000000), orderedInterval (12559317792 / 1000000000000) (12559317794 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (567531245286701 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-64464999624 / 1000000000000) (-64464999623 / 1000000000000), orderedInterval (-17971201080 / 1000000000000) (-17971201078 / 1000000000000)))) (orderedInterval (1781160273 / 1000000000000) (1781160335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (305220191238867 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90684989508 / 1000000000000) (90684989663 / 1000000000000), orderedInterval (-11509662156 / 1000000000000) (-11509662001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (828732192997601 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32331024220 / 1000000000000) (32331024221 / 1000000000000), orderedInterval (44949171119 / 1000000000000) (44949171120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1131562959043777 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38094342032 / 1000000000000) (38094342033 / 1000000000000), orderedInterval (28203303835 / 1000000000000) (28203303836 / 1000000000000)))) (orderedInterval (-3084202078 / 1000000000000) (-3084202048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (478468754713299 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62202532771 / 1000000000000) (62202532772 / 1000000000000), orderedInterval (37857798422 / 1000000000000) (37857798423 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1944948924118579 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2729682795 / 1000000000000) (-2729682794 / 1000000000000), orderedInterval (-36078041797 / 1000000000000) (-36078041796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1299135744474461 / 4000000000000) 1 (IntervalRat.scale (523 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40531162970 / 1000000000000) (-40531144811 / 1000000000000), orderedInterval (17876908606 / 1000000000000) (17876926765 / 1000000000000)))) (orderedInterval (1399246375 / 1000000000000) (1399250709 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_chunkChecks1 :
    compactCertificate390.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate390.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate390_chunkChecks1_0
    compactCertificate390_chunkChecks1_1 compactCertificate390_chunkChecks1_2

theorem compactCertificate390_chunkChecks2_0 :
    compactCertificate390.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (523 / 2) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49304786720 / 1000000000000) (-49304786658 / 1000000000000), orderedInterval (-1783494552 / 1000000000000) (-1783494490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (770478865752223 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-56383027268 / 1000000000000) (-56383026397 / 1000000000000), orderedInterval (11371519302 / 1000000000000) (11371520174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (249157034696959 / 800000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-42357992849 / 1000000000000) (-42357992848 / 1000000000000), orderedInterval (-15739403402 / 1000000000000) (-15739403400 / 1000000000000)))) (orderedInterval (23360153384 / 1000000000000) (23360153437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (224823811424861 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (45374513160 / 1000000000000) (45374513161 / 1000000000000), orderedInterval (95866802166 / 1000000000000) (95866802167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (603908381572217 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53388367728 / 1000000000000) (53388367729 / 1000000000000), orderedInterval (36787210705 / 1000000000000) (36787210706 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1639728732879189 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29116525528 / 1000000000000) (29116552936 / 1000000000000), orderedInterval (-26591412402 / 1000000000000) (-26591384995 / 1000000000000)))) (orderedInterval (4446119361 / 1000000000000) (4446124211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1207816763144957 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41840910627 / 1000000000000) (41840910628 / 1000000000000), orderedInterval (18842844616 / 1000000000000) (18842844617 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2069614610226161 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6071950180 / 1000000000000) (6071950184 / 1000000000000), orderedInterval (-34553576351 / 1000000000000) (-34553576347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1524468754713299 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-40065979516 / 1000000000000) (-40065976837 / 1000000000000), orderedInterval (8122278350 / 1000000000000) (8122281029 / 1000000000000)))) (orderedInterval (2780821677 / 1000000000000) (2780821862 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_chunkChecks2_1 :
    compactCertificate390.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2338927104464477 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30517452669 / 1000000000000) (30517452672 / 1000000000000), orderedInterval (12520733670 / 1000000000000) (12520733673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1350380193377333 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34335775770 / 1000000000000) (-34335698308 / 1000000000000), orderedInterval (26636642282 / 1000000000000) (26636719743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2396273350056697 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6178016880 / 1000000000000) (6178016883 / 1000000000000), orderedInterval (-32013210153 / 1000000000000) (-32013210150 / 1000000000000)))) (orderedInterval (26792874809 / 1000000000000) (26792884869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2238909400026493 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32576140354 / 1000000000000) (32576140375 / 1000000000000), orderedInterval (8698412097 / 1000000000000) (8698412118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1597791392307469 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37893530131 / 1000000000000) (-37893530128 / 1000000000000), orderedInterval (-12515560305 / 1000000000000) (-12515560302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1811725144716651 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36382664613 / 1000000000000) (36382664625 / 1000000000000), orderedInterval (9007257253 / 1000000000000) (9007257265 / 1000000000000)))) (orderedInterval (11616325982 / 1000000000000) (11616326069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1510427543823419 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (40468467461 / 1000000000000) (40468467482 / 1000000000000), orderedInterval (6891512364 / 1000000000000) (6891512385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1334508541639799 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43071612024 / 1000000000000) (43071612039 / 1000000000000), orderedInterval (7216359637 / 1000000000000) (7216359653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (386792590336101 / 800000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16453383801 / 1000000000000) (16453383802 / 1000000000000), orderedInterval (32324940926 / 1000000000000) (32324940927 / 1000000000000)))) (orderedInterval (1593266885 / 1000000000000) (1593266941 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_chunkChecks2_2 :
    compactCertificate390.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1069888660648447 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45844222819 / 1000000000000) (-45844222818 / 1000000000000), orderedInterval (-16600784223 / 1000000000000) (-16600784222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (906956466324167 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51450111397 / 1000000000000) (51450111399 / 1000000000000), orderedInterval (12559317792 / 1000000000000) (12559317794 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (567531245286701 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-64464999624 / 1000000000000) (-64464999623 / 1000000000000), orderedInterval (-17971201080 / 1000000000000) (-17971201078 / 1000000000000)))) (orderedInterval (-4868439768 / 1000000000000) (-4868439709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (305220191238867 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90684989508 / 1000000000000) (90684989663 / 1000000000000), orderedInterval (-11509662156 / 1000000000000) (-11509662001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (828732192997601 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32331024220 / 1000000000000) (32331024221 / 1000000000000), orderedInterval (44949171119 / 1000000000000) (44949171120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1131562959043777 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38094342032 / 1000000000000) (38094342033 / 1000000000000), orderedInterval (28203303835 / 1000000000000) (28203303836 / 1000000000000)))) (orderedInterval (4031471494 / 1000000000000) (4031471523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (478468754713299 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62202532771 / 1000000000000) (62202532772 / 1000000000000), orderedInterval (37857798422 / 1000000000000) (37857798423 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1944948924118579 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2729682795 / 1000000000000) (-2729682794 / 1000000000000), orderedInterval (-36078041797 / 1000000000000) (-36078041796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1299135744474461 / 4000000000000) 2 (IntervalRat.scale (523 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40531162970 / 1000000000000) (-40531144811 / 1000000000000), orderedInterval (17876908606 / 1000000000000) (17876926765 / 1000000000000)))) (orderedInterval (-12582891879 / 1000000000000) (-12582886456 / 1000000000000))) = true
  rfl'

theorem compactCertificate390_chunkChecks2 :
    compactCertificate390.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate390.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate390_chunkChecks2_0
    compactCertificate390_chunkChecks2_1 compactCertificate390_chunkChecks2_2

theorem compactCertificate390_chunkChecks3_0 :
    compactCertificate390.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (523 / 2) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49304786720 / 1000000000000) (-49304786658 / 1000000000000), orderedInterval (-1783494552 / 1000000000000) (-1783494490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (770478865752223 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-56383027268 / 1000000000000) (-56383026397 / 1000000000000), orderedInterval (11371519302 / 1000000000000) (11371520174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (249157034696959 / 800000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-42357992849 / 1000000000000) (-42357992848 / 1000000000000), orderedInterval (-15739403402 / 1000000000000) (-15739403400 / 1000000000000)))) (orderedInterval (2135557422 / 1000000000000) (2135557478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (224823811424861 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (45374513160 / 1000000000000) (45374513161 / 1000000000000), orderedInterval (95866802166 / 1000000000000) (95866802167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (603908381572217 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53388367728 / 1000000000000) (53388367729 / 1000000000000), orderedInterval (36787210705 / 1000000000000) (36787210706 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1639728732879189 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29116525528 / 1000000000000) (29116552936 / 1000000000000), orderedInterval (-26591412402 / 1000000000000) (-26591384995 / 1000000000000)))) (orderedInterval (-7547417787 / 1000000000000) (-7547410188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1207816763144957 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41840910627 / 1000000000000) (41840910628 / 1000000000000), orderedInterval (18842844616 / 1000000000000) (18842844617 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2069614610226161 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6071950180 / 1000000000000) (6071950184 / 1000000000000), orderedInterval (-34553576351 / 1000000000000) (-34553576347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1524468754713299 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-40065979516 / 1000000000000) (-40065976837 / 1000000000000), orderedInterval (8122278350 / 1000000000000) (8122281029 / 1000000000000)))) (orderedInterval (-8873666513 / 1000000000000) (-8873666228 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate390_chunkChecks3_1 :
    compactCertificate390.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2338927104464477 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30517452669 / 1000000000000) (30517452672 / 1000000000000), orderedInterval (12520733670 / 1000000000000) (12520733673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1350380193377333 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34335775770 / 1000000000000) (-34335698308 / 1000000000000), orderedInterval (26636642282 / 1000000000000) (26636719743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2396273350056697 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6178016880 / 1000000000000) (6178016883 / 1000000000000), orderedInterval (-32013210153 / 1000000000000) (-32013210150 / 1000000000000)))) (orderedInterval (75239971686 / 1000000000000) (75239985091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2238909400026493 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32576140354 / 1000000000000) (32576140375 / 1000000000000), orderedInterval (8698412097 / 1000000000000) (8698412118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1597791392307469 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37893530131 / 1000000000000) (-37893530128 / 1000000000000), orderedInterval (-12515560305 / 1000000000000) (-12515560302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1811725144716651 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36382664613 / 1000000000000) (36382664625 / 1000000000000), orderedInterval (9007257253 / 1000000000000) (9007257265 / 1000000000000)))) (orderedInterval (5950630423 / 1000000000000) (5950630571 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1510427543823419 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (40468467461 / 1000000000000) (40468467482 / 1000000000000), orderedInterval (6891512364 / 1000000000000) (6891512385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1334508541639799 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43071612024 / 1000000000000) (43071612039 / 1000000000000), orderedInterval (7216359637 / 1000000000000) (7216359653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (386792590336101 / 800000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16453383801 / 1000000000000) (16453383802 / 1000000000000), orderedInterval (32324940926 / 1000000000000) (32324940927 / 1000000000000)))) (orderedInterval (-4619202437 / 1000000000000) (-4619202351 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate390_chunkChecks3_2 :
    compactCertificate390.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1069888660648447 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45844222819 / 1000000000000) (-45844222818 / 1000000000000), orderedInterval (-16600784223 / 1000000000000) (-16600784222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (906956466324167 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51450111397 / 1000000000000) (51450111399 / 1000000000000), orderedInterval (12559317792 / 1000000000000) (12559317794 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (567531245286701 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-64464999624 / 1000000000000) (-64464999623 / 1000000000000), orderedInterval (-17971201080 / 1000000000000) (-17971201078 / 1000000000000)))) (orderedInterval (-2264903498 / 1000000000000) (-2264903441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (305220191238867 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90684989508 / 1000000000000) (90684989663 / 1000000000000), orderedInterval (-11509662156 / 1000000000000) (-11509662001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (828732192997601 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32331024220 / 1000000000000) (32331024221 / 1000000000000), orderedInterval (44949171119 / 1000000000000) (44949171120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1131562959043777 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38094342032 / 1000000000000) (38094342033 / 1000000000000), orderedInterval (28203303835 / 1000000000000) (28203303836 / 1000000000000)))) (orderedInterval (3222883199 / 1000000000000) (3222883229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (478468754713299 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62202532771 / 1000000000000) (62202532772 / 1000000000000), orderedInterval (37857798422 / 1000000000000) (37857798423 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1944948924118579 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2729682795 / 1000000000000) (-2729682794 / 1000000000000), orderedInterval (-36078041797 / 1000000000000) (-36078041796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1299135744474461 / 4000000000000) 3 (IntervalRat.scale (523 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40531162970 / 1000000000000) (-40531144811 / 1000000000000), orderedInterval (17876908606 / 1000000000000) (17876926765 / 1000000000000)))) (orderedInterval (-12427681925 / 1000000000000) (-12427675145 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate390_chunkChecks3 :
    compactCertificate390.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate390.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate390_chunkChecks3_0
    compactCertificate390_chunkChecks3_1 compactCertificate390_chunkChecks3_2

theorem compactCertificate390_chunkChecks4_0 :
    compactCertificate390.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (523 / 2) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-49304786720 / 1000000000000) (-49304786658 / 1000000000000), orderedInterval (-1783494552 / 1000000000000) (-1783494490 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (770478865752223 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-56383027268 / 1000000000000) (-56383026397 / 1000000000000), orderedInterval (11371519302 / 1000000000000) (11371520174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (249157034696959 / 800000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-42357992849 / 1000000000000) (-42357992848 / 1000000000000), orderedInterval (-15739403402 / 1000000000000) (-15739403400 / 1000000000000)))) (orderedInterval (-24714611511 / 1000000000000) (-24714611451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (224823811424861 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (45374513160 / 1000000000000) (45374513161 / 1000000000000), orderedInterval (95866802166 / 1000000000000) (95866802167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (603908381572217 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53388367728 / 1000000000000) (53388367729 / 1000000000000), orderedInterval (36787210705 / 1000000000000) (36787210706 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1639728732879189 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29116525528 / 1000000000000) (29116552936 / 1000000000000), orderedInterval (-26591412402 / 1000000000000) (-26591384995 / 1000000000000)))) (orderedInterval (-12226602376 / 1000000000000) (-12226590438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1207816763144957 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41840910627 / 1000000000000) (41840910628 / 1000000000000), orderedInterval (18842844616 / 1000000000000) (18842844617 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2069614610226161 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (6071950180 / 1000000000000) (6071950184 / 1000000000000), orderedInterval (-34553576351 / 1000000000000) (-34553576347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1524468754713299 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-40065979516 / 1000000000000) (-40065976837 / 1000000000000), orderedInterval (8122278350 / 1000000000000) (8122281029 / 1000000000000)))) (orderedInterval (-7171232494 / 1000000000000) (-7171232046 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate390_chunkChecks4_1 :
    compactCertificate390.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2338927104464477 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (30517452669 / 1000000000000) (30517452672 / 1000000000000), orderedInterval (12520733670 / 1000000000000) (12520733673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1350380193377333 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34335775770 / 1000000000000) (-34335698308 / 1000000000000), orderedInterval (26636642282 / 1000000000000) (26636719743 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2396273350056697 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6178016880 / 1000000000000) (6178016883 / 1000000000000), orderedInterval (-32013210153 / 1000000000000) (-32013210150 / 1000000000000)))) (orderedInterval (-119016471271 / 1000000000000) (-119016452969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2238909400026493 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32576140354 / 1000000000000) (32576140375 / 1000000000000), orderedInterval (8698412097 / 1000000000000) (8698412118 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1597791392307469 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37893530131 / 1000000000000) (-37893530128 / 1000000000000), orderedInterval (-12515560305 / 1000000000000) (-12515560302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1811725144716651 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (36382664613 / 1000000000000) (36382664625 / 1000000000000), orderedInterval (9007257253 / 1000000000000) (9007257265 / 1000000000000)))) (orderedInterval (-33556000209 / 1000000000000) (-33555999952 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1510427543823419 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (40468467461 / 1000000000000) (40468467482 / 1000000000000), orderedInterval (6891512364 / 1000000000000) (6891512385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1334508541639799 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43071612024 / 1000000000000) (43071612039 / 1000000000000), orderedInterval (7216359637 / 1000000000000) (7216359653 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (386792590336101 / 800000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16453383801 / 1000000000000) (16453383802 / 1000000000000), orderedInterval (32324940926 / 1000000000000) (32324940927 / 1000000000000)))) (orderedInterval (459616887 / 1000000000000) (459617023 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate390_chunkChecks4_2 :
    compactCertificate390.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1069888660648447 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45844222819 / 1000000000000) (-45844222818 / 1000000000000), orderedInterval (-16600784223 / 1000000000000) (-16600784222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (906956466324167 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (51450111397 / 1000000000000) (51450111399 / 1000000000000), orderedInterval (12559317792 / 1000000000000) (12559317794 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (567531245286701 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-64464999624 / 1000000000000) (-64464999623 / 1000000000000), orderedInterval (-17971201080 / 1000000000000) (-17971201078 / 1000000000000)))) (orderedInterval (6212467961 / 1000000000000) (6212468017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (305220191238867 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (90684989508 / 1000000000000) (90684989663 / 1000000000000), orderedInterval (-11509662156 / 1000000000000) (-11509662001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (828732192997601 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32331024220 / 1000000000000) (32331024221 / 1000000000000), orderedInterval (44949171119 / 1000000000000) (44949171120 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1131562959043777 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38094342032 / 1000000000000) (38094342033 / 1000000000000), orderedInterval (28203303835 / 1000000000000) (28203303836 / 1000000000000)))) (orderedInterval (-4324253080 / 1000000000000) (-4324253049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (478468754713299 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62202532771 / 1000000000000) (62202532772 / 1000000000000), orderedInterval (37857798422 / 1000000000000) (37857798423 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1944948924118579 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2729682795 / 1000000000000) (-2729682794 / 1000000000000), orderedInterval (-36078041797 / 1000000000000) (-36078041796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1299135744474461 / 4000000000000) 4 (IntervalRat.scale (523 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40531162970 / 1000000000000) (-40531144811 / 1000000000000), orderedInterval (17876908606 / 1000000000000) (17876926765 / 1000000000000)))) (orderedInterval (20863092033 / 1000000000000) (20863100563 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate390_chunkChecks4 :
    compactCertificate390.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate390.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate390_chunkChecks4_0
    compactCertificate390_chunkChecks4_1 compactCertificate390_chunkChecks4_2

theorem compactCertificate390_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate390.chunkCheck r b = true :=
  compactCertificate390.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate390_chunkChecks0
    · exact compactCertificate390_chunkChecks1
    · exact compactCertificate390_chunkChecks2
    · exact compactCertificate390_chunkChecks3
    · exact compactCertificate390_chunkChecks4)

theorem compactCertificate390_coefficient0 :
    compactCertificate390.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate390_coefficient1 :
    compactCertificate390.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate390_coefficient2 :
    compactCertificate390.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate390_coefficient3 :
    compactCertificate390.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate390_coefficient4 :
    compactCertificate390.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate390_coefficients : ∀ r : Fin 5,
    compactCertificate390.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate390_coefficient0
  · exact compactCertificate390_coefficient1
  · exact compactCertificate390_coefficient2
  · exact compactCertificate390_coefficient3
  · exact compactCertificate390_coefficient4

theorem compactCertificate390_lower : (1 : ℚ) ≤ compactCertificate390.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate390, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate390_proves {t : ℝ} (ht : t ∈ compactCertificate390.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate390.proves compactCertificate390_states compactCertificate390_chunks
    compactCertificate390_coefficients compactCertificate390_lower ht

end Erdos232
