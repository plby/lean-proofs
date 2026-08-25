/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate291 : CompactCertificate where
  left := 165
  right := 166
  center := 331 / 2
  grid := fun i =>
    match i.val with
    | 0 => 53
    | 1 => 39
    | 2 => 63
    | 3 => 11
    | 4 => 30
    | 5 => 83
    | 6 => 61
    | 7 => 104
    | 8 => 77
    | 9 => 118
    | 10 => 68
    | 11 => 121
    | 12 => 113
    | 13 => 81
    | 14 => 91
    | 15 => 76
    | 16 => 67
    | 17 => 97
    | 18 => 54
    | 19 => 46
    | 20 => 29
    | 21 => 15
    | 22 => 42
    | 23 => 57
    | 24 => 24
    | 25 => 98
    | _ => 65
  point := fun i =>
    match i.val with
    | 0 => 331 / 2
    | 1 => 487626203755231 / 4000000000000
    | 2 => 157688295381823 / 800000000000
    | 3 => 142288110098717 / 4000000000000
    | 4 => 382205878203449 / 4000000000000
    | 5 => 1037763308954133 / 4000000000000
    | 6 => 764411756407229 / 4000000000000
    | 7 => 1309832573584817 / 4000000000000
    | 8 => 964816745334803 / 4000000000000
    | 9 => 1480277001104669 / 4000000000000
    | 10 => 854638325062901 / 4000000000000
    | 11 => 1516570705294009 / 4000000000000
    | 12 => 1416977077263421 / 4000000000000
    | 13 => 1011221703353293 / 4000000000000
    | 14 => 1146617634610347 / 4000000000000
    | 15 => 955930242840443 / 4000000000000
    | 16 => 844593360005303 / 4000000000000
    | 17 => 244796075336997 / 800000000000
    | 18 => 677118827293759 / 4000000000000
    | 19 => 574001128782599 / 4000000000000
    | 20 => 359183254665197 / 4000000000000
    | 21 => 193169948948499 / 4000000000000
    | 22 => 524493988302497 / 4000000000000
    | 23 => 716151700656769 / 4000000000000
    | 24 => 302816745334803 / 4000000000000
    | 25 => 1230933257902963 / 4000000000000
    | _ => 822206369829917 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (13520802502 / 1000000000000) (13520802611 / 1000000000000), orderedInterval (-60570583972 / 1000000000000) (-60570583863 / 1000000000000))
    | 1 => (orderedInterval (-12141125446 / 1000000000000) (-12141125445 / 1000000000000), orderedInterval (-71188041153 / 1000000000000) (-71188041152 / 1000000000000))
    | 2 => (orderedInterval (1432211225 / 1000000000000) (1432211229 / 1000000000000), orderedInterval (-56816678354 / 1000000000000) (-56816678350 / 1000000000000))
    | 3 => (orderedInterval (-130382030293 / 1000000000000) (-130382029808 / 1000000000000), orderedInterval (31758486088 / 1000000000000) (31758486573 / 1000000000000))
    | 4 => (orderedInterval (70956963216 / 1000000000000) (70956979332 / 1000000000000), orderedInterval (-40715399276 / 1000000000000) (-40715383160 / 1000000000000))
    | 5 => (orderedInterval (24890045050 / 1000000000000) (24890047788 / 1000000000000), orderedInterval (-42876730700 / 1000000000000) (-42876727963 / 1000000000000))
    | 6 => (orderedInterval (-14309186608 / 1000000000000) (-14309186607 / 1000000000000), orderedInterval (-55878119578 / 1000000000000) (-55878119577 / 1000000000000))
    | 7 => (orderedInterval (44029663303 / 1000000000000) (44029663384 / 1000000000000), orderedInterval (2280563578 / 1000000000000) (2280563659 / 1000000000000))
    | 8 => (orderedInterval (-4434866799 / 1000000000000) (-4434866798 / 1000000000000), orderedInterval (-51173589034 / 1000000000000) (-51173589032 / 1000000000000))
    | 9 => (orderedInterval (6049518546 / 1000000000000) (6049518547 / 1000000000000), orderedInterval (41024457887 / 1000000000000) (41024457888 / 1000000000000))
    | 10 => (orderedInterval (39764288089 / 1000000000000) (39764288090 / 1000000000000), orderedInterval (37302124279 / 1000000000000) (37302124280 / 1000000000000))
    | 11 => (orderedInterval (8340187821 / 1000000000000) (8340187839 / 1000000000000), orderedInterval (-40130146868 / 1000000000000) (-40130146850 / 1000000000000))
    | 12 => (orderedInterval (-1243817541 / 1000000000000) (-1243817540 / 1000000000000), orderedInterval (-42372476948 / 1000000000000) (-42372476947 / 1000000000000))
    | 13 => (orderedInterval (38634652520 / 1000000000000) (38634736581 / 1000000000000), orderedInterval (-32101125742 / 1000000000000) (-32101041680 / 1000000000000))
    | 14 => (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000))
    | 15 => (orderedInterval (43608000986 / 1000000000000) (43608000987 / 1000000000000), orderedInterval (27517008561 / 1000000000000) (27517008562 / 1000000000000))
    | 16 => (orderedInterval (-54485227100 / 1000000000000) (-54485227088 / 1000000000000), orderedInterval (-6681815358 / 1000000000000) (-6681815346 / 1000000000000))
    | 17 => (orderedInterval (-40566922570 / 1000000000000) (-40566893263 / 1000000000000), orderedInterval (20918476571 / 1000000000000) (20918505879 / 1000000000000))
    | 18 => (orderedInterval (24914176949 / 1000000000000) (24914176950 / 1000000000000), orderedInterval (55962573056 / 1000000000000) (55962573057 / 1000000000000))
    | 19 => (orderedInterval (-15084277095 / 1000000000000) (-15084276951 / 1000000000000), orderedInterval (64928244521 / 1000000000000) (64928244665 / 1000000000000))
    | 20 => (orderedInterval (42301362744 / 1000000000000) (42301369510 / 1000000000000), orderedInterval (-73038603539 / 1000000000000) (-73038596773 / 1000000000000))
    | 21 => (orderedInterval (-106596120509 / 1000000000000) (-106596117341 / 1000000000000), orderedInterval (43757256721 / 1000000000000) (43757259889 / 1000000000000))
    | 22 => (orderedInterval (-2713251809 / 1000000000000) (-2713251800 / 1000000000000), orderedInterval (69636413893 / 1000000000000) (69636413902 / 1000000000000))
    | 23 => (orderedInterval (-40726677933 / 1000000000000) (-40726677932 / 1000000000000), orderedInterval (-43442207840 / 1000000000000) (-43442207839 / 1000000000000))
    | 24 => (orderedInterval (81292508299 / 1000000000000) (81292508300 / 1000000000000), orderedInterval (41898131092 / 1000000000000) (41898131093 / 1000000000000))
    | 25 => (orderedInterval (27243609782 / 1000000000000) (27243609783 / 1000000000000), orderedInterval (36377226778 / 1000000000000) (36377226779 / 1000000000000))
    | _ => (orderedInterval (-47090161501 / 1000000000000) (-47090120693 / 1000000000000), orderedInterval (29773307677 / 1000000000000) (29773348485 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5330084835 / 1000000000000) (5330084891 / 1000000000000)
      | 1 => orderedInterval (2235890628 / 1000000000000) (2235891437 / 1000000000000)
      | 2 => orderedInterval (-1465232967 / 1000000000000) (-1465232954 / 1000000000000)
      | 3 => orderedInterval (3056886929 / 1000000000000) (3056886998 / 1000000000000)
      | 4 => orderedInterval (3914310917 / 1000000000000) (3914318887 / 1000000000000)
      | 5 => orderedInterval (2582905831 / 1000000000000) (2582906599 / 1000000000000)
      | 6 => orderedInterval (-1752686875 / 1000000000000) (-1752686604 / 1000000000000)
      | 7 => orderedInterval (5151111513 / 1000000000000) (5151111592 / 1000000000000)
      | _ => orderedInterval (7107735434 / 1000000000000) (7107743137 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-28467539951 / 1000000000000) (-28467539894 / 1000000000000)
      | 1 => orderedInterval (3845902219 / 1000000000000) (3845902889 / 1000000000000)
      | 2 => orderedInterval (-1941672418 / 1000000000000) (-1941672396 / 1000000000000)
      | 3 => orderedInterval (-25800843735 / 1000000000000) (-25800843592 / 1000000000000)
      | 4 => orderedInterval (-2993535934 / 1000000000000) (-2993523758 / 1000000000000)
      | 5 => orderedInterval (1936958265 / 1000000000000) (1936959677 / 1000000000000)
      | 6 => orderedInterval (-13628903886 / 1000000000000) (-13628903720 / 1000000000000)
      | 7 => orderedInterval (2114256488 / 1000000000000) (2114256524 / 1000000000000)
      | _ => orderedInterval (-12328680330 / 1000000000000) (-12328670755 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-5244995680 / 1000000000000) (-5244995621 / 1000000000000)
      | 1 => orderedInterval (3396056360 / 1000000000000) (3396057070 / 1000000000000)
      | 2 => orderedInterval (5555968322 / 1000000000000) (5555968362 / 1000000000000)
      | 3 => orderedInterval (-5602103067 / 1000000000000) (-5602102761 / 1000000000000)
      | 4 => orderedInterval (-9324773937 / 1000000000000) (-9324755261 / 1000000000000)
      | 5 => orderedInterval (-2586281941 / 1000000000000) (-2586279332 / 1000000000000)
      | 6 => orderedInterval (3202689335 / 1000000000000) (3202689444 / 1000000000000)
      | 7 => orderedInterval (-3871776140 / 1000000000000) (-3871776116 / 1000000000000)
      | _ => orderedInterval (-5989777341 / 1000000000000) (-5989765376 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (29936416197 / 1000000000000) (29936416259 / 1000000000000)
      | 1 => orderedInterval (-11473049847 / 1000000000000) (-11473048933 / 1000000000000)
      | 2 => orderedInterval (4339887057 / 1000000000000) (4339887130 / 1000000000000)
      | 3 => orderedInterval (144174090578 / 1000000000000) (144174091250 / 1000000000000)
      | 4 => orderedInterval (3356040349 / 1000000000000) (3356068886 / 1000000000000)
      | 5 => orderedInterval (-5120353023 / 1000000000000) (-5120348210 / 1000000000000)
      | 6 => orderedInterval (12330709147 / 1000000000000) (12330709224 / 1000000000000)
      | 7 => orderedInterval (-3385794659 / 1000000000000) (-3385794639 / 1000000000000)
      | _ => orderedInterval (29750940857 / 1000000000000) (29750955745 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (5133016938 / 1000000000000) (5133017003 / 1000000000000)
      | 1 => orderedInterval (-10255811178 / 1000000000000) (-10255809854 / 1000000000000)
      | 2 => orderedInterval (-21349426231 / 1000000000000) (-21349426095 / 1000000000000)
      | 3 => orderedInterval (12223991715 / 1000000000000) (12223993209 / 1000000000000)
      | 4 => orderedInterval (22467262649 / 1000000000000) (22467306429 / 1000000000000)
      | 5 => orderedInterval (-1625649312 / 1000000000000) (-1625640400 / 1000000000000)
      | 6 => orderedInterval (-3907132932 / 1000000000000) (-3907132872 / 1000000000000)
      | 7 => orderedInterval (4354102845 / 1000000000000) (4354102865 / 1000000000000)
      | _ => orderedInterval (-5823971904 / 1000000000000) (-5823953272 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (26161006245 / 1000000000000) (26161023983 / 1000000000000)
    | 1 => orderedInterval (-77264059282 / 1000000000000) (-77264035025 / 1000000000000)
    | 2 => orderedInterval (-20464994089 / 1000000000000) (-20464959591 / 1000000000000)
    | 3 => orderedInterval (203908886656 / 1000000000000) (203908936712 / 1000000000000)
    | _ => orderedInterval (1216382590 / 1000000000000) (1216457013 / 1000000000000)

theorem compactCertificate291_stateChecks0 :
    compactCertificate291.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (331 / 2)) (orderedInterval (13520802502 / 1000000000000) (13520802611 / 1000000000000), orderedInterval (-60570583972 / 1000000000000) (-60570583863 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (487626203755231 / 4000000000000)) (orderedInterval (-12141125446 / 1000000000000) (-12141125445 / 1000000000000), orderedInterval (-71188041153 / 1000000000000) (-71188041152 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (157688295381823 / 800000000000)) (orderedInterval (1432211225 / 1000000000000) (1432211229 / 1000000000000), orderedInterval (-56816678354 / 1000000000000) (-56816678350 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_stateChecks1 :
    compactCertificate291.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (142288110098717 / 4000000000000)) (orderedInterval (-130382030293 / 1000000000000) (-130382029808 / 1000000000000), orderedInterval (31758486088 / 1000000000000) (31758486573 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (382205878203449 / 4000000000000)) (orderedInterval (70956963216 / 1000000000000) (70956979332 / 1000000000000), orderedInterval (-40715399276 / 1000000000000) (-40715383160 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1037763308954133 / 4000000000000)) (orderedInterval (24890045050 / 1000000000000) (24890047788 / 1000000000000), orderedInterval (-42876730700 / 1000000000000) (-42876727963 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_stateChecks2 :
    compactCertificate291.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (764411756407229 / 4000000000000)) (orderedInterval (-14309186608 / 1000000000000) (-14309186607 / 1000000000000), orderedInterval (-55878119578 / 1000000000000) (-55878119577 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1309832573584817 / 4000000000000)) (orderedInterval (44029663303 / 1000000000000) (44029663384 / 1000000000000), orderedInterval (2280563578 / 1000000000000) (2280563659 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (964816745334803 / 4000000000000)) (orderedInterval (-4434866799 / 1000000000000) (-4434866798 / 1000000000000), orderedInterval (-51173589034 / 1000000000000) (-51173589032 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_stateChecks3 :
    compactCertificate291.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1480277001104669 / 4000000000000)) (orderedInterval (6049518546 / 1000000000000) (6049518547 / 1000000000000), orderedInterval (41024457887 / 1000000000000) (41024457888 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (854638325062901 / 4000000000000)) (orderedInterval (39764288089 / 1000000000000) (39764288090 / 1000000000000), orderedInterval (37302124279 / 1000000000000) (37302124280 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1516570705294009 / 4000000000000)) (orderedInterval (8340187821 / 1000000000000) (8340187839 / 1000000000000), orderedInterval (-40130146868 / 1000000000000) (-40130146850 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_stateChecks4 :
    compactCertificate291.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1416977077263421 / 4000000000000)) (orderedInterval (-1243817541 / 1000000000000) (-1243817540 / 1000000000000), orderedInterval (-42372476948 / 1000000000000) (-42372476947 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1011221703353293 / 4000000000000)) (orderedInterval (38634652520 / 1000000000000) (38634736581 / 1000000000000), orderedInterval (-32101125742 / 1000000000000) (-32101041680 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1146617634610347 / 4000000000000)) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_stateChecks5 :
    compactCertificate291.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (955930242840443 / 4000000000000)) (orderedInterval (43608000986 / 1000000000000) (43608000987 / 1000000000000), orderedInterval (27517008561 / 1000000000000) (27517008562 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (844593360005303 / 4000000000000)) (orderedInterval (-54485227100 / 1000000000000) (-54485227088 / 1000000000000), orderedInterval (-6681815358 / 1000000000000) (-6681815346 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (244796075336997 / 800000000000)) (orderedInterval (-40566922570 / 1000000000000) (-40566893263 / 1000000000000), orderedInterval (20918476571 / 1000000000000) (20918505879 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_stateChecks6 :
    compactCertificate291.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (677118827293759 / 4000000000000)) (orderedInterval (24914176949 / 1000000000000) (24914176950 / 1000000000000), orderedInterval (55962573056 / 1000000000000) (55962573057 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (574001128782599 / 4000000000000)) (orderedInterval (-15084277095 / 1000000000000) (-15084276951 / 1000000000000), orderedInterval (64928244521 / 1000000000000) (64928244665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (359183254665197 / 4000000000000)) (orderedInterval (42301362744 / 1000000000000) (42301369510 / 1000000000000), orderedInterval (-73038603539 / 1000000000000) (-73038596773 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_stateChecks7 :
    compactCertificate291.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (193169948948499 / 4000000000000)) (orderedInterval (-106596120509 / 1000000000000) (-106596117341 / 1000000000000), orderedInterval (43757256721 / 1000000000000) (43757259889 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (524493988302497 / 4000000000000)) (orderedInterval (-2713251809 / 1000000000000) (-2713251800 / 1000000000000), orderedInterval (69636413893 / 1000000000000) (69636413902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (716151700656769 / 4000000000000)) (orderedInterval (-40726677933 / 1000000000000) (-40726677932 / 1000000000000), orderedInterval (-43442207840 / 1000000000000) (-43442207839 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_stateChecks8 :
    compactCertificate291.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (302816745334803 / 4000000000000)) (orderedInterval (81292508299 / 1000000000000) (81292508300 / 1000000000000), orderedInterval (41898131092 / 1000000000000) (41898131093 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1230933257902963 / 4000000000000)) (orderedInterval (27243609782 / 1000000000000) (27243609783 / 1000000000000), orderedInterval (36377226778 / 1000000000000) (36377226779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (822206369829917 / 4000000000000)) (orderedInterval (-47090161501 / 1000000000000) (-47090120693 / 1000000000000), orderedInterval (29773307677 / 1000000000000) (29773348485 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_states : ∀ j,
    BesselStateValid (compactCertificate291.point j) (compactCertificate291.state j) :=
  compactCertificate291.statesValid_of_checks3 compactCertificate291_stateChecks0
    compactCertificate291_stateChecks1 compactCertificate291_stateChecks2
    compactCertificate291_stateChecks3 compactCertificate291_stateChecks4
    compactCertificate291_stateChecks5 compactCertificate291_stateChecks6
    compactCertificate291_stateChecks7 compactCertificate291_stateChecks8

theorem compactCertificate291_chunkChecks0_0 :
    compactCertificate291.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (331 / 2) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13520802502 / 1000000000000) (13520802611 / 1000000000000), orderedInterval (-60570583972 / 1000000000000) (-60570583863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (487626203755231 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12141125446 / 1000000000000) (-12141125445 / 1000000000000), orderedInterval (-71188041153 / 1000000000000) (-71188041152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (157688295381823 / 800000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1432211225 / 1000000000000) (1432211229 / 1000000000000), orderedInterval (-56816678354 / 1000000000000) (-56816678350 / 1000000000000)))) (orderedInterval (5330084835 / 1000000000000) (5330084891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (142288110098717 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-130382030293 / 1000000000000) (-130382029808 / 1000000000000), orderedInterval (31758486088 / 1000000000000) (31758486573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (382205878203449 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (70956963216 / 1000000000000) (70956979332 / 1000000000000), orderedInterval (-40715399276 / 1000000000000) (-40715383160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1037763308954133 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24890045050 / 1000000000000) (24890047788 / 1000000000000), orderedInterval (-42876730700 / 1000000000000) (-42876727963 / 1000000000000)))) (orderedInterval (2235890628 / 1000000000000) (2235891437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (764411756407229 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14309186608 / 1000000000000) (-14309186607 / 1000000000000), orderedInterval (-55878119578 / 1000000000000) (-55878119577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1309832573584817 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44029663303 / 1000000000000) (44029663384 / 1000000000000), orderedInterval (2280563578 / 1000000000000) (2280563659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (964816745334803 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4434866799 / 1000000000000) (-4434866798 / 1000000000000), orderedInterval (-51173589034 / 1000000000000) (-51173589032 / 1000000000000)))) (orderedInterval (-1465232967 / 1000000000000) (-1465232954 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_chunkChecks0_1 :
    compactCertificate291.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1480277001104669 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6049518546 / 1000000000000) (6049518547 / 1000000000000), orderedInterval (41024457887 / 1000000000000) (41024457888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (854638325062901 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39764288089 / 1000000000000) (39764288090 / 1000000000000), orderedInterval (37302124279 / 1000000000000) (37302124280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1516570705294009 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8340187821 / 1000000000000) (8340187839 / 1000000000000), orderedInterval (-40130146868 / 1000000000000) (-40130146850 / 1000000000000)))) (orderedInterval (3056886929 / 1000000000000) (3056886998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1416977077263421 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1243817541 / 1000000000000) (-1243817540 / 1000000000000), orderedInterval (-42372476948 / 1000000000000) (-42372476947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1011221703353293 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38634652520 / 1000000000000) (38634736581 / 1000000000000), orderedInterval (-32101125742 / 1000000000000) (-32101041680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1146617634610347 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000)))) (orderedInterval (3914310917 / 1000000000000) (3914318887 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (955930242840443 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (43608000986 / 1000000000000) (43608000987 / 1000000000000), orderedInterval (27517008561 / 1000000000000) (27517008562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (844593360005303 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54485227100 / 1000000000000) (-54485227088 / 1000000000000), orderedInterval (-6681815358 / 1000000000000) (-6681815346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (244796075336997 / 800000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40566922570 / 1000000000000) (-40566893263 / 1000000000000), orderedInterval (20918476571 / 1000000000000) (20918505879 / 1000000000000)))) (orderedInterval (2582905831 / 1000000000000) (2582906599 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_chunkChecks0_2 :
    compactCertificate291.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (677118827293759 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24914176949 / 1000000000000) (24914176950 / 1000000000000), orderedInterval (55962573056 / 1000000000000) (55962573057 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (574001128782599 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-15084277095 / 1000000000000) (-15084276951 / 1000000000000), orderedInterval (64928244521 / 1000000000000) (64928244665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (359183254665197 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42301362744 / 1000000000000) (42301369510 / 1000000000000), orderedInterval (-73038603539 / 1000000000000) (-73038596773 / 1000000000000)))) (orderedInterval (-1752686875 / 1000000000000) (-1752686604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (193169948948499 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-106596120509 / 1000000000000) (-106596117341 / 1000000000000), orderedInterval (43757256721 / 1000000000000) (43757259889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (524493988302497 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2713251809 / 1000000000000) (-2713251800 / 1000000000000), orderedInterval (69636413893 / 1000000000000) (69636413902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (716151700656769 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40726677933 / 1000000000000) (-40726677932 / 1000000000000), orderedInterval (-43442207840 / 1000000000000) (-43442207839 / 1000000000000)))) (orderedInterval (5151111513 / 1000000000000) (5151111592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (302816745334803 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (81292508299 / 1000000000000) (81292508300 / 1000000000000), orderedInterval (41898131092 / 1000000000000) (41898131093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1230933257902963 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27243609782 / 1000000000000) (27243609783 / 1000000000000), orderedInterval (36377226778 / 1000000000000) (36377226779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (822206369829917 / 4000000000000) 0 (IntervalRat.scale (331 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-47090161501 / 1000000000000) (-47090120693 / 1000000000000), orderedInterval (29773307677 / 1000000000000) (29773348485 / 1000000000000)))) (orderedInterval (7107735434 / 1000000000000) (7107743137 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_chunkChecks0 :
    compactCertificate291.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate291.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate291_chunkChecks0_0
    compactCertificate291_chunkChecks0_1 compactCertificate291_chunkChecks0_2

theorem compactCertificate291_chunkChecks1_0 :
    compactCertificate291.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (331 / 2) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13520802502 / 1000000000000) (13520802611 / 1000000000000), orderedInterval (-60570583972 / 1000000000000) (-60570583863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (487626203755231 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12141125446 / 1000000000000) (-12141125445 / 1000000000000), orderedInterval (-71188041153 / 1000000000000) (-71188041152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (157688295381823 / 800000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1432211225 / 1000000000000) (1432211229 / 1000000000000), orderedInterval (-56816678354 / 1000000000000) (-56816678350 / 1000000000000)))) (orderedInterval (-28467539951 / 1000000000000) (-28467539894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (142288110098717 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-130382030293 / 1000000000000) (-130382029808 / 1000000000000), orderedInterval (31758486088 / 1000000000000) (31758486573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (382205878203449 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (70956963216 / 1000000000000) (70956979332 / 1000000000000), orderedInterval (-40715399276 / 1000000000000) (-40715383160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1037763308954133 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24890045050 / 1000000000000) (24890047788 / 1000000000000), orderedInterval (-42876730700 / 1000000000000) (-42876727963 / 1000000000000)))) (orderedInterval (3845902219 / 1000000000000) (3845902889 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (764411756407229 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14309186608 / 1000000000000) (-14309186607 / 1000000000000), orderedInterval (-55878119578 / 1000000000000) (-55878119577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1309832573584817 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44029663303 / 1000000000000) (44029663384 / 1000000000000), orderedInterval (2280563578 / 1000000000000) (2280563659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (964816745334803 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4434866799 / 1000000000000) (-4434866798 / 1000000000000), orderedInterval (-51173589034 / 1000000000000) (-51173589032 / 1000000000000)))) (orderedInterval (-1941672418 / 1000000000000) (-1941672396 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_chunkChecks1_1 :
    compactCertificate291.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1480277001104669 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6049518546 / 1000000000000) (6049518547 / 1000000000000), orderedInterval (41024457887 / 1000000000000) (41024457888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (854638325062901 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39764288089 / 1000000000000) (39764288090 / 1000000000000), orderedInterval (37302124279 / 1000000000000) (37302124280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1516570705294009 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8340187821 / 1000000000000) (8340187839 / 1000000000000), orderedInterval (-40130146868 / 1000000000000) (-40130146850 / 1000000000000)))) (orderedInterval (-25800843735 / 1000000000000) (-25800843592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1416977077263421 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1243817541 / 1000000000000) (-1243817540 / 1000000000000), orderedInterval (-42372476948 / 1000000000000) (-42372476947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1011221703353293 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38634652520 / 1000000000000) (38634736581 / 1000000000000), orderedInterval (-32101125742 / 1000000000000) (-32101041680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1146617634610347 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000)))) (orderedInterval (-2993535934 / 1000000000000) (-2993523758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (955930242840443 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (43608000986 / 1000000000000) (43608000987 / 1000000000000), orderedInterval (27517008561 / 1000000000000) (27517008562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (844593360005303 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54485227100 / 1000000000000) (-54485227088 / 1000000000000), orderedInterval (-6681815358 / 1000000000000) (-6681815346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (244796075336997 / 800000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40566922570 / 1000000000000) (-40566893263 / 1000000000000), orderedInterval (20918476571 / 1000000000000) (20918505879 / 1000000000000)))) (orderedInterval (1936958265 / 1000000000000) (1936959677 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_chunkChecks1_2 :
    compactCertificate291.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (677118827293759 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24914176949 / 1000000000000) (24914176950 / 1000000000000), orderedInterval (55962573056 / 1000000000000) (55962573057 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (574001128782599 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-15084277095 / 1000000000000) (-15084276951 / 1000000000000), orderedInterval (64928244521 / 1000000000000) (64928244665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (359183254665197 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42301362744 / 1000000000000) (42301369510 / 1000000000000), orderedInterval (-73038603539 / 1000000000000) (-73038596773 / 1000000000000)))) (orderedInterval (-13628903886 / 1000000000000) (-13628903720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (193169948948499 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-106596120509 / 1000000000000) (-106596117341 / 1000000000000), orderedInterval (43757256721 / 1000000000000) (43757259889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (524493988302497 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2713251809 / 1000000000000) (-2713251800 / 1000000000000), orderedInterval (69636413893 / 1000000000000) (69636413902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (716151700656769 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40726677933 / 1000000000000) (-40726677932 / 1000000000000), orderedInterval (-43442207840 / 1000000000000) (-43442207839 / 1000000000000)))) (orderedInterval (2114256488 / 1000000000000) (2114256524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (302816745334803 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (81292508299 / 1000000000000) (81292508300 / 1000000000000), orderedInterval (41898131092 / 1000000000000) (41898131093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1230933257902963 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27243609782 / 1000000000000) (27243609783 / 1000000000000), orderedInterval (36377226778 / 1000000000000) (36377226779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (822206369829917 / 4000000000000) 1 (IntervalRat.scale (331 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-47090161501 / 1000000000000) (-47090120693 / 1000000000000), orderedInterval (29773307677 / 1000000000000) (29773348485 / 1000000000000)))) (orderedInterval (-12328680330 / 1000000000000) (-12328670755 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_chunkChecks1 :
    compactCertificate291.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate291.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate291_chunkChecks1_0
    compactCertificate291_chunkChecks1_1 compactCertificate291_chunkChecks1_2

theorem compactCertificate291_chunkChecks2_0 :
    compactCertificate291.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (331 / 2) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13520802502 / 1000000000000) (13520802611 / 1000000000000), orderedInterval (-60570583972 / 1000000000000) (-60570583863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (487626203755231 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12141125446 / 1000000000000) (-12141125445 / 1000000000000), orderedInterval (-71188041153 / 1000000000000) (-71188041152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (157688295381823 / 800000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1432211225 / 1000000000000) (1432211229 / 1000000000000), orderedInterval (-56816678354 / 1000000000000) (-56816678350 / 1000000000000)))) (orderedInterval (-5244995680 / 1000000000000) (-5244995621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (142288110098717 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-130382030293 / 1000000000000) (-130382029808 / 1000000000000), orderedInterval (31758486088 / 1000000000000) (31758486573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (382205878203449 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (70956963216 / 1000000000000) (70956979332 / 1000000000000), orderedInterval (-40715399276 / 1000000000000) (-40715383160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1037763308954133 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24890045050 / 1000000000000) (24890047788 / 1000000000000), orderedInterval (-42876730700 / 1000000000000) (-42876727963 / 1000000000000)))) (orderedInterval (3396056360 / 1000000000000) (3396057070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (764411756407229 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14309186608 / 1000000000000) (-14309186607 / 1000000000000), orderedInterval (-55878119578 / 1000000000000) (-55878119577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1309832573584817 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44029663303 / 1000000000000) (44029663384 / 1000000000000), orderedInterval (2280563578 / 1000000000000) (2280563659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (964816745334803 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4434866799 / 1000000000000) (-4434866798 / 1000000000000), orderedInterval (-51173589034 / 1000000000000) (-51173589032 / 1000000000000)))) (orderedInterval (5555968322 / 1000000000000) (5555968362 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_chunkChecks2_1 :
    compactCertificate291.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1480277001104669 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6049518546 / 1000000000000) (6049518547 / 1000000000000), orderedInterval (41024457887 / 1000000000000) (41024457888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (854638325062901 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39764288089 / 1000000000000) (39764288090 / 1000000000000), orderedInterval (37302124279 / 1000000000000) (37302124280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1516570705294009 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8340187821 / 1000000000000) (8340187839 / 1000000000000), orderedInterval (-40130146868 / 1000000000000) (-40130146850 / 1000000000000)))) (orderedInterval (-5602103067 / 1000000000000) (-5602102761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1416977077263421 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1243817541 / 1000000000000) (-1243817540 / 1000000000000), orderedInterval (-42372476948 / 1000000000000) (-42372476947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1011221703353293 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38634652520 / 1000000000000) (38634736581 / 1000000000000), orderedInterval (-32101125742 / 1000000000000) (-32101041680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1146617634610347 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000)))) (orderedInterval (-9324773937 / 1000000000000) (-9324755261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (955930242840443 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (43608000986 / 1000000000000) (43608000987 / 1000000000000), orderedInterval (27517008561 / 1000000000000) (27517008562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (844593360005303 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54485227100 / 1000000000000) (-54485227088 / 1000000000000), orderedInterval (-6681815358 / 1000000000000) (-6681815346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (244796075336997 / 800000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40566922570 / 1000000000000) (-40566893263 / 1000000000000), orderedInterval (20918476571 / 1000000000000) (20918505879 / 1000000000000)))) (orderedInterval (-2586281941 / 1000000000000) (-2586279332 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_chunkChecks2_2 :
    compactCertificate291.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (677118827293759 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24914176949 / 1000000000000) (24914176950 / 1000000000000), orderedInterval (55962573056 / 1000000000000) (55962573057 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (574001128782599 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-15084277095 / 1000000000000) (-15084276951 / 1000000000000), orderedInterval (64928244521 / 1000000000000) (64928244665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (359183254665197 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42301362744 / 1000000000000) (42301369510 / 1000000000000), orderedInterval (-73038603539 / 1000000000000) (-73038596773 / 1000000000000)))) (orderedInterval (3202689335 / 1000000000000) (3202689444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (193169948948499 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-106596120509 / 1000000000000) (-106596117341 / 1000000000000), orderedInterval (43757256721 / 1000000000000) (43757259889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (524493988302497 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2713251809 / 1000000000000) (-2713251800 / 1000000000000), orderedInterval (69636413893 / 1000000000000) (69636413902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (716151700656769 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40726677933 / 1000000000000) (-40726677932 / 1000000000000), orderedInterval (-43442207840 / 1000000000000) (-43442207839 / 1000000000000)))) (orderedInterval (-3871776140 / 1000000000000) (-3871776116 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (302816745334803 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (81292508299 / 1000000000000) (81292508300 / 1000000000000), orderedInterval (41898131092 / 1000000000000) (41898131093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1230933257902963 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27243609782 / 1000000000000) (27243609783 / 1000000000000), orderedInterval (36377226778 / 1000000000000) (36377226779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (822206369829917 / 4000000000000) 2 (IntervalRat.scale (331 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-47090161501 / 1000000000000) (-47090120693 / 1000000000000), orderedInterval (29773307677 / 1000000000000) (29773348485 / 1000000000000)))) (orderedInterval (-5989777341 / 1000000000000) (-5989765376 / 1000000000000))) = true
  rfl'

theorem compactCertificate291_chunkChecks2 :
    compactCertificate291.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate291.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate291_chunkChecks2_0
    compactCertificate291_chunkChecks2_1 compactCertificate291_chunkChecks2_2

theorem compactCertificate291_chunkChecks3_0 :
    compactCertificate291.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (331 / 2) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13520802502 / 1000000000000) (13520802611 / 1000000000000), orderedInterval (-60570583972 / 1000000000000) (-60570583863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (487626203755231 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12141125446 / 1000000000000) (-12141125445 / 1000000000000), orderedInterval (-71188041153 / 1000000000000) (-71188041152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (157688295381823 / 800000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1432211225 / 1000000000000) (1432211229 / 1000000000000), orderedInterval (-56816678354 / 1000000000000) (-56816678350 / 1000000000000)))) (orderedInterval (29936416197 / 1000000000000) (29936416259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (142288110098717 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-130382030293 / 1000000000000) (-130382029808 / 1000000000000), orderedInterval (31758486088 / 1000000000000) (31758486573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (382205878203449 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (70956963216 / 1000000000000) (70956979332 / 1000000000000), orderedInterval (-40715399276 / 1000000000000) (-40715383160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1037763308954133 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24890045050 / 1000000000000) (24890047788 / 1000000000000), orderedInterval (-42876730700 / 1000000000000) (-42876727963 / 1000000000000)))) (orderedInterval (-11473049847 / 1000000000000) (-11473048933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (764411756407229 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14309186608 / 1000000000000) (-14309186607 / 1000000000000), orderedInterval (-55878119578 / 1000000000000) (-55878119577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1309832573584817 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44029663303 / 1000000000000) (44029663384 / 1000000000000), orderedInterval (2280563578 / 1000000000000) (2280563659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (964816745334803 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4434866799 / 1000000000000) (-4434866798 / 1000000000000), orderedInterval (-51173589034 / 1000000000000) (-51173589032 / 1000000000000)))) (orderedInterval (4339887057 / 1000000000000) (4339887130 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate291_chunkChecks3_1 :
    compactCertificate291.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1480277001104669 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6049518546 / 1000000000000) (6049518547 / 1000000000000), orderedInterval (41024457887 / 1000000000000) (41024457888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (854638325062901 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39764288089 / 1000000000000) (39764288090 / 1000000000000), orderedInterval (37302124279 / 1000000000000) (37302124280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1516570705294009 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8340187821 / 1000000000000) (8340187839 / 1000000000000), orderedInterval (-40130146868 / 1000000000000) (-40130146850 / 1000000000000)))) (orderedInterval (144174090578 / 1000000000000) (144174091250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1416977077263421 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1243817541 / 1000000000000) (-1243817540 / 1000000000000), orderedInterval (-42372476948 / 1000000000000) (-42372476947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1011221703353293 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38634652520 / 1000000000000) (38634736581 / 1000000000000), orderedInterval (-32101125742 / 1000000000000) (-32101041680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1146617634610347 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000)))) (orderedInterval (3356040349 / 1000000000000) (3356068886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (955930242840443 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (43608000986 / 1000000000000) (43608000987 / 1000000000000), orderedInterval (27517008561 / 1000000000000) (27517008562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (844593360005303 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54485227100 / 1000000000000) (-54485227088 / 1000000000000), orderedInterval (-6681815358 / 1000000000000) (-6681815346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (244796075336997 / 800000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40566922570 / 1000000000000) (-40566893263 / 1000000000000), orderedInterval (20918476571 / 1000000000000) (20918505879 / 1000000000000)))) (orderedInterval (-5120353023 / 1000000000000) (-5120348210 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate291_chunkChecks3_2 :
    compactCertificate291.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (677118827293759 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24914176949 / 1000000000000) (24914176950 / 1000000000000), orderedInterval (55962573056 / 1000000000000) (55962573057 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (574001128782599 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-15084277095 / 1000000000000) (-15084276951 / 1000000000000), orderedInterval (64928244521 / 1000000000000) (64928244665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (359183254665197 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42301362744 / 1000000000000) (42301369510 / 1000000000000), orderedInterval (-73038603539 / 1000000000000) (-73038596773 / 1000000000000)))) (orderedInterval (12330709147 / 1000000000000) (12330709224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (193169948948499 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-106596120509 / 1000000000000) (-106596117341 / 1000000000000), orderedInterval (43757256721 / 1000000000000) (43757259889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (524493988302497 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2713251809 / 1000000000000) (-2713251800 / 1000000000000), orderedInterval (69636413893 / 1000000000000) (69636413902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (716151700656769 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40726677933 / 1000000000000) (-40726677932 / 1000000000000), orderedInterval (-43442207840 / 1000000000000) (-43442207839 / 1000000000000)))) (orderedInterval (-3385794659 / 1000000000000) (-3385794639 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (302816745334803 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (81292508299 / 1000000000000) (81292508300 / 1000000000000), orderedInterval (41898131092 / 1000000000000) (41898131093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1230933257902963 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27243609782 / 1000000000000) (27243609783 / 1000000000000), orderedInterval (36377226778 / 1000000000000) (36377226779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (822206369829917 / 4000000000000) 3 (IntervalRat.scale (331 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-47090161501 / 1000000000000) (-47090120693 / 1000000000000), orderedInterval (29773307677 / 1000000000000) (29773348485 / 1000000000000)))) (orderedInterval (29750940857 / 1000000000000) (29750955745 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate291_chunkChecks3 :
    compactCertificate291.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate291.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate291_chunkChecks3_0
    compactCertificate291_chunkChecks3_1 compactCertificate291_chunkChecks3_2

theorem compactCertificate291_chunkChecks4_0 :
    compactCertificate291.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (331 / 2) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13520802502 / 1000000000000) (13520802611 / 1000000000000), orderedInterval (-60570583972 / 1000000000000) (-60570583863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (487626203755231 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-12141125446 / 1000000000000) (-12141125445 / 1000000000000), orderedInterval (-71188041153 / 1000000000000) (-71188041152 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (157688295381823 / 800000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (1432211225 / 1000000000000) (1432211229 / 1000000000000), orderedInterval (-56816678354 / 1000000000000) (-56816678350 / 1000000000000)))) (orderedInterval (5133016938 / 1000000000000) (5133017003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (142288110098717 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-130382030293 / 1000000000000) (-130382029808 / 1000000000000), orderedInterval (31758486088 / 1000000000000) (31758486573 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (382205878203449 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (70956963216 / 1000000000000) (70956979332 / 1000000000000), orderedInterval (-40715399276 / 1000000000000) (-40715383160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1037763308954133 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24890045050 / 1000000000000) (24890047788 / 1000000000000), orderedInterval (-42876730700 / 1000000000000) (-42876727963 / 1000000000000)))) (orderedInterval (-10255811178 / 1000000000000) (-10255809854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (764411756407229 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14309186608 / 1000000000000) (-14309186607 / 1000000000000), orderedInterval (-55878119578 / 1000000000000) (-55878119577 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1309832573584817 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (44029663303 / 1000000000000) (44029663384 / 1000000000000), orderedInterval (2280563578 / 1000000000000) (2280563659 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (964816745334803 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-4434866799 / 1000000000000) (-4434866798 / 1000000000000), orderedInterval (-51173589034 / 1000000000000) (-51173589032 / 1000000000000)))) (orderedInterval (-21349426231 / 1000000000000) (-21349426095 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate291_chunkChecks4_1 :
    compactCertificate291.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1480277001104669 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (6049518546 / 1000000000000) (6049518547 / 1000000000000), orderedInterval (41024457887 / 1000000000000) (41024457888 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (854638325062901 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39764288089 / 1000000000000) (39764288090 / 1000000000000), orderedInterval (37302124279 / 1000000000000) (37302124280 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1516570705294009 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8340187821 / 1000000000000) (8340187839 / 1000000000000), orderedInterval (-40130146868 / 1000000000000) (-40130146850 / 1000000000000)))) (orderedInterval (12223991715 / 1000000000000) (12223993209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1416977077263421 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1243817541 / 1000000000000) (-1243817540 / 1000000000000), orderedInterval (-42372476948 / 1000000000000) (-42372476947 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1011221703353293 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (38634652520 / 1000000000000) (38634736581 / 1000000000000), orderedInterval (-32101125742 / 1000000000000) (-32101041680 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1146617634610347 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-47119678424 / 1000000000000) (-47119678322 / 1000000000000), orderedInterval (-688620149 / 1000000000000) (-688620048 / 1000000000000)))) (orderedInterval (22467262649 / 1000000000000) (22467306429 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (955930242840443 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (43608000986 / 1000000000000) (43608000987 / 1000000000000), orderedInterval (27517008561 / 1000000000000) (27517008562 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (844593360005303 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54485227100 / 1000000000000) (-54485227088 / 1000000000000), orderedInterval (-6681815358 / 1000000000000) (-6681815346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (244796075336997 / 800000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-40566922570 / 1000000000000) (-40566893263 / 1000000000000), orderedInterval (20918476571 / 1000000000000) (20918505879 / 1000000000000)))) (orderedInterval (-1625649312 / 1000000000000) (-1625640400 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate291_chunkChecks4_2 :
    compactCertificate291.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (677118827293759 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24914176949 / 1000000000000) (24914176950 / 1000000000000), orderedInterval (55962573056 / 1000000000000) (55962573057 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (574001128782599 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-15084277095 / 1000000000000) (-15084276951 / 1000000000000), orderedInterval (64928244521 / 1000000000000) (64928244665 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (359183254665197 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (42301362744 / 1000000000000) (42301369510 / 1000000000000), orderedInterval (-73038603539 / 1000000000000) (-73038596773 / 1000000000000)))) (orderedInterval (-3907132932 / 1000000000000) (-3907132872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (193169948948499 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-106596120509 / 1000000000000) (-106596117341 / 1000000000000), orderedInterval (43757256721 / 1000000000000) (43757259889 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (524493988302497 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2713251809 / 1000000000000) (-2713251800 / 1000000000000), orderedInterval (69636413893 / 1000000000000) (69636413902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (716151700656769 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-40726677933 / 1000000000000) (-40726677932 / 1000000000000), orderedInterval (-43442207840 / 1000000000000) (-43442207839 / 1000000000000)))) (orderedInterval (4354102845 / 1000000000000) (4354102865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (302816745334803 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (81292508299 / 1000000000000) (81292508300 / 1000000000000), orderedInterval (41898131092 / 1000000000000) (41898131093 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1230933257902963 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27243609782 / 1000000000000) (27243609783 / 1000000000000), orderedInterval (36377226778 / 1000000000000) (36377226779 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (822206369829917 / 4000000000000) 4 (IntervalRat.scale (331 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-47090161501 / 1000000000000) (-47090120693 / 1000000000000), orderedInterval (29773307677 / 1000000000000) (29773348485 / 1000000000000)))) (orderedInterval (-5823971904 / 1000000000000) (-5823953272 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate291_chunkChecks4 :
    compactCertificate291.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate291.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate291_chunkChecks4_0
    compactCertificate291_chunkChecks4_1 compactCertificate291_chunkChecks4_2

theorem compactCertificate291_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate291.chunkCheck r b = true :=
  compactCertificate291.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate291_chunkChecks0
    · exact compactCertificate291_chunkChecks1
    · exact compactCertificate291_chunkChecks2
    · exact compactCertificate291_chunkChecks3
    · exact compactCertificate291_chunkChecks4)

theorem compactCertificate291_coefficient0 :
    compactCertificate291.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate291_coefficient1 :
    compactCertificate291.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate291_coefficient2 :
    compactCertificate291.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate291_coefficient3 :
    compactCertificate291.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate291_coefficient4 :
    compactCertificate291.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate291_coefficients : ∀ r : Fin 5,
    compactCertificate291.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate291_coefficient0
  · exact compactCertificate291_coefficient1
  · exact compactCertificate291_coefficient2
  · exact compactCertificate291_coefficient3
  · exact compactCertificate291_coefficient4

theorem compactCertificate291_lower : (1 : ℚ) ≤ compactCertificate291.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate291, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate291_proves {t : ℝ} (ht : t ∈ compactCertificate291.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate291.proves compactCertificate291_states compactCertificate291_chunks
    compactCertificate291_coefficients compactCertificate291_lower ht

end Erdos232
