/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate314 : CompactCertificate where
  left := 187
  right := 188
  center := 375 / 2
  grid := fun i =>
    match i.val with
    | 0 => 60
    | 1 => 44
    | 2 => 71
    | 3 => 13
    | 4 => 34
    | 5 => 94
    | 6 => 69
    | 7 => 118
    | 8 => 87
    | 9 => 134
    | 10 => 77
    | 11 => 137
    | 12 => 128
    | 13 => 91
    | 14 => 103
    | 15 => 86
    | 16 => 76
    | 17 => 110
    | 18 => 61
    | 19 => 52
    | 20 => 32
    | 21 => 17
    | 22 => 47
    | 23 => 65
    | 24 => 27
    | 25 => 111
    | _ => 74
  point := fun i =>
    match i.val with
    | 0 => 375 / 2
    | 1 => 4419572843703 / 32000000000
    | 2 => 1429199051799 / 6400000000
    | 3 => 1289620333221 / 32000000000
    | 4 => 3464101615137 / 32000000000
    | 5 => 9405709748829 / 32000000000
    | 6 => 6928203230277 / 32000000000
    | 7 => 11871594322521 / 32000000000
    | 8 => 8744562646539 / 32000000000
    | 9 => 13416407864997 / 32000000000
    | 10 => 7745966692413 / 32000000000
    | 11 => 13745353824417 / 32000000000
    | 12 => 12842692543173 / 32000000000
    | 13 => 9165151389909 / 32000000000
    | 14 => 10392304845411 / 32000000000
    | 15 => 8664020327859 / 32000000000
    | 16 => 7654924713039 / 32000000000
    | 17 => 2218695546861 / 6400000000
    | 18 => 6137028646167 / 32000000000
    | 19 => 5202427149087 / 32000000000
    | 20 => 3255437353461 / 32000000000
    | 21 => 1750785035787 / 32000000000
    | 22 => 4753721948361 / 32000000000
    | 23 => 6490800912297 / 32000000000
    | 24 => 2744562646539 / 32000000000
    | 25 => 11156494784619 / 32000000000
    | _ => 7452021478821 / 32000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-12193946540 / 1000000000000) (-12193946457 / 1000000000000), orderedInterval (57011672190 / 1000000000000) (57011672273 / 1000000000000))
    | 1 => (orderedInterval (41950869753 / 1000000000000) (41950869754 / 1000000000000), orderedInterval (53229671273 / 1000000000000) (53229671274 / 1000000000000))
    | 2 => (orderedInterval (-46156971776 / 1000000000000) (-46156971775 / 1000000000000), orderedInterval (-26735703107 / 1000000000000) (-26735703106 / 1000000000000))
    | 3 => (orderedInterval (-30146514422 / 1000000000000) (-30146514421 / 1000000000000), orderedInterval (-121646650682 / 1000000000000) (-121646650681 / 1000000000000))
    | 4 => (orderedInterval (60933708369 / 1000000000000) (60933767280 / 1000000000000), orderedInterval (-46842223908 / 1000000000000) (-46842164997 / 1000000000000))
    | 5 => (orderedInterval (-26135980740 / 1000000000000) (-26135975923 / 1000000000000), orderedInterval (38551760679 / 1000000000000) (38551765496 / 1000000000000))
    | 6 => (orderedInterval (-27003760463 / 1000000000000) (-27003760462 / 1000000000000), orderedInterval (-46961266437 / 1000000000000) (-46961266436 / 1000000000000))
    | 7 => (orderedInterval (36226918267 / 1000000000000) (36226918268 / 1000000000000), orderedInterval (20041582370 / 1000000000000) (20041582371 / 1000000000000))
    | 8 => (orderedInterval (-32329719738 / 1000000000000) (-32329719737 / 1000000000000), orderedInterval (-35780025244 / 1000000000000) (-35780025243 / 1000000000000))
    | 9 => (orderedInterval (-31133227505 / 1000000000000) (-31133166467 / 1000000000000), orderedInterval (23471056521 / 1000000000000) (23471117559 / 1000000000000))
    | 10 => (orderedInterval (-41526147447 / 1000000000000) (-41526147446 / 1000000000000), orderedInterval (-30006908255 / 1000000000000) (-30006908254 / 1000000000000))
    | 11 => (orderedInterval (2722582008 / 1000000000000) (2722582010 / 1000000000000), orderedInterval (-38404694892 / 1000000000000) (-38404694890 / 1000000000000))
    | 12 => (orderedInterval (-184441392 / 1000000000000) (-184441391 / 1000000000000), orderedInterval (39827681467 / 1000000000000) (39827681468 / 1000000000000))
    | 13 => (orderedInterval (-45564029916 / 1000000000000) (-45564029913 / 1000000000000), orderedInterval (-12031006920 / 1000000000000) (-12031006917 / 1000000000000))
    | 14 => (orderedInterval (-40955429781 / 1000000000000) (-40955415421 / 1000000000000), orderedInterval (16883636172 / 1000000000000) (16883650532 / 1000000000000))
    | 15 => (orderedInterval (47402741512 / 1000000000000) (47402741517 / 1000000000000), orderedInterval (10124732452 / 1000000000000) (10124732457 / 1000000000000))
    | 16 => (orderedInterval (48794463983 / 1000000000000) (48794463985 / 1000000000000), orderedInterval (16642180337 / 1000000000000) (16642180339 / 1000000000000))
    | 17 => (orderedInterval (40807332840 / 1000000000000) (40807340110 / 1000000000000), orderedInterval (-13140870380 / 1000000000000) (-13140863110 / 1000000000000))
    | 18 => (orderedInterval (-46176331070 / 1000000000000) (-46176331069 / 1000000000000), orderedInterval (-34335929435 / 1000000000000) (-34335929434 / 1000000000000))
    | 19 => (orderedInterval (-146445756 / 1000000000000) (-146445751 / 1000000000000), orderedInterval (62577039119 / 1000000000000) (62577039123 / 1000000000000))
    | 20 => (orderedInterval (72396472930 / 1000000000000) (72396478922 / 1000000000000), orderedInterval (-32238189561 / 1000000000000) (-32238183569 / 1000000000000))
    | 21 => (orderedInterval (-93754982700 / 1000000000000) (-93754969350 / 1000000000000), orderedInterval (54200739144 / 1000000000000) (54200752494 / 1000000000000))
    | 22 => (orderedInterval (-65047739727 / 1000000000000) (-65047739498 / 1000000000000), orderedInterval (7582143878 / 1000000000000) (7582144106 / 1000000000000))
    | 23 => (orderedInterval (30758638530 / 1000000000000) (30758645178 / 1000000000000), orderedInterval (-46899745752 / 1000000000000) (-46899739104 / 1000000000000))
    | 24 => (orderedInterval (-85084449071 / 1000000000000) (-85084448797 / 1000000000000), orderedInterval (14028626948 / 1000000000000) (14028627222 / 1000000000000))
    | 25 => (orderedInterval (-27812417993 / 1000000000000) (-27812417992 / 1000000000000), orderedInterval (-32402003585 / 1000000000000) (-32402003584 / 1000000000000))
    | _ => (orderedInterval (48396197423 / 1000000000000) (48396197424 / 1000000000000), orderedInterval (19683359153 / 1000000000000) (19683359155 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-7150896543 / 1000000000000) (-7150896496 / 1000000000000)
      | 1 => orderedInterval (4409861524 / 1000000000000) (4409864041 / 1000000000000)
      | 2 => orderedInterval (-1898728648 / 1000000000000) (-1898728637 / 1000000000000)
      | 3 => orderedInterval (2842273009 / 1000000000000) (2842283930 / 1000000000000)
      | 4 => orderedInterval (-4098077538 / 1000000000000) (-4098077442 / 1000000000000)
      | 5 => orderedInterval (-1200124913 / 1000000000000) (-1200124708 / 1000000000000)
      | 6 => orderedInterval (9748421932 / 1000000000000) (9748422175 / 1000000000000)
      | 7 => orderedInterval (849617747 / 1000000000000) (849618531 / 1000000000000)
      | _ => orderedInterval (-7329347188 / 1000000000000) (-7329347134 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (21094243715 / 1000000000000) (21094243763 / 1000000000000)
      | 1 => orderedInterval (-5000031585 / 1000000000000) (-5000029780 / 1000000000000)
      | 2 => orderedInterval (-2483380674 / 1000000000000) (-2483380655 / 1000000000000)
      | 3 => orderedInterval (-24702841164 / 1000000000000) (-24702816757 / 1000000000000)
      | 4 => orderedInterval (-3424842531 / 1000000000000) (-3424842367 / 1000000000000)
      | 5 => orderedInterval (-1668315235 / 1000000000000) (-1668314864 / 1000000000000)
      | 6 => orderedInterval (1974952594 / 1000000000000) (1974952744 / 1000000000000)
      | 7 => orderedInterval (3460037786 / 1000000000000) (3460038434 / 1000000000000)
      | _ => orderedInterval (356174701 / 1000000000000) (356174776 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (8350671435 / 1000000000000) (8350671486 / 1000000000000)
      | 1 => orderedInterval (-5295935831 / 1000000000000) (-5295934227 / 1000000000000)
      | 2 => orderedInterval (6047287829 / 1000000000000) (6047287862 / 1000000000000)
      | 3 => orderedInterval (-24431546920 / 1000000000000) (-24431492230 / 1000000000000)
      | 4 => orderedInterval (9434788606 / 1000000000000) (9434788886 / 1000000000000)
      | 5 => orderedInterval (-159067116 / 1000000000000) (-159066438 / 1000000000000)
      | 6 => orderedInterval (-8434933764 / 1000000000000) (-8434933663 / 1000000000000)
      | 7 => orderedInterval (1666536492 / 1000000000000) (1666537137 / 1000000000000)
      | _ => orderedInterval (6285071187 / 1000000000000) (6285071297 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-20189116394 / 1000000000000) (-20189116341 / 1000000000000)
      | 1 => orderedInterval (10901896351 / 1000000000000) (10901898146 / 1000000000000)
      | 2 => orderedInterval (7432882309 / 1000000000000) (7432882369 / 1000000000000)
      | 3 => orderedInterval (117180360040 / 1000000000000) (117180482314 / 1000000000000)
      | 4 => orderedInterval (11499523319 / 1000000000000) (11499523801 / 1000000000000)
      | 5 => orderedInterval (3753120403 / 1000000000000) (3753121643 / 1000000000000)
      | 6 => orderedInterval (-3353332740 / 1000000000000) (-3353332667 / 1000000000000)
      | 7 => orderedInterval (-4448891716 / 1000000000000) (-4448891037 / 1000000000000)
      | _ => orderedInterval (-9922489679 / 1000000000000) (-9922489511 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9952407999 / 1000000000000) (-9952407942 / 1000000000000)
      | 1 => orderedInterval (11351808897 / 1000000000000) (11351811305 / 1000000000000)
      | 2 => orderedInterval (-20729473293 / 1000000000000) (-20729473182 / 1000000000000)
      | 3 => orderedInterval (139162740977 / 1000000000000) (139163015024 / 1000000000000)
      | 4 => orderedInterval (-21645467194 / 1000000000000) (-21645466357 / 1000000000000)
      | 5 => orderedInterval (7151568985 / 1000000000000) (7151571268 / 1000000000000)
      | 6 => orderedInterval (8325651229 / 1000000000000) (8325651287 / 1000000000000)
      | 7 => orderedInterval (-2586992021 / 1000000000000) (-2586991291 / 1000000000000)
      | _ => orderedInterval (5539615130 / 1000000000000) (5539615399 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3827000618 / 1000000000000) (-3826985740 / 1000000000000)
    | 1 => orderedInterval (-10394002393 / 1000000000000) (-10393974706 / 1000000000000)
    | 2 => orderedInterval (-6537128082 / 1000000000000) (-6537069890 / 1000000000000)
    | 3 => orderedInterval (112853951893 / 1000000000000) (112854078717 / 1000000000000)
    | _ => orderedInterval (116617044711 / 1000000000000) (116617325511 / 1000000000000)

theorem compactCertificate314_stateChecks0 :
    compactCertificate314.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (375 / 2)) (orderedInterval (-12193946540 / 1000000000000) (-12193946457 / 1000000000000), orderedInterval (57011672190 / 1000000000000) (57011672273 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (4419572843703 / 32000000000)) (orderedInterval (41950869753 / 1000000000000) (41950869754 / 1000000000000), orderedInterval (53229671273 / 1000000000000) (53229671274 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (1429199051799 / 6400000000)) (orderedInterval (-46156971776 / 1000000000000) (-46156971775 / 1000000000000), orderedInterval (-26735703107 / 1000000000000) (-26735703106 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_stateChecks1 :
    compactCertificate314.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (1289620333221 / 32000000000)) (orderedInterval (-30146514422 / 1000000000000) (-30146514421 / 1000000000000), orderedInterval (-121646650682 / 1000000000000) (-121646650681 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (3464101615137 / 32000000000)) (orderedInterval (60933708369 / 1000000000000) (60933767280 / 1000000000000), orderedInterval (-46842223908 / 1000000000000) (-46842164997 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (9405709748829 / 32000000000)) (orderedInterval (-26135980740 / 1000000000000) (-26135975923 / 1000000000000), orderedInterval (38551760679 / 1000000000000) (38551765496 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_stateChecks2 :
    compactCertificate314.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (6928203230277 / 32000000000)) (orderedInterval (-27003760463 / 1000000000000) (-27003760462 / 1000000000000), orderedInterval (-46961266437 / 1000000000000) (-46961266436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (11871594322521 / 32000000000)) (orderedInterval (36226918267 / 1000000000000) (36226918268 / 1000000000000), orderedInterval (20041582370 / 1000000000000) (20041582371 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (8744562646539 / 32000000000)) (orderedInterval (-32329719738 / 1000000000000) (-32329719737 / 1000000000000), orderedInterval (-35780025244 / 1000000000000) (-35780025243 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_stateChecks3 :
    compactCertificate314.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (13416407864997 / 32000000000)) (orderedInterval (-31133227505 / 1000000000000) (-31133166467 / 1000000000000), orderedInterval (23471056521 / 1000000000000) (23471117559 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (7745966692413 / 32000000000)) (orderedInterval (-41526147447 / 1000000000000) (-41526147446 / 1000000000000), orderedInterval (-30006908255 / 1000000000000) (-30006908254 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (13745353824417 / 32000000000)) (orderedInterval (2722582008 / 1000000000000) (2722582010 / 1000000000000), orderedInterval (-38404694892 / 1000000000000) (-38404694890 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_stateChecks4 :
    compactCertificate314.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (12842692543173 / 32000000000)) (orderedInterval (-184441392 / 1000000000000) (-184441391 / 1000000000000), orderedInterval (39827681467 / 1000000000000) (39827681468 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (9165151389909 / 32000000000)) (orderedInterval (-45564029916 / 1000000000000) (-45564029913 / 1000000000000), orderedInterval (-12031006920 / 1000000000000) (-12031006917 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (10392304845411 / 32000000000)) (orderedInterval (-40955429781 / 1000000000000) (-40955415421 / 1000000000000), orderedInterval (16883636172 / 1000000000000) (16883650532 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_stateChecks5 :
    compactCertificate314.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (8664020327859 / 32000000000)) (orderedInterval (47402741512 / 1000000000000) (47402741517 / 1000000000000), orderedInterval (10124732452 / 1000000000000) (10124732457 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (7654924713039 / 32000000000)) (orderedInterval (48794463983 / 1000000000000) (48794463985 / 1000000000000), orderedInterval (16642180337 / 1000000000000) (16642180339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (2218695546861 / 6400000000)) (orderedInterval (40807332840 / 1000000000000) (40807340110 / 1000000000000), orderedInterval (-13140870380 / 1000000000000) (-13140863110 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_stateChecks6 :
    compactCertificate314.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (6137028646167 / 32000000000)) (orderedInterval (-46176331070 / 1000000000000) (-46176331069 / 1000000000000), orderedInterval (-34335929435 / 1000000000000) (-34335929434 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (5202427149087 / 32000000000)) (orderedInterval (-146445756 / 1000000000000) (-146445751 / 1000000000000), orderedInterval (62577039119 / 1000000000000) (62577039123 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (3255437353461 / 32000000000)) (orderedInterval (72396472930 / 1000000000000) (72396478922 / 1000000000000), orderedInterval (-32238189561 / 1000000000000) (-32238183569 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_stateChecks7 :
    compactCertificate314.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (1750785035787 / 32000000000)) (orderedInterval (-93754982700 / 1000000000000) (-93754969350 / 1000000000000), orderedInterval (54200739144 / 1000000000000) (54200752494 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (4753721948361 / 32000000000)) (orderedInterval (-65047739727 / 1000000000000) (-65047739498 / 1000000000000), orderedInterval (7582143878 / 1000000000000) (7582144106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (6490800912297 / 32000000000)) (orderedInterval (30758638530 / 1000000000000) (30758645178 / 1000000000000), orderedInterval (-46899745752 / 1000000000000) (-46899739104 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_stateChecks8 :
    compactCertificate314.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (2744562646539 / 32000000000)) (orderedInterval (-85084449071 / 1000000000000) (-85084448797 / 1000000000000), orderedInterval (14028626948 / 1000000000000) (14028627222 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (11156494784619 / 32000000000)) (orderedInterval (-27812417993 / 1000000000000) (-27812417992 / 1000000000000), orderedInterval (-32402003585 / 1000000000000) (-32402003584 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (7452021478821 / 32000000000)) (orderedInterval (48396197423 / 1000000000000) (48396197424 / 1000000000000), orderedInterval (19683359153 / 1000000000000) (19683359155 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_states : ∀ j,
    BesselStateValid (compactCertificate314.point j) (compactCertificate314.state j) :=
  compactCertificate314.statesValid_of_checks3 compactCertificate314_stateChecks0
    compactCertificate314_stateChecks1 compactCertificate314_stateChecks2
    compactCertificate314_stateChecks3 compactCertificate314_stateChecks4
    compactCertificate314_stateChecks5 compactCertificate314_stateChecks6
    compactCertificate314_stateChecks7 compactCertificate314_stateChecks8

theorem compactCertificate314_chunkChecks0_0 :
    compactCertificate314.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (375 / 2) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12193946540 / 1000000000000) (-12193946457 / 1000000000000), orderedInterval (57011672190 / 1000000000000) (57011672273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (4419572843703 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41950869753 / 1000000000000) (41950869754 / 1000000000000), orderedInterval (53229671273 / 1000000000000) (53229671274 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (1429199051799 / 6400000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-46156971776 / 1000000000000) (-46156971775 / 1000000000000), orderedInterval (-26735703107 / 1000000000000) (-26735703106 / 1000000000000)))) (orderedInterval (-7150896543 / 1000000000000) (-7150896496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (1289620333221 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-30146514422 / 1000000000000) (-30146514421 / 1000000000000), orderedInterval (-121646650682 / 1000000000000) (-121646650681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (3464101615137 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (60933708369 / 1000000000000) (60933767280 / 1000000000000), orderedInterval (-46842223908 / 1000000000000) (-46842164997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (9405709748829 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26135980740 / 1000000000000) (-26135975923 / 1000000000000), orderedInterval (38551760679 / 1000000000000) (38551765496 / 1000000000000)))) (orderedInterval (4409861524 / 1000000000000) (4409864041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (6928203230277 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-27003760463 / 1000000000000) (-27003760462 / 1000000000000), orderedInterval (-46961266437 / 1000000000000) (-46961266436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (11871594322521 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36226918267 / 1000000000000) (36226918268 / 1000000000000), orderedInterval (20041582370 / 1000000000000) (20041582371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (8744562646539 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32329719738 / 1000000000000) (-32329719737 / 1000000000000), orderedInterval (-35780025244 / 1000000000000) (-35780025243 / 1000000000000)))) (orderedInterval (-1898728648 / 1000000000000) (-1898728637 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_chunkChecks0_1 :
    compactCertificate314.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (13416407864997 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31133227505 / 1000000000000) (-31133166467 / 1000000000000), orderedInterval (23471056521 / 1000000000000) (23471117559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (7745966692413 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41526147447 / 1000000000000) (-41526147446 / 1000000000000), orderedInterval (-30006908255 / 1000000000000) (-30006908254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (13745353824417 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2722582008 / 1000000000000) (2722582010 / 1000000000000), orderedInterval (-38404694892 / 1000000000000) (-38404694890 / 1000000000000)))) (orderedInterval (2842273009 / 1000000000000) (2842283930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (12842692543173 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-184441392 / 1000000000000) (-184441391 / 1000000000000), orderedInterval (39827681467 / 1000000000000) (39827681468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (9165151389909 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-45564029916 / 1000000000000) (-45564029913 / 1000000000000), orderedInterval (-12031006920 / 1000000000000) (-12031006917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (10392304845411 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40955429781 / 1000000000000) (-40955415421 / 1000000000000), orderedInterval (16883636172 / 1000000000000) (16883650532 / 1000000000000)))) (orderedInterval (-4098077538 / 1000000000000) (-4098077442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (8664020327859 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47402741512 / 1000000000000) (47402741517 / 1000000000000), orderedInterval (10124732452 / 1000000000000) (10124732457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (7654924713039 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (48794463983 / 1000000000000) (48794463985 / 1000000000000), orderedInterval (16642180337 / 1000000000000) (16642180339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (2218695546861 / 6400000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40807332840 / 1000000000000) (40807340110 / 1000000000000), orderedInterval (-13140870380 / 1000000000000) (-13140863110 / 1000000000000)))) (orderedInterval (-1200124913 / 1000000000000) (-1200124708 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_chunkChecks0_2 :
    compactCertificate314.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (6137028646167 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46176331070 / 1000000000000) (-46176331069 / 1000000000000), orderedInterval (-34335929435 / 1000000000000) (-34335929434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (5202427149087 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-146445756 / 1000000000000) (-146445751 / 1000000000000), orderedInterval (62577039119 / 1000000000000) (62577039123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (3255437353461 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72396472930 / 1000000000000) (72396478922 / 1000000000000), orderedInterval (-32238189561 / 1000000000000) (-32238183569 / 1000000000000)))) (orderedInterval (9748421932 / 1000000000000) (9748422175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (1750785035787 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-93754982700 / 1000000000000) (-93754969350 / 1000000000000), orderedInterval (54200739144 / 1000000000000) (54200752494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (4753721948361 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-65047739727 / 1000000000000) (-65047739498 / 1000000000000), orderedInterval (7582143878 / 1000000000000) (7582144106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (6490800912297 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30758638530 / 1000000000000) (30758645178 / 1000000000000), orderedInterval (-46899745752 / 1000000000000) (-46899739104 / 1000000000000)))) (orderedInterval (849617747 / 1000000000000) (849618531 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (2744562646539 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-85084449071 / 1000000000000) (-85084448797 / 1000000000000), orderedInterval (14028626948 / 1000000000000) (14028627222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (11156494784619 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27812417993 / 1000000000000) (-27812417992 / 1000000000000), orderedInterval (-32402003585 / 1000000000000) (-32402003584 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (7452021478821 / 32000000000) 0 (IntervalRat.scale (375 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48396197423 / 1000000000000) (48396197424 / 1000000000000), orderedInterval (19683359153 / 1000000000000) (19683359155 / 1000000000000)))) (orderedInterval (-7329347188 / 1000000000000) (-7329347134 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_chunkChecks0 :
    compactCertificate314.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate314.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate314_chunkChecks0_0
    compactCertificate314_chunkChecks0_1 compactCertificate314_chunkChecks0_2

theorem compactCertificate314_chunkChecks1_0 :
    compactCertificate314.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (375 / 2) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12193946540 / 1000000000000) (-12193946457 / 1000000000000), orderedInterval (57011672190 / 1000000000000) (57011672273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (4419572843703 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41950869753 / 1000000000000) (41950869754 / 1000000000000), orderedInterval (53229671273 / 1000000000000) (53229671274 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (1429199051799 / 6400000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-46156971776 / 1000000000000) (-46156971775 / 1000000000000), orderedInterval (-26735703107 / 1000000000000) (-26735703106 / 1000000000000)))) (orderedInterval (21094243715 / 1000000000000) (21094243763 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (1289620333221 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-30146514422 / 1000000000000) (-30146514421 / 1000000000000), orderedInterval (-121646650682 / 1000000000000) (-121646650681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (3464101615137 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (60933708369 / 1000000000000) (60933767280 / 1000000000000), orderedInterval (-46842223908 / 1000000000000) (-46842164997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (9405709748829 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26135980740 / 1000000000000) (-26135975923 / 1000000000000), orderedInterval (38551760679 / 1000000000000) (38551765496 / 1000000000000)))) (orderedInterval (-5000031585 / 1000000000000) (-5000029780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (6928203230277 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-27003760463 / 1000000000000) (-27003760462 / 1000000000000), orderedInterval (-46961266437 / 1000000000000) (-46961266436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (11871594322521 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36226918267 / 1000000000000) (36226918268 / 1000000000000), orderedInterval (20041582370 / 1000000000000) (20041582371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (8744562646539 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32329719738 / 1000000000000) (-32329719737 / 1000000000000), orderedInterval (-35780025244 / 1000000000000) (-35780025243 / 1000000000000)))) (orderedInterval (-2483380674 / 1000000000000) (-2483380655 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_chunkChecks1_1 :
    compactCertificate314.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (13416407864997 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31133227505 / 1000000000000) (-31133166467 / 1000000000000), orderedInterval (23471056521 / 1000000000000) (23471117559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (7745966692413 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41526147447 / 1000000000000) (-41526147446 / 1000000000000), orderedInterval (-30006908255 / 1000000000000) (-30006908254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (13745353824417 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2722582008 / 1000000000000) (2722582010 / 1000000000000), orderedInterval (-38404694892 / 1000000000000) (-38404694890 / 1000000000000)))) (orderedInterval (-24702841164 / 1000000000000) (-24702816757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (12842692543173 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-184441392 / 1000000000000) (-184441391 / 1000000000000), orderedInterval (39827681467 / 1000000000000) (39827681468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (9165151389909 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-45564029916 / 1000000000000) (-45564029913 / 1000000000000), orderedInterval (-12031006920 / 1000000000000) (-12031006917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (10392304845411 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40955429781 / 1000000000000) (-40955415421 / 1000000000000), orderedInterval (16883636172 / 1000000000000) (16883650532 / 1000000000000)))) (orderedInterval (-3424842531 / 1000000000000) (-3424842367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (8664020327859 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47402741512 / 1000000000000) (47402741517 / 1000000000000), orderedInterval (10124732452 / 1000000000000) (10124732457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (7654924713039 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (48794463983 / 1000000000000) (48794463985 / 1000000000000), orderedInterval (16642180337 / 1000000000000) (16642180339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (2218695546861 / 6400000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40807332840 / 1000000000000) (40807340110 / 1000000000000), orderedInterval (-13140870380 / 1000000000000) (-13140863110 / 1000000000000)))) (orderedInterval (-1668315235 / 1000000000000) (-1668314864 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_chunkChecks1_2 :
    compactCertificate314.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (6137028646167 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46176331070 / 1000000000000) (-46176331069 / 1000000000000), orderedInterval (-34335929435 / 1000000000000) (-34335929434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (5202427149087 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-146445756 / 1000000000000) (-146445751 / 1000000000000), orderedInterval (62577039119 / 1000000000000) (62577039123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (3255437353461 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72396472930 / 1000000000000) (72396478922 / 1000000000000), orderedInterval (-32238189561 / 1000000000000) (-32238183569 / 1000000000000)))) (orderedInterval (1974952594 / 1000000000000) (1974952744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (1750785035787 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-93754982700 / 1000000000000) (-93754969350 / 1000000000000), orderedInterval (54200739144 / 1000000000000) (54200752494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (4753721948361 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-65047739727 / 1000000000000) (-65047739498 / 1000000000000), orderedInterval (7582143878 / 1000000000000) (7582144106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (6490800912297 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30758638530 / 1000000000000) (30758645178 / 1000000000000), orderedInterval (-46899745752 / 1000000000000) (-46899739104 / 1000000000000)))) (orderedInterval (3460037786 / 1000000000000) (3460038434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (2744562646539 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-85084449071 / 1000000000000) (-85084448797 / 1000000000000), orderedInterval (14028626948 / 1000000000000) (14028627222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (11156494784619 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27812417993 / 1000000000000) (-27812417992 / 1000000000000), orderedInterval (-32402003585 / 1000000000000) (-32402003584 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (7452021478821 / 32000000000) 1 (IntervalRat.scale (375 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48396197423 / 1000000000000) (48396197424 / 1000000000000), orderedInterval (19683359153 / 1000000000000) (19683359155 / 1000000000000)))) (orderedInterval (356174701 / 1000000000000) (356174776 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_chunkChecks1 :
    compactCertificate314.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate314.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate314_chunkChecks1_0
    compactCertificate314_chunkChecks1_1 compactCertificate314_chunkChecks1_2

theorem compactCertificate314_chunkChecks2_0 :
    compactCertificate314.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (375 / 2) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12193946540 / 1000000000000) (-12193946457 / 1000000000000), orderedInterval (57011672190 / 1000000000000) (57011672273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (4419572843703 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41950869753 / 1000000000000) (41950869754 / 1000000000000), orderedInterval (53229671273 / 1000000000000) (53229671274 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (1429199051799 / 6400000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-46156971776 / 1000000000000) (-46156971775 / 1000000000000), orderedInterval (-26735703107 / 1000000000000) (-26735703106 / 1000000000000)))) (orderedInterval (8350671435 / 1000000000000) (8350671486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (1289620333221 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-30146514422 / 1000000000000) (-30146514421 / 1000000000000), orderedInterval (-121646650682 / 1000000000000) (-121646650681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (3464101615137 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (60933708369 / 1000000000000) (60933767280 / 1000000000000), orderedInterval (-46842223908 / 1000000000000) (-46842164997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (9405709748829 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26135980740 / 1000000000000) (-26135975923 / 1000000000000), orderedInterval (38551760679 / 1000000000000) (38551765496 / 1000000000000)))) (orderedInterval (-5295935831 / 1000000000000) (-5295934227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (6928203230277 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-27003760463 / 1000000000000) (-27003760462 / 1000000000000), orderedInterval (-46961266437 / 1000000000000) (-46961266436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (11871594322521 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36226918267 / 1000000000000) (36226918268 / 1000000000000), orderedInterval (20041582370 / 1000000000000) (20041582371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (8744562646539 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32329719738 / 1000000000000) (-32329719737 / 1000000000000), orderedInterval (-35780025244 / 1000000000000) (-35780025243 / 1000000000000)))) (orderedInterval (6047287829 / 1000000000000) (6047287862 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_chunkChecks2_1 :
    compactCertificate314.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (13416407864997 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31133227505 / 1000000000000) (-31133166467 / 1000000000000), orderedInterval (23471056521 / 1000000000000) (23471117559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (7745966692413 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41526147447 / 1000000000000) (-41526147446 / 1000000000000), orderedInterval (-30006908255 / 1000000000000) (-30006908254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (13745353824417 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2722582008 / 1000000000000) (2722582010 / 1000000000000), orderedInterval (-38404694892 / 1000000000000) (-38404694890 / 1000000000000)))) (orderedInterval (-24431546920 / 1000000000000) (-24431492230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (12842692543173 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-184441392 / 1000000000000) (-184441391 / 1000000000000), orderedInterval (39827681467 / 1000000000000) (39827681468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (9165151389909 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-45564029916 / 1000000000000) (-45564029913 / 1000000000000), orderedInterval (-12031006920 / 1000000000000) (-12031006917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (10392304845411 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40955429781 / 1000000000000) (-40955415421 / 1000000000000), orderedInterval (16883636172 / 1000000000000) (16883650532 / 1000000000000)))) (orderedInterval (9434788606 / 1000000000000) (9434788886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (8664020327859 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47402741512 / 1000000000000) (47402741517 / 1000000000000), orderedInterval (10124732452 / 1000000000000) (10124732457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (7654924713039 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (48794463983 / 1000000000000) (48794463985 / 1000000000000), orderedInterval (16642180337 / 1000000000000) (16642180339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (2218695546861 / 6400000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40807332840 / 1000000000000) (40807340110 / 1000000000000), orderedInterval (-13140870380 / 1000000000000) (-13140863110 / 1000000000000)))) (orderedInterval (-159067116 / 1000000000000) (-159066438 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_chunkChecks2_2 :
    compactCertificate314.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (6137028646167 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46176331070 / 1000000000000) (-46176331069 / 1000000000000), orderedInterval (-34335929435 / 1000000000000) (-34335929434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (5202427149087 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-146445756 / 1000000000000) (-146445751 / 1000000000000), orderedInterval (62577039119 / 1000000000000) (62577039123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (3255437353461 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72396472930 / 1000000000000) (72396478922 / 1000000000000), orderedInterval (-32238189561 / 1000000000000) (-32238183569 / 1000000000000)))) (orderedInterval (-8434933764 / 1000000000000) (-8434933663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (1750785035787 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-93754982700 / 1000000000000) (-93754969350 / 1000000000000), orderedInterval (54200739144 / 1000000000000) (54200752494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (4753721948361 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-65047739727 / 1000000000000) (-65047739498 / 1000000000000), orderedInterval (7582143878 / 1000000000000) (7582144106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (6490800912297 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30758638530 / 1000000000000) (30758645178 / 1000000000000), orderedInterval (-46899745752 / 1000000000000) (-46899739104 / 1000000000000)))) (orderedInterval (1666536492 / 1000000000000) (1666537137 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (2744562646539 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-85084449071 / 1000000000000) (-85084448797 / 1000000000000), orderedInterval (14028626948 / 1000000000000) (14028627222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (11156494784619 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27812417993 / 1000000000000) (-27812417992 / 1000000000000), orderedInterval (-32402003585 / 1000000000000) (-32402003584 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (7452021478821 / 32000000000) 2 (IntervalRat.scale (375 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48396197423 / 1000000000000) (48396197424 / 1000000000000), orderedInterval (19683359153 / 1000000000000) (19683359155 / 1000000000000)))) (orderedInterval (6285071187 / 1000000000000) (6285071297 / 1000000000000))) = true
  rfl'

theorem compactCertificate314_chunkChecks2 :
    compactCertificate314.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate314.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate314_chunkChecks2_0
    compactCertificate314_chunkChecks2_1 compactCertificate314_chunkChecks2_2

theorem compactCertificate314_chunkChecks3_0 :
    compactCertificate314.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (375 / 2) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12193946540 / 1000000000000) (-12193946457 / 1000000000000), orderedInterval (57011672190 / 1000000000000) (57011672273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (4419572843703 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41950869753 / 1000000000000) (41950869754 / 1000000000000), orderedInterval (53229671273 / 1000000000000) (53229671274 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (1429199051799 / 6400000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-46156971776 / 1000000000000) (-46156971775 / 1000000000000), orderedInterval (-26735703107 / 1000000000000) (-26735703106 / 1000000000000)))) (orderedInterval (-20189116394 / 1000000000000) (-20189116341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (1289620333221 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-30146514422 / 1000000000000) (-30146514421 / 1000000000000), orderedInterval (-121646650682 / 1000000000000) (-121646650681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (3464101615137 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (60933708369 / 1000000000000) (60933767280 / 1000000000000), orderedInterval (-46842223908 / 1000000000000) (-46842164997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (9405709748829 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26135980740 / 1000000000000) (-26135975923 / 1000000000000), orderedInterval (38551760679 / 1000000000000) (38551765496 / 1000000000000)))) (orderedInterval (10901896351 / 1000000000000) (10901898146 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (6928203230277 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-27003760463 / 1000000000000) (-27003760462 / 1000000000000), orderedInterval (-46961266437 / 1000000000000) (-46961266436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (11871594322521 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36226918267 / 1000000000000) (36226918268 / 1000000000000), orderedInterval (20041582370 / 1000000000000) (20041582371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (8744562646539 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32329719738 / 1000000000000) (-32329719737 / 1000000000000), orderedInterval (-35780025244 / 1000000000000) (-35780025243 / 1000000000000)))) (orderedInterval (7432882309 / 1000000000000) (7432882369 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate314_chunkChecks3_1 :
    compactCertificate314.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (13416407864997 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31133227505 / 1000000000000) (-31133166467 / 1000000000000), orderedInterval (23471056521 / 1000000000000) (23471117559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (7745966692413 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41526147447 / 1000000000000) (-41526147446 / 1000000000000), orderedInterval (-30006908255 / 1000000000000) (-30006908254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (13745353824417 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2722582008 / 1000000000000) (2722582010 / 1000000000000), orderedInterval (-38404694892 / 1000000000000) (-38404694890 / 1000000000000)))) (orderedInterval (117180360040 / 1000000000000) (117180482314 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (12842692543173 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-184441392 / 1000000000000) (-184441391 / 1000000000000), orderedInterval (39827681467 / 1000000000000) (39827681468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (9165151389909 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-45564029916 / 1000000000000) (-45564029913 / 1000000000000), orderedInterval (-12031006920 / 1000000000000) (-12031006917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (10392304845411 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40955429781 / 1000000000000) (-40955415421 / 1000000000000), orderedInterval (16883636172 / 1000000000000) (16883650532 / 1000000000000)))) (orderedInterval (11499523319 / 1000000000000) (11499523801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (8664020327859 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47402741512 / 1000000000000) (47402741517 / 1000000000000), orderedInterval (10124732452 / 1000000000000) (10124732457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (7654924713039 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (48794463983 / 1000000000000) (48794463985 / 1000000000000), orderedInterval (16642180337 / 1000000000000) (16642180339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (2218695546861 / 6400000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40807332840 / 1000000000000) (40807340110 / 1000000000000), orderedInterval (-13140870380 / 1000000000000) (-13140863110 / 1000000000000)))) (orderedInterval (3753120403 / 1000000000000) (3753121643 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate314_chunkChecks3_2 :
    compactCertificate314.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (6137028646167 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46176331070 / 1000000000000) (-46176331069 / 1000000000000), orderedInterval (-34335929435 / 1000000000000) (-34335929434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (5202427149087 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-146445756 / 1000000000000) (-146445751 / 1000000000000), orderedInterval (62577039119 / 1000000000000) (62577039123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (3255437353461 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72396472930 / 1000000000000) (72396478922 / 1000000000000), orderedInterval (-32238189561 / 1000000000000) (-32238183569 / 1000000000000)))) (orderedInterval (-3353332740 / 1000000000000) (-3353332667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (1750785035787 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-93754982700 / 1000000000000) (-93754969350 / 1000000000000), orderedInterval (54200739144 / 1000000000000) (54200752494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (4753721948361 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-65047739727 / 1000000000000) (-65047739498 / 1000000000000), orderedInterval (7582143878 / 1000000000000) (7582144106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (6490800912297 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30758638530 / 1000000000000) (30758645178 / 1000000000000), orderedInterval (-46899745752 / 1000000000000) (-46899739104 / 1000000000000)))) (orderedInterval (-4448891716 / 1000000000000) (-4448891037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (2744562646539 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-85084449071 / 1000000000000) (-85084448797 / 1000000000000), orderedInterval (14028626948 / 1000000000000) (14028627222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (11156494784619 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27812417993 / 1000000000000) (-27812417992 / 1000000000000), orderedInterval (-32402003585 / 1000000000000) (-32402003584 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (7452021478821 / 32000000000) 3 (IntervalRat.scale (375 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48396197423 / 1000000000000) (48396197424 / 1000000000000), orderedInterval (19683359153 / 1000000000000) (19683359155 / 1000000000000)))) (orderedInterval (-9922489679 / 1000000000000) (-9922489511 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate314_chunkChecks3 :
    compactCertificate314.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate314.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate314_chunkChecks3_0
    compactCertificate314_chunkChecks3_1 compactCertificate314_chunkChecks3_2

theorem compactCertificate314_chunkChecks4_0 :
    compactCertificate314.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (375 / 2) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12193946540 / 1000000000000) (-12193946457 / 1000000000000), orderedInterval (57011672190 / 1000000000000) (57011672273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (4419572843703 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41950869753 / 1000000000000) (41950869754 / 1000000000000), orderedInterval (53229671273 / 1000000000000) (53229671274 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (1429199051799 / 6400000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-46156971776 / 1000000000000) (-46156971775 / 1000000000000), orderedInterval (-26735703107 / 1000000000000) (-26735703106 / 1000000000000)))) (orderedInterval (-9952407999 / 1000000000000) (-9952407942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (1289620333221 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-30146514422 / 1000000000000) (-30146514421 / 1000000000000), orderedInterval (-121646650682 / 1000000000000) (-121646650681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (3464101615137 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (60933708369 / 1000000000000) (60933767280 / 1000000000000), orderedInterval (-46842223908 / 1000000000000) (-46842164997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (9405709748829 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26135980740 / 1000000000000) (-26135975923 / 1000000000000), orderedInterval (38551760679 / 1000000000000) (38551765496 / 1000000000000)))) (orderedInterval (11351808897 / 1000000000000) (11351811305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (6928203230277 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-27003760463 / 1000000000000) (-27003760462 / 1000000000000), orderedInterval (-46961266437 / 1000000000000) (-46961266436 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (11871594322521 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36226918267 / 1000000000000) (36226918268 / 1000000000000), orderedInterval (20041582370 / 1000000000000) (20041582371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (8744562646539 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-32329719738 / 1000000000000) (-32329719737 / 1000000000000), orderedInterval (-35780025244 / 1000000000000) (-35780025243 / 1000000000000)))) (orderedInterval (-20729473293 / 1000000000000) (-20729473182 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate314_chunkChecks4_1 :
    compactCertificate314.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (13416407864997 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31133227505 / 1000000000000) (-31133166467 / 1000000000000), orderedInterval (23471056521 / 1000000000000) (23471117559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (7745966692413 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-41526147447 / 1000000000000) (-41526147446 / 1000000000000), orderedInterval (-30006908255 / 1000000000000) (-30006908254 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (13745353824417 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2722582008 / 1000000000000) (2722582010 / 1000000000000), orderedInterval (-38404694892 / 1000000000000) (-38404694890 / 1000000000000)))) (orderedInterval (139162740977 / 1000000000000) (139163015024 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (12842692543173 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-184441392 / 1000000000000) (-184441391 / 1000000000000), orderedInterval (39827681467 / 1000000000000) (39827681468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (9165151389909 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-45564029916 / 1000000000000) (-45564029913 / 1000000000000), orderedInterval (-12031006920 / 1000000000000) (-12031006917 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (10392304845411 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-40955429781 / 1000000000000) (-40955415421 / 1000000000000), orderedInterval (16883636172 / 1000000000000) (16883650532 / 1000000000000)))) (orderedInterval (-21645467194 / 1000000000000) (-21645466357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (8664020327859 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47402741512 / 1000000000000) (47402741517 / 1000000000000), orderedInterval (10124732452 / 1000000000000) (10124732457 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (7654924713039 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (48794463983 / 1000000000000) (48794463985 / 1000000000000), orderedInterval (16642180337 / 1000000000000) (16642180339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (2218695546861 / 6400000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40807332840 / 1000000000000) (40807340110 / 1000000000000), orderedInterval (-13140870380 / 1000000000000) (-13140863110 / 1000000000000)))) (orderedInterval (7151568985 / 1000000000000) (7151571268 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate314_chunkChecks4_2 :
    compactCertificate314.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (6137028646167 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-46176331070 / 1000000000000) (-46176331069 / 1000000000000), orderedInterval (-34335929435 / 1000000000000) (-34335929434 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (5202427149087 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-146445756 / 1000000000000) (-146445751 / 1000000000000), orderedInterval (62577039119 / 1000000000000) (62577039123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (3255437353461 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (72396472930 / 1000000000000) (72396478922 / 1000000000000), orderedInterval (-32238189561 / 1000000000000) (-32238183569 / 1000000000000)))) (orderedInterval (8325651229 / 1000000000000) (8325651287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (1750785035787 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-93754982700 / 1000000000000) (-93754969350 / 1000000000000), orderedInterval (54200739144 / 1000000000000) (54200752494 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (4753721948361 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-65047739727 / 1000000000000) (-65047739498 / 1000000000000), orderedInterval (7582143878 / 1000000000000) (7582144106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (6490800912297 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30758638530 / 1000000000000) (30758645178 / 1000000000000), orderedInterval (-46899745752 / 1000000000000) (-46899739104 / 1000000000000)))) (orderedInterval (-2586992021 / 1000000000000) (-2586991291 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (2744562646539 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-85084449071 / 1000000000000) (-85084448797 / 1000000000000), orderedInterval (14028626948 / 1000000000000) (14028627222 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (11156494784619 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-27812417993 / 1000000000000) (-27812417992 / 1000000000000), orderedInterval (-32402003585 / 1000000000000) (-32402003584 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (7452021478821 / 32000000000) 4 (IntervalRat.scale (375 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (48396197423 / 1000000000000) (48396197424 / 1000000000000), orderedInterval (19683359153 / 1000000000000) (19683359155 / 1000000000000)))) (orderedInterval (5539615130 / 1000000000000) (5539615399 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate314_chunkChecks4 :
    compactCertificate314.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate314.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate314_chunkChecks4_0
    compactCertificate314_chunkChecks4_1 compactCertificate314_chunkChecks4_2

theorem compactCertificate314_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate314.chunkCheck r b = true :=
  compactCertificate314.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate314_chunkChecks0
    · exact compactCertificate314_chunkChecks1
    · exact compactCertificate314_chunkChecks2
    · exact compactCertificate314_chunkChecks3
    · exact compactCertificate314_chunkChecks4)

theorem compactCertificate314_coefficient0 :
    compactCertificate314.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate314_coefficient1 :
    compactCertificate314.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate314_coefficient2 :
    compactCertificate314.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate314_coefficient3 :
    compactCertificate314.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate314_coefficient4 :
    compactCertificate314.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate314_coefficients : ∀ r : Fin 5,
    compactCertificate314.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate314_coefficient0
  · exact compactCertificate314_coefficient1
  · exact compactCertificate314_coefficient2
  · exact compactCertificate314_coefficient3
  · exact compactCertificate314_coefficient4

theorem compactCertificate314_lower : (1 : ℚ) ≤ compactCertificate314.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate314, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate314_proves {t : ℝ} (ht : t ∈ compactCertificate314.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate314.proves compactCertificate314_states compactCertificate314_chunks
    compactCertificate314_coefficients compactCertificate314_lower ht

end Erdos232
