/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate370 : CompactCertificate where
  left := 241
  right := 242
  center := 483 / 2
  grid := fun i =>
    match i.val with
    | 0 => 77
    | 1 => 57
    | 2 => 92
    | 3 => 17
    | 4 => 44
    | 5 => 121
    | 6 => 89
    | 7 => 152
    | 8 => 112
    | 9 => 172
    | 10 => 99
    | 11 => 176
    | 12 => 165
    | 13 => 117
    | 14 => 133
    | 15 => 111
    | 16 => 98
    | 17 => 142
    | 18 => 79
    | 19 => 67
    | 20 => 42
    | 21 => 22
    | 22 => 61
    | 23 => 83
    | 24 => 35
    | 25 => 143
    | _ => 96
  point := fun i =>
    match i.val with
    | 0 => 483 / 2
    | 1 => 711551227836183 / 4000000000000
    | 2 => 230101047339639 / 800000000000
    | 3 => 207628873648581 / 4000000000000
    | 4 => 557720360037057 / 4000000000000
    | 5 => 1514319269561469 / 4000000000000
    | 6 => 1115440720074597 / 4000000000000
    | 7 => 1911326685925881 / 4000000000000
    | 8 => 1407874586092779 / 4000000000000
    | 9 => 2160041666264517 / 4000000000000
    | 10 => 1247100637478493 / 4000000000000
    | 11 => 2213001965731137 / 4000000000000
    | 12 => 2067673499450853 / 4000000000000
    | 13 => 1475589373775349 / 4000000000000
    | 14 => 1673161080111171 / 4000000000000
    | 15 => 1394907272785299 / 4000000000000
    | 16 => 1232442878799279 / 4000000000000
    | 17 => 357209983044621 / 800000000000
    | 18 => 988061612032887 / 4000000000000
    | 19 => 837590771003007 / 4000000000000
    | 20 => 524125413907221 / 4000000000000
    | 21 => 281876390761707 / 4000000000000
    | 22 => 765349233686121 / 4000000000000
    | 23 => 1045018946879817 / 4000000000000
    | 24 => 441874586092779 / 4000000000000
    | 25 => 1796195660323659 / 4000000000000
    | _ => 1199775458090181 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-19151213993 / 1000000000000) (-19151213992 / 1000000000000), orderedInterval (-47597958696 / 1000000000000) (-47597958695 / 1000000000000))
    | 1 => (orderedInterval (23201189032 / 1000000000000) (23201190044 / 1000000000000), orderedInterval (-55205814639 / 1000000000000) (-55205813628 / 1000000000000))
    | 2 => (orderedInterval (-27153422626 / 1000000000000) (-27153416554 / 1000000000000), orderedInterval (38466597430 / 1000000000000) (38466603502 / 1000000000000))
    | 3 => (orderedInterval (72760913351 / 1000000000000) (72760962619 / 1000000000000), orderedInterval (-84190319959 / 1000000000000) (-84190270692 / 1000000000000))
    | 4 => (orderedInterval (61870189917 / 1000000000000) (61870197106 / 1000000000000), orderedInterval (-27386736432 / 1000000000000) (-27386729243 / 1000000000000))
    | 5 => (orderedInterval (28482537813 / 1000000000000) (28482555333 / 1000000000000), orderedInterval (-29539226884 / 1000000000000) (-29539209364 / 1000000000000))
    | 6 => (orderedInterval (-2072227482 / 1000000000000) (-2072227481 / 1000000000000), orderedInterval (-47731438339 / 1000000000000) (-47731438338 / 1000000000000))
    | 7 => (orderedInterval (32441995238 / 1000000000000) (32441995239 / 1000000000000), orderedInterval (16694060145 / 1000000000000) (16694060147 / 1000000000000))
    | 8 => (orderedInterval (33190024480 / 1000000000000) (33190024481 / 1000000000000), orderedInterval (26545366548 / 1000000000000) (26545366549 / 1000000000000))
    | 9 => (orderedInterval (14675832493 / 1000000000000) (14675832494 / 1000000000000), orderedInterval (31027078812 / 1000000000000) (31027078813 / 1000000000000))
    | 10 => (orderedInterval (-45169464377 / 1000000000000) (-45169464275 / 1000000000000), orderedInterval (-1206761697 / 1000000000000) (-1206761594 / 1000000000000))
    | 11 => (orderedInterval (30464085826 / 1000000000000) (30464085828 / 1000000000000), orderedInterval (14893229562 / 1000000000000) (14893229564 / 1000000000000))
    | 12 => (orderedInterval (21495913437 / 1000000000000) (21495916250 / 1000000000000), orderedInterval (-27760532321 / 1000000000000) (-27760529508 / 1000000000000))
    | 13 => (orderedInterval (-35517979190 / 1000000000000) (-35517906605 / 1000000000000), orderedInterval (21593679638 / 1000000000000) (21593752223 / 1000000000000))
    | 14 => (orderedInterval (-36941868887 / 1000000000000) (-36941868885 / 1000000000000), orderedInterval (-12495952886 / 1000000000000) (-12495952883 / 1000000000000))
    | 15 => (orderedInterval (-30503077597 / 1000000000000) (-30503077596 / 1000000000000), orderedInterval (-29874764576 / 1000000000000) (-29874764575 / 1000000000000))
    | 16 => (orderedInterval (38724235589 / 1000000000000) (38724235590 / 1000000000000), orderedInterval (23741295019 / 1000000000000) (23741295021 / 1000000000000))
    | 17 => (orderedInterval (35074671993 / 1000000000000) (35074671995 / 1000000000000), orderedInterval (13943822548 / 1000000000000) (13943822550 / 1000000000000))
    | 18 => (orderedInterval (19090514375 / 1000000000000) (19090514943 / 1000000000000), orderedInterval (-47079085747 / 1000000000000) (-47079085180 / 1000000000000))
    | 19 => (orderedInterval (16516306685 / 1000000000000) (16516306940 / 1000000000000), orderedInterval (-52646103063 / 1000000000000) (-52646102807 / 1000000000000))
    | 20 => (orderedInterval (-9111465064 / 1000000000000) (-9111465025 / 1000000000000), orderedInterval (69140089136 / 1000000000000) (69140089175 / 1000000000000))
    | 21 => (orderedInterval (80178817460 / 1000000000000) (80178840490 / 1000000000000), orderedInterval (-51610884265 / 1000000000000) (-51610861235 / 1000000000000))
    | 22 => (orderedInterval (-26886749601 / 1000000000000) (-26886749600 / 1000000000000), orderedInterval (-50962289175 / 1000000000000) (-50962289174 / 1000000000000))
    | 23 => (orderedInterval (-47395545826 / 1000000000000) (-47395545824 / 1000000000000), orderedInterval (-13709161816 / 1000000000000) (-13709161815 / 1000000000000))
    | 24 => (orderedInterval (-73089202991 / 1000000000000) (-73089202990 / 1000000000000), orderedInterval (-20183043672 / 1000000000000) (-20183043671 / 1000000000000))
    | 25 => (orderedInterval (-20831986632 / 1000000000000) (-20831986631 / 1000000000000), orderedInterval (-31341364512 / 1000000000000) (-31341364511 / 1000000000000))
    | _ => (orderedInterval (-35035372981 / 1000000000000) (-35035312534 / 1000000000000), orderedInterval (29974709950 / 1000000000000) (29974770398 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8968074532 / 1000000000000) (-8968074149 / 1000000000000)
      | 1 => orderedInterval (-555230846 / 1000000000000) (-555228774 / 1000000000000)
      | 2 => orderedInterval (-198503533 / 1000000000000) (-198503519 / 1000000000000)
      | 3 => orderedInterval (-1623754603 / 1000000000000) (-1623754498 / 1000000000000)
      | 4 => orderedInterval (-3559802411 / 1000000000000) (-3559795467 / 1000000000000)
      | 5 => orderedInterval (-1670248660 / 1000000000000) (-1670248636 / 1000000000000)
      | 6 => orderedInterval (-4283877544 / 1000000000000) (-4283877377 / 1000000000000)
      | 7 => orderedInterval (2761805367 / 1000000000000) (2761805822 / 1000000000000)
      | _ => orderedInterval (7828709021 / 1000000000000) (7828720430 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-16556678069 / 1000000000000) (-16556677618 / 1000000000000)
      | 1 => orderedInterval (2910901467 / 1000000000000) (2910903719 / 1000000000000)
      | 2 => orderedInterval (-83792531 / 1000000000000) (-83792507 / 1000000000000)
      | 3 => orderedInterval (-7592992771 / 1000000000000) (-7592992561 / 1000000000000)
      | 4 => orderedInterval (4301389172 / 1000000000000) (4301399813 / 1000000000000)
      | 5 => orderedInterval (-1571440044 / 1000000000000) (-1571440010 / 1000000000000)
      | 6 => orderedInterval (11504439389 / 1000000000000) (11504439552 / 1000000000000)
      | 7 => orderedInterval (2330703518 / 1000000000000) (2330703669 / 1000000000000)
      | _ => orderedInterval (-2296939328 / 1000000000000) (-2296925147 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9802324901 / 1000000000000) (9802325436 / 1000000000000)
      | 1 => orderedInterval (4247250284 / 1000000000000) (4247253513 / 1000000000000)
      | 2 => orderedInterval (2213895249 / 1000000000000) (2213895291 / 1000000000000)
      | 3 => orderedInterval (-4080218428 / 1000000000000) (-4080217988 / 1000000000000)
      | 4 => orderedInterval (9036195504 / 1000000000000) (9036211874 / 1000000000000)
      | 5 => orderedInterval (1278133097 / 1000000000000) (1278133148 / 1000000000000)
      | 6 => orderedInterval (3935940394 / 1000000000000) (3935940554 / 1000000000000)
      | 7 => orderedInterval (-4517383118 / 1000000000000) (-4517383055 / 1000000000000)
      | _ => orderedInterval (-15901469691 / 1000000000000) (-15901451998 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15217440189 / 1000000000000) (15217440823 / 1000000000000)
      | 1 => orderedInterval (-7923756988 / 1000000000000) (-7923752052 / 1000000000000)
      | 2 => orderedInterval (1993247644 / 1000000000000) (1993247722 / 1000000000000)
      | 3 => orderedInterval (36393207978 / 1000000000000) (36393208932 / 1000000000000)
      | 4 => orderedInterval (-12558625286 / 1000000000000) (-12558600125 / 1000000000000)
      | 5 => orderedInterval (1598344916 / 1000000000000) (1598344994 / 1000000000000)
      | 6 => orderedInterval (-10373264240 / 1000000000000) (-10373264080 / 1000000000000)
      | 7 => orderedInterval (-1910087746 / 1000000000000) (-1910087708 / 1000000000000)
      | _ => orderedInterval (-5548953139 / 1000000000000) (-5548931123 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10859123313 / 1000000000000) (-10859122558 / 1000000000000)
      | 1 => orderedInterval (-11912742597 / 1000000000000) (-11912734900 / 1000000000000)
      | 2 => orderedInterval (-11733312871 / 1000000000000) (-11733312729 / 1000000000000)
      | 3 => orderedInterval (44490351599 / 1000000000000) (44490353702 / 1000000000000)
      | 4 => orderedInterval (-24645142244 / 1000000000000) (-24645103374 / 1000000000000)
      | 5 => orderedInterval (3078541866 / 1000000000000) (3078541989 / 1000000000000)
      | 6 => orderedInterval (-3809089547 / 1000000000000) (-3809089387 / 1000000000000)
      | 7 => orderedInterval (5220147009 / 1000000000000) (5220147041 / 1000000000000)
      | _ => orderedInterval (35939155734 / 1000000000000) (35939183246 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-10268977741 / 1000000000000) (-10268956168 / 1000000000000)
    | 1 => orderedInterval (-7054409197 / 1000000000000) (-7054381090 / 1000000000000)
    | 2 => orderedInterval (6014668192 / 1000000000000) (6014706775 / 1000000000000)
    | 3 => orderedInterval (16887553328 / 1000000000000) (16887607383 / 1000000000000)
    | _ => orderedInterval (25768785636 / 1000000000000) (25768863030 / 1000000000000)

theorem compactCertificate370_stateChecks0 :
    compactCertificate370.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (483 / 2)) (orderedInterval (-19151213993 / 1000000000000) (-19151213992 / 1000000000000), orderedInterval (-47597958696 / 1000000000000) (-47597958695 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (711551227836183 / 4000000000000)) (orderedInterval (23201189032 / 1000000000000) (23201190044 / 1000000000000), orderedInterval (-55205814639 / 1000000000000) (-55205813628 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (230101047339639 / 800000000000)) (orderedInterval (-27153422626 / 1000000000000) (-27153416554 / 1000000000000), orderedInterval (38466597430 / 1000000000000) (38466603502 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_stateChecks1 :
    compactCertificate370.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (207628873648581 / 4000000000000)) (orderedInterval (72760913351 / 1000000000000) (72760962619 / 1000000000000), orderedInterval (-84190319959 / 1000000000000) (-84190270692 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (557720360037057 / 4000000000000)) (orderedInterval (61870189917 / 1000000000000) (61870197106 / 1000000000000), orderedInterval (-27386736432 / 1000000000000) (-27386729243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1514319269561469 / 4000000000000)) (orderedInterval (28482537813 / 1000000000000) (28482555333 / 1000000000000), orderedInterval (-29539226884 / 1000000000000) (-29539209364 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_stateChecks2 :
    compactCertificate370.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1115440720074597 / 4000000000000)) (orderedInterval (-2072227482 / 1000000000000) (-2072227481 / 1000000000000), orderedInterval (-47731438339 / 1000000000000) (-47731438338 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1911326685925881 / 4000000000000)) (orderedInterval (32441995238 / 1000000000000) (32441995239 / 1000000000000), orderedInterval (16694060145 / 1000000000000) (16694060147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1407874586092779 / 4000000000000)) (orderedInterval (33190024480 / 1000000000000) (33190024481 / 1000000000000), orderedInterval (26545366548 / 1000000000000) (26545366549 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_stateChecks3 :
    compactCertificate370.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2160041666264517 / 4000000000000)) (orderedInterval (14675832493 / 1000000000000) (14675832494 / 1000000000000), orderedInterval (31027078812 / 1000000000000) (31027078813 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1247100637478493 / 4000000000000)) (orderedInterval (-45169464377 / 1000000000000) (-45169464275 / 1000000000000), orderedInterval (-1206761697 / 1000000000000) (-1206761594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2213001965731137 / 4000000000000)) (orderedInterval (30464085826 / 1000000000000) (30464085828 / 1000000000000), orderedInterval (14893229562 / 1000000000000) (14893229564 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_stateChecks4 :
    compactCertificate370.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2067673499450853 / 4000000000000)) (orderedInterval (21495913437 / 1000000000000) (21495916250 / 1000000000000), orderedInterval (-27760532321 / 1000000000000) (-27760529508 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1475589373775349 / 4000000000000)) (orderedInterval (-35517979190 / 1000000000000) (-35517906605 / 1000000000000), orderedInterval (21593679638 / 1000000000000) (21593752223 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1673161080111171 / 4000000000000)) (orderedInterval (-36941868887 / 1000000000000) (-36941868885 / 1000000000000), orderedInterval (-12495952886 / 1000000000000) (-12495952883 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_stateChecks5 :
    compactCertificate370.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1394907272785299 / 4000000000000)) (orderedInterval (-30503077597 / 1000000000000) (-30503077596 / 1000000000000), orderedInterval (-29874764576 / 1000000000000) (-29874764575 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1232442878799279 / 4000000000000)) (orderedInterval (38724235589 / 1000000000000) (38724235590 / 1000000000000), orderedInterval (23741295019 / 1000000000000) (23741295021 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (357209983044621 / 800000000000)) (orderedInterval (35074671993 / 1000000000000) (35074671995 / 1000000000000), orderedInterval (13943822548 / 1000000000000) (13943822550 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_stateChecks6 :
    compactCertificate370.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (988061612032887 / 4000000000000)) (orderedInterval (19090514375 / 1000000000000) (19090514943 / 1000000000000), orderedInterval (-47079085747 / 1000000000000) (-47079085180 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (837590771003007 / 4000000000000)) (orderedInterval (16516306685 / 1000000000000) (16516306940 / 1000000000000), orderedInterval (-52646103063 / 1000000000000) (-52646102807 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (524125413907221 / 4000000000000)) (orderedInterval (-9111465064 / 1000000000000) (-9111465025 / 1000000000000), orderedInterval (69140089136 / 1000000000000) (69140089175 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_stateChecks7 :
    compactCertificate370.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (281876390761707 / 4000000000000)) (orderedInterval (80178817460 / 1000000000000) (80178840490 / 1000000000000), orderedInterval (-51610884265 / 1000000000000) (-51610861235 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (765349233686121 / 4000000000000)) (orderedInterval (-26886749601 / 1000000000000) (-26886749600 / 1000000000000), orderedInterval (-50962289175 / 1000000000000) (-50962289174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1045018946879817 / 4000000000000)) (orderedInterval (-47395545826 / 1000000000000) (-47395545824 / 1000000000000), orderedInterval (-13709161816 / 1000000000000) (-13709161815 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_stateChecks8 :
    compactCertificate370.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (441874586092779 / 4000000000000)) (orderedInterval (-73089202991 / 1000000000000) (-73089202990 / 1000000000000), orderedInterval (-20183043672 / 1000000000000) (-20183043671 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1796195660323659 / 4000000000000)) (orderedInterval (-20831986632 / 1000000000000) (-20831986631 / 1000000000000), orderedInterval (-31341364512 / 1000000000000) (-31341364511 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1199775458090181 / 4000000000000)) (orderedInterval (-35035372981 / 1000000000000) (-35035312534 / 1000000000000), orderedInterval (29974709950 / 1000000000000) (29974770398 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_states : ∀ j,
    BesselStateValid (compactCertificate370.point j) (compactCertificate370.state j) :=
  compactCertificate370.statesValid_of_checks3 compactCertificate370_stateChecks0
    compactCertificate370_stateChecks1 compactCertificate370_stateChecks2
    compactCertificate370_stateChecks3 compactCertificate370_stateChecks4
    compactCertificate370_stateChecks5 compactCertificate370_stateChecks6
    compactCertificate370_stateChecks7 compactCertificate370_stateChecks8

theorem compactCertificate370_chunkChecks0_0 :
    compactCertificate370.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (483 / 2) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19151213993 / 1000000000000) (-19151213992 / 1000000000000), orderedInterval (-47597958696 / 1000000000000) (-47597958695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (711551227836183 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23201189032 / 1000000000000) (23201190044 / 1000000000000), orderedInterval (-55205814639 / 1000000000000) (-55205813628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (230101047339639 / 800000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27153422626 / 1000000000000) (-27153416554 / 1000000000000), orderedInterval (38466597430 / 1000000000000) (38466603502 / 1000000000000)))) (orderedInterval (-8968074532 / 1000000000000) (-8968074149 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (207628873648581 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72760913351 / 1000000000000) (72760962619 / 1000000000000), orderedInterval (-84190319959 / 1000000000000) (-84190270692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (557720360037057 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61870189917 / 1000000000000) (61870197106 / 1000000000000), orderedInterval (-27386736432 / 1000000000000) (-27386729243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1514319269561469 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28482537813 / 1000000000000) (28482555333 / 1000000000000), orderedInterval (-29539226884 / 1000000000000) (-29539209364 / 1000000000000)))) (orderedInterval (-555230846 / 1000000000000) (-555228774 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1115440720074597 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2072227482 / 1000000000000) (-2072227481 / 1000000000000), orderedInterval (-47731438339 / 1000000000000) (-47731438338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1911326685925881 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32441995238 / 1000000000000) (32441995239 / 1000000000000), orderedInterval (16694060145 / 1000000000000) (16694060147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1407874586092779 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33190024480 / 1000000000000) (33190024481 / 1000000000000), orderedInterval (26545366548 / 1000000000000) (26545366549 / 1000000000000)))) (orderedInterval (-198503533 / 1000000000000) (-198503519 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_chunkChecks0_1 :
    compactCertificate370.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2160041666264517 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14675832493 / 1000000000000) (14675832494 / 1000000000000), orderedInterval (31027078812 / 1000000000000) (31027078813 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1247100637478493 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45169464377 / 1000000000000) (-45169464275 / 1000000000000), orderedInterval (-1206761697 / 1000000000000) (-1206761594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2213001965731137 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30464085826 / 1000000000000) (30464085828 / 1000000000000), orderedInterval (14893229562 / 1000000000000) (14893229564 / 1000000000000)))) (orderedInterval (-1623754603 / 1000000000000) (-1623754498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2067673499450853 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21495913437 / 1000000000000) (21495916250 / 1000000000000), orderedInterval (-27760532321 / 1000000000000) (-27760529508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1475589373775349 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35517979190 / 1000000000000) (-35517906605 / 1000000000000), orderedInterval (21593679638 / 1000000000000) (21593752223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1673161080111171 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36941868887 / 1000000000000) (-36941868885 / 1000000000000), orderedInterval (-12495952886 / 1000000000000) (-12495952883 / 1000000000000)))) (orderedInterval (-3559802411 / 1000000000000) (-3559795467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1394907272785299 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30503077597 / 1000000000000) (-30503077596 / 1000000000000), orderedInterval (-29874764576 / 1000000000000) (-29874764575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1232442878799279 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38724235589 / 1000000000000) (38724235590 / 1000000000000), orderedInterval (23741295019 / 1000000000000) (23741295021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (357209983044621 / 800000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35074671993 / 1000000000000) (35074671995 / 1000000000000), orderedInterval (13943822548 / 1000000000000) (13943822550 / 1000000000000)))) (orderedInterval (-1670248660 / 1000000000000) (-1670248636 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_chunkChecks0_2 :
    compactCertificate370.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (988061612032887 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19090514375 / 1000000000000) (19090514943 / 1000000000000), orderedInterval (-47079085747 / 1000000000000) (-47079085180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (837590771003007 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (16516306685 / 1000000000000) (16516306940 / 1000000000000), orderedInterval (-52646103063 / 1000000000000) (-52646102807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (524125413907221 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9111465064 / 1000000000000) (-9111465025 / 1000000000000), orderedInterval (69140089136 / 1000000000000) (69140089175 / 1000000000000)))) (orderedInterval (-4283877544 / 1000000000000) (-4283877377 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (281876390761707 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (80178817460 / 1000000000000) (80178840490 / 1000000000000), orderedInterval (-51610884265 / 1000000000000) (-51610861235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (765349233686121 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-26886749601 / 1000000000000) (-26886749600 / 1000000000000), orderedInterval (-50962289175 / 1000000000000) (-50962289174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1045018946879817 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47395545826 / 1000000000000) (-47395545824 / 1000000000000), orderedInterval (-13709161816 / 1000000000000) (-13709161815 / 1000000000000)))) (orderedInterval (2761805367 / 1000000000000) (2761805822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (441874586092779 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73089202991 / 1000000000000) (-73089202990 / 1000000000000), orderedInterval (-20183043672 / 1000000000000) (-20183043671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1796195660323659 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20831986632 / 1000000000000) (-20831986631 / 1000000000000), orderedInterval (-31341364512 / 1000000000000) (-31341364511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1199775458090181 / 4000000000000) 0 (IntervalRat.scale (483 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35035372981 / 1000000000000) (-35035312534 / 1000000000000), orderedInterval (29974709950 / 1000000000000) (29974770398 / 1000000000000)))) (orderedInterval (7828709021 / 1000000000000) (7828720430 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_chunkChecks0 :
    compactCertificate370.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate370.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate370_chunkChecks0_0
    compactCertificate370_chunkChecks0_1 compactCertificate370_chunkChecks0_2

theorem compactCertificate370_chunkChecks1_0 :
    compactCertificate370.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (483 / 2) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19151213993 / 1000000000000) (-19151213992 / 1000000000000), orderedInterval (-47597958696 / 1000000000000) (-47597958695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (711551227836183 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23201189032 / 1000000000000) (23201190044 / 1000000000000), orderedInterval (-55205814639 / 1000000000000) (-55205813628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (230101047339639 / 800000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27153422626 / 1000000000000) (-27153416554 / 1000000000000), orderedInterval (38466597430 / 1000000000000) (38466603502 / 1000000000000)))) (orderedInterval (-16556678069 / 1000000000000) (-16556677618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (207628873648581 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72760913351 / 1000000000000) (72760962619 / 1000000000000), orderedInterval (-84190319959 / 1000000000000) (-84190270692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (557720360037057 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61870189917 / 1000000000000) (61870197106 / 1000000000000), orderedInterval (-27386736432 / 1000000000000) (-27386729243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1514319269561469 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28482537813 / 1000000000000) (28482555333 / 1000000000000), orderedInterval (-29539226884 / 1000000000000) (-29539209364 / 1000000000000)))) (orderedInterval (2910901467 / 1000000000000) (2910903719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1115440720074597 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2072227482 / 1000000000000) (-2072227481 / 1000000000000), orderedInterval (-47731438339 / 1000000000000) (-47731438338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1911326685925881 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32441995238 / 1000000000000) (32441995239 / 1000000000000), orderedInterval (16694060145 / 1000000000000) (16694060147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1407874586092779 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33190024480 / 1000000000000) (33190024481 / 1000000000000), orderedInterval (26545366548 / 1000000000000) (26545366549 / 1000000000000)))) (orderedInterval (-83792531 / 1000000000000) (-83792507 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_chunkChecks1_1 :
    compactCertificate370.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2160041666264517 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14675832493 / 1000000000000) (14675832494 / 1000000000000), orderedInterval (31027078812 / 1000000000000) (31027078813 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1247100637478493 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45169464377 / 1000000000000) (-45169464275 / 1000000000000), orderedInterval (-1206761697 / 1000000000000) (-1206761594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2213001965731137 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30464085826 / 1000000000000) (30464085828 / 1000000000000), orderedInterval (14893229562 / 1000000000000) (14893229564 / 1000000000000)))) (orderedInterval (-7592992771 / 1000000000000) (-7592992561 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2067673499450853 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21495913437 / 1000000000000) (21495916250 / 1000000000000), orderedInterval (-27760532321 / 1000000000000) (-27760529508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1475589373775349 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35517979190 / 1000000000000) (-35517906605 / 1000000000000), orderedInterval (21593679638 / 1000000000000) (21593752223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1673161080111171 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36941868887 / 1000000000000) (-36941868885 / 1000000000000), orderedInterval (-12495952886 / 1000000000000) (-12495952883 / 1000000000000)))) (orderedInterval (4301389172 / 1000000000000) (4301399813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1394907272785299 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30503077597 / 1000000000000) (-30503077596 / 1000000000000), orderedInterval (-29874764576 / 1000000000000) (-29874764575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1232442878799279 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38724235589 / 1000000000000) (38724235590 / 1000000000000), orderedInterval (23741295019 / 1000000000000) (23741295021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (357209983044621 / 800000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35074671993 / 1000000000000) (35074671995 / 1000000000000), orderedInterval (13943822548 / 1000000000000) (13943822550 / 1000000000000)))) (orderedInterval (-1571440044 / 1000000000000) (-1571440010 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_chunkChecks1_2 :
    compactCertificate370.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (988061612032887 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19090514375 / 1000000000000) (19090514943 / 1000000000000), orderedInterval (-47079085747 / 1000000000000) (-47079085180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (837590771003007 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (16516306685 / 1000000000000) (16516306940 / 1000000000000), orderedInterval (-52646103063 / 1000000000000) (-52646102807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (524125413907221 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9111465064 / 1000000000000) (-9111465025 / 1000000000000), orderedInterval (69140089136 / 1000000000000) (69140089175 / 1000000000000)))) (orderedInterval (11504439389 / 1000000000000) (11504439552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (281876390761707 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (80178817460 / 1000000000000) (80178840490 / 1000000000000), orderedInterval (-51610884265 / 1000000000000) (-51610861235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (765349233686121 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-26886749601 / 1000000000000) (-26886749600 / 1000000000000), orderedInterval (-50962289175 / 1000000000000) (-50962289174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1045018946879817 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47395545826 / 1000000000000) (-47395545824 / 1000000000000), orderedInterval (-13709161816 / 1000000000000) (-13709161815 / 1000000000000)))) (orderedInterval (2330703518 / 1000000000000) (2330703669 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (441874586092779 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73089202991 / 1000000000000) (-73089202990 / 1000000000000), orderedInterval (-20183043672 / 1000000000000) (-20183043671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1796195660323659 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20831986632 / 1000000000000) (-20831986631 / 1000000000000), orderedInterval (-31341364512 / 1000000000000) (-31341364511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1199775458090181 / 4000000000000) 1 (IntervalRat.scale (483 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35035372981 / 1000000000000) (-35035312534 / 1000000000000), orderedInterval (29974709950 / 1000000000000) (29974770398 / 1000000000000)))) (orderedInterval (-2296939328 / 1000000000000) (-2296925147 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_chunkChecks1 :
    compactCertificate370.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate370.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate370_chunkChecks1_0
    compactCertificate370_chunkChecks1_1 compactCertificate370_chunkChecks1_2

theorem compactCertificate370_chunkChecks2_0 :
    compactCertificate370.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (483 / 2) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19151213993 / 1000000000000) (-19151213992 / 1000000000000), orderedInterval (-47597958696 / 1000000000000) (-47597958695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (711551227836183 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23201189032 / 1000000000000) (23201190044 / 1000000000000), orderedInterval (-55205814639 / 1000000000000) (-55205813628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (230101047339639 / 800000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27153422626 / 1000000000000) (-27153416554 / 1000000000000), orderedInterval (38466597430 / 1000000000000) (38466603502 / 1000000000000)))) (orderedInterval (9802324901 / 1000000000000) (9802325436 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (207628873648581 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72760913351 / 1000000000000) (72760962619 / 1000000000000), orderedInterval (-84190319959 / 1000000000000) (-84190270692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (557720360037057 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61870189917 / 1000000000000) (61870197106 / 1000000000000), orderedInterval (-27386736432 / 1000000000000) (-27386729243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1514319269561469 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28482537813 / 1000000000000) (28482555333 / 1000000000000), orderedInterval (-29539226884 / 1000000000000) (-29539209364 / 1000000000000)))) (orderedInterval (4247250284 / 1000000000000) (4247253513 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1115440720074597 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2072227482 / 1000000000000) (-2072227481 / 1000000000000), orderedInterval (-47731438339 / 1000000000000) (-47731438338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1911326685925881 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32441995238 / 1000000000000) (32441995239 / 1000000000000), orderedInterval (16694060145 / 1000000000000) (16694060147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1407874586092779 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33190024480 / 1000000000000) (33190024481 / 1000000000000), orderedInterval (26545366548 / 1000000000000) (26545366549 / 1000000000000)))) (orderedInterval (2213895249 / 1000000000000) (2213895291 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_chunkChecks2_1 :
    compactCertificate370.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2160041666264517 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14675832493 / 1000000000000) (14675832494 / 1000000000000), orderedInterval (31027078812 / 1000000000000) (31027078813 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1247100637478493 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45169464377 / 1000000000000) (-45169464275 / 1000000000000), orderedInterval (-1206761697 / 1000000000000) (-1206761594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2213001965731137 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30464085826 / 1000000000000) (30464085828 / 1000000000000), orderedInterval (14893229562 / 1000000000000) (14893229564 / 1000000000000)))) (orderedInterval (-4080218428 / 1000000000000) (-4080217988 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2067673499450853 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21495913437 / 1000000000000) (21495916250 / 1000000000000), orderedInterval (-27760532321 / 1000000000000) (-27760529508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1475589373775349 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35517979190 / 1000000000000) (-35517906605 / 1000000000000), orderedInterval (21593679638 / 1000000000000) (21593752223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1673161080111171 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36941868887 / 1000000000000) (-36941868885 / 1000000000000), orderedInterval (-12495952886 / 1000000000000) (-12495952883 / 1000000000000)))) (orderedInterval (9036195504 / 1000000000000) (9036211874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1394907272785299 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30503077597 / 1000000000000) (-30503077596 / 1000000000000), orderedInterval (-29874764576 / 1000000000000) (-29874764575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1232442878799279 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38724235589 / 1000000000000) (38724235590 / 1000000000000), orderedInterval (23741295019 / 1000000000000) (23741295021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (357209983044621 / 800000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35074671993 / 1000000000000) (35074671995 / 1000000000000), orderedInterval (13943822548 / 1000000000000) (13943822550 / 1000000000000)))) (orderedInterval (1278133097 / 1000000000000) (1278133148 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_chunkChecks2_2 :
    compactCertificate370.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (988061612032887 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19090514375 / 1000000000000) (19090514943 / 1000000000000), orderedInterval (-47079085747 / 1000000000000) (-47079085180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (837590771003007 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (16516306685 / 1000000000000) (16516306940 / 1000000000000), orderedInterval (-52646103063 / 1000000000000) (-52646102807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (524125413907221 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9111465064 / 1000000000000) (-9111465025 / 1000000000000), orderedInterval (69140089136 / 1000000000000) (69140089175 / 1000000000000)))) (orderedInterval (3935940394 / 1000000000000) (3935940554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (281876390761707 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (80178817460 / 1000000000000) (80178840490 / 1000000000000), orderedInterval (-51610884265 / 1000000000000) (-51610861235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (765349233686121 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-26886749601 / 1000000000000) (-26886749600 / 1000000000000), orderedInterval (-50962289175 / 1000000000000) (-50962289174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1045018946879817 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47395545826 / 1000000000000) (-47395545824 / 1000000000000), orderedInterval (-13709161816 / 1000000000000) (-13709161815 / 1000000000000)))) (orderedInterval (-4517383118 / 1000000000000) (-4517383055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (441874586092779 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73089202991 / 1000000000000) (-73089202990 / 1000000000000), orderedInterval (-20183043672 / 1000000000000) (-20183043671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1796195660323659 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20831986632 / 1000000000000) (-20831986631 / 1000000000000), orderedInterval (-31341364512 / 1000000000000) (-31341364511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1199775458090181 / 4000000000000) 2 (IntervalRat.scale (483 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35035372981 / 1000000000000) (-35035312534 / 1000000000000), orderedInterval (29974709950 / 1000000000000) (29974770398 / 1000000000000)))) (orderedInterval (-15901469691 / 1000000000000) (-15901451998 / 1000000000000))) = true
  rfl'

theorem compactCertificate370_chunkChecks2 :
    compactCertificate370.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate370.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate370_chunkChecks2_0
    compactCertificate370_chunkChecks2_1 compactCertificate370_chunkChecks2_2

theorem compactCertificate370_chunkChecks3_0 :
    compactCertificate370.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (483 / 2) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19151213993 / 1000000000000) (-19151213992 / 1000000000000), orderedInterval (-47597958696 / 1000000000000) (-47597958695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (711551227836183 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23201189032 / 1000000000000) (23201190044 / 1000000000000), orderedInterval (-55205814639 / 1000000000000) (-55205813628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (230101047339639 / 800000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27153422626 / 1000000000000) (-27153416554 / 1000000000000), orderedInterval (38466597430 / 1000000000000) (38466603502 / 1000000000000)))) (orderedInterval (15217440189 / 1000000000000) (15217440823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (207628873648581 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72760913351 / 1000000000000) (72760962619 / 1000000000000), orderedInterval (-84190319959 / 1000000000000) (-84190270692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (557720360037057 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61870189917 / 1000000000000) (61870197106 / 1000000000000), orderedInterval (-27386736432 / 1000000000000) (-27386729243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1514319269561469 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28482537813 / 1000000000000) (28482555333 / 1000000000000), orderedInterval (-29539226884 / 1000000000000) (-29539209364 / 1000000000000)))) (orderedInterval (-7923756988 / 1000000000000) (-7923752052 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1115440720074597 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2072227482 / 1000000000000) (-2072227481 / 1000000000000), orderedInterval (-47731438339 / 1000000000000) (-47731438338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1911326685925881 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32441995238 / 1000000000000) (32441995239 / 1000000000000), orderedInterval (16694060145 / 1000000000000) (16694060147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1407874586092779 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33190024480 / 1000000000000) (33190024481 / 1000000000000), orderedInterval (26545366548 / 1000000000000) (26545366549 / 1000000000000)))) (orderedInterval (1993247644 / 1000000000000) (1993247722 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate370_chunkChecks3_1 :
    compactCertificate370.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2160041666264517 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14675832493 / 1000000000000) (14675832494 / 1000000000000), orderedInterval (31027078812 / 1000000000000) (31027078813 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1247100637478493 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45169464377 / 1000000000000) (-45169464275 / 1000000000000), orderedInterval (-1206761697 / 1000000000000) (-1206761594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2213001965731137 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30464085826 / 1000000000000) (30464085828 / 1000000000000), orderedInterval (14893229562 / 1000000000000) (14893229564 / 1000000000000)))) (orderedInterval (36393207978 / 1000000000000) (36393208932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2067673499450853 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21495913437 / 1000000000000) (21495916250 / 1000000000000), orderedInterval (-27760532321 / 1000000000000) (-27760529508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1475589373775349 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35517979190 / 1000000000000) (-35517906605 / 1000000000000), orderedInterval (21593679638 / 1000000000000) (21593752223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1673161080111171 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36941868887 / 1000000000000) (-36941868885 / 1000000000000), orderedInterval (-12495952886 / 1000000000000) (-12495952883 / 1000000000000)))) (orderedInterval (-12558625286 / 1000000000000) (-12558600125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1394907272785299 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30503077597 / 1000000000000) (-30503077596 / 1000000000000), orderedInterval (-29874764576 / 1000000000000) (-29874764575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1232442878799279 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38724235589 / 1000000000000) (38724235590 / 1000000000000), orderedInterval (23741295019 / 1000000000000) (23741295021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (357209983044621 / 800000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35074671993 / 1000000000000) (35074671995 / 1000000000000), orderedInterval (13943822548 / 1000000000000) (13943822550 / 1000000000000)))) (orderedInterval (1598344916 / 1000000000000) (1598344994 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate370_chunkChecks3_2 :
    compactCertificate370.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (988061612032887 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19090514375 / 1000000000000) (19090514943 / 1000000000000), orderedInterval (-47079085747 / 1000000000000) (-47079085180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (837590771003007 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (16516306685 / 1000000000000) (16516306940 / 1000000000000), orderedInterval (-52646103063 / 1000000000000) (-52646102807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (524125413907221 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9111465064 / 1000000000000) (-9111465025 / 1000000000000), orderedInterval (69140089136 / 1000000000000) (69140089175 / 1000000000000)))) (orderedInterval (-10373264240 / 1000000000000) (-10373264080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (281876390761707 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (80178817460 / 1000000000000) (80178840490 / 1000000000000), orderedInterval (-51610884265 / 1000000000000) (-51610861235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (765349233686121 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-26886749601 / 1000000000000) (-26886749600 / 1000000000000), orderedInterval (-50962289175 / 1000000000000) (-50962289174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1045018946879817 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47395545826 / 1000000000000) (-47395545824 / 1000000000000), orderedInterval (-13709161816 / 1000000000000) (-13709161815 / 1000000000000)))) (orderedInterval (-1910087746 / 1000000000000) (-1910087708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (441874586092779 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73089202991 / 1000000000000) (-73089202990 / 1000000000000), orderedInterval (-20183043672 / 1000000000000) (-20183043671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1796195660323659 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20831986632 / 1000000000000) (-20831986631 / 1000000000000), orderedInterval (-31341364512 / 1000000000000) (-31341364511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1199775458090181 / 4000000000000) 3 (IntervalRat.scale (483 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35035372981 / 1000000000000) (-35035312534 / 1000000000000), orderedInterval (29974709950 / 1000000000000) (29974770398 / 1000000000000)))) (orderedInterval (-5548953139 / 1000000000000) (-5548931123 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate370_chunkChecks3 :
    compactCertificate370.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate370.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate370_chunkChecks3_0
    compactCertificate370_chunkChecks3_1 compactCertificate370_chunkChecks3_2

theorem compactCertificate370_chunkChecks4_0 :
    compactCertificate370.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (483 / 2) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-19151213993 / 1000000000000) (-19151213992 / 1000000000000), orderedInterval (-47597958696 / 1000000000000) (-47597958695 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (711551227836183 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23201189032 / 1000000000000) (23201190044 / 1000000000000), orderedInterval (-55205814639 / 1000000000000) (-55205813628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (230101047339639 / 800000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-27153422626 / 1000000000000) (-27153416554 / 1000000000000), orderedInterval (38466597430 / 1000000000000) (38466603502 / 1000000000000)))) (orderedInterval (-10859123313 / 1000000000000) (-10859122558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (207628873648581 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72760913351 / 1000000000000) (72760962619 / 1000000000000), orderedInterval (-84190319959 / 1000000000000) (-84190270692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (557720360037057 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (61870189917 / 1000000000000) (61870197106 / 1000000000000), orderedInterval (-27386736432 / 1000000000000) (-27386729243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1514319269561469 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28482537813 / 1000000000000) (28482555333 / 1000000000000), orderedInterval (-29539226884 / 1000000000000) (-29539209364 / 1000000000000)))) (orderedInterval (-11912742597 / 1000000000000) (-11912734900 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1115440720074597 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-2072227482 / 1000000000000) (-2072227481 / 1000000000000), orderedInterval (-47731438339 / 1000000000000) (-47731438338 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1911326685925881 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32441995238 / 1000000000000) (32441995239 / 1000000000000), orderedInterval (16694060145 / 1000000000000) (16694060147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1407874586092779 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33190024480 / 1000000000000) (33190024481 / 1000000000000), orderedInterval (26545366548 / 1000000000000) (26545366549 / 1000000000000)))) (orderedInterval (-11733312871 / 1000000000000) (-11733312729 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate370_chunkChecks4_1 :
    compactCertificate370.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2160041666264517 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (14675832493 / 1000000000000) (14675832494 / 1000000000000), orderedInterval (31027078812 / 1000000000000) (31027078813 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1247100637478493 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-45169464377 / 1000000000000) (-45169464275 / 1000000000000), orderedInterval (-1206761697 / 1000000000000) (-1206761594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2213001965731137 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30464085826 / 1000000000000) (30464085828 / 1000000000000), orderedInterval (14893229562 / 1000000000000) (14893229564 / 1000000000000)))) (orderedInterval (44490351599 / 1000000000000) (44490353702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2067673499450853 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21495913437 / 1000000000000) (21495916250 / 1000000000000), orderedInterval (-27760532321 / 1000000000000) (-27760529508 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1475589373775349 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35517979190 / 1000000000000) (-35517906605 / 1000000000000), orderedInterval (21593679638 / 1000000000000) (21593752223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1673161080111171 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-36941868887 / 1000000000000) (-36941868885 / 1000000000000), orderedInterval (-12495952886 / 1000000000000) (-12495952883 / 1000000000000)))) (orderedInterval (-24645142244 / 1000000000000) (-24645103374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1394907272785299 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30503077597 / 1000000000000) (-30503077596 / 1000000000000), orderedInterval (-29874764576 / 1000000000000) (-29874764575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1232442878799279 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38724235589 / 1000000000000) (38724235590 / 1000000000000), orderedInterval (23741295019 / 1000000000000) (23741295021 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (357209983044621 / 800000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (35074671993 / 1000000000000) (35074671995 / 1000000000000), orderedInterval (13943822548 / 1000000000000) (13943822550 / 1000000000000)))) (orderedInterval (3078541866 / 1000000000000) (3078541989 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate370_chunkChecks4_2 :
    compactCertificate370.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (988061612032887 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (19090514375 / 1000000000000) (19090514943 / 1000000000000), orderedInterval (-47079085747 / 1000000000000) (-47079085180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (837590771003007 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (16516306685 / 1000000000000) (16516306940 / 1000000000000), orderedInterval (-52646103063 / 1000000000000) (-52646102807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (524125413907221 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9111465064 / 1000000000000) (-9111465025 / 1000000000000), orderedInterval (69140089136 / 1000000000000) (69140089175 / 1000000000000)))) (orderedInterval (-3809089547 / 1000000000000) (-3809089387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (281876390761707 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (80178817460 / 1000000000000) (80178840490 / 1000000000000), orderedInterval (-51610884265 / 1000000000000) (-51610861235 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (765349233686121 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-26886749601 / 1000000000000) (-26886749600 / 1000000000000), orderedInterval (-50962289175 / 1000000000000) (-50962289174 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1045018946879817 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47395545826 / 1000000000000) (-47395545824 / 1000000000000), orderedInterval (-13709161816 / 1000000000000) (-13709161815 / 1000000000000)))) (orderedInterval (5220147009 / 1000000000000) (5220147041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (441874586092779 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-73089202991 / 1000000000000) (-73089202990 / 1000000000000), orderedInterval (-20183043672 / 1000000000000) (-20183043671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1796195660323659 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-20831986632 / 1000000000000) (-20831986631 / 1000000000000), orderedInterval (-31341364512 / 1000000000000) (-31341364511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1199775458090181 / 4000000000000) 4 (IntervalRat.scale (483 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35035372981 / 1000000000000) (-35035312534 / 1000000000000), orderedInterval (29974709950 / 1000000000000) (29974770398 / 1000000000000)))) (orderedInterval (35939155734 / 1000000000000) (35939183246 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate370_chunkChecks4 :
    compactCertificate370.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate370.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate370_chunkChecks4_0
    compactCertificate370_chunkChecks4_1 compactCertificate370_chunkChecks4_2

theorem compactCertificate370_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate370.chunkCheck r b = true :=
  compactCertificate370.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate370_chunkChecks0
    · exact compactCertificate370_chunkChecks1
    · exact compactCertificate370_chunkChecks2
    · exact compactCertificate370_chunkChecks3
    · exact compactCertificate370_chunkChecks4)

theorem compactCertificate370_coefficient0 :
    compactCertificate370.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate370_coefficient1 :
    compactCertificate370.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate370_coefficient2 :
    compactCertificate370.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate370_coefficient3 :
    compactCertificate370.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate370_coefficient4 :
    compactCertificate370.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate370_coefficients : ∀ r : Fin 5,
    compactCertificate370.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate370_coefficient0
  · exact compactCertificate370_coefficient1
  · exact compactCertificate370_coefficient2
  · exact compactCertificate370_coefficient3
  · exact compactCertificate370_coefficient4

theorem compactCertificate370_lower : (1 : ℚ) ≤ compactCertificate370.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate370, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate370_proves {t : ℝ} (ht : t ∈ compactCertificate370.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate370.proves compactCertificate370_states compactCertificate370_chunks
    compactCertificate370_coefficients compactCertificate370_lower ht

end Erdos232
