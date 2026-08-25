/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate309 : CompactCertificate where
  left := 182
  right := 183
  center := 365 / 2
  grid := fun i =>
    match i.val with
    | 0 => 58
    | 1 => 43
    | 2 => 69
    | 3 => 12
    | 4 => 34
    | 5 => 91
    | 6 => 67
    | 7 => 115
    | 8 => 85
    | 9 => 130
    | 10 => 75
    | 11 => 133
    | 12 => 124
    | 13 => 89
    | 14 => 101
    | 15 => 84
    | 16 => 74
    | 17 => 107
    | 18 => 59
    | 19 => 50
    | 20 => 32
    | 21 => 17
    | 22 => 46
    | 23 => 63
    | 24 => 27
    | 25 => 108
    | _ => 72
  point := fun i =>
    match i.val with
    | 0 => 365 / 2
    | 1 => 107542939196773 / 800000000000
    | 2 => 34777176927109 / 160000000000
    | 3 => 31380761441711 / 800000000000
    | 4 => 84293139301667 / 800000000000
    | 5 => 228872270554839 / 800000000000
    | 6 => 168586278603407 / 800000000000
    | 7 => 288875461848011 / 800000000000
    | 8 => 212784357732449 / 800000000000
    | 9 => 326465924714927 / 800000000000
    | 10 => 188485189515383 / 800000000000
    | 11 => 334470276394147 / 800000000000
    | 12 => 312505518550543 / 800000000000
    | 13 => 223018683821119 / 800000000000
    | 14 => 252879417905001 / 800000000000
    | 15 => 210824494644569 / 800000000000
    | 16 => 186269834683949 / 800000000000
    | 17 => 53988258306951 / 160000000000
    | 18 => 149334363723397 / 800000000000
    | 19 => 126592393961117 / 800000000000
    | 20 => 79215642267551 / 800000000000
    | 21 => 42602435870817 / 800000000000
    | 22 => 115673900743451 / 800000000000
    | 23 => 157942822199227 / 800000000000
    | 24 => 66784357732449 / 800000000000
    | 25 => 271474706425729 / 800000000000
    | _ => 181332522651311 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (51875370826 / 1000000000000) (51875370827 / 1000000000000), orderedInterval (28093781463 / 1000000000000) (28093781464 / 1000000000000))
    | 1 => (orderedInterval (-8556342167 / 1000000000000) (-8556342166 / 1000000000000), orderedInterval (-68251150399 / 1000000000000) (-68251150397 / 1000000000000))
    | 2 => (orderedInterval (-53056490390 / 1000000000000) (-53056490386 / 1000000000000), orderedInterval (-10550815494 / 1000000000000) (-10550815490 / 1000000000000))
    | 3 => (orderedInterval (94223182307 / 1000000000000) (94223274841 / 1000000000000), orderedInterval (-86941268248 / 1000000000000) (-86941175714 / 1000000000000))
    | 4 => (orderedInterval (-47872844161 / 1000000000000) (-47872820147 / 1000000000000), orderedInterval (61465777088 / 1000000000000) (61465801102 / 1000000000000))
    | 5 => (orderedInterval (-39446887767 / 1000000000000) (-39446887766 / 1000000000000), orderedInterval (-25799612574 / 1000000000000) (-25799612573 / 1000000000000))
    | 6 => (orderedInterval (-47146771245 / 1000000000000) (-47146771244 / 1000000000000), orderedInterval (-28139830547 / 1000000000000) (-28139830546 / 1000000000000))
    | 7 => (orderedInterval (-23577425345 / 1000000000000) (-23577425344 / 1000000000000), orderedInterval (-34711196116 / 1000000000000) (-34711196115 / 1000000000000))
    | 8 => (orderedInterval (13049362930 / 1000000000000) (13049363039 / 1000000000000), orderedInterval (-47175364206 / 1000000000000) (-47175364097 / 1000000000000))
    | 9 => (orderedInterval (17550716002 / 1000000000000) (17550716003 / 1000000000000), orderedInterval (35362116208 / 1000000000000) (35362116209 / 1000000000000))
    | 10 => (orderedInterval (-36256959172 / 1000000000000) (-36256959171 / 1000000000000), orderedInterval (-37171948439 / 1000000000000) (-37171948438 / 1000000000000))
    | 11 => (orderedInterval (-33674612496 / 1000000000000) (-33674612495 / 1000000000000), orderedInterval (-19675552635 / 1000000000000) (-19675552634 / 1000000000000))
    | 12 => (orderedInterval (38699137265 / 1000000000000) (38699144588 / 1000000000000), orderedInterval (-11542718172 / 1000000000000) (-11542710849 / 1000000000000))
    | 13 => (orderedInterval (2075312409 / 1000000000000) (2075312412 / 1000000000000), orderedInterval (-47746189189 / 1000000000000) (-47746189185 / 1000000000000))
    | 14 => (orderedInterval (18159114668 / 1000000000000) (18159115209 / 1000000000000), orderedInterval (-41068157071 / 1000000000000) (-41068156531 / 1000000000000))
    | 15 => (orderedInterval (20120375251 / 1000000000000) (20120375252 / 1000000000000), orderedInterval (44804963231 / 1000000000000) (44804963232 / 1000000000000))
    | 16 => (orderedInterval (47605277445 / 1000000000000) (47605277446 / 1000000000000), orderedInterval (21529147806 / 1000000000000) (21529147807 / 1000000000000))
    | 17 => (orderedInterval (-38316226232 / 1000000000000) (-38316187206 / 1000000000000), orderedInterval (20515450623 / 1000000000000) (20515489648 / 1000000000000))
    | 18 => (orderedInterval (-50448254892 / 1000000000000) (-50448227450 / 1000000000000), orderedInterval (29552937832 / 1000000000000) (29552965274 / 1000000000000))
    | 19 => (orderedInterval (59027742907 / 1000000000000) (59027748198 / 1000000000000), orderedInterval (-23399139391 / 1000000000000) (-23399134099 / 1000000000000))
    | 20 => (orderedInterval (-53308010604 / 1000000000000) (-53307966439 / 1000000000000), orderedInterval (60164897458 / 1000000000000) (60164941623 / 1000000000000))
    | 21 => (orderedInterval (-64327485548 / 1000000000000) (-64327485547 / 1000000000000), orderedInterval (-87808482251 / 1000000000000) (-87808482250 / 1000000000000))
    | 22 => (orderedInterval (50443338630 / 1000000000000) (50443338631 / 1000000000000), orderedInterval (42933851347 / 1000000000000) (42933851348 / 1000000000000))
    | 23 => (orderedInterval (-16398581345 / 1000000000000) (-16398581344 / 1000000000000), orderedInterval (-54324390388 / 1000000000000) (-54324390387 / 1000000000000))
    | 24 => (orderedInterval (46286722436 / 1000000000000) (46286732122 / 1000000000000), orderedInterval (-74328379478 / 1000000000000) (-74328369793 / 1000000000000))
    | 25 => (orderedInterval (32148763043 / 1000000000000) (32148763044 / 1000000000000), orderedInterval (28978326012 / 1000000000000) (28978326013 / 1000000000000))
    | _ => (orderedInterval (50389356322 / 1000000000000) (50389356323 / 1000000000000), orderedInterval (16306412250 / 1000000000000) (16306412251 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17368437137 / 1000000000000) (17368437151 / 1000000000000)
      | 1 => orderedInterval (34088225 / 1000000000000) (34090128 / 1000000000000)
      | 2 => orderedInterval (1042599481 / 1000000000000) (1042599495 / 1000000000000)
      | 3 => orderedInterval (-10591937256 / 1000000000000) (-10591937183 / 1000000000000)
      | 4 => orderedInterval (-594287090 / 1000000000000) (-594286932 / 1000000000000)
      | 5 => orderedInterval (-3472995132 / 1000000000000) (-3472994114 / 1000000000000)
      | 6 => orderedInterval (2989865576 / 1000000000000) (2989871747 / 1000000000000)
      | 7 => orderedInterval (1300182217 / 1000000000000) (1300182240 / 1000000000000)
      | _ => orderedInterval (-11792314845 / 1000000000000) (-11792314736 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9929552140 / 1000000000000) (9929552156 / 1000000000000)
      | 1 => orderedInterval (4373587237 / 1000000000000) (4373587985 / 1000000000000)
      | 2 => orderedInterval (456687436 / 1000000000000) (456687458 / 1000000000000)
      | 3 => orderedInterval (-24013346395 / 1000000000000) (-24013346244 / 1000000000000)
      | 4 => orderedInterval (-6090802026 / 1000000000000) (-6090801702 / 1000000000000)
      | 5 => orderedInterval (146443524 / 1000000000000) (146445397 / 1000000000000)
      | 6 => orderedInterval (-2622143104 / 1000000000000) (-2622137533 / 1000000000000)
      | 7 => orderedInterval (4205327297 / 1000000000000) (4205327318 / 1000000000000)
      | _ => orderedInterval (-8391043462 / 1000000000000) (-8391043363 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-16156416335 / 1000000000000) (-16156416317 / 1000000000000)
      | 1 => orderedInterval (-6285375936 / 1000000000000) (-6285375558 / 1000000000000)
      | 2 => orderedInterval (-3519362121 / 1000000000000) (-3519362083 / 1000000000000)
      | 3 => orderedInterval (45324876388 / 1000000000000) (45324876712 / 1000000000000)
      | 4 => orderedInterval (3051978652 / 1000000000000) (3051979327 / 1000000000000)
      | 5 => orderedInterval (7302792650 / 1000000000000) (7302796114 / 1000000000000)
      | 6 => orderedInterval (-5401898155 / 1000000000000) (-5401892845 / 1000000000000)
      | 7 => orderedInterval (-876604246 / 1000000000000) (-876604225 / 1000000000000)
      | _ => orderedInterval (23619634712 / 1000000000000) (23619634830 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9746426617 / 1000000000000) (-9746426597 / 1000000000000)
      | 1 => orderedInterval (-7472155955 / 1000000000000) (-7472155722 / 1000000000000)
      | 2 => orderedInterval (-4744209701 / 1000000000000) (-4744209634 / 1000000000000)
      | 3 => orderedInterval (109556033176 / 1000000000000) (109556033885 / 1000000000000)
      | 4 => orderedInterval (12952225065 / 1000000000000) (12952226480 / 1000000000000)
      | 5 => orderedInterval (-2359307596 / 1000000000000) (-2359301203 / 1000000000000)
      | 6 => orderedInterval (3909823429 / 1000000000000) (3909828618 / 1000000000000)
      | 7 => orderedInterval (-4821838277 / 1000000000000) (-4821838256 / 1000000000000)
      | _ => orderedInterval (20939680724 / 1000000000000) (20939680892 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (14379983410 / 1000000000000) (14379983434 / 1000000000000)
      | 1 => orderedInterval (16820112998 / 1000000000000) (16820113180 / 1000000000000)
      | 2 => orderedInterval (12620264133 / 1000000000000) (12620264253 / 1000000000000)
      | 3 => orderedInterval (-218476901090 / 1000000000000) (-218476899517 / 1000000000000)
      | 4 => orderedInterval (-14565116713 / 1000000000000) (-14565113725 / 1000000000000)
      | 5 => orderedInterval (-17646170919 / 1000000000000) (-17646159080 / 1000000000000)
      | 6 => orderedInterval (6746998202 / 1000000000000) (6747003393 / 1000000000000)
      | 7 => orderedInterval (1331745568 / 1000000000000) (1331745590 / 1000000000000)
      | _ => orderedInterval (-53996239734 / 1000000000000) (-53996239470 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3716361687 / 1000000000000) (-3716352204 / 1000000000000)
    | 1 => orderedInterval (-22005737353 / 1000000000000) (-22005728528 / 1000000000000)
    | 2 => orderedInterval (47059625609 / 1000000000000) (47059635955 / 1000000000000)
    | 3 => orderedInterval (118213824248 / 1000000000000) (118213838463 / 1000000000000)
    | _ => orderedInterval (-252785324145 / 1000000000000) (-252785301942 / 1000000000000)

theorem compactCertificate309_stateChecks0 :
    compactCertificate309.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (365 / 2)) (orderedInterval (51875370826 / 1000000000000) (51875370827 / 1000000000000), orderedInterval (28093781463 / 1000000000000) (28093781464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (107542939196773 / 800000000000)) (orderedInterval (-8556342167 / 1000000000000) (-8556342166 / 1000000000000), orderedInterval (-68251150399 / 1000000000000) (-68251150397 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (34777176927109 / 160000000000)) (orderedInterval (-53056490390 / 1000000000000) (-53056490386 / 1000000000000), orderedInterval (-10550815494 / 1000000000000) (-10550815490 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_stateChecks1 :
    compactCertificate309.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (31380761441711 / 800000000000)) (orderedInterval (94223182307 / 1000000000000) (94223274841 / 1000000000000), orderedInterval (-86941268248 / 1000000000000) (-86941175714 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (84293139301667 / 800000000000)) (orderedInterval (-47872844161 / 1000000000000) (-47872820147 / 1000000000000), orderedInterval (61465777088 / 1000000000000) (61465801102 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (228872270554839 / 800000000000)) (orderedInterval (-39446887767 / 1000000000000) (-39446887766 / 1000000000000), orderedInterval (-25799612574 / 1000000000000) (-25799612573 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_stateChecks2 :
    compactCertificate309.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (168586278603407 / 800000000000)) (orderedInterval (-47146771245 / 1000000000000) (-47146771244 / 1000000000000), orderedInterval (-28139830547 / 1000000000000) (-28139830546 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (288875461848011 / 800000000000)) (orderedInterval (-23577425345 / 1000000000000) (-23577425344 / 1000000000000), orderedInterval (-34711196116 / 1000000000000) (-34711196115 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (212784357732449 / 800000000000)) (orderedInterval (13049362930 / 1000000000000) (13049363039 / 1000000000000), orderedInterval (-47175364206 / 1000000000000) (-47175364097 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_stateChecks3 :
    compactCertificate309.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (326465924714927 / 800000000000)) (orderedInterval (17550716002 / 1000000000000) (17550716003 / 1000000000000), orderedInterval (35362116208 / 1000000000000) (35362116209 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (188485189515383 / 800000000000)) (orderedInterval (-36256959172 / 1000000000000) (-36256959171 / 1000000000000), orderedInterval (-37171948439 / 1000000000000) (-37171948438 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (334470276394147 / 800000000000)) (orderedInterval (-33674612496 / 1000000000000) (-33674612495 / 1000000000000), orderedInterval (-19675552635 / 1000000000000) (-19675552634 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_stateChecks4 :
    compactCertificate309.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (312505518550543 / 800000000000)) (orderedInterval (38699137265 / 1000000000000) (38699144588 / 1000000000000), orderedInterval (-11542718172 / 1000000000000) (-11542710849 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (223018683821119 / 800000000000)) (orderedInterval (2075312409 / 1000000000000) (2075312412 / 1000000000000), orderedInterval (-47746189189 / 1000000000000) (-47746189185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (252879417905001 / 800000000000)) (orderedInterval (18159114668 / 1000000000000) (18159115209 / 1000000000000), orderedInterval (-41068157071 / 1000000000000) (-41068156531 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_stateChecks5 :
    compactCertificate309.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (210824494644569 / 800000000000)) (orderedInterval (20120375251 / 1000000000000) (20120375252 / 1000000000000), orderedInterval (44804963231 / 1000000000000) (44804963232 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (186269834683949 / 800000000000)) (orderedInterval (47605277445 / 1000000000000) (47605277446 / 1000000000000), orderedInterval (21529147806 / 1000000000000) (21529147807 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (53988258306951 / 160000000000)) (orderedInterval (-38316226232 / 1000000000000) (-38316187206 / 1000000000000), orderedInterval (20515450623 / 1000000000000) (20515489648 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_stateChecks6 :
    compactCertificate309.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (149334363723397 / 800000000000)) (orderedInterval (-50448254892 / 1000000000000) (-50448227450 / 1000000000000), orderedInterval (29552937832 / 1000000000000) (29552965274 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (126592393961117 / 800000000000)) (orderedInterval (59027742907 / 1000000000000) (59027748198 / 1000000000000), orderedInterval (-23399139391 / 1000000000000) (-23399134099 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (79215642267551 / 800000000000)) (orderedInterval (-53308010604 / 1000000000000) (-53307966439 / 1000000000000), orderedInterval (60164897458 / 1000000000000) (60164941623 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_stateChecks7 :
    compactCertificate309.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (42602435870817 / 800000000000)) (orderedInterval (-64327485548 / 1000000000000) (-64327485547 / 1000000000000), orderedInterval (-87808482251 / 1000000000000) (-87808482250 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (115673900743451 / 800000000000)) (orderedInterval (50443338630 / 1000000000000) (50443338631 / 1000000000000), orderedInterval (42933851347 / 1000000000000) (42933851348 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (157942822199227 / 800000000000)) (orderedInterval (-16398581345 / 1000000000000) (-16398581344 / 1000000000000), orderedInterval (-54324390388 / 1000000000000) (-54324390387 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_stateChecks8 :
    compactCertificate309.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (66784357732449 / 800000000000)) (orderedInterval (46286722436 / 1000000000000) (46286732122 / 1000000000000), orderedInterval (-74328379478 / 1000000000000) (-74328369793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (271474706425729 / 800000000000)) (orderedInterval (32148763043 / 1000000000000) (32148763044 / 1000000000000), orderedInterval (28978326012 / 1000000000000) (28978326013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (181332522651311 / 800000000000)) (orderedInterval (50389356322 / 1000000000000) (50389356323 / 1000000000000), orderedInterval (16306412250 / 1000000000000) (16306412251 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_states : ∀ j,
    BesselStateValid (compactCertificate309.point j) (compactCertificate309.state j) :=
  compactCertificate309.statesValid_of_checks3 compactCertificate309_stateChecks0
    compactCertificate309_stateChecks1 compactCertificate309_stateChecks2
    compactCertificate309_stateChecks3 compactCertificate309_stateChecks4
    compactCertificate309_stateChecks5 compactCertificate309_stateChecks6
    compactCertificate309_stateChecks7 compactCertificate309_stateChecks8

theorem compactCertificate309_chunkChecks0_0 :
    compactCertificate309.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (365 / 2) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51875370826 / 1000000000000) (51875370827 / 1000000000000), orderedInterval (28093781463 / 1000000000000) (28093781464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (107542939196773 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8556342167 / 1000000000000) (-8556342166 / 1000000000000), orderedInterval (-68251150399 / 1000000000000) (-68251150397 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (34777176927109 / 160000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-53056490390 / 1000000000000) (-53056490386 / 1000000000000), orderedInterval (-10550815494 / 1000000000000) (-10550815490 / 1000000000000)))) (orderedInterval (17368437137 / 1000000000000) (17368437151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (31380761441711 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94223182307 / 1000000000000) (94223274841 / 1000000000000), orderedInterval (-86941268248 / 1000000000000) (-86941175714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (84293139301667 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47872844161 / 1000000000000) (-47872820147 / 1000000000000), orderedInterval (61465777088 / 1000000000000) (61465801102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (228872270554839 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-39446887767 / 1000000000000) (-39446887766 / 1000000000000), orderedInterval (-25799612574 / 1000000000000) (-25799612573 / 1000000000000)))) (orderedInterval (34088225 / 1000000000000) (34090128 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (168586278603407 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47146771245 / 1000000000000) (-47146771244 / 1000000000000), orderedInterval (-28139830547 / 1000000000000) (-28139830546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (288875461848011 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23577425345 / 1000000000000) (-23577425344 / 1000000000000), orderedInterval (-34711196116 / 1000000000000) (-34711196115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (212784357732449 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13049362930 / 1000000000000) (13049363039 / 1000000000000), orderedInterval (-47175364206 / 1000000000000) (-47175364097 / 1000000000000)))) (orderedInterval (1042599481 / 1000000000000) (1042599495 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_chunkChecks0_1 :
    compactCertificate309.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (326465924714927 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17550716002 / 1000000000000) (17550716003 / 1000000000000), orderedInterval (35362116208 / 1000000000000) (35362116209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (188485189515383 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36256959172 / 1000000000000) (-36256959171 / 1000000000000), orderedInterval (-37171948439 / 1000000000000) (-37171948438 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (334470276394147 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33674612496 / 1000000000000) (-33674612495 / 1000000000000), orderedInterval (-19675552635 / 1000000000000) (-19675552634 / 1000000000000)))) (orderedInterval (-10591937256 / 1000000000000) (-10591937183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (312505518550543 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38699137265 / 1000000000000) (38699144588 / 1000000000000), orderedInterval (-11542718172 / 1000000000000) (-11542710849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (223018683821119 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2075312409 / 1000000000000) (2075312412 / 1000000000000), orderedInterval (-47746189189 / 1000000000000) (-47746189185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (252879417905001 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18159114668 / 1000000000000) (18159115209 / 1000000000000), orderedInterval (-41068157071 / 1000000000000) (-41068156531 / 1000000000000)))) (orderedInterval (-594287090 / 1000000000000) (-594286932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (210824494644569 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (20120375251 / 1000000000000) (20120375252 / 1000000000000), orderedInterval (44804963231 / 1000000000000) (44804963232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (186269834683949 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (47605277445 / 1000000000000) (47605277446 / 1000000000000), orderedInterval (21529147806 / 1000000000000) (21529147807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (53988258306951 / 160000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38316226232 / 1000000000000) (-38316187206 / 1000000000000), orderedInterval (20515450623 / 1000000000000) (20515489648 / 1000000000000)))) (orderedInterval (-3472995132 / 1000000000000) (-3472994114 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_chunkChecks0_2 :
    compactCertificate309.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (149334363723397 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50448254892 / 1000000000000) (-50448227450 / 1000000000000), orderedInterval (29552937832 / 1000000000000) (29552965274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (126592393961117 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (59027742907 / 1000000000000) (59027748198 / 1000000000000), orderedInterval (-23399139391 / 1000000000000) (-23399134099 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (79215642267551 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-53308010604 / 1000000000000) (-53307966439 / 1000000000000), orderedInterval (60164897458 / 1000000000000) (60164941623 / 1000000000000)))) (orderedInterval (2989865576 / 1000000000000) (2989871747 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (42602435870817 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64327485548 / 1000000000000) (-64327485547 / 1000000000000), orderedInterval (-87808482251 / 1000000000000) (-87808482250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (115673900743451 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (50443338630 / 1000000000000) (50443338631 / 1000000000000), orderedInterval (42933851347 / 1000000000000) (42933851348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (157942822199227 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16398581345 / 1000000000000) (-16398581344 / 1000000000000), orderedInterval (-54324390388 / 1000000000000) (-54324390387 / 1000000000000)))) (orderedInterval (1300182217 / 1000000000000) (1300182240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (66784357732449 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46286722436 / 1000000000000) (46286732122 / 1000000000000), orderedInterval (-74328379478 / 1000000000000) (-74328369793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (271474706425729 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32148763043 / 1000000000000) (32148763044 / 1000000000000), orderedInterval (28978326012 / 1000000000000) (28978326013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (181332522651311 / 800000000000) 0 (IntervalRat.scale (365 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (50389356322 / 1000000000000) (50389356323 / 1000000000000), orderedInterval (16306412250 / 1000000000000) (16306412251 / 1000000000000)))) (orderedInterval (-11792314845 / 1000000000000) (-11792314736 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_chunkChecks0 :
    compactCertificate309.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate309.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate309_chunkChecks0_0
    compactCertificate309_chunkChecks0_1 compactCertificate309_chunkChecks0_2

theorem compactCertificate309_chunkChecks1_0 :
    compactCertificate309.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (365 / 2) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51875370826 / 1000000000000) (51875370827 / 1000000000000), orderedInterval (28093781463 / 1000000000000) (28093781464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (107542939196773 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8556342167 / 1000000000000) (-8556342166 / 1000000000000), orderedInterval (-68251150399 / 1000000000000) (-68251150397 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (34777176927109 / 160000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-53056490390 / 1000000000000) (-53056490386 / 1000000000000), orderedInterval (-10550815494 / 1000000000000) (-10550815490 / 1000000000000)))) (orderedInterval (9929552140 / 1000000000000) (9929552156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (31380761441711 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94223182307 / 1000000000000) (94223274841 / 1000000000000), orderedInterval (-86941268248 / 1000000000000) (-86941175714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (84293139301667 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47872844161 / 1000000000000) (-47872820147 / 1000000000000), orderedInterval (61465777088 / 1000000000000) (61465801102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (228872270554839 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-39446887767 / 1000000000000) (-39446887766 / 1000000000000), orderedInterval (-25799612574 / 1000000000000) (-25799612573 / 1000000000000)))) (orderedInterval (4373587237 / 1000000000000) (4373587985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (168586278603407 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47146771245 / 1000000000000) (-47146771244 / 1000000000000), orderedInterval (-28139830547 / 1000000000000) (-28139830546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (288875461848011 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23577425345 / 1000000000000) (-23577425344 / 1000000000000), orderedInterval (-34711196116 / 1000000000000) (-34711196115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (212784357732449 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13049362930 / 1000000000000) (13049363039 / 1000000000000), orderedInterval (-47175364206 / 1000000000000) (-47175364097 / 1000000000000)))) (orderedInterval (456687436 / 1000000000000) (456687458 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_chunkChecks1_1 :
    compactCertificate309.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (326465924714927 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17550716002 / 1000000000000) (17550716003 / 1000000000000), orderedInterval (35362116208 / 1000000000000) (35362116209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (188485189515383 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36256959172 / 1000000000000) (-36256959171 / 1000000000000), orderedInterval (-37171948439 / 1000000000000) (-37171948438 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (334470276394147 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33674612496 / 1000000000000) (-33674612495 / 1000000000000), orderedInterval (-19675552635 / 1000000000000) (-19675552634 / 1000000000000)))) (orderedInterval (-24013346395 / 1000000000000) (-24013346244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (312505518550543 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38699137265 / 1000000000000) (38699144588 / 1000000000000), orderedInterval (-11542718172 / 1000000000000) (-11542710849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (223018683821119 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2075312409 / 1000000000000) (2075312412 / 1000000000000), orderedInterval (-47746189189 / 1000000000000) (-47746189185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (252879417905001 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18159114668 / 1000000000000) (18159115209 / 1000000000000), orderedInterval (-41068157071 / 1000000000000) (-41068156531 / 1000000000000)))) (orderedInterval (-6090802026 / 1000000000000) (-6090801702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (210824494644569 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (20120375251 / 1000000000000) (20120375252 / 1000000000000), orderedInterval (44804963231 / 1000000000000) (44804963232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (186269834683949 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (47605277445 / 1000000000000) (47605277446 / 1000000000000), orderedInterval (21529147806 / 1000000000000) (21529147807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (53988258306951 / 160000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38316226232 / 1000000000000) (-38316187206 / 1000000000000), orderedInterval (20515450623 / 1000000000000) (20515489648 / 1000000000000)))) (orderedInterval (146443524 / 1000000000000) (146445397 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_chunkChecks1_2 :
    compactCertificate309.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (149334363723397 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50448254892 / 1000000000000) (-50448227450 / 1000000000000), orderedInterval (29552937832 / 1000000000000) (29552965274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (126592393961117 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (59027742907 / 1000000000000) (59027748198 / 1000000000000), orderedInterval (-23399139391 / 1000000000000) (-23399134099 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (79215642267551 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-53308010604 / 1000000000000) (-53307966439 / 1000000000000), orderedInterval (60164897458 / 1000000000000) (60164941623 / 1000000000000)))) (orderedInterval (-2622143104 / 1000000000000) (-2622137533 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (42602435870817 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64327485548 / 1000000000000) (-64327485547 / 1000000000000), orderedInterval (-87808482251 / 1000000000000) (-87808482250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (115673900743451 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (50443338630 / 1000000000000) (50443338631 / 1000000000000), orderedInterval (42933851347 / 1000000000000) (42933851348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (157942822199227 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16398581345 / 1000000000000) (-16398581344 / 1000000000000), orderedInterval (-54324390388 / 1000000000000) (-54324390387 / 1000000000000)))) (orderedInterval (4205327297 / 1000000000000) (4205327318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (66784357732449 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46286722436 / 1000000000000) (46286732122 / 1000000000000), orderedInterval (-74328379478 / 1000000000000) (-74328369793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (271474706425729 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32148763043 / 1000000000000) (32148763044 / 1000000000000), orderedInterval (28978326012 / 1000000000000) (28978326013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (181332522651311 / 800000000000) 1 (IntervalRat.scale (365 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (50389356322 / 1000000000000) (50389356323 / 1000000000000), orderedInterval (16306412250 / 1000000000000) (16306412251 / 1000000000000)))) (orderedInterval (-8391043462 / 1000000000000) (-8391043363 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_chunkChecks1 :
    compactCertificate309.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate309.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate309_chunkChecks1_0
    compactCertificate309_chunkChecks1_1 compactCertificate309_chunkChecks1_2

theorem compactCertificate309_chunkChecks2_0 :
    compactCertificate309.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (365 / 2) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51875370826 / 1000000000000) (51875370827 / 1000000000000), orderedInterval (28093781463 / 1000000000000) (28093781464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (107542939196773 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8556342167 / 1000000000000) (-8556342166 / 1000000000000), orderedInterval (-68251150399 / 1000000000000) (-68251150397 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (34777176927109 / 160000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-53056490390 / 1000000000000) (-53056490386 / 1000000000000), orderedInterval (-10550815494 / 1000000000000) (-10550815490 / 1000000000000)))) (orderedInterval (-16156416335 / 1000000000000) (-16156416317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (31380761441711 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94223182307 / 1000000000000) (94223274841 / 1000000000000), orderedInterval (-86941268248 / 1000000000000) (-86941175714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (84293139301667 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47872844161 / 1000000000000) (-47872820147 / 1000000000000), orderedInterval (61465777088 / 1000000000000) (61465801102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (228872270554839 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-39446887767 / 1000000000000) (-39446887766 / 1000000000000), orderedInterval (-25799612574 / 1000000000000) (-25799612573 / 1000000000000)))) (orderedInterval (-6285375936 / 1000000000000) (-6285375558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (168586278603407 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47146771245 / 1000000000000) (-47146771244 / 1000000000000), orderedInterval (-28139830547 / 1000000000000) (-28139830546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (288875461848011 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23577425345 / 1000000000000) (-23577425344 / 1000000000000), orderedInterval (-34711196116 / 1000000000000) (-34711196115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (212784357732449 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13049362930 / 1000000000000) (13049363039 / 1000000000000), orderedInterval (-47175364206 / 1000000000000) (-47175364097 / 1000000000000)))) (orderedInterval (-3519362121 / 1000000000000) (-3519362083 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_chunkChecks2_1 :
    compactCertificate309.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (326465924714927 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17550716002 / 1000000000000) (17550716003 / 1000000000000), orderedInterval (35362116208 / 1000000000000) (35362116209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (188485189515383 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36256959172 / 1000000000000) (-36256959171 / 1000000000000), orderedInterval (-37171948439 / 1000000000000) (-37171948438 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (334470276394147 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33674612496 / 1000000000000) (-33674612495 / 1000000000000), orderedInterval (-19675552635 / 1000000000000) (-19675552634 / 1000000000000)))) (orderedInterval (45324876388 / 1000000000000) (45324876712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (312505518550543 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38699137265 / 1000000000000) (38699144588 / 1000000000000), orderedInterval (-11542718172 / 1000000000000) (-11542710849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (223018683821119 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2075312409 / 1000000000000) (2075312412 / 1000000000000), orderedInterval (-47746189189 / 1000000000000) (-47746189185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (252879417905001 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18159114668 / 1000000000000) (18159115209 / 1000000000000), orderedInterval (-41068157071 / 1000000000000) (-41068156531 / 1000000000000)))) (orderedInterval (3051978652 / 1000000000000) (3051979327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (210824494644569 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (20120375251 / 1000000000000) (20120375252 / 1000000000000), orderedInterval (44804963231 / 1000000000000) (44804963232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (186269834683949 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (47605277445 / 1000000000000) (47605277446 / 1000000000000), orderedInterval (21529147806 / 1000000000000) (21529147807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (53988258306951 / 160000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38316226232 / 1000000000000) (-38316187206 / 1000000000000), orderedInterval (20515450623 / 1000000000000) (20515489648 / 1000000000000)))) (orderedInterval (7302792650 / 1000000000000) (7302796114 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_chunkChecks2_2 :
    compactCertificate309.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (149334363723397 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50448254892 / 1000000000000) (-50448227450 / 1000000000000), orderedInterval (29552937832 / 1000000000000) (29552965274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (126592393961117 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (59027742907 / 1000000000000) (59027748198 / 1000000000000), orderedInterval (-23399139391 / 1000000000000) (-23399134099 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (79215642267551 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-53308010604 / 1000000000000) (-53307966439 / 1000000000000), orderedInterval (60164897458 / 1000000000000) (60164941623 / 1000000000000)))) (orderedInterval (-5401898155 / 1000000000000) (-5401892845 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (42602435870817 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64327485548 / 1000000000000) (-64327485547 / 1000000000000), orderedInterval (-87808482251 / 1000000000000) (-87808482250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (115673900743451 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (50443338630 / 1000000000000) (50443338631 / 1000000000000), orderedInterval (42933851347 / 1000000000000) (42933851348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (157942822199227 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16398581345 / 1000000000000) (-16398581344 / 1000000000000), orderedInterval (-54324390388 / 1000000000000) (-54324390387 / 1000000000000)))) (orderedInterval (-876604246 / 1000000000000) (-876604225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (66784357732449 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46286722436 / 1000000000000) (46286732122 / 1000000000000), orderedInterval (-74328379478 / 1000000000000) (-74328369793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (271474706425729 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32148763043 / 1000000000000) (32148763044 / 1000000000000), orderedInterval (28978326012 / 1000000000000) (28978326013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (181332522651311 / 800000000000) 2 (IntervalRat.scale (365 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (50389356322 / 1000000000000) (50389356323 / 1000000000000), orderedInterval (16306412250 / 1000000000000) (16306412251 / 1000000000000)))) (orderedInterval (23619634712 / 1000000000000) (23619634830 / 1000000000000))) = true
  rfl'

theorem compactCertificate309_chunkChecks2 :
    compactCertificate309.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate309.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate309_chunkChecks2_0
    compactCertificate309_chunkChecks2_1 compactCertificate309_chunkChecks2_2

theorem compactCertificate309_chunkChecks3_0 :
    compactCertificate309.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (365 / 2) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51875370826 / 1000000000000) (51875370827 / 1000000000000), orderedInterval (28093781463 / 1000000000000) (28093781464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (107542939196773 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8556342167 / 1000000000000) (-8556342166 / 1000000000000), orderedInterval (-68251150399 / 1000000000000) (-68251150397 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (34777176927109 / 160000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-53056490390 / 1000000000000) (-53056490386 / 1000000000000), orderedInterval (-10550815494 / 1000000000000) (-10550815490 / 1000000000000)))) (orderedInterval (-9746426617 / 1000000000000) (-9746426597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (31380761441711 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94223182307 / 1000000000000) (94223274841 / 1000000000000), orderedInterval (-86941268248 / 1000000000000) (-86941175714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (84293139301667 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47872844161 / 1000000000000) (-47872820147 / 1000000000000), orderedInterval (61465777088 / 1000000000000) (61465801102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (228872270554839 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-39446887767 / 1000000000000) (-39446887766 / 1000000000000), orderedInterval (-25799612574 / 1000000000000) (-25799612573 / 1000000000000)))) (orderedInterval (-7472155955 / 1000000000000) (-7472155722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (168586278603407 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47146771245 / 1000000000000) (-47146771244 / 1000000000000), orderedInterval (-28139830547 / 1000000000000) (-28139830546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (288875461848011 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23577425345 / 1000000000000) (-23577425344 / 1000000000000), orderedInterval (-34711196116 / 1000000000000) (-34711196115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (212784357732449 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13049362930 / 1000000000000) (13049363039 / 1000000000000), orderedInterval (-47175364206 / 1000000000000) (-47175364097 / 1000000000000)))) (orderedInterval (-4744209701 / 1000000000000) (-4744209634 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate309_chunkChecks3_1 :
    compactCertificate309.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (326465924714927 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17550716002 / 1000000000000) (17550716003 / 1000000000000), orderedInterval (35362116208 / 1000000000000) (35362116209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (188485189515383 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36256959172 / 1000000000000) (-36256959171 / 1000000000000), orderedInterval (-37171948439 / 1000000000000) (-37171948438 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (334470276394147 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33674612496 / 1000000000000) (-33674612495 / 1000000000000), orderedInterval (-19675552635 / 1000000000000) (-19675552634 / 1000000000000)))) (orderedInterval (109556033176 / 1000000000000) (109556033885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (312505518550543 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38699137265 / 1000000000000) (38699144588 / 1000000000000), orderedInterval (-11542718172 / 1000000000000) (-11542710849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (223018683821119 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2075312409 / 1000000000000) (2075312412 / 1000000000000), orderedInterval (-47746189189 / 1000000000000) (-47746189185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (252879417905001 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18159114668 / 1000000000000) (18159115209 / 1000000000000), orderedInterval (-41068157071 / 1000000000000) (-41068156531 / 1000000000000)))) (orderedInterval (12952225065 / 1000000000000) (12952226480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (210824494644569 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (20120375251 / 1000000000000) (20120375252 / 1000000000000), orderedInterval (44804963231 / 1000000000000) (44804963232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (186269834683949 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (47605277445 / 1000000000000) (47605277446 / 1000000000000), orderedInterval (21529147806 / 1000000000000) (21529147807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (53988258306951 / 160000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38316226232 / 1000000000000) (-38316187206 / 1000000000000), orderedInterval (20515450623 / 1000000000000) (20515489648 / 1000000000000)))) (orderedInterval (-2359307596 / 1000000000000) (-2359301203 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate309_chunkChecks3_2 :
    compactCertificate309.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (149334363723397 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50448254892 / 1000000000000) (-50448227450 / 1000000000000), orderedInterval (29552937832 / 1000000000000) (29552965274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (126592393961117 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (59027742907 / 1000000000000) (59027748198 / 1000000000000), orderedInterval (-23399139391 / 1000000000000) (-23399134099 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (79215642267551 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-53308010604 / 1000000000000) (-53307966439 / 1000000000000), orderedInterval (60164897458 / 1000000000000) (60164941623 / 1000000000000)))) (orderedInterval (3909823429 / 1000000000000) (3909828618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (42602435870817 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64327485548 / 1000000000000) (-64327485547 / 1000000000000), orderedInterval (-87808482251 / 1000000000000) (-87808482250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (115673900743451 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (50443338630 / 1000000000000) (50443338631 / 1000000000000), orderedInterval (42933851347 / 1000000000000) (42933851348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (157942822199227 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16398581345 / 1000000000000) (-16398581344 / 1000000000000), orderedInterval (-54324390388 / 1000000000000) (-54324390387 / 1000000000000)))) (orderedInterval (-4821838277 / 1000000000000) (-4821838256 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (66784357732449 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46286722436 / 1000000000000) (46286732122 / 1000000000000), orderedInterval (-74328379478 / 1000000000000) (-74328369793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (271474706425729 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32148763043 / 1000000000000) (32148763044 / 1000000000000), orderedInterval (28978326012 / 1000000000000) (28978326013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (181332522651311 / 800000000000) 3 (IntervalRat.scale (365 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (50389356322 / 1000000000000) (50389356323 / 1000000000000), orderedInterval (16306412250 / 1000000000000) (16306412251 / 1000000000000)))) (orderedInterval (20939680724 / 1000000000000) (20939680892 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate309_chunkChecks3 :
    compactCertificate309.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate309.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate309_chunkChecks3_0
    compactCertificate309_chunkChecks3_1 compactCertificate309_chunkChecks3_2

theorem compactCertificate309_chunkChecks4_0 :
    compactCertificate309.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (365 / 2) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51875370826 / 1000000000000) (51875370827 / 1000000000000), orderedInterval (28093781463 / 1000000000000) (28093781464 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (107542939196773 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-8556342167 / 1000000000000) (-8556342166 / 1000000000000), orderedInterval (-68251150399 / 1000000000000) (-68251150397 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (34777176927109 / 160000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-53056490390 / 1000000000000) (-53056490386 / 1000000000000), orderedInterval (-10550815494 / 1000000000000) (-10550815490 / 1000000000000)))) (orderedInterval (14379983410 / 1000000000000) (14379983434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (31380761441711 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (94223182307 / 1000000000000) (94223274841 / 1000000000000), orderedInterval (-86941268248 / 1000000000000) (-86941175714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (84293139301667 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47872844161 / 1000000000000) (-47872820147 / 1000000000000), orderedInterval (61465777088 / 1000000000000) (61465801102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (228872270554839 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-39446887767 / 1000000000000) (-39446887766 / 1000000000000), orderedInterval (-25799612574 / 1000000000000) (-25799612573 / 1000000000000)))) (orderedInterval (16820112998 / 1000000000000) (16820113180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (168586278603407 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-47146771245 / 1000000000000) (-47146771244 / 1000000000000), orderedInterval (-28139830547 / 1000000000000) (-28139830546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (288875461848011 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23577425345 / 1000000000000) (-23577425344 / 1000000000000), orderedInterval (-34711196116 / 1000000000000) (-34711196115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (212784357732449 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (13049362930 / 1000000000000) (13049363039 / 1000000000000), orderedInterval (-47175364206 / 1000000000000) (-47175364097 / 1000000000000)))) (orderedInterval (12620264133 / 1000000000000) (12620264253 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate309_chunkChecks4_1 :
    compactCertificate309.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (326465924714927 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (17550716002 / 1000000000000) (17550716003 / 1000000000000), orderedInterval (35362116208 / 1000000000000) (35362116209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (188485189515383 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-36256959172 / 1000000000000) (-36256959171 / 1000000000000), orderedInterval (-37171948439 / 1000000000000) (-37171948438 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (334470276394147 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33674612496 / 1000000000000) (-33674612495 / 1000000000000), orderedInterval (-19675552635 / 1000000000000) (-19675552634 / 1000000000000)))) (orderedInterval (-218476901090 / 1000000000000) (-218476899517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (312505518550543 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38699137265 / 1000000000000) (38699144588 / 1000000000000), orderedInterval (-11542718172 / 1000000000000) (-11542710849 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (223018683821119 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2075312409 / 1000000000000) (2075312412 / 1000000000000), orderedInterval (-47746189189 / 1000000000000) (-47746189185 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (252879417905001 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18159114668 / 1000000000000) (18159115209 / 1000000000000), orderedInterval (-41068157071 / 1000000000000) (-41068156531 / 1000000000000)))) (orderedInterval (-14565116713 / 1000000000000) (-14565113725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (210824494644569 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (20120375251 / 1000000000000) (20120375252 / 1000000000000), orderedInterval (44804963231 / 1000000000000) (44804963232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (186269834683949 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (47605277445 / 1000000000000) (47605277446 / 1000000000000), orderedInterval (21529147806 / 1000000000000) (21529147807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (53988258306951 / 160000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-38316226232 / 1000000000000) (-38316187206 / 1000000000000), orderedInterval (20515450623 / 1000000000000) (20515489648 / 1000000000000)))) (orderedInterval (-17646170919 / 1000000000000) (-17646159080 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate309_chunkChecks4_2 :
    compactCertificate309.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (149334363723397 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50448254892 / 1000000000000) (-50448227450 / 1000000000000), orderedInterval (29552937832 / 1000000000000) (29552965274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (126592393961117 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (59027742907 / 1000000000000) (59027748198 / 1000000000000), orderedInterval (-23399139391 / 1000000000000) (-23399134099 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (79215642267551 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-53308010604 / 1000000000000) (-53307966439 / 1000000000000), orderedInterval (60164897458 / 1000000000000) (60164941623 / 1000000000000)))) (orderedInterval (6746998202 / 1000000000000) (6747003393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (42602435870817 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-64327485548 / 1000000000000) (-64327485547 / 1000000000000), orderedInterval (-87808482251 / 1000000000000) (-87808482250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (115673900743451 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (50443338630 / 1000000000000) (50443338631 / 1000000000000), orderedInterval (42933851347 / 1000000000000) (42933851348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (157942822199227 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16398581345 / 1000000000000) (-16398581344 / 1000000000000), orderedInterval (-54324390388 / 1000000000000) (-54324390387 / 1000000000000)))) (orderedInterval (1331745568 / 1000000000000) (1331745590 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (66784357732449 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (46286722436 / 1000000000000) (46286732122 / 1000000000000), orderedInterval (-74328379478 / 1000000000000) (-74328369793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (271474706425729 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32148763043 / 1000000000000) (32148763044 / 1000000000000), orderedInterval (28978326012 / 1000000000000) (28978326013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (181332522651311 / 800000000000) 4 (IntervalRat.scale (365 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (50389356322 / 1000000000000) (50389356323 / 1000000000000), orderedInterval (16306412250 / 1000000000000) (16306412251 / 1000000000000)))) (orderedInterval (-53996239734 / 1000000000000) (-53996239470 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate309_chunkChecks4 :
    compactCertificate309.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate309.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate309_chunkChecks4_0
    compactCertificate309_chunkChecks4_1 compactCertificate309_chunkChecks4_2

theorem compactCertificate309_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate309.chunkCheck r b = true :=
  compactCertificate309.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate309_chunkChecks0
    · exact compactCertificate309_chunkChecks1
    · exact compactCertificate309_chunkChecks2
    · exact compactCertificate309_chunkChecks3
    · exact compactCertificate309_chunkChecks4)

theorem compactCertificate309_coefficient0 :
    compactCertificate309.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate309_coefficient1 :
    compactCertificate309.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate309_coefficient2 :
    compactCertificate309.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate309_coefficient3 :
    compactCertificate309.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate309_coefficient4 :
    compactCertificate309.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate309_coefficients : ∀ r : Fin 5,
    compactCertificate309.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate309_coefficient0
  · exact compactCertificate309_coefficient1
  · exact compactCertificate309_coefficient2
  · exact compactCertificate309_coefficient3
  · exact compactCertificate309_coefficient4

theorem compactCertificate309_lower : (1 : ℚ) ≤ compactCertificate309.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate309, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate309_proves {t : ℝ} (ht : t ∈ compactCertificate309.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate309.proves compactCertificate309_states compactCertificate309_chunks
    compactCertificate309_coefficients compactCertificate309_lower ht

end Erdos232
