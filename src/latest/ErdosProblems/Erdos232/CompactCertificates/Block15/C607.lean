/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate607 : CompactCertificate where
  left := 478
  right := 479
  center := 957 / 2
  grid := fun i =>
    match i.val with
    | 0 => 152
    | 1 => 112
    | 2 => 181
    | 3 => 33
    | 4 => 88
    | 5 => 239
    | 6 => 176
    | 7 => 302
    | 8 => 222
    | 9 => 341
    | 10 => 197
    | 11 => 349
    | 12 => 326
    | 13 => 233
    | 14 => 264
    | 15 => 220
    | 16 => 194
    | 17 => 282
    | 18 => 156
    | 19 => 132
    | 20 => 83
    | 21 => 44
    | 22 => 121
    | 23 => 165
    | 24 => 70
    | 25 => 283
    | _ => 189
  point := fun i =>
    match i.val with
    | 0 => 957 / 2
    | 1 => 1409843737141257 / 4000000000000
    | 2 => 455914497523881 / 800000000000
    | 3 => 411388886297499 / 4000000000000
    | 4 => 1105048415228703 / 4000000000000
    | 5 => 3000421409876451 / 4000000000000
    | 6 => 2210096830458363 / 4000000000000
    | 7 => 3787038588884199 / 4000000000000
    | 8 => 2789515484245941 / 4000000000000
    | 9 => 4279834108934043 / 4000000000000
    | 10 => 2470963374879747 / 4000000000000
    | 11 => 4384767869989023 / 4000000000000
    | 12 => 4096818921272187 / 4000000000000
    | 13 => 2923683293380971 / 4000000000000
    | 14 => 3315145245686109 / 4000000000000
    | 15 => 2763822484587021 / 4000000000000
    | 16 => 2441920983459441 / 4000000000000
    | 17 => 707763879448659 / 800000000000
    | 18 => 1957712138127273 / 4000000000000
    | 19 => 1659574260558753 / 4000000000000
    | 20 => 1038484515754059 / 4000000000000
    | 21 => 558500426416053 / 4000000000000
    | 22 => 1516437301527159 / 4000000000000
    | 23 => 2070565491022743 / 4000000000000
    | 24 => 875515484245941 / 4000000000000
    | 25 => 3558921836293461 / 4000000000000
    | _ => 2377194851743899 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (35803264292 / 1000000000000) (35803268553 / 1000000000000), orderedInterval (-7006939173 / 1000000000000) (-7006934912 / 1000000000000))
    | 1 => (orderedInterval (41788387146 / 1000000000000) (41788387160 / 1000000000000), orderedInterval (7682987257 / 1000000000000) (7682987271 / 1000000000000))
    | 2 => (orderedInterval (-29657743884 / 1000000000000) (-29657645613 / 1000000000000), orderedInterval (15437234665 / 1000000000000) (15437332937 / 1000000000000))
    | 3 => (orderedInterval (3236844761 / 1000000000000) (3236844774 / 1000000000000), orderedInterval (-78625860412 / 1000000000000) (-78625860400 / 1000000000000))
    | 4 => (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000))
    | 5 => (orderedInterval (-1454269792 / 1000000000000) (-1454269791 / 1000000000000), orderedInterval (-29095292107 / 1000000000000) (-29095292106 / 1000000000000))
    | 6 => (orderedInterval (12876029931 / 1000000000000) (12876029932 / 1000000000000), orderedInterval (31395523736 / 1000000000000) (31395523737 / 1000000000000))
    | 7 => (orderedInterval (-24316645647 / 1000000000000) (-24316571168 / 1000000000000), orderedInterval (9019583662 / 1000000000000) (9019658141 / 1000000000000))
    | 8 => (orderedInterval (20160402758 / 1000000000000) (20160402759 / 1000000000000), orderedInterval (22489617164 / 1000000000000) (22489617165 / 1000000000000))
    | 9 => (orderedInterval (12526134542 / 1000000000000) (12526134556 / 1000000000000), orderedInterval (-20936472181 / 1000000000000) (-20936472167 / 1000000000000))
    | 10 => (orderedInterval (11540232045 / 1000000000000) (11540232078 / 1000000000000), orderedInterval (-29965717940 / 1000000000000) (-29965717907 / 1000000000000))
    | 11 => (orderedInterval (-12829877911 / 1000000000000) (-12829877910 / 1000000000000), orderedInterval (-20393902746 / 1000000000000) (-20393902745 / 1000000000000))
    | 12 => (orderedInterval (18411138894 / 1000000000000) (18411138895 / 1000000000000), orderedInterval (16801862103 / 1000000000000) (16801862104 / 1000000000000))
    | 13 => (orderedInterval (8298707593 / 1000000000000) (8298707597 / 1000000000000), orderedInterval (-28327308969 / 1000000000000) (-28327308965 / 1000000000000))
    | 14 => (orderedInterval (5264157104 / 1000000000000) (5264157105 / 1000000000000), orderedInterval (27207553285 / 1000000000000) (27207553286 / 1000000000000))
    | 15 => (orderedInterval (16899208128 / 1000000000000) (16899208129 / 1000000000000), orderedInterval (25202412931 / 1000000000000) (25202412932 / 1000000000000))
    | 16 => (orderedInterval (31473893882 / 1000000000000) (31473905775 / 1000000000000), orderedInterval (-7251520965 / 1000000000000) (-7251509072 / 1000000000000))
    | 17 => (orderedInterval (-11402116459 / 1000000000000) (-11402116446 / 1000000000000), orderedInterval (24287633716 / 1000000000000) (24287633729 / 1000000000000))
    | 18 => (orderedInterval (4486593113 / 1000000000000) (4486593114 / 1000000000000), orderedInterval (35781076910 / 1000000000000) (35781076911 / 1000000000000))
    | 19 => (orderedInterval (32714746751 / 1000000000000) (32714746752 / 1000000000000), orderedInterval (21504993447 / 1000000000000) (21504993448 / 1000000000000))
    | 20 => (orderedInterval (16800404325 / 1000000000000) (16800404643 / 1000000000000), orderedInterval (-46614119279 / 1000000000000) (-46614118961 / 1000000000000))
    | 21 => (orderedInterval (55394561946 / 1000000000000) (55394607978 / 1000000000000), orderedInterval (-38810863946 / 1000000000000) (-38810817914 / 1000000000000))
    | 22 => (orderedInterval (9673738724 / 1000000000000) (9673738754 / 1000000000000), orderedInterval (-39833246080 / 1000000000000) (-39833246050 / 1000000000000))
    | 23 => (orderedInterval (-2233851420 / 1000000000000) (-2233851419 / 1000000000000), orderedInterval (-34995808469 / 1000000000000) (-34995808468 / 1000000000000))
    | 24 => (orderedInterval (-13227076038 / 1000000000000) (-13227075926 / 1000000000000), orderedInterval (52314050805 / 1000000000000) (52314050916 / 1000000000000))
    | 25 => (orderedInterval (-26537816164 / 1000000000000) (-26537814909 / 1000000000000), orderedInterval (-3341283010 / 1000000000000) (-3341281755 / 1000000000000))
    | _ => (orderedInterval (-31728766707 / 1000000000000) (-31728766674 / 1000000000000), orderedInterval (-8004295370 / 1000000000000) (-8004295337 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (12840197061 / 1000000000000) (12840204551 / 1000000000000)
      | 1 => orderedInterval (1038883723 / 1000000000000) (1038883781 / 1000000000000)
      | 2 => orderedInterval (1237257490 / 1000000000000) (1237259815 / 1000000000000)
      | 3 => orderedInterval (-3194549474 / 1000000000000) (-3194549279 / 1000000000000)
      | 4 => orderedInterval (425732005 / 1000000000000) (425732062 / 1000000000000)
      | 5 => orderedInterval (-1897939804 / 1000000000000) (-1897939077 / 1000000000000)
      | 6 => orderedInterval (-2022083900 / 1000000000000) (-2022083770 / 1000000000000)
      | 7 => orderedInterval (-1071134874 / 1000000000000) (-1071133966 / 1000000000000)
      | _ => orderedInterval (8033646369 / 1000000000000) (8033646611 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-1645676302 / 1000000000000) (-1645667708 / 1000000000000)
      | 1 => orderedInterval (4267354717 / 1000000000000) (4267354783 / 1000000000000)
      | 2 => orderedInterval (241703962 / 1000000000000) (241708555 / 1000000000000)
      | 3 => orderedInterval (-1189312774 / 1000000000000) (-1189312372 / 1000000000000)
      | 4 => orderedInterval (-4979531051 / 1000000000000) (-4979530958 / 1000000000000)
      | 5 => orderedInterval (2099450681 / 1000000000000) (2099451616 / 1000000000000)
      | 6 => orderedInterval (-7730540142 / 1000000000000) (-7730540025 / 1000000000000)
      | 7 => orderedInterval (3826528912 / 1000000000000) (3826529213 / 1000000000000)
      | _ => orderedInterval (2515256053 / 1000000000000) (2515256438 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11930351490 / 1000000000000) (-11930341560 / 1000000000000)
      | 1 => orderedInterval (-584892581 / 1000000000000) (-584892490 / 1000000000000)
      | 2 => orderedInterval (-3971671898 / 1000000000000) (-3971662812 / 1000000000000)
      | 3 => orderedInterval (19278007783 / 1000000000000) (19278008642 / 1000000000000)
      | 4 => orderedInterval (-217960703 / 1000000000000) (-217960548 / 1000000000000)
      | 5 => orderedInterval (3518451218 / 1000000000000) (3518452428 / 1000000000000)
      | 6 => orderedInterval (1997753397 / 1000000000000) (1997753507 / 1000000000000)
      | 7 => orderedInterval (16505521 / 1000000000000) (16505646 / 1000000000000)
      | _ => orderedInterval (-16640574971 / 1000000000000) (-16640574333 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (1243216675 / 1000000000000) (1243228177 / 1000000000000)
      | 1 => orderedInterval (-8255770445 / 1000000000000) (-8255770309 / 1000000000000)
      | 2 => orderedInterval (480607179 / 1000000000000) (480625143 / 1000000000000)
      | 3 => orderedInterval (-1999656022 / 1000000000000) (-1999654141 / 1000000000000)
      | 4 => orderedInterval (13237966906 / 1000000000000) (13237967167 / 1000000000000)
      | 5 => orderedInterval (-5675844528 / 1000000000000) (-5675842959 / 1000000000000)
      | 6 => orderedInterval (7153753345 / 1000000000000) (7153753450 / 1000000000000)
      | 7 => orderedInterval (-3862778556 / 1000000000000) (-3862778481 / 1000000000000)
      | _ => orderedInterval (-4621246428 / 1000000000000) (-4621245335 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10798812754 / 1000000000000) (10798826153 / 1000000000000)
      | 1 => orderedInterval (766603327 / 1000000000000) (766603535 / 1000000000000)
      | 2 => orderedInterval (13691152211 / 1000000000000) (13691187772 / 1000000000000)
      | 3 => orderedInterval (-103494993344 / 1000000000000) (-103494989172 / 1000000000000)
      | 4 => orderedInterval (-2999286233 / 1000000000000) (-2999285780 / 1000000000000)
      | 5 => orderedInterval (-7311480179 / 1000000000000) (-7311478126 / 1000000000000)
      | 6 => orderedInterval (-1814273018 / 1000000000000) (-1814272915 / 1000000000000)
      | 7 => orderedInterval (156725418 / 1000000000000) (156725480 / 1000000000000)
      | _ => orderedInterval (40004382850 / 1000000000000) (40004384769 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (15390008596 / 1000000000000) (15390020728 / 1000000000000)
    | 1 => orderedInterval (-2594765944 / 1000000000000) (-2594750458 / 1000000000000)
    | 2 => orderedInterval (-8534733724 / 1000000000000) (-8534711520 / 1000000000000)
    | 3 => orderedInterval (-2299751874 / 1000000000000) (-2299717288 / 1000000000000)
    | _ => orderedInterval (-50202356214 / 1000000000000) (-50202298284 / 1000000000000)

theorem compactCertificate607_stateChecks0 :
    compactCertificate607.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (957 / 2)) (orderedInterval (35803264292 / 1000000000000) (35803268553 / 1000000000000), orderedInterval (-7006939173 / 1000000000000) (-7006934912 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1409843737141257 / 4000000000000)) (orderedInterval (41788387146 / 1000000000000) (41788387160 / 1000000000000), orderedInterval (7682987257 / 1000000000000) (7682987271 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (455914497523881 / 800000000000)) (orderedInterval (-29657743884 / 1000000000000) (-29657645613 / 1000000000000), orderedInterval (15437234665 / 1000000000000) (15437332937 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_stateChecks1 :
    compactCertificate607.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (411388886297499 / 4000000000000)) (orderedInterval (3236844761 / 1000000000000) (3236844774 / 1000000000000), orderedInterval (-78625860412 / 1000000000000) (-78625860400 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1105048415228703 / 4000000000000)) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (3000421409876451 / 4000000000000)) (orderedInterval (-1454269792 / 1000000000000) (-1454269791 / 1000000000000), orderedInterval (-29095292107 / 1000000000000) (-29095292106 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_stateChecks2 :
    compactCertificate607.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2210096830458363 / 4000000000000)) (orderedInterval (12876029931 / 1000000000000) (12876029932 / 1000000000000), orderedInterval (31395523736 / 1000000000000) (31395523737 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 302 12 (3787038588884199 / 4000000000000)) (orderedInterval (-24316645647 / 1000000000000) (-24316571168 / 1000000000000), orderedInterval (9019583662 / 1000000000000) (9019658141 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2789515484245941 / 4000000000000)) (orderedInterval (20160402758 / 1000000000000) (20160402759 / 1000000000000), orderedInterval (22489617164 / 1000000000000) (22489617165 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_stateChecks3 :
    compactCertificate607.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 341 12 (4279834108934043 / 4000000000000)) (orderedInterval (12526134542 / 1000000000000) (12526134556 / 1000000000000), orderedInterval (-20936472181 / 1000000000000) (-20936472167 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2470963374879747 / 4000000000000)) (orderedInterval (11540232045 / 1000000000000) (11540232078 / 1000000000000), orderedInterval (-29965717940 / 1000000000000) (-29965717907 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 349 12 (4384767869989023 / 4000000000000)) (orderedInterval (-12829877911 / 1000000000000) (-12829877910 / 1000000000000), orderedInterval (-20393902746 / 1000000000000) (-20393902745 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_stateChecks4 :
    compactCertificate607.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 326 12 (4096818921272187 / 4000000000000)) (orderedInterval (18411138894 / 1000000000000) (18411138895 / 1000000000000), orderedInterval (16801862103 / 1000000000000) (16801862104 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (2923683293380971 / 4000000000000)) (orderedInterval (8298707593 / 1000000000000) (8298707597 / 1000000000000), orderedInterval (-28327308969 / 1000000000000) (-28327308965 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (3315145245686109 / 4000000000000)) (orderedInterval (5264157104 / 1000000000000) (5264157105 / 1000000000000), orderedInterval (27207553285 / 1000000000000) (27207553286 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_stateChecks5 :
    compactCertificate607.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2763822484587021 / 4000000000000)) (orderedInterval (16899208128 / 1000000000000) (16899208129 / 1000000000000), orderedInterval (25202412931 / 1000000000000) (25202412932 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2441920983459441 / 4000000000000)) (orderedInterval (31473893882 / 1000000000000) (31473905775 / 1000000000000), orderedInterval (-7251520965 / 1000000000000) (-7251509072 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 282 12 (707763879448659 / 800000000000)) (orderedInterval (-11402116459 / 1000000000000) (-11402116446 / 1000000000000), orderedInterval (24287633716 / 1000000000000) (24287633729 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_stateChecks6 :
    compactCertificate607.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1957712138127273 / 4000000000000)) (orderedInterval (4486593113 / 1000000000000) (4486593114 / 1000000000000), orderedInterval (35781076910 / 1000000000000) (35781076911 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1659574260558753 / 4000000000000)) (orderedInterval (32714746751 / 1000000000000) (32714746752 / 1000000000000), orderedInterval (21504993447 / 1000000000000) (21504993448 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1038484515754059 / 4000000000000)) (orderedInterval (16800404325 / 1000000000000) (16800404643 / 1000000000000), orderedInterval (-46614119279 / 1000000000000) (-46614118961 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_stateChecks7 :
    compactCertificate607.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (558500426416053 / 4000000000000)) (orderedInterval (55394561946 / 1000000000000) (55394607978 / 1000000000000), orderedInterval (-38810863946 / 1000000000000) (-38810817914 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1516437301527159 / 4000000000000)) (orderedInterval (9673738724 / 1000000000000) (9673738754 / 1000000000000), orderedInterval (-39833246080 / 1000000000000) (-39833246050 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2070565491022743 / 4000000000000)) (orderedInterval (-2233851420 / 1000000000000) (-2233851419 / 1000000000000), orderedInterval (-34995808469 / 1000000000000) (-34995808468 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_stateChecks8 :
    compactCertificate607.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (875515484245941 / 4000000000000)) (orderedInterval (-13227076038 / 1000000000000) (-13227075926 / 1000000000000), orderedInterval (52314050805 / 1000000000000) (52314050916 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 283 12 (3558921836293461 / 4000000000000)) (orderedInterval (-26537816164 / 1000000000000) (-26537814909 / 1000000000000), orderedInterval (-3341283010 / 1000000000000) (-3341281755 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2377194851743899 / 4000000000000)) (orderedInterval (-31728766707 / 1000000000000) (-31728766674 / 1000000000000), orderedInterval (-8004295370 / 1000000000000) (-8004295337 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_states : ∀ j,
    BesselStateValid (compactCertificate607.point j) (compactCertificate607.state j) :=
  compactCertificate607.statesValid_of_checks3 compactCertificate607_stateChecks0
    compactCertificate607_stateChecks1 compactCertificate607_stateChecks2
    compactCertificate607_stateChecks3 compactCertificate607_stateChecks4
    compactCertificate607_stateChecks5 compactCertificate607_stateChecks6
    compactCertificate607_stateChecks7 compactCertificate607_stateChecks8

theorem compactCertificate607_chunkChecks0_0 :
    compactCertificate607.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (957 / 2) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35803264292 / 1000000000000) (35803268553 / 1000000000000), orderedInterval (-7006939173 / 1000000000000) (-7006934912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1409843737141257 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41788387146 / 1000000000000) (41788387160 / 1000000000000), orderedInterval (7682987257 / 1000000000000) (7682987271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (455914497523881 / 800000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29657743884 / 1000000000000) (-29657645613 / 1000000000000), orderedInterval (15437234665 / 1000000000000) (15437332937 / 1000000000000)))) (orderedInterval (12840197061 / 1000000000000) (12840204551 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (411388886297499 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (3236844761 / 1000000000000) (3236844774 / 1000000000000), orderedInterval (-78625860412 / 1000000000000) (-78625860400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1105048415228703 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3000421409876451 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1454269792 / 1000000000000) (-1454269791 / 1000000000000), orderedInterval (-29095292107 / 1000000000000) (-29095292106 / 1000000000000)))) (orderedInterval (1038883723 / 1000000000000) (1038883781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2210096830458363 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12876029931 / 1000000000000) (12876029932 / 1000000000000), orderedInterval (31395523736 / 1000000000000) (31395523737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3787038588884199 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24316645647 / 1000000000000) (-24316571168 / 1000000000000), orderedInterval (9019583662 / 1000000000000) (9019658141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2789515484245941 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (20160402758 / 1000000000000) (20160402759 / 1000000000000), orderedInterval (22489617164 / 1000000000000) (22489617165 / 1000000000000)))) (orderedInterval (1237257490 / 1000000000000) (1237259815 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_chunkChecks0_1 :
    compactCertificate607.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4279834108934043 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12526134542 / 1000000000000) (12526134556 / 1000000000000), orderedInterval (-20936472181 / 1000000000000) (-20936472167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2470963374879747 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11540232045 / 1000000000000) (11540232078 / 1000000000000), orderedInterval (-29965717940 / 1000000000000) (-29965717907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4384767869989023 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12829877911 / 1000000000000) (-12829877910 / 1000000000000), orderedInterval (-20393902746 / 1000000000000) (-20393902745 / 1000000000000)))) (orderedInterval (-3194549474 / 1000000000000) (-3194549279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4096818921272187 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18411138894 / 1000000000000) (18411138895 / 1000000000000), orderedInterval (16801862103 / 1000000000000) (16801862104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2923683293380971 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8298707593 / 1000000000000) (8298707597 / 1000000000000), orderedInterval (-28327308969 / 1000000000000) (-28327308965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3315145245686109 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5264157104 / 1000000000000) (5264157105 / 1000000000000), orderedInterval (27207553285 / 1000000000000) (27207553286 / 1000000000000)))) (orderedInterval (425732005 / 1000000000000) (425732062 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2763822484587021 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16899208128 / 1000000000000) (16899208129 / 1000000000000), orderedInterval (25202412931 / 1000000000000) (25202412932 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2441920983459441 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31473893882 / 1000000000000) (31473905775 / 1000000000000), orderedInterval (-7251520965 / 1000000000000) (-7251509072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (707763879448659 / 800000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11402116459 / 1000000000000) (-11402116446 / 1000000000000), orderedInterval (24287633716 / 1000000000000) (24287633729 / 1000000000000)))) (orderedInterval (-1897939804 / 1000000000000) (-1897939077 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_chunkChecks0_2 :
    compactCertificate607.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1957712138127273 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4486593113 / 1000000000000) (4486593114 / 1000000000000), orderedInterval (35781076910 / 1000000000000) (35781076911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1659574260558753 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32714746751 / 1000000000000) (32714746752 / 1000000000000), orderedInterval (21504993447 / 1000000000000) (21504993448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1038484515754059 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16800404325 / 1000000000000) (16800404643 / 1000000000000), orderedInterval (-46614119279 / 1000000000000) (-46614118961 / 1000000000000)))) (orderedInterval (-2022083900 / 1000000000000) (-2022083770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (558500426416053 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55394561946 / 1000000000000) (55394607978 / 1000000000000), orderedInterval (-38810863946 / 1000000000000) (-38810817914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1516437301527159 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (9673738724 / 1000000000000) (9673738754 / 1000000000000), orderedInterval (-39833246080 / 1000000000000) (-39833246050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2070565491022743 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2233851420 / 1000000000000) (-2233851419 / 1000000000000), orderedInterval (-34995808469 / 1000000000000) (-34995808468 / 1000000000000)))) (orderedInterval (-1071134874 / 1000000000000) (-1071133966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (875515484245941 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13227076038 / 1000000000000) (-13227075926 / 1000000000000), orderedInterval (52314050805 / 1000000000000) (52314050916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3558921836293461 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26537816164 / 1000000000000) (-26537814909 / 1000000000000), orderedInterval (-3341283010 / 1000000000000) (-3341281755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2377194851743899 / 4000000000000) 0 (IntervalRat.scale (957 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31728766707 / 1000000000000) (-31728766674 / 1000000000000), orderedInterval (-8004295370 / 1000000000000) (-8004295337 / 1000000000000)))) (orderedInterval (8033646369 / 1000000000000) (8033646611 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_chunkChecks0 :
    compactCertificate607.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate607.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate607_chunkChecks0_0
    compactCertificate607_chunkChecks0_1 compactCertificate607_chunkChecks0_2

theorem compactCertificate607_chunkChecks1_0 :
    compactCertificate607.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (957 / 2) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35803264292 / 1000000000000) (35803268553 / 1000000000000), orderedInterval (-7006939173 / 1000000000000) (-7006934912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1409843737141257 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41788387146 / 1000000000000) (41788387160 / 1000000000000), orderedInterval (7682987257 / 1000000000000) (7682987271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (455914497523881 / 800000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29657743884 / 1000000000000) (-29657645613 / 1000000000000), orderedInterval (15437234665 / 1000000000000) (15437332937 / 1000000000000)))) (orderedInterval (-1645676302 / 1000000000000) (-1645667708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (411388886297499 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (3236844761 / 1000000000000) (3236844774 / 1000000000000), orderedInterval (-78625860412 / 1000000000000) (-78625860400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1105048415228703 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3000421409876451 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1454269792 / 1000000000000) (-1454269791 / 1000000000000), orderedInterval (-29095292107 / 1000000000000) (-29095292106 / 1000000000000)))) (orderedInterval (4267354717 / 1000000000000) (4267354783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2210096830458363 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12876029931 / 1000000000000) (12876029932 / 1000000000000), orderedInterval (31395523736 / 1000000000000) (31395523737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3787038588884199 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24316645647 / 1000000000000) (-24316571168 / 1000000000000), orderedInterval (9019583662 / 1000000000000) (9019658141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2789515484245941 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (20160402758 / 1000000000000) (20160402759 / 1000000000000), orderedInterval (22489617164 / 1000000000000) (22489617165 / 1000000000000)))) (orderedInterval (241703962 / 1000000000000) (241708555 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_chunkChecks1_1 :
    compactCertificate607.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4279834108934043 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12526134542 / 1000000000000) (12526134556 / 1000000000000), orderedInterval (-20936472181 / 1000000000000) (-20936472167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2470963374879747 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11540232045 / 1000000000000) (11540232078 / 1000000000000), orderedInterval (-29965717940 / 1000000000000) (-29965717907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4384767869989023 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12829877911 / 1000000000000) (-12829877910 / 1000000000000), orderedInterval (-20393902746 / 1000000000000) (-20393902745 / 1000000000000)))) (orderedInterval (-1189312774 / 1000000000000) (-1189312372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4096818921272187 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18411138894 / 1000000000000) (18411138895 / 1000000000000), orderedInterval (16801862103 / 1000000000000) (16801862104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2923683293380971 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8298707593 / 1000000000000) (8298707597 / 1000000000000), orderedInterval (-28327308969 / 1000000000000) (-28327308965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3315145245686109 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5264157104 / 1000000000000) (5264157105 / 1000000000000), orderedInterval (27207553285 / 1000000000000) (27207553286 / 1000000000000)))) (orderedInterval (-4979531051 / 1000000000000) (-4979530958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2763822484587021 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16899208128 / 1000000000000) (16899208129 / 1000000000000), orderedInterval (25202412931 / 1000000000000) (25202412932 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2441920983459441 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31473893882 / 1000000000000) (31473905775 / 1000000000000), orderedInterval (-7251520965 / 1000000000000) (-7251509072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (707763879448659 / 800000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11402116459 / 1000000000000) (-11402116446 / 1000000000000), orderedInterval (24287633716 / 1000000000000) (24287633729 / 1000000000000)))) (orderedInterval (2099450681 / 1000000000000) (2099451616 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_chunkChecks1_2 :
    compactCertificate607.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1957712138127273 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4486593113 / 1000000000000) (4486593114 / 1000000000000), orderedInterval (35781076910 / 1000000000000) (35781076911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1659574260558753 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32714746751 / 1000000000000) (32714746752 / 1000000000000), orderedInterval (21504993447 / 1000000000000) (21504993448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1038484515754059 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16800404325 / 1000000000000) (16800404643 / 1000000000000), orderedInterval (-46614119279 / 1000000000000) (-46614118961 / 1000000000000)))) (orderedInterval (-7730540142 / 1000000000000) (-7730540025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (558500426416053 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55394561946 / 1000000000000) (55394607978 / 1000000000000), orderedInterval (-38810863946 / 1000000000000) (-38810817914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1516437301527159 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (9673738724 / 1000000000000) (9673738754 / 1000000000000), orderedInterval (-39833246080 / 1000000000000) (-39833246050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2070565491022743 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2233851420 / 1000000000000) (-2233851419 / 1000000000000), orderedInterval (-34995808469 / 1000000000000) (-34995808468 / 1000000000000)))) (orderedInterval (3826528912 / 1000000000000) (3826529213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (875515484245941 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13227076038 / 1000000000000) (-13227075926 / 1000000000000), orderedInterval (52314050805 / 1000000000000) (52314050916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3558921836293461 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26537816164 / 1000000000000) (-26537814909 / 1000000000000), orderedInterval (-3341283010 / 1000000000000) (-3341281755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2377194851743899 / 4000000000000) 1 (IntervalRat.scale (957 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31728766707 / 1000000000000) (-31728766674 / 1000000000000), orderedInterval (-8004295370 / 1000000000000) (-8004295337 / 1000000000000)))) (orderedInterval (2515256053 / 1000000000000) (2515256438 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_chunkChecks1 :
    compactCertificate607.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate607.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate607_chunkChecks1_0
    compactCertificate607_chunkChecks1_1 compactCertificate607_chunkChecks1_2

theorem compactCertificate607_chunkChecks2_0 :
    compactCertificate607.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (957 / 2) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35803264292 / 1000000000000) (35803268553 / 1000000000000), orderedInterval (-7006939173 / 1000000000000) (-7006934912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1409843737141257 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41788387146 / 1000000000000) (41788387160 / 1000000000000), orderedInterval (7682987257 / 1000000000000) (7682987271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (455914497523881 / 800000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29657743884 / 1000000000000) (-29657645613 / 1000000000000), orderedInterval (15437234665 / 1000000000000) (15437332937 / 1000000000000)))) (orderedInterval (-11930351490 / 1000000000000) (-11930341560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (411388886297499 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (3236844761 / 1000000000000) (3236844774 / 1000000000000), orderedInterval (-78625860412 / 1000000000000) (-78625860400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1105048415228703 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3000421409876451 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1454269792 / 1000000000000) (-1454269791 / 1000000000000), orderedInterval (-29095292107 / 1000000000000) (-29095292106 / 1000000000000)))) (orderedInterval (-584892581 / 1000000000000) (-584892490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2210096830458363 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12876029931 / 1000000000000) (12876029932 / 1000000000000), orderedInterval (31395523736 / 1000000000000) (31395523737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3787038588884199 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24316645647 / 1000000000000) (-24316571168 / 1000000000000), orderedInterval (9019583662 / 1000000000000) (9019658141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2789515484245941 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (20160402758 / 1000000000000) (20160402759 / 1000000000000), orderedInterval (22489617164 / 1000000000000) (22489617165 / 1000000000000)))) (orderedInterval (-3971671898 / 1000000000000) (-3971662812 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_chunkChecks2_1 :
    compactCertificate607.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4279834108934043 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12526134542 / 1000000000000) (12526134556 / 1000000000000), orderedInterval (-20936472181 / 1000000000000) (-20936472167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2470963374879747 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11540232045 / 1000000000000) (11540232078 / 1000000000000), orderedInterval (-29965717940 / 1000000000000) (-29965717907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4384767869989023 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12829877911 / 1000000000000) (-12829877910 / 1000000000000), orderedInterval (-20393902746 / 1000000000000) (-20393902745 / 1000000000000)))) (orderedInterval (19278007783 / 1000000000000) (19278008642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4096818921272187 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18411138894 / 1000000000000) (18411138895 / 1000000000000), orderedInterval (16801862103 / 1000000000000) (16801862104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2923683293380971 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8298707593 / 1000000000000) (8298707597 / 1000000000000), orderedInterval (-28327308969 / 1000000000000) (-28327308965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3315145245686109 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5264157104 / 1000000000000) (5264157105 / 1000000000000), orderedInterval (27207553285 / 1000000000000) (27207553286 / 1000000000000)))) (orderedInterval (-217960703 / 1000000000000) (-217960548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2763822484587021 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16899208128 / 1000000000000) (16899208129 / 1000000000000), orderedInterval (25202412931 / 1000000000000) (25202412932 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2441920983459441 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31473893882 / 1000000000000) (31473905775 / 1000000000000), orderedInterval (-7251520965 / 1000000000000) (-7251509072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (707763879448659 / 800000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11402116459 / 1000000000000) (-11402116446 / 1000000000000), orderedInterval (24287633716 / 1000000000000) (24287633729 / 1000000000000)))) (orderedInterval (3518451218 / 1000000000000) (3518452428 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_chunkChecks2_2 :
    compactCertificate607.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1957712138127273 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4486593113 / 1000000000000) (4486593114 / 1000000000000), orderedInterval (35781076910 / 1000000000000) (35781076911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1659574260558753 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32714746751 / 1000000000000) (32714746752 / 1000000000000), orderedInterval (21504993447 / 1000000000000) (21504993448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1038484515754059 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16800404325 / 1000000000000) (16800404643 / 1000000000000), orderedInterval (-46614119279 / 1000000000000) (-46614118961 / 1000000000000)))) (orderedInterval (1997753397 / 1000000000000) (1997753507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (558500426416053 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55394561946 / 1000000000000) (55394607978 / 1000000000000), orderedInterval (-38810863946 / 1000000000000) (-38810817914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1516437301527159 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (9673738724 / 1000000000000) (9673738754 / 1000000000000), orderedInterval (-39833246080 / 1000000000000) (-39833246050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2070565491022743 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2233851420 / 1000000000000) (-2233851419 / 1000000000000), orderedInterval (-34995808469 / 1000000000000) (-34995808468 / 1000000000000)))) (orderedInterval (16505521 / 1000000000000) (16505646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (875515484245941 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13227076038 / 1000000000000) (-13227075926 / 1000000000000), orderedInterval (52314050805 / 1000000000000) (52314050916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3558921836293461 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26537816164 / 1000000000000) (-26537814909 / 1000000000000), orderedInterval (-3341283010 / 1000000000000) (-3341281755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2377194851743899 / 4000000000000) 2 (IntervalRat.scale (957 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31728766707 / 1000000000000) (-31728766674 / 1000000000000), orderedInterval (-8004295370 / 1000000000000) (-8004295337 / 1000000000000)))) (orderedInterval (-16640574971 / 1000000000000) (-16640574333 / 1000000000000))) = true
  rfl'

theorem compactCertificate607_chunkChecks2 :
    compactCertificate607.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate607.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate607_chunkChecks2_0
    compactCertificate607_chunkChecks2_1 compactCertificate607_chunkChecks2_2

theorem compactCertificate607_chunkChecks3_0 :
    compactCertificate607.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (957 / 2) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35803264292 / 1000000000000) (35803268553 / 1000000000000), orderedInterval (-7006939173 / 1000000000000) (-7006934912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1409843737141257 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41788387146 / 1000000000000) (41788387160 / 1000000000000), orderedInterval (7682987257 / 1000000000000) (7682987271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (455914497523881 / 800000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29657743884 / 1000000000000) (-29657645613 / 1000000000000), orderedInterval (15437234665 / 1000000000000) (15437332937 / 1000000000000)))) (orderedInterval (1243216675 / 1000000000000) (1243228177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (411388886297499 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (3236844761 / 1000000000000) (3236844774 / 1000000000000), orderedInterval (-78625860412 / 1000000000000) (-78625860400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1105048415228703 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3000421409876451 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1454269792 / 1000000000000) (-1454269791 / 1000000000000), orderedInterval (-29095292107 / 1000000000000) (-29095292106 / 1000000000000)))) (orderedInterval (-8255770445 / 1000000000000) (-8255770309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2210096830458363 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12876029931 / 1000000000000) (12876029932 / 1000000000000), orderedInterval (31395523736 / 1000000000000) (31395523737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3787038588884199 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24316645647 / 1000000000000) (-24316571168 / 1000000000000), orderedInterval (9019583662 / 1000000000000) (9019658141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2789515484245941 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (20160402758 / 1000000000000) (20160402759 / 1000000000000), orderedInterval (22489617164 / 1000000000000) (22489617165 / 1000000000000)))) (orderedInterval (480607179 / 1000000000000) (480625143 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate607_chunkChecks3_1 :
    compactCertificate607.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4279834108934043 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12526134542 / 1000000000000) (12526134556 / 1000000000000), orderedInterval (-20936472181 / 1000000000000) (-20936472167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2470963374879747 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11540232045 / 1000000000000) (11540232078 / 1000000000000), orderedInterval (-29965717940 / 1000000000000) (-29965717907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4384767869989023 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12829877911 / 1000000000000) (-12829877910 / 1000000000000), orderedInterval (-20393902746 / 1000000000000) (-20393902745 / 1000000000000)))) (orderedInterval (-1999656022 / 1000000000000) (-1999654141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4096818921272187 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18411138894 / 1000000000000) (18411138895 / 1000000000000), orderedInterval (16801862103 / 1000000000000) (16801862104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2923683293380971 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8298707593 / 1000000000000) (8298707597 / 1000000000000), orderedInterval (-28327308969 / 1000000000000) (-28327308965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3315145245686109 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5264157104 / 1000000000000) (5264157105 / 1000000000000), orderedInterval (27207553285 / 1000000000000) (27207553286 / 1000000000000)))) (orderedInterval (13237966906 / 1000000000000) (13237967167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2763822484587021 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16899208128 / 1000000000000) (16899208129 / 1000000000000), orderedInterval (25202412931 / 1000000000000) (25202412932 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2441920983459441 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31473893882 / 1000000000000) (31473905775 / 1000000000000), orderedInterval (-7251520965 / 1000000000000) (-7251509072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (707763879448659 / 800000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11402116459 / 1000000000000) (-11402116446 / 1000000000000), orderedInterval (24287633716 / 1000000000000) (24287633729 / 1000000000000)))) (orderedInterval (-5675844528 / 1000000000000) (-5675842959 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate607_chunkChecks3_2 :
    compactCertificate607.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1957712138127273 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4486593113 / 1000000000000) (4486593114 / 1000000000000), orderedInterval (35781076910 / 1000000000000) (35781076911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1659574260558753 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32714746751 / 1000000000000) (32714746752 / 1000000000000), orderedInterval (21504993447 / 1000000000000) (21504993448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1038484515754059 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16800404325 / 1000000000000) (16800404643 / 1000000000000), orderedInterval (-46614119279 / 1000000000000) (-46614118961 / 1000000000000)))) (orderedInterval (7153753345 / 1000000000000) (7153753450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (558500426416053 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55394561946 / 1000000000000) (55394607978 / 1000000000000), orderedInterval (-38810863946 / 1000000000000) (-38810817914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1516437301527159 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (9673738724 / 1000000000000) (9673738754 / 1000000000000), orderedInterval (-39833246080 / 1000000000000) (-39833246050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2070565491022743 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2233851420 / 1000000000000) (-2233851419 / 1000000000000), orderedInterval (-34995808469 / 1000000000000) (-34995808468 / 1000000000000)))) (orderedInterval (-3862778556 / 1000000000000) (-3862778481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (875515484245941 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13227076038 / 1000000000000) (-13227075926 / 1000000000000), orderedInterval (52314050805 / 1000000000000) (52314050916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3558921836293461 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26537816164 / 1000000000000) (-26537814909 / 1000000000000), orderedInterval (-3341283010 / 1000000000000) (-3341281755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2377194851743899 / 4000000000000) 3 (IntervalRat.scale (957 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31728766707 / 1000000000000) (-31728766674 / 1000000000000), orderedInterval (-8004295370 / 1000000000000) (-8004295337 / 1000000000000)))) (orderedInterval (-4621246428 / 1000000000000) (-4621245335 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate607_chunkChecks3 :
    compactCertificate607.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate607.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate607_chunkChecks3_0
    compactCertificate607_chunkChecks3_1 compactCertificate607_chunkChecks3_2

theorem compactCertificate607_chunkChecks4_0 :
    compactCertificate607.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (957 / 2) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35803264292 / 1000000000000) (35803268553 / 1000000000000), orderedInterval (-7006939173 / 1000000000000) (-7006934912 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1409843737141257 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (41788387146 / 1000000000000) (41788387160 / 1000000000000), orderedInterval (7682987257 / 1000000000000) (7682987271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (455914497523881 / 800000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29657743884 / 1000000000000) (-29657645613 / 1000000000000), orderedInterval (15437234665 / 1000000000000) (15437332937 / 1000000000000)))) (orderedInterval (10798812754 / 1000000000000) (10798826153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (411388886297499 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (3236844761 / 1000000000000) (3236844774 / 1000000000000), orderedInterval (-78625860412 / 1000000000000) (-78625860400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1105048415228703 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (26583711054 / 1000000000000) (26583711055 / 1000000000000), orderedInterval (39923286256 / 1000000000000) (39923286257 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3000421409876451 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-1454269792 / 1000000000000) (-1454269791 / 1000000000000), orderedInterval (-29095292107 / 1000000000000) (-29095292106 / 1000000000000)))) (orderedInterval (766603327 / 1000000000000) (766603535 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2210096830458363 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (12876029931 / 1000000000000) (12876029932 / 1000000000000), orderedInterval (31395523736 / 1000000000000) (31395523737 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3787038588884199 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24316645647 / 1000000000000) (-24316571168 / 1000000000000), orderedInterval (9019583662 / 1000000000000) (9019658141 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2789515484245941 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (20160402758 / 1000000000000) (20160402759 / 1000000000000), orderedInterval (22489617164 / 1000000000000) (22489617165 / 1000000000000)))) (orderedInterval (13691152211 / 1000000000000) (13691187772 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate607_chunkChecks4_1 :
    compactCertificate607.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4279834108934043 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12526134542 / 1000000000000) (12526134556 / 1000000000000), orderedInterval (-20936472181 / 1000000000000) (-20936472167 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2470963374879747 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (11540232045 / 1000000000000) (11540232078 / 1000000000000), orderedInterval (-29965717940 / 1000000000000) (-29965717907 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4384767869989023 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-12829877911 / 1000000000000) (-12829877910 / 1000000000000), orderedInterval (-20393902746 / 1000000000000) (-20393902745 / 1000000000000)))) (orderedInterval (-103494993344 / 1000000000000) (-103494989172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4096818921272187 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18411138894 / 1000000000000) (18411138895 / 1000000000000), orderedInterval (16801862103 / 1000000000000) (16801862104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2923683293380971 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8298707593 / 1000000000000) (8298707597 / 1000000000000), orderedInterval (-28327308969 / 1000000000000) (-28327308965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3315145245686109 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (5264157104 / 1000000000000) (5264157105 / 1000000000000), orderedInterval (27207553285 / 1000000000000) (27207553286 / 1000000000000)))) (orderedInterval (-2999286233 / 1000000000000) (-2999285780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2763822484587021 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16899208128 / 1000000000000) (16899208129 / 1000000000000), orderedInterval (25202412931 / 1000000000000) (25202412932 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2441920983459441 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (31473893882 / 1000000000000) (31473905775 / 1000000000000), orderedInterval (-7251520965 / 1000000000000) (-7251509072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (707763879448659 / 800000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11402116459 / 1000000000000) (-11402116446 / 1000000000000), orderedInterval (24287633716 / 1000000000000) (24287633729 / 1000000000000)))) (orderedInterval (-7311480179 / 1000000000000) (-7311478126 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate607_chunkChecks4_2 :
    compactCertificate607.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1957712138127273 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4486593113 / 1000000000000) (4486593114 / 1000000000000), orderedInterval (35781076910 / 1000000000000) (35781076911 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1659574260558753 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (32714746751 / 1000000000000) (32714746752 / 1000000000000), orderedInterval (21504993447 / 1000000000000) (21504993448 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1038484515754059 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16800404325 / 1000000000000) (16800404643 / 1000000000000), orderedInterval (-46614119279 / 1000000000000) (-46614118961 / 1000000000000)))) (orderedInterval (-1814273018 / 1000000000000) (-1814272915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (558500426416053 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55394561946 / 1000000000000) (55394607978 / 1000000000000), orderedInterval (-38810863946 / 1000000000000) (-38810817914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1516437301527159 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (9673738724 / 1000000000000) (9673738754 / 1000000000000), orderedInterval (-39833246080 / 1000000000000) (-39833246050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2070565491022743 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-2233851420 / 1000000000000) (-2233851419 / 1000000000000), orderedInterval (-34995808469 / 1000000000000) (-34995808468 / 1000000000000)))) (orderedInterval (156725418 / 1000000000000) (156725480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (875515484245941 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13227076038 / 1000000000000) (-13227075926 / 1000000000000), orderedInterval (52314050805 / 1000000000000) (52314050916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3558921836293461 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-26537816164 / 1000000000000) (-26537814909 / 1000000000000), orderedInterval (-3341283010 / 1000000000000) (-3341281755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2377194851743899 / 4000000000000) 4 (IntervalRat.scale (957 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31728766707 / 1000000000000) (-31728766674 / 1000000000000), orderedInterval (-8004295370 / 1000000000000) (-8004295337 / 1000000000000)))) (orderedInterval (40004382850 / 1000000000000) (40004384769 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate607_chunkChecks4 :
    compactCertificate607.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate607.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate607_chunkChecks4_0
    compactCertificate607_chunkChecks4_1 compactCertificate607_chunkChecks4_2

theorem compactCertificate607_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate607.chunkCheck r b = true :=
  compactCertificate607.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate607_chunkChecks0
    · exact compactCertificate607_chunkChecks1
    · exact compactCertificate607_chunkChecks2
    · exact compactCertificate607_chunkChecks3
    · exact compactCertificate607_chunkChecks4)

theorem compactCertificate607_coefficient0 :
    compactCertificate607.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate607_coefficient1 :
    compactCertificate607.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate607_coefficient2 :
    compactCertificate607.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate607_coefficient3 :
    compactCertificate607.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate607_coefficient4 :
    compactCertificate607.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate607_coefficients : ∀ r : Fin 5,
    compactCertificate607.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate607_coefficient0
  · exact compactCertificate607_coefficient1
  · exact compactCertificate607_coefficient2
  · exact compactCertificate607_coefficient3
  · exact compactCertificate607_coefficient4

theorem compactCertificate607_lower : (1 : ℚ) ≤ compactCertificate607.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate607, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate607_proves {t : ℝ} (ht : t ∈ compactCertificate607.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate607.proves compactCertificate607_states compactCertificate607_chunks
    compactCertificate607_coefficients compactCertificate607_lower ht

end Erdos232
