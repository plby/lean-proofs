/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate575 : CompactCertificate where
  left := 446
  right := 447
  center := 893 / 2
  grid := fun i =>
    match i.val with
    | 0 => 142
    | 1 => 105
    | 2 => 169
    | 3 => 31
    | 4 => 82
    | 5 => 223
    | 6 => 164
    | 7 => 281
    | 8 => 207
    | 9 => 318
    | 10 => 184
    | 11 => 326
    | 12 => 304
    | 13 => 217
    | 14 => 246
    | 15 => 205
    | 16 => 181
    | 17 => 263
    | 18 => 145
    | 19 => 123
    | 20 => 77
    | 21 => 41
    | 22 => 113
    | 23 => 154
    | 24 => 65
    | 25 => 264
    | _ => 177
  point := fun i =>
    match i.val with
    | 0 => 893 / 2
    | 1 => 1315559516475593 / 4000000000000
    | 2 => 425424917752169 / 800000000000
    | 3 => 383876985855451 / 4000000000000
    | 4 => 1031147580772447 / 4000000000000
    | 5 => 2799766268568099 / 4000000000000
    | 6 => 2062295161545787 / 4000000000000
    | 7 => 3533777910003751 / 4000000000000
    | 8 => 2602964814453109 / 4000000000000
    | 9 => 3993617407814107 / 4000000000000
    | 10 => 2305716085441603 / 4000000000000
    | 11 => 4091533655068127 / 4000000000000
    | 12 => 3822841480351163 / 4000000000000
    | 13 => 2728160063729579 / 4000000000000
    | 14 => 3093442742317341 / 4000000000000
    | 15 => 2578990050926029 / 4000000000000
    | 16 => 2278615922914609 / 4000000000000
    | 17 => 660431707782291 / 800000000000
    | 18 => 1826788860342377 / 4000000000000
    | 19 => 1548589148044897 / 4000000000000
    | 20 => 969035185546891 / 4000000000000
    | 21 => 521150345652597 / 4000000000000
    | 22 => 1415024566628791 / 4000000000000
    | 23 => 1932095071560407 / 4000000000000
    | 24 => 816964814453109 / 4000000000000
    | 25 => 3320916614221589 / 4000000000000
    | _ => 2218218393529051 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (34897940910 / 1000000000000) (34897940911 / 1000000000000), orderedInterval (14380811351 / 1000000000000) (14380811352 / 1000000000000))
    | 1 => (orderedInterval (8409766451 / 1000000000000) (8409766472 / 1000000000000), orderedInterval (-43197739620 / 1000000000000) (-43197739598 / 1000000000000))
    | 2 => (orderedInterval (-34523648994 / 1000000000000) (-34523647572 / 1000000000000), orderedInterval (2326663148 / 1000000000000) (2326664569 / 1000000000000))
    | 3 => (orderedInterval (48379587085 / 1000000000000) (48379606460 / 1000000000000), orderedInterval (-65773217638 / 1000000000000) (-65773198263 / 1000000000000))
    | 4 => (orderedInterval (40743881622 / 1000000000000) (40743881623 / 1000000000000), orderedInterval (28372561535 / 1000000000000) (28372561536 / 1000000000000))
    | 5 => (orderedInterval (-4555273733 / 1000000000000) (-4555273732 / 1000000000000), orderedInterval (-29809200476 / 1000000000000) (-29809200475 / 1000000000000))
    | 6 => (orderedInterval (31895766830 / 1000000000000) (31895766831 / 1000000000000), orderedInterval (14714875377 / 1000000000000) (14714875378 / 1000000000000))
    | 7 => (orderedInterval (-26622535451 / 1000000000000) (-26622534281 / 1000000000000), orderedInterval (-3427531597 / 1000000000000) (-3427530428 / 1000000000000))
    | 8 => (orderedInterval (-29337637704 / 1000000000000) (-29337637693 / 1000000000000), orderedInterval (-10821915949 / 1000000000000) (-10821915938 / 1000000000000))
    | 9 => (orderedInterval (4101802235 / 1000000000000) (4101802236 / 1000000000000), orderedInterval (24914055291 / 1000000000000) (24914055292 / 1000000000000))
    | 10 => (orderedInterval (-24720966265 / 1000000000000) (-24720953052 / 1000000000000), orderedInterval (22231662866 / 1000000000000) (22231676079 / 1000000000000))
    | 11 => (orderedInterval (-11752279795 / 1000000000000) (-11752279786 / 1000000000000), orderedInterval (22011689514 / 1000000000000) (22011689524 / 1000000000000))
    | 12 => (orderedInterval (25625811646 / 1000000000000) (25625813632 / 1000000000000), orderedInterval (3059003319 / 1000000000000) (3059005304 / 1000000000000))
    | 13 => (orderedInterval (-27222681937 / 1000000000000) (-27222681934 / 1000000000000), orderedInterval (-13848379464 / 1000000000000) (-13848379461 / 1000000000000))
    | 14 => (orderedInterval (27751334560 / 1000000000000) (27751334671 / 1000000000000), orderedInterval (7265558755 / 1000000000000) (7265558866 / 1000000000000))
    | 15 => (orderedInterval (-31357331083 / 1000000000000) (-31357330495 / 1000000000000), orderedInterval (-2003348513 / 1000000000000) (-2003347924 / 1000000000000))
    | 16 => (orderedInterval (-32470949027 / 1000000000000) (-32470937847 / 1000000000000), orderedInterval (7977875195 / 1000000000000) (7977886375 / 1000000000000))
    | 17 => (orderedInterval (-2385626473 / 1000000000000) (-2385626472 / 1000000000000), orderedInterval (-27665590382 / 1000000000000) (-27665590381 / 1000000000000))
    | 18 => (orderedInterval (-34664039586 / 1000000000000) (-34664014744 / 1000000000000), orderedInterval (13907661814 / 1000000000000) (13907686656 / 1000000000000))
    | 19 => (orderedInterval (-40491184486 / 1000000000000) (-40491184365 / 1000000000000), orderedInterval (-2149777749 / 1000000000000) (-2149777628 / 1000000000000))
    | 20 => (orderedInterval (-46601157612 / 1000000000000) (-46601157611 / 1000000000000), orderedInterval (-21262153901 / 1000000000000) (-21262153900 / 1000000000000))
    | 21 => (orderedInterval (-53646549390 / 1000000000000) (-53646455575 / 1000000000000), orderedInterval (45020017905 / 1000000000000) (45020111719 / 1000000000000))
    | 22 => (orderedInterval (18786763598 / 1000000000000) (18786764318 / 1000000000000), orderedInterval (-38061527124 / 1000000000000) (-38061526404 / 1000000000000))
    | 23 => (orderedInterval (132096350 / 1000000000000) (132096351 / 1000000000000), orderedInterval (36303744029 / 1000000000000) (36303744030 / 1000000000000))
    | 24 => (orderedInterval (-40913731734 / 1000000000000) (-40913731733 / 1000000000000), orderedInterval (-37887543198 / 1000000000000) (-37887543197 / 1000000000000))
    | 25 => (orderedInterval (27635962163 / 1000000000000) (27635969283 / 1000000000000), orderedInterval (-1764023663 / 1000000000000) (-1764016543 / 1000000000000))
    | _ => (orderedInterval (22395375311 / 1000000000000) (22395379824 / 1000000000000), orderedInterval (-25445202956 / 1000000000000) (-25445198443 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11884797717 / 1000000000000) (11884797833 / 1000000000000)
      | 1 => orderedInterval (1286578575 / 1000000000000) (1286578839 / 1000000000000)
      | 2 => orderedInterval (112112641 / 1000000000000) (112112703 / 1000000000000)
      | 3 => orderedInterval (-4231116809 / 1000000000000) (-4231115652 / 1000000000000)
      | 4 => orderedInterval (-3177317606 / 1000000000000) (-3177317516 / 1000000000000)
      | 5 => orderedInterval (1435018278 / 1000000000000) (1435018968 / 1000000000000)
      | 6 => orderedInterval (6317199849 / 1000000000000) (6317203940 / 1000000000000)
      | 7 => orderedInterval (554251607 / 1000000000000) (554253410 / 1000000000000)
      | _ => orderedInterval (-6698225802 / 1000000000000) (-6698224252 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (5566165010 / 1000000000000) (5566165145 / 1000000000000)
      | 1 => orderedInterval (4073452374 / 1000000000000) (4073452481 / 1000000000000)
      | 2 => orderedInterval (-172006835 / 1000000000000) (-172006719 / 1000000000000)
      | 3 => orderedInterval (-603993697 / 1000000000000) (-603992063 / 1000000000000)
      | 4 => orderedInterval (-2182248255 / 1000000000000) (-2182248090 / 1000000000000)
      | 5 => orderedInterval (-1925553472 / 1000000000000) (-1925552583 / 1000000000000)
      | 6 => orderedInterval (-2544583354 / 1000000000000) (-2544579181 / 1000000000000)
      | 7 => orderedInterval (-2568303322 / 1000000000000) (-2568302755 / 1000000000000)
      | _ => orderedInterval (6092091637 / 1000000000000) (6092093940 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11013627422 / 1000000000000) (-11013627263 / 1000000000000)
      | 1 => orderedInterval (-1276546813 / 1000000000000) (-1276546718 / 1000000000000)
      | 2 => orderedInterval (-1708227569 / 1000000000000) (-1708227349 / 1000000000000)
      | 3 => orderedInterval (15466169699 / 1000000000000) (15466172127 / 1000000000000)
      | 4 => orderedInterval (8552321197 / 1000000000000) (8552321507 / 1000000000000)
      | 5 => orderedInterval (-2056476142 / 1000000000000) (-2056474992 / 1000000000000)
      | 6 => orderedInterval (-7069258443 / 1000000000000) (-7069254174 / 1000000000000)
      | 7 => orderedInterval (200796886 / 1000000000000) (200797093 / 1000000000000)
      | _ => orderedInterval (14297687328 / 1000000000000) (14297690899 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-5745143287 / 1000000000000) (-5745143099 / 1000000000000)
      | 1 => orderedInterval (-8367094386 / 1000000000000) (-8367094257 / 1000000000000)
      | 2 => orderedInterval (-5399151 / 1000000000000) (-5398730 / 1000000000000)
      | 3 => orderedInterval (8294560646 / 1000000000000) (8294564498 / 1000000000000)
      | 4 => orderedInterval (5380950284 / 1000000000000) (5380950882 / 1000000000000)
      | 5 => orderedInterval (5499447929 / 1000000000000) (5499449423 / 1000000000000)
      | 6 => orderedInterval (2426656023 / 1000000000000) (2426660383 / 1000000000000)
      | 7 => orderedInterval (3113169576 / 1000000000000) (3113169677 / 1000000000000)
      | _ => orderedInterval (-10080061339 / 1000000000000) (-10080055588 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9804816758 / 1000000000000) (9804816982 / 1000000000000)
      | 1 => orderedInterval (2157253344 / 1000000000000) (2157253540 / 1000000000000)
      | 2 => orderedInterval (9385963509 / 1000000000000) (9385964326 / 1000000000000)
      | 3 => orderedInterval (-69361592782 / 1000000000000) (-69361586189 / 1000000000000)
      | 4 => orderedInterval (-25014040553 / 1000000000000) (-25014039371 / 1000000000000)
      | 5 => orderedInterval (2610441762 / 1000000000000) (2610443718 / 1000000000000)
      | 6 => orderedInterval (7219439755 / 1000000000000) (7219444220 / 1000000000000)
      | 7 => orderedInterval (-188568366 / 1000000000000) (-188568295 / 1000000000000)
      | _ => orderedInterval (-36855764336 / 1000000000000) (-36855754734 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (7483298450 / 1000000000000) (7483308273 / 1000000000000)
    | 1 => orderedInterval (5735020086 / 1000000000000) (5735030175 / 1000000000000)
    | 2 => orderedInterval (15392838721 / 1000000000000) (15392851130 / 1000000000000)
    | 3 => orderedInterval (517086295 / 1000000000000) (517103189 / 1000000000000)
    | _ => orderedInterval (-100242050909 / 1000000000000) (-100242025803 / 1000000000000)

theorem compactCertificate575_stateChecks0 :
    compactCertificate575.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (893 / 2)) (orderedInterval (34897940910 / 1000000000000) (34897940911 / 1000000000000), orderedInterval (14380811351 / 1000000000000) (14380811352 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1315559516475593 / 4000000000000)) (orderedInterval (8409766451 / 1000000000000) (8409766472 / 1000000000000), orderedInterval (-43197739620 / 1000000000000) (-43197739598 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (425424917752169 / 800000000000)) (orderedInterval (-34523648994 / 1000000000000) (-34523647572 / 1000000000000), orderedInterval (2326663148 / 1000000000000) (2326664569 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_stateChecks1 :
    compactCertificate575.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (383876985855451 / 4000000000000)) (orderedInterval (48379587085 / 1000000000000) (48379606460 / 1000000000000), orderedInterval (-65773217638 / 1000000000000) (-65773198263 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1031147580772447 / 4000000000000)) (orderedInterval (40743881622 / 1000000000000) (40743881623 / 1000000000000), orderedInterval (28372561535 / 1000000000000) (28372561536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2799766268568099 / 4000000000000)) (orderedInterval (-4555273733 / 1000000000000) (-4555273732 / 1000000000000), orderedInterval (-29809200476 / 1000000000000) (-29809200475 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_stateChecks2 :
    compactCertificate575.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2062295161545787 / 4000000000000)) (orderedInterval (31895766830 / 1000000000000) (31895766831 / 1000000000000), orderedInterval (14714875377 / 1000000000000) (14714875378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 281 12 (3533777910003751 / 4000000000000)) (orderedInterval (-26622535451 / 1000000000000) (-26622534281 / 1000000000000), orderedInterval (-3427531597 / 1000000000000) (-3427530428 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2602964814453109 / 4000000000000)) (orderedInterval (-29337637704 / 1000000000000) (-29337637693 / 1000000000000), orderedInterval (-10821915949 / 1000000000000) (-10821915938 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_stateChecks3 :
    compactCertificate575.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 318 12 (3993617407814107 / 4000000000000)) (orderedInterval (4101802235 / 1000000000000) (4101802236 / 1000000000000), orderedInterval (24914055291 / 1000000000000) (24914055292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2305716085441603 / 4000000000000)) (orderedInterval (-24720966265 / 1000000000000) (-24720953052 / 1000000000000), orderedInterval (22231662866 / 1000000000000) (22231676079 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 326 12 (4091533655068127 / 4000000000000)) (orderedInterval (-11752279795 / 1000000000000) (-11752279786 / 1000000000000), orderedInterval (22011689514 / 1000000000000) (22011689524 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_stateChecks4 :
    compactCertificate575.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 304 12 (3822841480351163 / 4000000000000)) (orderedInterval (25625811646 / 1000000000000) (25625813632 / 1000000000000), orderedInterval (3059003319 / 1000000000000) (3059005304 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2728160063729579 / 4000000000000)) (orderedInterval (-27222681937 / 1000000000000) (-27222681934 / 1000000000000), orderedInterval (-13848379464 / 1000000000000) (-13848379461 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (3093442742317341 / 4000000000000)) (orderedInterval (27751334560 / 1000000000000) (27751334671 / 1000000000000), orderedInterval (7265558755 / 1000000000000) (7265558866 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_stateChecks5 :
    compactCertificate575.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2578990050926029 / 4000000000000)) (orderedInterval (-31357331083 / 1000000000000) (-31357330495 / 1000000000000), orderedInterval (-2003348513 / 1000000000000) (-2003347924 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2278615922914609 / 4000000000000)) (orderedInterval (-32470949027 / 1000000000000) (-32470937847 / 1000000000000), orderedInterval (7977875195 / 1000000000000) (7977886375 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (660431707782291 / 800000000000)) (orderedInterval (-2385626473 / 1000000000000) (-2385626472 / 1000000000000), orderedInterval (-27665590382 / 1000000000000) (-27665590381 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_stateChecks6 :
    compactCertificate575.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1826788860342377 / 4000000000000)) (orderedInterval (-34664039586 / 1000000000000) (-34664014744 / 1000000000000), orderedInterval (13907661814 / 1000000000000) (13907686656 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1548589148044897 / 4000000000000)) (orderedInterval (-40491184486 / 1000000000000) (-40491184365 / 1000000000000), orderedInterval (-2149777749 / 1000000000000) (-2149777628 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (969035185546891 / 4000000000000)) (orderedInterval (-46601157612 / 1000000000000) (-46601157611 / 1000000000000), orderedInterval (-21262153901 / 1000000000000) (-21262153900 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_stateChecks7 :
    compactCertificate575.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (521150345652597 / 4000000000000)) (orderedInterval (-53646549390 / 1000000000000) (-53646455575 / 1000000000000), orderedInterval (45020017905 / 1000000000000) (45020111719 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1415024566628791 / 4000000000000)) (orderedInterval (18786763598 / 1000000000000) (18786764318 / 1000000000000), orderedInterval (-38061527124 / 1000000000000) (-38061526404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1932095071560407 / 4000000000000)) (orderedInterval (132096350 / 1000000000000) (132096351 / 1000000000000), orderedInterval (36303744029 / 1000000000000) (36303744030 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_stateChecks8 :
    compactCertificate575.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (816964814453109 / 4000000000000)) (orderedInterval (-40913731734 / 1000000000000) (-40913731733 / 1000000000000), orderedInterval (-37887543198 / 1000000000000) (-37887543197 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (3320916614221589 / 4000000000000)) (orderedInterval (27635962163 / 1000000000000) (27635969283 / 1000000000000), orderedInterval (-1764023663 / 1000000000000) (-1764016543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2218218393529051 / 4000000000000)) (orderedInterval (22395375311 / 1000000000000) (22395379824 / 1000000000000), orderedInterval (-25445202956 / 1000000000000) (-25445198443 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_states : ∀ j,
    BesselStateValid (compactCertificate575.point j) (compactCertificate575.state j) :=
  compactCertificate575.statesValid_of_checks3 compactCertificate575_stateChecks0
    compactCertificate575_stateChecks1 compactCertificate575_stateChecks2
    compactCertificate575_stateChecks3 compactCertificate575_stateChecks4
    compactCertificate575_stateChecks5 compactCertificate575_stateChecks6
    compactCertificate575_stateChecks7 compactCertificate575_stateChecks8

theorem compactCertificate575_chunkChecks0_0 :
    compactCertificate575.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (893 / 2) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34897940910 / 1000000000000) (34897940911 / 1000000000000), orderedInterval (14380811351 / 1000000000000) (14380811352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1315559516475593 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8409766451 / 1000000000000) (8409766472 / 1000000000000), orderedInterval (-43197739620 / 1000000000000) (-43197739598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (425424917752169 / 800000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34523648994 / 1000000000000) (-34523647572 / 1000000000000), orderedInterval (2326663148 / 1000000000000) (2326664569 / 1000000000000)))) (orderedInterval (11884797717 / 1000000000000) (11884797833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (383876985855451 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (48379587085 / 1000000000000) (48379606460 / 1000000000000), orderedInterval (-65773217638 / 1000000000000) (-65773198263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1031147580772447 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40743881622 / 1000000000000) (40743881623 / 1000000000000), orderedInterval (28372561535 / 1000000000000) (28372561536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2799766268568099 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4555273733 / 1000000000000) (-4555273732 / 1000000000000), orderedInterval (-29809200476 / 1000000000000) (-29809200475 / 1000000000000)))) (orderedInterval (1286578575 / 1000000000000) (1286578839 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2062295161545787 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31895766830 / 1000000000000) (31895766831 / 1000000000000), orderedInterval (14714875377 / 1000000000000) (14714875378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3533777910003751 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26622535451 / 1000000000000) (-26622534281 / 1000000000000), orderedInterval (-3427531597 / 1000000000000) (-3427530428 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2602964814453109 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29337637704 / 1000000000000) (-29337637693 / 1000000000000), orderedInterval (-10821915949 / 1000000000000) (-10821915938 / 1000000000000)))) (orderedInterval (112112641 / 1000000000000) (112112703 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_chunkChecks0_1 :
    compactCertificate575.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3993617407814107 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4101802235 / 1000000000000) (4101802236 / 1000000000000), orderedInterval (24914055291 / 1000000000000) (24914055292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2305716085441603 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24720966265 / 1000000000000) (-24720953052 / 1000000000000), orderedInterval (22231662866 / 1000000000000) (22231676079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4091533655068127 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11752279795 / 1000000000000) (-11752279786 / 1000000000000), orderedInterval (22011689514 / 1000000000000) (22011689524 / 1000000000000)))) (orderedInterval (-4231116809 / 1000000000000) (-4231115652 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3822841480351163 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25625811646 / 1000000000000) (25625813632 / 1000000000000), orderedInterval (3059003319 / 1000000000000) (3059005304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2728160063729579 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27222681937 / 1000000000000) (-27222681934 / 1000000000000), orderedInterval (-13848379464 / 1000000000000) (-13848379461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3093442742317341 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27751334560 / 1000000000000) (27751334671 / 1000000000000), orderedInterval (7265558755 / 1000000000000) (7265558866 / 1000000000000)))) (orderedInterval (-3177317606 / 1000000000000) (-3177317516 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2578990050926029 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31357331083 / 1000000000000) (-31357330495 / 1000000000000), orderedInterval (-2003348513 / 1000000000000) (-2003347924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2278615922914609 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32470949027 / 1000000000000) (-32470937847 / 1000000000000), orderedInterval (7977875195 / 1000000000000) (7977886375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (660431707782291 / 800000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2385626473 / 1000000000000) (-2385626472 / 1000000000000), orderedInterval (-27665590382 / 1000000000000) (-27665590381 / 1000000000000)))) (orderedInterval (1435018278 / 1000000000000) (1435018968 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_chunkChecks0_2 :
    compactCertificate575.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1826788860342377 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34664039586 / 1000000000000) (-34664014744 / 1000000000000), orderedInterval (13907661814 / 1000000000000) (13907686656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1548589148044897 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40491184486 / 1000000000000) (-40491184365 / 1000000000000), orderedInterval (-2149777749 / 1000000000000) (-2149777628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (969035185546891 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46601157612 / 1000000000000) (-46601157611 / 1000000000000), orderedInterval (-21262153901 / 1000000000000) (-21262153900 / 1000000000000)))) (orderedInterval (6317199849 / 1000000000000) (6317203940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (521150345652597 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-53646549390 / 1000000000000) (-53646455575 / 1000000000000), orderedInterval (45020017905 / 1000000000000) (45020111719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1415024566628791 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18786763598 / 1000000000000) (18786764318 / 1000000000000), orderedInterval (-38061527124 / 1000000000000) (-38061526404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1932095071560407 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (132096350 / 1000000000000) (132096351 / 1000000000000), orderedInterval (36303744029 / 1000000000000) (36303744030 / 1000000000000)))) (orderedInterval (554251607 / 1000000000000) (554253410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (816964814453109 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40913731734 / 1000000000000) (-40913731733 / 1000000000000), orderedInterval (-37887543198 / 1000000000000) (-37887543197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3320916614221589 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27635962163 / 1000000000000) (27635969283 / 1000000000000), orderedInterval (-1764023663 / 1000000000000) (-1764016543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2218218393529051 / 4000000000000) 0 (IntervalRat.scale (893 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22395375311 / 1000000000000) (22395379824 / 1000000000000), orderedInterval (-25445202956 / 1000000000000) (-25445198443 / 1000000000000)))) (orderedInterval (-6698225802 / 1000000000000) (-6698224252 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_chunkChecks0 :
    compactCertificate575.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate575.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate575_chunkChecks0_0
    compactCertificate575_chunkChecks0_1 compactCertificate575_chunkChecks0_2

theorem compactCertificate575_chunkChecks1_0 :
    compactCertificate575.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (893 / 2) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34897940910 / 1000000000000) (34897940911 / 1000000000000), orderedInterval (14380811351 / 1000000000000) (14380811352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1315559516475593 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8409766451 / 1000000000000) (8409766472 / 1000000000000), orderedInterval (-43197739620 / 1000000000000) (-43197739598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (425424917752169 / 800000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34523648994 / 1000000000000) (-34523647572 / 1000000000000), orderedInterval (2326663148 / 1000000000000) (2326664569 / 1000000000000)))) (orderedInterval (5566165010 / 1000000000000) (5566165145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (383876985855451 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (48379587085 / 1000000000000) (48379606460 / 1000000000000), orderedInterval (-65773217638 / 1000000000000) (-65773198263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1031147580772447 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40743881622 / 1000000000000) (40743881623 / 1000000000000), orderedInterval (28372561535 / 1000000000000) (28372561536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2799766268568099 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4555273733 / 1000000000000) (-4555273732 / 1000000000000), orderedInterval (-29809200476 / 1000000000000) (-29809200475 / 1000000000000)))) (orderedInterval (4073452374 / 1000000000000) (4073452481 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2062295161545787 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31895766830 / 1000000000000) (31895766831 / 1000000000000), orderedInterval (14714875377 / 1000000000000) (14714875378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3533777910003751 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26622535451 / 1000000000000) (-26622534281 / 1000000000000), orderedInterval (-3427531597 / 1000000000000) (-3427530428 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2602964814453109 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29337637704 / 1000000000000) (-29337637693 / 1000000000000), orderedInterval (-10821915949 / 1000000000000) (-10821915938 / 1000000000000)))) (orderedInterval (-172006835 / 1000000000000) (-172006719 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_chunkChecks1_1 :
    compactCertificate575.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3993617407814107 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4101802235 / 1000000000000) (4101802236 / 1000000000000), orderedInterval (24914055291 / 1000000000000) (24914055292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2305716085441603 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24720966265 / 1000000000000) (-24720953052 / 1000000000000), orderedInterval (22231662866 / 1000000000000) (22231676079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4091533655068127 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11752279795 / 1000000000000) (-11752279786 / 1000000000000), orderedInterval (22011689514 / 1000000000000) (22011689524 / 1000000000000)))) (orderedInterval (-603993697 / 1000000000000) (-603992063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3822841480351163 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25625811646 / 1000000000000) (25625813632 / 1000000000000), orderedInterval (3059003319 / 1000000000000) (3059005304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2728160063729579 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27222681937 / 1000000000000) (-27222681934 / 1000000000000), orderedInterval (-13848379464 / 1000000000000) (-13848379461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3093442742317341 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27751334560 / 1000000000000) (27751334671 / 1000000000000), orderedInterval (7265558755 / 1000000000000) (7265558866 / 1000000000000)))) (orderedInterval (-2182248255 / 1000000000000) (-2182248090 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2578990050926029 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31357331083 / 1000000000000) (-31357330495 / 1000000000000), orderedInterval (-2003348513 / 1000000000000) (-2003347924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2278615922914609 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32470949027 / 1000000000000) (-32470937847 / 1000000000000), orderedInterval (7977875195 / 1000000000000) (7977886375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (660431707782291 / 800000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2385626473 / 1000000000000) (-2385626472 / 1000000000000), orderedInterval (-27665590382 / 1000000000000) (-27665590381 / 1000000000000)))) (orderedInterval (-1925553472 / 1000000000000) (-1925552583 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_chunkChecks1_2 :
    compactCertificate575.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1826788860342377 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34664039586 / 1000000000000) (-34664014744 / 1000000000000), orderedInterval (13907661814 / 1000000000000) (13907686656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1548589148044897 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40491184486 / 1000000000000) (-40491184365 / 1000000000000), orderedInterval (-2149777749 / 1000000000000) (-2149777628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (969035185546891 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46601157612 / 1000000000000) (-46601157611 / 1000000000000), orderedInterval (-21262153901 / 1000000000000) (-21262153900 / 1000000000000)))) (orderedInterval (-2544583354 / 1000000000000) (-2544579181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (521150345652597 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-53646549390 / 1000000000000) (-53646455575 / 1000000000000), orderedInterval (45020017905 / 1000000000000) (45020111719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1415024566628791 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18786763598 / 1000000000000) (18786764318 / 1000000000000), orderedInterval (-38061527124 / 1000000000000) (-38061526404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1932095071560407 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (132096350 / 1000000000000) (132096351 / 1000000000000), orderedInterval (36303744029 / 1000000000000) (36303744030 / 1000000000000)))) (orderedInterval (-2568303322 / 1000000000000) (-2568302755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (816964814453109 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40913731734 / 1000000000000) (-40913731733 / 1000000000000), orderedInterval (-37887543198 / 1000000000000) (-37887543197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3320916614221589 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27635962163 / 1000000000000) (27635969283 / 1000000000000), orderedInterval (-1764023663 / 1000000000000) (-1764016543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2218218393529051 / 4000000000000) 1 (IntervalRat.scale (893 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22395375311 / 1000000000000) (22395379824 / 1000000000000), orderedInterval (-25445202956 / 1000000000000) (-25445198443 / 1000000000000)))) (orderedInterval (6092091637 / 1000000000000) (6092093940 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_chunkChecks1 :
    compactCertificate575.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate575.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate575_chunkChecks1_0
    compactCertificate575_chunkChecks1_1 compactCertificate575_chunkChecks1_2

theorem compactCertificate575_chunkChecks2_0 :
    compactCertificate575.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (893 / 2) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34897940910 / 1000000000000) (34897940911 / 1000000000000), orderedInterval (14380811351 / 1000000000000) (14380811352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1315559516475593 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8409766451 / 1000000000000) (8409766472 / 1000000000000), orderedInterval (-43197739620 / 1000000000000) (-43197739598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (425424917752169 / 800000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34523648994 / 1000000000000) (-34523647572 / 1000000000000), orderedInterval (2326663148 / 1000000000000) (2326664569 / 1000000000000)))) (orderedInterval (-11013627422 / 1000000000000) (-11013627263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (383876985855451 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (48379587085 / 1000000000000) (48379606460 / 1000000000000), orderedInterval (-65773217638 / 1000000000000) (-65773198263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1031147580772447 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40743881622 / 1000000000000) (40743881623 / 1000000000000), orderedInterval (28372561535 / 1000000000000) (28372561536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2799766268568099 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4555273733 / 1000000000000) (-4555273732 / 1000000000000), orderedInterval (-29809200476 / 1000000000000) (-29809200475 / 1000000000000)))) (orderedInterval (-1276546813 / 1000000000000) (-1276546718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2062295161545787 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31895766830 / 1000000000000) (31895766831 / 1000000000000), orderedInterval (14714875377 / 1000000000000) (14714875378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3533777910003751 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26622535451 / 1000000000000) (-26622534281 / 1000000000000), orderedInterval (-3427531597 / 1000000000000) (-3427530428 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2602964814453109 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29337637704 / 1000000000000) (-29337637693 / 1000000000000), orderedInterval (-10821915949 / 1000000000000) (-10821915938 / 1000000000000)))) (orderedInterval (-1708227569 / 1000000000000) (-1708227349 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_chunkChecks2_1 :
    compactCertificate575.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3993617407814107 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4101802235 / 1000000000000) (4101802236 / 1000000000000), orderedInterval (24914055291 / 1000000000000) (24914055292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2305716085441603 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24720966265 / 1000000000000) (-24720953052 / 1000000000000), orderedInterval (22231662866 / 1000000000000) (22231676079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4091533655068127 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11752279795 / 1000000000000) (-11752279786 / 1000000000000), orderedInterval (22011689514 / 1000000000000) (22011689524 / 1000000000000)))) (orderedInterval (15466169699 / 1000000000000) (15466172127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3822841480351163 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25625811646 / 1000000000000) (25625813632 / 1000000000000), orderedInterval (3059003319 / 1000000000000) (3059005304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2728160063729579 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27222681937 / 1000000000000) (-27222681934 / 1000000000000), orderedInterval (-13848379464 / 1000000000000) (-13848379461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3093442742317341 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27751334560 / 1000000000000) (27751334671 / 1000000000000), orderedInterval (7265558755 / 1000000000000) (7265558866 / 1000000000000)))) (orderedInterval (8552321197 / 1000000000000) (8552321507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2578990050926029 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31357331083 / 1000000000000) (-31357330495 / 1000000000000), orderedInterval (-2003348513 / 1000000000000) (-2003347924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2278615922914609 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32470949027 / 1000000000000) (-32470937847 / 1000000000000), orderedInterval (7977875195 / 1000000000000) (7977886375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (660431707782291 / 800000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2385626473 / 1000000000000) (-2385626472 / 1000000000000), orderedInterval (-27665590382 / 1000000000000) (-27665590381 / 1000000000000)))) (orderedInterval (-2056476142 / 1000000000000) (-2056474992 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_chunkChecks2_2 :
    compactCertificate575.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1826788860342377 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34664039586 / 1000000000000) (-34664014744 / 1000000000000), orderedInterval (13907661814 / 1000000000000) (13907686656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1548589148044897 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40491184486 / 1000000000000) (-40491184365 / 1000000000000), orderedInterval (-2149777749 / 1000000000000) (-2149777628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (969035185546891 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46601157612 / 1000000000000) (-46601157611 / 1000000000000), orderedInterval (-21262153901 / 1000000000000) (-21262153900 / 1000000000000)))) (orderedInterval (-7069258443 / 1000000000000) (-7069254174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (521150345652597 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-53646549390 / 1000000000000) (-53646455575 / 1000000000000), orderedInterval (45020017905 / 1000000000000) (45020111719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1415024566628791 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18786763598 / 1000000000000) (18786764318 / 1000000000000), orderedInterval (-38061527124 / 1000000000000) (-38061526404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1932095071560407 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (132096350 / 1000000000000) (132096351 / 1000000000000), orderedInterval (36303744029 / 1000000000000) (36303744030 / 1000000000000)))) (orderedInterval (200796886 / 1000000000000) (200797093 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (816964814453109 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40913731734 / 1000000000000) (-40913731733 / 1000000000000), orderedInterval (-37887543198 / 1000000000000) (-37887543197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3320916614221589 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27635962163 / 1000000000000) (27635969283 / 1000000000000), orderedInterval (-1764023663 / 1000000000000) (-1764016543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2218218393529051 / 4000000000000) 2 (IntervalRat.scale (893 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22395375311 / 1000000000000) (22395379824 / 1000000000000), orderedInterval (-25445202956 / 1000000000000) (-25445198443 / 1000000000000)))) (orderedInterval (14297687328 / 1000000000000) (14297690899 / 1000000000000))) = true
  rfl'

theorem compactCertificate575_chunkChecks2 :
    compactCertificate575.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate575.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate575_chunkChecks2_0
    compactCertificate575_chunkChecks2_1 compactCertificate575_chunkChecks2_2

theorem compactCertificate575_chunkChecks3_0 :
    compactCertificate575.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (893 / 2) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34897940910 / 1000000000000) (34897940911 / 1000000000000), orderedInterval (14380811351 / 1000000000000) (14380811352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1315559516475593 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8409766451 / 1000000000000) (8409766472 / 1000000000000), orderedInterval (-43197739620 / 1000000000000) (-43197739598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (425424917752169 / 800000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34523648994 / 1000000000000) (-34523647572 / 1000000000000), orderedInterval (2326663148 / 1000000000000) (2326664569 / 1000000000000)))) (orderedInterval (-5745143287 / 1000000000000) (-5745143099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (383876985855451 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (48379587085 / 1000000000000) (48379606460 / 1000000000000), orderedInterval (-65773217638 / 1000000000000) (-65773198263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1031147580772447 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40743881622 / 1000000000000) (40743881623 / 1000000000000), orderedInterval (28372561535 / 1000000000000) (28372561536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2799766268568099 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4555273733 / 1000000000000) (-4555273732 / 1000000000000), orderedInterval (-29809200476 / 1000000000000) (-29809200475 / 1000000000000)))) (orderedInterval (-8367094386 / 1000000000000) (-8367094257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2062295161545787 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31895766830 / 1000000000000) (31895766831 / 1000000000000), orderedInterval (14714875377 / 1000000000000) (14714875378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3533777910003751 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26622535451 / 1000000000000) (-26622534281 / 1000000000000), orderedInterval (-3427531597 / 1000000000000) (-3427530428 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2602964814453109 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29337637704 / 1000000000000) (-29337637693 / 1000000000000), orderedInterval (-10821915949 / 1000000000000) (-10821915938 / 1000000000000)))) (orderedInterval (-5399151 / 1000000000000) (-5398730 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate575_chunkChecks3_1 :
    compactCertificate575.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3993617407814107 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4101802235 / 1000000000000) (4101802236 / 1000000000000), orderedInterval (24914055291 / 1000000000000) (24914055292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2305716085441603 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24720966265 / 1000000000000) (-24720953052 / 1000000000000), orderedInterval (22231662866 / 1000000000000) (22231676079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4091533655068127 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11752279795 / 1000000000000) (-11752279786 / 1000000000000), orderedInterval (22011689514 / 1000000000000) (22011689524 / 1000000000000)))) (orderedInterval (8294560646 / 1000000000000) (8294564498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3822841480351163 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25625811646 / 1000000000000) (25625813632 / 1000000000000), orderedInterval (3059003319 / 1000000000000) (3059005304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2728160063729579 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27222681937 / 1000000000000) (-27222681934 / 1000000000000), orderedInterval (-13848379464 / 1000000000000) (-13848379461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3093442742317341 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27751334560 / 1000000000000) (27751334671 / 1000000000000), orderedInterval (7265558755 / 1000000000000) (7265558866 / 1000000000000)))) (orderedInterval (5380950284 / 1000000000000) (5380950882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2578990050926029 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31357331083 / 1000000000000) (-31357330495 / 1000000000000), orderedInterval (-2003348513 / 1000000000000) (-2003347924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2278615922914609 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32470949027 / 1000000000000) (-32470937847 / 1000000000000), orderedInterval (7977875195 / 1000000000000) (7977886375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (660431707782291 / 800000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2385626473 / 1000000000000) (-2385626472 / 1000000000000), orderedInterval (-27665590382 / 1000000000000) (-27665590381 / 1000000000000)))) (orderedInterval (5499447929 / 1000000000000) (5499449423 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate575_chunkChecks3_2 :
    compactCertificate575.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1826788860342377 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34664039586 / 1000000000000) (-34664014744 / 1000000000000), orderedInterval (13907661814 / 1000000000000) (13907686656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1548589148044897 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40491184486 / 1000000000000) (-40491184365 / 1000000000000), orderedInterval (-2149777749 / 1000000000000) (-2149777628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (969035185546891 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46601157612 / 1000000000000) (-46601157611 / 1000000000000), orderedInterval (-21262153901 / 1000000000000) (-21262153900 / 1000000000000)))) (orderedInterval (2426656023 / 1000000000000) (2426660383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (521150345652597 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-53646549390 / 1000000000000) (-53646455575 / 1000000000000), orderedInterval (45020017905 / 1000000000000) (45020111719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1415024566628791 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18786763598 / 1000000000000) (18786764318 / 1000000000000), orderedInterval (-38061527124 / 1000000000000) (-38061526404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1932095071560407 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (132096350 / 1000000000000) (132096351 / 1000000000000), orderedInterval (36303744029 / 1000000000000) (36303744030 / 1000000000000)))) (orderedInterval (3113169576 / 1000000000000) (3113169677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (816964814453109 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40913731734 / 1000000000000) (-40913731733 / 1000000000000), orderedInterval (-37887543198 / 1000000000000) (-37887543197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3320916614221589 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27635962163 / 1000000000000) (27635969283 / 1000000000000), orderedInterval (-1764023663 / 1000000000000) (-1764016543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2218218393529051 / 4000000000000) 3 (IntervalRat.scale (893 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22395375311 / 1000000000000) (22395379824 / 1000000000000), orderedInterval (-25445202956 / 1000000000000) (-25445198443 / 1000000000000)))) (orderedInterval (-10080061339 / 1000000000000) (-10080055588 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate575_chunkChecks3 :
    compactCertificate575.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate575.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate575_chunkChecks3_0
    compactCertificate575_chunkChecks3_1 compactCertificate575_chunkChecks3_2

theorem compactCertificate575_chunkChecks4_0 :
    compactCertificate575.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (893 / 2) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (34897940910 / 1000000000000) (34897940911 / 1000000000000), orderedInterval (14380811351 / 1000000000000) (14380811352 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1315559516475593 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (8409766451 / 1000000000000) (8409766472 / 1000000000000), orderedInterval (-43197739620 / 1000000000000) (-43197739598 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (425424917752169 / 800000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34523648994 / 1000000000000) (-34523647572 / 1000000000000), orderedInterval (2326663148 / 1000000000000) (2326664569 / 1000000000000)))) (orderedInterval (9804816758 / 1000000000000) (9804816982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (383876985855451 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (48379587085 / 1000000000000) (48379606460 / 1000000000000), orderedInterval (-65773217638 / 1000000000000) (-65773198263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1031147580772447 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40743881622 / 1000000000000) (40743881623 / 1000000000000), orderedInterval (28372561535 / 1000000000000) (28372561536 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2799766268568099 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4555273733 / 1000000000000) (-4555273732 / 1000000000000), orderedInterval (-29809200476 / 1000000000000) (-29809200475 / 1000000000000)))) (orderedInterval (2157253344 / 1000000000000) (2157253540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2062295161545787 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31895766830 / 1000000000000) (31895766831 / 1000000000000), orderedInterval (14714875377 / 1000000000000) (14714875378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3533777910003751 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26622535451 / 1000000000000) (-26622534281 / 1000000000000), orderedInterval (-3427531597 / 1000000000000) (-3427530428 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2602964814453109 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29337637704 / 1000000000000) (-29337637693 / 1000000000000), orderedInterval (-10821915949 / 1000000000000) (-10821915938 / 1000000000000)))) (orderedInterval (9385963509 / 1000000000000) (9385964326 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate575_chunkChecks4_1 :
    compactCertificate575.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3993617407814107 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (4101802235 / 1000000000000) (4101802236 / 1000000000000), orderedInterval (24914055291 / 1000000000000) (24914055292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2305716085441603 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24720966265 / 1000000000000) (-24720953052 / 1000000000000), orderedInterval (22231662866 / 1000000000000) (22231676079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4091533655068127 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-11752279795 / 1000000000000) (-11752279786 / 1000000000000), orderedInterval (22011689514 / 1000000000000) (22011689524 / 1000000000000)))) (orderedInterval (-69361592782 / 1000000000000) (-69361586189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3822841480351163 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25625811646 / 1000000000000) (25625813632 / 1000000000000), orderedInterval (3059003319 / 1000000000000) (3059005304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2728160063729579 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27222681937 / 1000000000000) (-27222681934 / 1000000000000), orderedInterval (-13848379464 / 1000000000000) (-13848379461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3093442742317341 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27751334560 / 1000000000000) (27751334671 / 1000000000000), orderedInterval (7265558755 / 1000000000000) (7265558866 / 1000000000000)))) (orderedInterval (-25014040553 / 1000000000000) (-25014039371 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2578990050926029 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31357331083 / 1000000000000) (-31357330495 / 1000000000000), orderedInterval (-2003348513 / 1000000000000) (-2003347924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2278615922914609 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32470949027 / 1000000000000) (-32470937847 / 1000000000000), orderedInterval (7977875195 / 1000000000000) (7977886375 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (660431707782291 / 800000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-2385626473 / 1000000000000) (-2385626472 / 1000000000000), orderedInterval (-27665590382 / 1000000000000) (-27665590381 / 1000000000000)))) (orderedInterval (2610441762 / 1000000000000) (2610443718 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate575_chunkChecks4_2 :
    compactCertificate575.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1826788860342377 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34664039586 / 1000000000000) (-34664014744 / 1000000000000), orderedInterval (13907661814 / 1000000000000) (13907686656 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1548589148044897 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-40491184486 / 1000000000000) (-40491184365 / 1000000000000), orderedInterval (-2149777749 / 1000000000000) (-2149777628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (969035185546891 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46601157612 / 1000000000000) (-46601157611 / 1000000000000), orderedInterval (-21262153901 / 1000000000000) (-21262153900 / 1000000000000)))) (orderedInterval (7219439755 / 1000000000000) (7219444220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (521150345652597 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-53646549390 / 1000000000000) (-53646455575 / 1000000000000), orderedInterval (45020017905 / 1000000000000) (45020111719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1415024566628791 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (18786763598 / 1000000000000) (18786764318 / 1000000000000), orderedInterval (-38061527124 / 1000000000000) (-38061526404 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1932095071560407 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (132096350 / 1000000000000) (132096351 / 1000000000000), orderedInterval (36303744029 / 1000000000000) (36303744030 / 1000000000000)))) (orderedInterval (-188568366 / 1000000000000) (-188568295 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (816964814453109 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-40913731734 / 1000000000000) (-40913731733 / 1000000000000), orderedInterval (-37887543198 / 1000000000000) (-37887543197 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3320916614221589 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27635962163 / 1000000000000) (27635969283 / 1000000000000), orderedInterval (-1764023663 / 1000000000000) (-1764016543 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2218218393529051 / 4000000000000) 4 (IntervalRat.scale (893 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22395375311 / 1000000000000) (22395379824 / 1000000000000), orderedInterval (-25445202956 / 1000000000000) (-25445198443 / 1000000000000)))) (orderedInterval (-36855764336 / 1000000000000) (-36855754734 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate575_chunkChecks4 :
    compactCertificate575.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate575.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate575_chunkChecks4_0
    compactCertificate575_chunkChecks4_1 compactCertificate575_chunkChecks4_2

theorem compactCertificate575_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate575.chunkCheck r b = true :=
  compactCertificate575.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate575_chunkChecks0
    · exact compactCertificate575_chunkChecks1
    · exact compactCertificate575_chunkChecks2
    · exact compactCertificate575_chunkChecks3
    · exact compactCertificate575_chunkChecks4)

theorem compactCertificate575_coefficient0 :
    compactCertificate575.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate575_coefficient1 :
    compactCertificate575.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate575_coefficient2 :
    compactCertificate575.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate575_coefficient3 :
    compactCertificate575.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate575_coefficient4 :
    compactCertificate575.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate575_coefficients : ∀ r : Fin 5,
    compactCertificate575.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate575_coefficient0
  · exact compactCertificate575_coefficient1
  · exact compactCertificate575_coefficient2
  · exact compactCertificate575_coefficient3
  · exact compactCertificate575_coefficient4

theorem compactCertificate575_lower : (1 : ℚ) ≤ compactCertificate575.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate575, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate575_proves {t : ℝ} (ht : t ∈ compactCertificate575.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate575.proves compactCertificate575_states compactCertificate575_chunks
    compactCertificate575_coefficients compactCertificate575_lower ht

end Erdos232
