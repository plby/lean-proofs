/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate564 : CompactCertificate where
  left := 435
  right := 436
  center := 871 / 2
  grid := fun i =>
    match i.val with
    | 0 => 139
    | 1 => 102
    | 2 => 165
    | 3 => 30
    | 4 => 80
    | 5 => 217
    | 6 => 160
    | 7 => 274
    | 8 => 202
    | 9 => 310
    | 10 => 179
    | 11 => 318
    | 12 => 297
    | 13 => 212
    | 14 => 240
    | 15 => 200
    | 16 => 177
    | 17 => 256
    | 18 => 142
    | 19 => 120
    | 20 => 75
    | 21 => 40
    | 22 => 110
    | 23 => 150
    | 24 => 63
    | 25 => 258
    | _ => 172
  point := fun i =>
    match i.val with
    | 0 => 871 / 2
    | 1 => 1283149315621771 / 4000000000000
    | 2 => 414944124705643 / 800000000000
    | 3 => 374419770078497 / 4000000000000
    | 4 => 1005744168928109 / 4000000000000
    | 5 => 2730791063743353 / 4000000000000
    | 6 => 2011488337857089 / 4000000000000
    | 7 => 3446719551638597 / 4000000000000
    | 8 => 2538838021711823 / 4000000000000
    | 9 => 3895230416804129 / 4000000000000
    | 10 => 2248912329697241 / 4000000000000
    | 11 => 3990734393689069 / 4000000000000
    | 12 => 3728661735034561 / 4000000000000
    | 13 => 2660948953536913 / 4000000000000
    | 14 => 3017232506784327 / 4000000000000
    | 15 => 2515453901855063 / 4000000000000
    | 16 => 2222479808352323 / 4000000000000
    | 17 => 644161273771977 / 800000000000
    | 18 => 1781783983603819 / 4000000000000
    | 19 => 1510438015618259 / 4000000000000
    | 20 => 945161978288177 / 4000000000000
    | 21 => 508311255390159 / 4000000000000
    | 22 => 1380163939007477 / 4000000000000
    | 23 => 1884495864870229 / 4000000000000
    | 24 => 796838021711823 / 4000000000000
    | 25 => 3239102319134383 / 4000000000000
    | _ => 2163570236017697 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (14757349272 / 1000000000000) (14757349462 / 1000000000000), orderedInterval (-35287820574 / 1000000000000) (-35287820384 / 1000000000000))
    | 1 => (orderedInterval (40287878028 / 1000000000000) (40287878029 / 1000000000000), orderedInterval (18948762851 / 1000000000000) (18948762852 / 1000000000000))
    | 2 => (orderedInterval (-31262617989 / 1000000000000) (-31262617987 / 1000000000000), orderedInterval (-15782278418 / 1000000000000) (-15782278416 / 1000000000000))
    | 3 => (orderedInterval (11607985894 / 1000000000000) (11607985895 / 1000000000000), orderedInterval (81586523759 / 1000000000000) (81586523761 / 1000000000000))
    | 4 => (orderedInterval (39212505938 / 1000000000000) (39212505939 / 1000000000000), orderedInterval (31454760636 / 1000000000000) (31454760637 / 1000000000000))
    | 5 => (orderedInterval (-30006981955 / 1000000000000) (-30006970349 / 1000000000000), orderedInterval (5686523276 / 1000000000000) (5686534882 / 1000000000000))
    | 6 => (orderedInterval (29986132706 / 1000000000000) (29986132707 / 1000000000000), orderedInterval (19122187535 / 1000000000000) (19122187536 / 1000000000000))
    | 7 => (orderedInterval (27050788607 / 1000000000000) (27050800458 / 1000000000000), orderedInterval (-2674042006 / 1000000000000) (-2674030154 / 1000000000000))
    | 8 => (orderedInterval (24669617296 / 1000000000000) (24669617297 / 1000000000000), orderedInterval (19840565904 / 1000000000000) (19840565905 / 1000000000000))
    | 9 => (orderedInterval (16455010554 / 1000000000000) (16455010555 / 1000000000000), orderedInterval (19561311207 / 1000000000000) (19561311208 / 1000000000000))
    | 10 => (orderedInterval (-20847897131 / 1000000000000) (-20847897130 / 1000000000000), orderedInterval (-26395114110 / 1000000000000) (-26395114109 / 1000000000000))
    | 11 => (orderedInterval (-13366517154 / 1000000000000) (-13366517122 / 1000000000000), orderedInterval (21441113098 / 1000000000000) (21441113130 / 1000000000000))
    | 12 => (orderedInterval (2669299032 / 1000000000000) (2669299033 / 1000000000000), orderedInterval (-25998011131 / 1000000000000) (-25998011130 / 1000000000000))
    | 13 => (orderedInterval (148676182 / 1000000000000) (148676183 / 1000000000000), orderedInterval (30934653954 / 1000000000000) (30934653955 / 1000000000000))
    | 14 => (orderedInterval (26035695439 / 1000000000000) (26035695443 / 1000000000000), orderedInterval (12871530123 / 1000000000000) (12871530127 / 1000000000000))
    | 15 => (orderedInterval (30900304762 / 1000000000000) (30900304811 / 1000000000000), orderedInterval (7558617833 / 1000000000000) (7558617882 / 1000000000000))
    | 16 => (orderedInterval (-11391215308 / 1000000000000) (-11391215307 / 1000000000000), orderedInterval (-31864870294 / 1000000000000) (-31864870293 / 1000000000000))
    | 17 => (orderedInterval (27720827928 / 1000000000000) (27720845685 / 1000000000000), orderedInterval (-4727750077 / 1000000000000) (-4727732320 / 1000000000000))
    | 18 => (orderedInterval (4711627482 / 1000000000000) (4711627483 / 1000000000000), orderedInterval (37504380717 / 1000000000000) (37504380718 / 1000000000000))
    | 19 => (orderedInterval (40486370325 / 1000000000000) (40486370347 / 1000000000000), orderedInterval (6785497086 / 1000000000000) (6785497107 / 1000000000000))
    | 20 => (orderedInterval (-51563722312 / 1000000000000) (-51563722296 / 1000000000000), orderedInterval (-5840824993 / 1000000000000) (-5840824977 / 1000000000000))
    | 21 => (orderedInterval (57285911135 / 1000000000000) (57285962636 / 1000000000000), orderedInterval (-41794564178 / 1000000000000) (-41794512677 / 1000000000000))
    | 22 => (orderedInterval (10661498884 / 1000000000000) (10661498885 / 1000000000000), orderedInterval (41594521059 / 1000000000000) (41594521060 / 1000000000000))
    | 23 => (orderedInterval (22833070216 / 1000000000000) (22833070217 / 1000000000000), orderedInterval (28784269013 / 1000000000000) (28784269014 / 1000000000000))
    | 24 => (orderedInterval (-49524949161 / 1000000000000) (-49524926043 / 1000000000000), orderedInterval (27382409325 / 1000000000000) (27382432443 / 1000000000000))
    | 25 => (orderedInterval (838763146 / 1000000000000) (838763147 / 1000000000000), orderedInterval (28025626673 / 1000000000000) (28025626674 / 1000000000000))
    | _ => (orderedInterval (33265867843 / 1000000000000) (33265867866 / 1000000000000), orderedInterval (8357436186 / 1000000000000) (8357436209 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (4390175427 / 1000000000000) (4390175533 / 1000000000000)
      | 1 => orderedInterval (3438963363 / 1000000000000) (3438964241 / 1000000000000)
      | 2 => orderedInterval (-238138952 / 1000000000000) (-238138561 / 1000000000000)
      | 3 => orderedInterval (-6368643573 / 1000000000000) (-6368643396 / 1000000000000)
      | 4 => orderedInterval (-165885481 / 1000000000000) (-165885428 / 1000000000000)
      | 5 => orderedInterval (1718470592 / 1000000000000) (1718471090 / 1000000000000)
      | 6 => orderedInterval (-4723551413 / 1000000000000) (-4723551301 / 1000000000000)
      | 7 => orderedInterval (-3049568683 / 1000000000000) (-3049567679 / 1000000000000)
      | _ => orderedInterval (-6608388764 / 1000000000000) (-6608388500 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14959809946 / 1000000000000) (-14959809837 / 1000000000000)
      | 1 => orderedInterval (-160899635 / 1000000000000) (-160898281 / 1000000000000)
      | 2 => orderedInterval (862037438 / 1000000000000) (862038204 / 1000000000000)
      | 3 => orderedInterval (-3314296942 / 1000000000000) (-3314296574 / 1000000000000)
      | 4 => orderedInterval (5360209263 / 1000000000000) (5360209348 / 1000000000000)
      | 5 => orderedInterval (2228715303 / 1000000000000) (2228716206 / 1000000000000)
      | 6 => orderedInterval (-6569795991 / 1000000000000) (-6569795888 / 1000000000000)
      | 7 => orderedInterval (-2908893488 / 1000000000000) (-2908893163 / 1000000000000)
      | _ => orderedInterval (-6114001288 / 1000000000000) (-6114001049 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-3416393444 / 1000000000000) (-3416393329 / 1000000000000)
      | 1 => orderedInterval (-5713199584 / 1000000000000) (-5713197471 / 1000000000000)
      | 2 => orderedInterval (1997978326 / 1000000000000) (1997979835 / 1000000000000)
      | 3 => orderedInterval (27173557019 / 1000000000000) (27173557810 / 1000000000000)
      | 4 => orderedInterval (570932996 / 1000000000000) (570933136 / 1000000000000)
      | 5 => orderedInterval (-4236542993 / 1000000000000) (-4236541345 / 1000000000000)
      | 6 => orderedInterval (3020216980 / 1000000000000) (3020217078 / 1000000000000)
      | 7 => orderedInterval (2296469948 / 1000000000000) (2296470077 / 1000000000000)
      | _ => orderedInterval (9940630108 / 1000000000000) (9940630394 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15488654477 / 1000000000000) (15488654598 / 1000000000000)
      | 1 => orderedInterval (1358190777 / 1000000000000) (1358194084 / 1000000000000)
      | 2 => orderedInterval (-2127869587 / 1000000000000) (-2127866614 / 1000000000000)
      | 3 => orderedInterval (6360252123 / 1000000000000) (6360253860 / 1000000000000)
      | 4 => orderedInterval (-14691769794 / 1000000000000) (-14691769557 / 1000000000000)
      | 5 => orderedInterval (-3274849758 / 1000000000000) (-3274846741 / 1000000000000)
      | 6 => orderedInterval (6690739568 / 1000000000000) (6690739663 / 1000000000000)
      | 7 => orderedInterval (3237681336 / 1000000000000) (3237681408 / 1000000000000)
      | _ => orderedInterval (17631830407 / 1000000000000) (17631830815 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (2197443308 / 1000000000000) (2197443437 / 1000000000000)
      | 1 => orderedInterval (13034735029 / 1000000000000) (13034740216 / 1000000000000)
      | 2 => orderedInterval (-10087618722 / 1000000000000) (-10087612853 / 1000000000000)
      | 3 => orderedInterval (-129752356179 / 1000000000000) (-129752352318 / 1000000000000)
      | 4 => orderedInterval (-2053287172 / 1000000000000) (-2053286761 / 1000000000000)
      | 5 => orderedInterval (11587864532 / 1000000000000) (11587870080 / 1000000000000)
      | 6 => orderedInterval (-2295978226 / 1000000000000) (-2295978133 / 1000000000000)
      | 7 => orderedInterval (-2514465153 / 1000000000000) (-2514465095 / 1000000000000)
      | _ => orderedInterval (-15762143654 / 1000000000000) (-15762143017 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-11606567484 / 1000000000000) (-11606564001 / 1000000000000)
    | 1 => orderedInterval (-25576735286 / 1000000000000) (-25576731034 / 1000000000000)
    | 2 => orderedInterval (31633649356 / 1000000000000) (31633656185 / 1000000000000)
    | 3 => orderedInterval (30672859549 / 1000000000000) (30672871516 / 1000000000000)
    | _ => orderedInterval (-135645806237 / 1000000000000) (-135645784444 / 1000000000000)

theorem compactCertificate564_stateChecks0 :
    compactCertificate564.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (871 / 2)) (orderedInterval (14757349272 / 1000000000000) (14757349462 / 1000000000000), orderedInterval (-35287820574 / 1000000000000) (-35287820384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1283149315621771 / 4000000000000)) (orderedInterval (40287878028 / 1000000000000) (40287878029 / 1000000000000), orderedInterval (18948762851 / 1000000000000) (18948762852 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (414944124705643 / 800000000000)) (orderedInterval (-31262617989 / 1000000000000) (-31262617987 / 1000000000000), orderedInterval (-15782278418 / 1000000000000) (-15782278416 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_stateChecks1 :
    compactCertificate564.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (374419770078497 / 4000000000000)) (orderedInterval (11607985894 / 1000000000000) (11607985895 / 1000000000000), orderedInterval (81586523759 / 1000000000000) (81586523761 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1005744168928109 / 4000000000000)) (orderedInterval (39212505938 / 1000000000000) (39212505939 / 1000000000000), orderedInterval (31454760636 / 1000000000000) (31454760637 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2730791063743353 / 4000000000000)) (orderedInterval (-30006981955 / 1000000000000) (-30006970349 / 1000000000000), orderedInterval (5686523276 / 1000000000000) (5686534882 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_stateChecks2 :
    compactCertificate564.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2011488337857089 / 4000000000000)) (orderedInterval (29986132706 / 1000000000000) (29986132707 / 1000000000000), orderedInterval (19122187535 / 1000000000000) (19122187536 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (3446719551638597 / 4000000000000)) (orderedInterval (27050788607 / 1000000000000) (27050800458 / 1000000000000), orderedInterval (-2674042006 / 1000000000000) (-2674030154 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2538838021711823 / 4000000000000)) (orderedInterval (24669617296 / 1000000000000) (24669617297 / 1000000000000), orderedInterval (19840565904 / 1000000000000) (19840565905 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_stateChecks3 :
    compactCertificate564.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 310 12 (3895230416804129 / 4000000000000)) (orderedInterval (16455010554 / 1000000000000) (16455010555 / 1000000000000), orderedInterval (19561311207 / 1000000000000) (19561311208 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2248912329697241 / 4000000000000)) (orderedInterval (-20847897131 / 1000000000000) (-20847897130 / 1000000000000), orderedInterval (-26395114110 / 1000000000000) (-26395114109 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 318 12 (3990734393689069 / 4000000000000)) (orderedInterval (-13366517154 / 1000000000000) (-13366517122 / 1000000000000), orderedInterval (21441113098 / 1000000000000) (21441113130 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_stateChecks4 :
    compactCertificate564.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 297 12 (3728661735034561 / 4000000000000)) (orderedInterval (2669299032 / 1000000000000) (2669299033 / 1000000000000), orderedInterval (-25998011131 / 1000000000000) (-25998011130 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2660948953536913 / 4000000000000)) (orderedInterval (148676182 / 1000000000000) (148676183 / 1000000000000), orderedInterval (30934653954 / 1000000000000) (30934653955 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3017232506784327 / 4000000000000)) (orderedInterval (26035695439 / 1000000000000) (26035695443 / 1000000000000), orderedInterval (12871530123 / 1000000000000) (12871530127 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_stateChecks5 :
    compactCertificate564.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2515453901855063 / 4000000000000)) (orderedInterval (30900304762 / 1000000000000) (30900304811 / 1000000000000), orderedInterval (7558617833 / 1000000000000) (7558617882 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2222479808352323 / 4000000000000)) (orderedInterval (-11391215308 / 1000000000000) (-11391215307 / 1000000000000), orderedInterval (-31864870294 / 1000000000000) (-31864870293 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (644161273771977 / 800000000000)) (orderedInterval (27720827928 / 1000000000000) (27720845685 / 1000000000000), orderedInterval (-4727750077 / 1000000000000) (-4727732320 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_stateChecks6 :
    compactCertificate564.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1781783983603819 / 4000000000000)) (orderedInterval (4711627482 / 1000000000000) (4711627483 / 1000000000000), orderedInterval (37504380717 / 1000000000000) (37504380718 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1510438015618259 / 4000000000000)) (orderedInterval (40486370325 / 1000000000000) (40486370347 / 1000000000000), orderedInterval (6785497086 / 1000000000000) (6785497107 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (945161978288177 / 4000000000000)) (orderedInterval (-51563722312 / 1000000000000) (-51563722296 / 1000000000000), orderedInterval (-5840824993 / 1000000000000) (-5840824977 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_stateChecks7 :
    compactCertificate564.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (508311255390159 / 4000000000000)) (orderedInterval (57285911135 / 1000000000000) (57285962636 / 1000000000000), orderedInterval (-41794564178 / 1000000000000) (-41794512677 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1380163939007477 / 4000000000000)) (orderedInterval (10661498884 / 1000000000000) (10661498885 / 1000000000000), orderedInterval (41594521059 / 1000000000000) (41594521060 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1884495864870229 / 4000000000000)) (orderedInterval (22833070216 / 1000000000000) (22833070217 / 1000000000000), orderedInterval (28784269013 / 1000000000000) (28784269014 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_stateChecks8 :
    compactCertificate564.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (796838021711823 / 4000000000000)) (orderedInterval (-49524949161 / 1000000000000) (-49524926043 / 1000000000000), orderedInterval (27382409325 / 1000000000000) (27382432443 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 258 12 (3239102319134383 / 4000000000000)) (orderedInterval (838763146 / 1000000000000) (838763147 / 1000000000000), orderedInterval (28025626673 / 1000000000000) (28025626674 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2163570236017697 / 4000000000000)) (orderedInterval (33265867843 / 1000000000000) (33265867866 / 1000000000000), orderedInterval (8357436186 / 1000000000000) (8357436209 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_states : ∀ j,
    BesselStateValid (compactCertificate564.point j) (compactCertificate564.state j) :=
  compactCertificate564.statesValid_of_checks3 compactCertificate564_stateChecks0
    compactCertificate564_stateChecks1 compactCertificate564_stateChecks2
    compactCertificate564_stateChecks3 compactCertificate564_stateChecks4
    compactCertificate564_stateChecks5 compactCertificate564_stateChecks6
    compactCertificate564_stateChecks7 compactCertificate564_stateChecks8

theorem compactCertificate564_chunkChecks0_0 :
    compactCertificate564.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (871 / 2) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (14757349272 / 1000000000000) (14757349462 / 1000000000000), orderedInterval (-35287820574 / 1000000000000) (-35287820384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1283149315621771 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40287878028 / 1000000000000) (40287878029 / 1000000000000), orderedInterval (18948762851 / 1000000000000) (18948762852 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (414944124705643 / 800000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31262617989 / 1000000000000) (-31262617987 / 1000000000000), orderedInterval (-15782278418 / 1000000000000) (-15782278416 / 1000000000000)))) (orderedInterval (4390175427 / 1000000000000) (4390175533 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (374419770078497 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (11607985894 / 1000000000000) (11607985895 / 1000000000000), orderedInterval (81586523759 / 1000000000000) (81586523761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1005744168928109 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39212505938 / 1000000000000) (39212505939 / 1000000000000), orderedInterval (31454760636 / 1000000000000) (31454760637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2730791063743353 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30006981955 / 1000000000000) (-30006970349 / 1000000000000), orderedInterval (5686523276 / 1000000000000) (5686534882 / 1000000000000)))) (orderedInterval (3438963363 / 1000000000000) (3438964241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2011488337857089 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29986132706 / 1000000000000) (29986132707 / 1000000000000), orderedInterval (19122187535 / 1000000000000) (19122187536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3446719551638597 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27050788607 / 1000000000000) (27050800458 / 1000000000000), orderedInterval (-2674042006 / 1000000000000) (-2674030154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2538838021711823 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24669617296 / 1000000000000) (24669617297 / 1000000000000), orderedInterval (19840565904 / 1000000000000) (19840565905 / 1000000000000)))) (orderedInterval (-238138952 / 1000000000000) (-238138561 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_chunkChecks0_1 :
    compactCertificate564.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3895230416804129 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16455010554 / 1000000000000) (16455010555 / 1000000000000), orderedInterval (19561311207 / 1000000000000) (19561311208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2248912329697241 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20847897131 / 1000000000000) (-20847897130 / 1000000000000), orderedInterval (-26395114110 / 1000000000000) (-26395114109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3990734393689069 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13366517154 / 1000000000000) (-13366517122 / 1000000000000), orderedInterval (21441113098 / 1000000000000) (21441113130 / 1000000000000)))) (orderedInterval (-6368643573 / 1000000000000) (-6368643396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3728661735034561 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2669299032 / 1000000000000) (2669299033 / 1000000000000), orderedInterval (-25998011131 / 1000000000000) (-25998011130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2660948953536913 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (148676182 / 1000000000000) (148676183 / 1000000000000), orderedInterval (30934653954 / 1000000000000) (30934653955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3017232506784327 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26035695439 / 1000000000000) (26035695443 / 1000000000000), orderedInterval (12871530123 / 1000000000000) (12871530127 / 1000000000000)))) (orderedInterval (-165885481 / 1000000000000) (-165885428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2515453901855063 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30900304762 / 1000000000000) (30900304811 / 1000000000000), orderedInterval (7558617833 / 1000000000000) (7558617882 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2222479808352323 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11391215308 / 1000000000000) (-11391215307 / 1000000000000), orderedInterval (-31864870294 / 1000000000000) (-31864870293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (644161273771977 / 800000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27720827928 / 1000000000000) (27720845685 / 1000000000000), orderedInterval (-4727750077 / 1000000000000) (-4727732320 / 1000000000000)))) (orderedInterval (1718470592 / 1000000000000) (1718471090 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_chunkChecks0_2 :
    compactCertificate564.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1781783983603819 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4711627482 / 1000000000000) (4711627483 / 1000000000000), orderedInterval (37504380717 / 1000000000000) (37504380718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1510438015618259 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40486370325 / 1000000000000) (40486370347 / 1000000000000), orderedInterval (6785497086 / 1000000000000) (6785497107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (945161978288177 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51563722312 / 1000000000000) (-51563722296 / 1000000000000), orderedInterval (-5840824993 / 1000000000000) (-5840824977 / 1000000000000)))) (orderedInterval (-4723551413 / 1000000000000) (-4723551301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (508311255390159 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (57285911135 / 1000000000000) (57285962636 / 1000000000000), orderedInterval (-41794564178 / 1000000000000) (-41794512677 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1380163939007477 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10661498884 / 1000000000000) (10661498885 / 1000000000000), orderedInterval (41594521059 / 1000000000000) (41594521060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1884495864870229 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22833070216 / 1000000000000) (22833070217 / 1000000000000), orderedInterval (28784269013 / 1000000000000) (28784269014 / 1000000000000)))) (orderedInterval (-3049568683 / 1000000000000) (-3049567679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (796838021711823 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49524949161 / 1000000000000) (-49524926043 / 1000000000000), orderedInterval (27382409325 / 1000000000000) (27382432443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3239102319134383 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (838763146 / 1000000000000) (838763147 / 1000000000000), orderedInterval (28025626673 / 1000000000000) (28025626674 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2163570236017697 / 4000000000000) 0 (IntervalRat.scale (871 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33265867843 / 1000000000000) (33265867866 / 1000000000000), orderedInterval (8357436186 / 1000000000000) (8357436209 / 1000000000000)))) (orderedInterval (-6608388764 / 1000000000000) (-6608388500 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_chunkChecks0 :
    compactCertificate564.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate564.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate564_chunkChecks0_0
    compactCertificate564_chunkChecks0_1 compactCertificate564_chunkChecks0_2

theorem compactCertificate564_chunkChecks1_0 :
    compactCertificate564.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (871 / 2) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (14757349272 / 1000000000000) (14757349462 / 1000000000000), orderedInterval (-35287820574 / 1000000000000) (-35287820384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1283149315621771 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40287878028 / 1000000000000) (40287878029 / 1000000000000), orderedInterval (18948762851 / 1000000000000) (18948762852 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (414944124705643 / 800000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31262617989 / 1000000000000) (-31262617987 / 1000000000000), orderedInterval (-15782278418 / 1000000000000) (-15782278416 / 1000000000000)))) (orderedInterval (-14959809946 / 1000000000000) (-14959809837 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (374419770078497 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (11607985894 / 1000000000000) (11607985895 / 1000000000000), orderedInterval (81586523759 / 1000000000000) (81586523761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1005744168928109 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39212505938 / 1000000000000) (39212505939 / 1000000000000), orderedInterval (31454760636 / 1000000000000) (31454760637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2730791063743353 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30006981955 / 1000000000000) (-30006970349 / 1000000000000), orderedInterval (5686523276 / 1000000000000) (5686534882 / 1000000000000)))) (orderedInterval (-160899635 / 1000000000000) (-160898281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2011488337857089 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29986132706 / 1000000000000) (29986132707 / 1000000000000), orderedInterval (19122187535 / 1000000000000) (19122187536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3446719551638597 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27050788607 / 1000000000000) (27050800458 / 1000000000000), orderedInterval (-2674042006 / 1000000000000) (-2674030154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2538838021711823 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24669617296 / 1000000000000) (24669617297 / 1000000000000), orderedInterval (19840565904 / 1000000000000) (19840565905 / 1000000000000)))) (orderedInterval (862037438 / 1000000000000) (862038204 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_chunkChecks1_1 :
    compactCertificate564.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3895230416804129 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16455010554 / 1000000000000) (16455010555 / 1000000000000), orderedInterval (19561311207 / 1000000000000) (19561311208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2248912329697241 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20847897131 / 1000000000000) (-20847897130 / 1000000000000), orderedInterval (-26395114110 / 1000000000000) (-26395114109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3990734393689069 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13366517154 / 1000000000000) (-13366517122 / 1000000000000), orderedInterval (21441113098 / 1000000000000) (21441113130 / 1000000000000)))) (orderedInterval (-3314296942 / 1000000000000) (-3314296574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3728661735034561 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2669299032 / 1000000000000) (2669299033 / 1000000000000), orderedInterval (-25998011131 / 1000000000000) (-25998011130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2660948953536913 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (148676182 / 1000000000000) (148676183 / 1000000000000), orderedInterval (30934653954 / 1000000000000) (30934653955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3017232506784327 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26035695439 / 1000000000000) (26035695443 / 1000000000000), orderedInterval (12871530123 / 1000000000000) (12871530127 / 1000000000000)))) (orderedInterval (5360209263 / 1000000000000) (5360209348 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2515453901855063 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30900304762 / 1000000000000) (30900304811 / 1000000000000), orderedInterval (7558617833 / 1000000000000) (7558617882 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2222479808352323 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11391215308 / 1000000000000) (-11391215307 / 1000000000000), orderedInterval (-31864870294 / 1000000000000) (-31864870293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (644161273771977 / 800000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27720827928 / 1000000000000) (27720845685 / 1000000000000), orderedInterval (-4727750077 / 1000000000000) (-4727732320 / 1000000000000)))) (orderedInterval (2228715303 / 1000000000000) (2228716206 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_chunkChecks1_2 :
    compactCertificate564.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1781783983603819 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4711627482 / 1000000000000) (4711627483 / 1000000000000), orderedInterval (37504380717 / 1000000000000) (37504380718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1510438015618259 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40486370325 / 1000000000000) (40486370347 / 1000000000000), orderedInterval (6785497086 / 1000000000000) (6785497107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (945161978288177 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51563722312 / 1000000000000) (-51563722296 / 1000000000000), orderedInterval (-5840824993 / 1000000000000) (-5840824977 / 1000000000000)))) (orderedInterval (-6569795991 / 1000000000000) (-6569795888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (508311255390159 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (57285911135 / 1000000000000) (57285962636 / 1000000000000), orderedInterval (-41794564178 / 1000000000000) (-41794512677 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1380163939007477 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10661498884 / 1000000000000) (10661498885 / 1000000000000), orderedInterval (41594521059 / 1000000000000) (41594521060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1884495864870229 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22833070216 / 1000000000000) (22833070217 / 1000000000000), orderedInterval (28784269013 / 1000000000000) (28784269014 / 1000000000000)))) (orderedInterval (-2908893488 / 1000000000000) (-2908893163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (796838021711823 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49524949161 / 1000000000000) (-49524926043 / 1000000000000), orderedInterval (27382409325 / 1000000000000) (27382432443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3239102319134383 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (838763146 / 1000000000000) (838763147 / 1000000000000), orderedInterval (28025626673 / 1000000000000) (28025626674 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2163570236017697 / 4000000000000) 1 (IntervalRat.scale (871 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33265867843 / 1000000000000) (33265867866 / 1000000000000), orderedInterval (8357436186 / 1000000000000) (8357436209 / 1000000000000)))) (orderedInterval (-6114001288 / 1000000000000) (-6114001049 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_chunkChecks1 :
    compactCertificate564.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate564.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate564_chunkChecks1_0
    compactCertificate564_chunkChecks1_1 compactCertificate564_chunkChecks1_2

theorem compactCertificate564_chunkChecks2_0 :
    compactCertificate564.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (871 / 2) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (14757349272 / 1000000000000) (14757349462 / 1000000000000), orderedInterval (-35287820574 / 1000000000000) (-35287820384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1283149315621771 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40287878028 / 1000000000000) (40287878029 / 1000000000000), orderedInterval (18948762851 / 1000000000000) (18948762852 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (414944124705643 / 800000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31262617989 / 1000000000000) (-31262617987 / 1000000000000), orderedInterval (-15782278418 / 1000000000000) (-15782278416 / 1000000000000)))) (orderedInterval (-3416393444 / 1000000000000) (-3416393329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (374419770078497 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (11607985894 / 1000000000000) (11607985895 / 1000000000000), orderedInterval (81586523759 / 1000000000000) (81586523761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1005744168928109 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39212505938 / 1000000000000) (39212505939 / 1000000000000), orderedInterval (31454760636 / 1000000000000) (31454760637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2730791063743353 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30006981955 / 1000000000000) (-30006970349 / 1000000000000), orderedInterval (5686523276 / 1000000000000) (5686534882 / 1000000000000)))) (orderedInterval (-5713199584 / 1000000000000) (-5713197471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2011488337857089 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29986132706 / 1000000000000) (29986132707 / 1000000000000), orderedInterval (19122187535 / 1000000000000) (19122187536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3446719551638597 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27050788607 / 1000000000000) (27050800458 / 1000000000000), orderedInterval (-2674042006 / 1000000000000) (-2674030154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2538838021711823 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24669617296 / 1000000000000) (24669617297 / 1000000000000), orderedInterval (19840565904 / 1000000000000) (19840565905 / 1000000000000)))) (orderedInterval (1997978326 / 1000000000000) (1997979835 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_chunkChecks2_1 :
    compactCertificate564.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3895230416804129 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16455010554 / 1000000000000) (16455010555 / 1000000000000), orderedInterval (19561311207 / 1000000000000) (19561311208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2248912329697241 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20847897131 / 1000000000000) (-20847897130 / 1000000000000), orderedInterval (-26395114110 / 1000000000000) (-26395114109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3990734393689069 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13366517154 / 1000000000000) (-13366517122 / 1000000000000), orderedInterval (21441113098 / 1000000000000) (21441113130 / 1000000000000)))) (orderedInterval (27173557019 / 1000000000000) (27173557810 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3728661735034561 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2669299032 / 1000000000000) (2669299033 / 1000000000000), orderedInterval (-25998011131 / 1000000000000) (-25998011130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2660948953536913 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (148676182 / 1000000000000) (148676183 / 1000000000000), orderedInterval (30934653954 / 1000000000000) (30934653955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3017232506784327 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26035695439 / 1000000000000) (26035695443 / 1000000000000), orderedInterval (12871530123 / 1000000000000) (12871530127 / 1000000000000)))) (orderedInterval (570932996 / 1000000000000) (570933136 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2515453901855063 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30900304762 / 1000000000000) (30900304811 / 1000000000000), orderedInterval (7558617833 / 1000000000000) (7558617882 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2222479808352323 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11391215308 / 1000000000000) (-11391215307 / 1000000000000), orderedInterval (-31864870294 / 1000000000000) (-31864870293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (644161273771977 / 800000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27720827928 / 1000000000000) (27720845685 / 1000000000000), orderedInterval (-4727750077 / 1000000000000) (-4727732320 / 1000000000000)))) (orderedInterval (-4236542993 / 1000000000000) (-4236541345 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_chunkChecks2_2 :
    compactCertificate564.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1781783983603819 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4711627482 / 1000000000000) (4711627483 / 1000000000000), orderedInterval (37504380717 / 1000000000000) (37504380718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1510438015618259 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40486370325 / 1000000000000) (40486370347 / 1000000000000), orderedInterval (6785497086 / 1000000000000) (6785497107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (945161978288177 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51563722312 / 1000000000000) (-51563722296 / 1000000000000), orderedInterval (-5840824993 / 1000000000000) (-5840824977 / 1000000000000)))) (orderedInterval (3020216980 / 1000000000000) (3020217078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (508311255390159 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (57285911135 / 1000000000000) (57285962636 / 1000000000000), orderedInterval (-41794564178 / 1000000000000) (-41794512677 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1380163939007477 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10661498884 / 1000000000000) (10661498885 / 1000000000000), orderedInterval (41594521059 / 1000000000000) (41594521060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1884495864870229 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22833070216 / 1000000000000) (22833070217 / 1000000000000), orderedInterval (28784269013 / 1000000000000) (28784269014 / 1000000000000)))) (orderedInterval (2296469948 / 1000000000000) (2296470077 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (796838021711823 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49524949161 / 1000000000000) (-49524926043 / 1000000000000), orderedInterval (27382409325 / 1000000000000) (27382432443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3239102319134383 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (838763146 / 1000000000000) (838763147 / 1000000000000), orderedInterval (28025626673 / 1000000000000) (28025626674 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2163570236017697 / 4000000000000) 2 (IntervalRat.scale (871 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33265867843 / 1000000000000) (33265867866 / 1000000000000), orderedInterval (8357436186 / 1000000000000) (8357436209 / 1000000000000)))) (orderedInterval (9940630108 / 1000000000000) (9940630394 / 1000000000000))) = true
  rfl'

theorem compactCertificate564_chunkChecks2 :
    compactCertificate564.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate564.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate564_chunkChecks2_0
    compactCertificate564_chunkChecks2_1 compactCertificate564_chunkChecks2_2

theorem compactCertificate564_chunkChecks3_0 :
    compactCertificate564.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (871 / 2) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (14757349272 / 1000000000000) (14757349462 / 1000000000000), orderedInterval (-35287820574 / 1000000000000) (-35287820384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1283149315621771 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40287878028 / 1000000000000) (40287878029 / 1000000000000), orderedInterval (18948762851 / 1000000000000) (18948762852 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (414944124705643 / 800000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31262617989 / 1000000000000) (-31262617987 / 1000000000000), orderedInterval (-15782278418 / 1000000000000) (-15782278416 / 1000000000000)))) (orderedInterval (15488654477 / 1000000000000) (15488654598 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (374419770078497 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (11607985894 / 1000000000000) (11607985895 / 1000000000000), orderedInterval (81586523759 / 1000000000000) (81586523761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1005744168928109 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39212505938 / 1000000000000) (39212505939 / 1000000000000), orderedInterval (31454760636 / 1000000000000) (31454760637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2730791063743353 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30006981955 / 1000000000000) (-30006970349 / 1000000000000), orderedInterval (5686523276 / 1000000000000) (5686534882 / 1000000000000)))) (orderedInterval (1358190777 / 1000000000000) (1358194084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2011488337857089 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29986132706 / 1000000000000) (29986132707 / 1000000000000), orderedInterval (19122187535 / 1000000000000) (19122187536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3446719551638597 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27050788607 / 1000000000000) (27050800458 / 1000000000000), orderedInterval (-2674042006 / 1000000000000) (-2674030154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2538838021711823 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24669617296 / 1000000000000) (24669617297 / 1000000000000), orderedInterval (19840565904 / 1000000000000) (19840565905 / 1000000000000)))) (orderedInterval (-2127869587 / 1000000000000) (-2127866614 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate564_chunkChecks3_1 :
    compactCertificate564.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3895230416804129 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16455010554 / 1000000000000) (16455010555 / 1000000000000), orderedInterval (19561311207 / 1000000000000) (19561311208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2248912329697241 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20847897131 / 1000000000000) (-20847897130 / 1000000000000), orderedInterval (-26395114110 / 1000000000000) (-26395114109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3990734393689069 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13366517154 / 1000000000000) (-13366517122 / 1000000000000), orderedInterval (21441113098 / 1000000000000) (21441113130 / 1000000000000)))) (orderedInterval (6360252123 / 1000000000000) (6360253860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3728661735034561 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2669299032 / 1000000000000) (2669299033 / 1000000000000), orderedInterval (-25998011131 / 1000000000000) (-25998011130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2660948953536913 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (148676182 / 1000000000000) (148676183 / 1000000000000), orderedInterval (30934653954 / 1000000000000) (30934653955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3017232506784327 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26035695439 / 1000000000000) (26035695443 / 1000000000000), orderedInterval (12871530123 / 1000000000000) (12871530127 / 1000000000000)))) (orderedInterval (-14691769794 / 1000000000000) (-14691769557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2515453901855063 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30900304762 / 1000000000000) (30900304811 / 1000000000000), orderedInterval (7558617833 / 1000000000000) (7558617882 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2222479808352323 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11391215308 / 1000000000000) (-11391215307 / 1000000000000), orderedInterval (-31864870294 / 1000000000000) (-31864870293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (644161273771977 / 800000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27720827928 / 1000000000000) (27720845685 / 1000000000000), orderedInterval (-4727750077 / 1000000000000) (-4727732320 / 1000000000000)))) (orderedInterval (-3274849758 / 1000000000000) (-3274846741 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate564_chunkChecks3_2 :
    compactCertificate564.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1781783983603819 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4711627482 / 1000000000000) (4711627483 / 1000000000000), orderedInterval (37504380717 / 1000000000000) (37504380718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1510438015618259 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40486370325 / 1000000000000) (40486370347 / 1000000000000), orderedInterval (6785497086 / 1000000000000) (6785497107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (945161978288177 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51563722312 / 1000000000000) (-51563722296 / 1000000000000), orderedInterval (-5840824993 / 1000000000000) (-5840824977 / 1000000000000)))) (orderedInterval (6690739568 / 1000000000000) (6690739663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (508311255390159 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (57285911135 / 1000000000000) (57285962636 / 1000000000000), orderedInterval (-41794564178 / 1000000000000) (-41794512677 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1380163939007477 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10661498884 / 1000000000000) (10661498885 / 1000000000000), orderedInterval (41594521059 / 1000000000000) (41594521060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1884495864870229 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22833070216 / 1000000000000) (22833070217 / 1000000000000), orderedInterval (28784269013 / 1000000000000) (28784269014 / 1000000000000)))) (orderedInterval (3237681336 / 1000000000000) (3237681408 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (796838021711823 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49524949161 / 1000000000000) (-49524926043 / 1000000000000), orderedInterval (27382409325 / 1000000000000) (27382432443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3239102319134383 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (838763146 / 1000000000000) (838763147 / 1000000000000), orderedInterval (28025626673 / 1000000000000) (28025626674 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2163570236017697 / 4000000000000) 3 (IntervalRat.scale (871 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33265867843 / 1000000000000) (33265867866 / 1000000000000), orderedInterval (8357436186 / 1000000000000) (8357436209 / 1000000000000)))) (orderedInterval (17631830407 / 1000000000000) (17631830815 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate564_chunkChecks3 :
    compactCertificate564.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate564.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate564_chunkChecks3_0
    compactCertificate564_chunkChecks3_1 compactCertificate564_chunkChecks3_2

theorem compactCertificate564_chunkChecks4_0 :
    compactCertificate564.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (871 / 2) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (14757349272 / 1000000000000) (14757349462 / 1000000000000), orderedInterval (-35287820574 / 1000000000000) (-35287820384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1283149315621771 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40287878028 / 1000000000000) (40287878029 / 1000000000000), orderedInterval (18948762851 / 1000000000000) (18948762852 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (414944124705643 / 800000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-31262617989 / 1000000000000) (-31262617987 / 1000000000000), orderedInterval (-15782278418 / 1000000000000) (-15782278416 / 1000000000000)))) (orderedInterval (2197443308 / 1000000000000) (2197443437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (374419770078497 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (11607985894 / 1000000000000) (11607985895 / 1000000000000), orderedInterval (81586523759 / 1000000000000) (81586523761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1005744168928109 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39212505938 / 1000000000000) (39212505939 / 1000000000000), orderedInterval (31454760636 / 1000000000000) (31454760637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2730791063743353 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30006981955 / 1000000000000) (-30006970349 / 1000000000000), orderedInterval (5686523276 / 1000000000000) (5686534882 / 1000000000000)))) (orderedInterval (13034735029 / 1000000000000) (13034740216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2011488337857089 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (29986132706 / 1000000000000) (29986132707 / 1000000000000), orderedInterval (19122187535 / 1000000000000) (19122187536 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3446719551638597 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (27050788607 / 1000000000000) (27050800458 / 1000000000000), orderedInterval (-2674042006 / 1000000000000) (-2674030154 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2538838021711823 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24669617296 / 1000000000000) (24669617297 / 1000000000000), orderedInterval (19840565904 / 1000000000000) (19840565905 / 1000000000000)))) (orderedInterval (-10087618722 / 1000000000000) (-10087612853 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate564_chunkChecks4_1 :
    compactCertificate564.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3895230416804129 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (16455010554 / 1000000000000) (16455010555 / 1000000000000), orderedInterval (19561311207 / 1000000000000) (19561311208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2248912329697241 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-20847897131 / 1000000000000) (-20847897130 / 1000000000000), orderedInterval (-26395114110 / 1000000000000) (-26395114109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3990734393689069 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13366517154 / 1000000000000) (-13366517122 / 1000000000000), orderedInterval (21441113098 / 1000000000000) (21441113130 / 1000000000000)))) (orderedInterval (-129752356179 / 1000000000000) (-129752352318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3728661735034561 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2669299032 / 1000000000000) (2669299033 / 1000000000000), orderedInterval (-25998011131 / 1000000000000) (-25998011130 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2660948953536913 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (148676182 / 1000000000000) (148676183 / 1000000000000), orderedInterval (30934653954 / 1000000000000) (30934653955 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3017232506784327 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26035695439 / 1000000000000) (26035695443 / 1000000000000), orderedInterval (12871530123 / 1000000000000) (12871530127 / 1000000000000)))) (orderedInterval (-2053287172 / 1000000000000) (-2053286761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2515453901855063 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30900304762 / 1000000000000) (30900304811 / 1000000000000), orderedInterval (7558617833 / 1000000000000) (7558617882 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2222479808352323 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11391215308 / 1000000000000) (-11391215307 / 1000000000000), orderedInterval (-31864870294 / 1000000000000) (-31864870293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (644161273771977 / 800000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27720827928 / 1000000000000) (27720845685 / 1000000000000), orderedInterval (-4727750077 / 1000000000000) (-4727732320 / 1000000000000)))) (orderedInterval (11587864532 / 1000000000000) (11587870080 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate564_chunkChecks4_2 :
    compactCertificate564.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1781783983603819 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4711627482 / 1000000000000) (4711627483 / 1000000000000), orderedInterval (37504380717 / 1000000000000) (37504380718 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1510438015618259 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40486370325 / 1000000000000) (40486370347 / 1000000000000), orderedInterval (6785497086 / 1000000000000) (6785497107 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (945161978288177 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51563722312 / 1000000000000) (-51563722296 / 1000000000000), orderedInterval (-5840824993 / 1000000000000) (-5840824977 / 1000000000000)))) (orderedInterval (-2295978226 / 1000000000000) (-2295978133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (508311255390159 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (57285911135 / 1000000000000) (57285962636 / 1000000000000), orderedInterval (-41794564178 / 1000000000000) (-41794512677 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1380163939007477 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10661498884 / 1000000000000) (10661498885 / 1000000000000), orderedInterval (41594521059 / 1000000000000) (41594521060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1884495864870229 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (22833070216 / 1000000000000) (22833070217 / 1000000000000), orderedInterval (28784269013 / 1000000000000) (28784269014 / 1000000000000)))) (orderedInterval (-2514465153 / 1000000000000) (-2514465095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (796838021711823 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49524949161 / 1000000000000) (-49524926043 / 1000000000000), orderedInterval (27382409325 / 1000000000000) (27382432443 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3239102319134383 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (838763146 / 1000000000000) (838763147 / 1000000000000), orderedInterval (28025626673 / 1000000000000) (28025626674 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2163570236017697 / 4000000000000) 4 (IntervalRat.scale (871 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (33265867843 / 1000000000000) (33265867866 / 1000000000000), orderedInterval (8357436186 / 1000000000000) (8357436209 / 1000000000000)))) (orderedInterval (-15762143654 / 1000000000000) (-15762143017 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate564_chunkChecks4 :
    compactCertificate564.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate564.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate564_chunkChecks4_0
    compactCertificate564_chunkChecks4_1 compactCertificate564_chunkChecks4_2

theorem compactCertificate564_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate564.chunkCheck r b = true :=
  compactCertificate564.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate564_chunkChecks0
    · exact compactCertificate564_chunkChecks1
    · exact compactCertificate564_chunkChecks2
    · exact compactCertificate564_chunkChecks3
    · exact compactCertificate564_chunkChecks4)

theorem compactCertificate564_coefficient0 :
    compactCertificate564.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate564_coefficient1 :
    compactCertificate564.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate564_coefficient2 :
    compactCertificate564.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate564_coefficient3 :
    compactCertificate564.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate564_coefficient4 :
    compactCertificate564.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate564_coefficients : ∀ r : Fin 5,
    compactCertificate564.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate564_coefficient0
  · exact compactCertificate564_coefficient1
  · exact compactCertificate564_coefficient2
  · exact compactCertificate564_coefficient3
  · exact compactCertificate564_coefficient4

theorem compactCertificate564_lower : (1 : ℚ) ≤ compactCertificate564.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate564, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate564_proves {t : ℝ} (ht : t ∈ compactCertificate564.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate564.proves compactCertificate564_states compactCertificate564_chunks
    compactCertificate564_coefficients compactCertificate564_lower ht

end Erdos232
