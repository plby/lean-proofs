/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate434 : CompactCertificate where
  left := 305
  right := 306
  center := 611 / 2
  grid := fun i =>
    match i.val with
    | 0 => 97
    | 1 => 72
    | 2 => 116
    | 3 => 21
    | 4 => 56
    | 5 => 153
    | 6 => 112
    | 7 => 193
    | 8 => 142
    | 9 => 218
    | 10 => 126
    | 11 => 223
    | 12 => 208
    | 13 => 149
    | 14 => 169
    | 15 => 140
    | 16 => 124
    | 17 => 180
    | 18 => 100
    | 19 => 84
    | 20 => 53
    | 21 => 28
    | 22 => 77
    | 23 => 105
    | 24 => 45
    | 25 => 181
    | _ => 121
  point := fun i =>
    match i.val with
    | 0 => 611 / 2
    | 1 => 900119669167511 / 4000000000000
    | 2 => 291080206883063 / 800000000000
    | 3 => 262652674532677 / 4000000000000
    | 4 => 705522028949569 / 4000000000000
    | 5 => 1915629552178173 / 4000000000000
    | 6 => 1411044057899749 / 4000000000000
    | 7 => 2417848043686777 / 4000000000000
    | 8 => 1780975925678443 / 4000000000000
    | 9 => 2732475068504389 / 4000000000000
    | 10 => 1577595216354781 / 4000000000000
    | 11 => 2799470395572929 / 4000000000000
    | 12 => 2615628381292901 / 4000000000000
    | 13 => 1866635833078133 / 4000000000000
    | 14 => 2116566086848707 / 4000000000000
    | 15 => 1764572140107283 / 4000000000000
    | 16 => 1559052999888943 / 4000000000000
    | 17 => 451874326377357 / 800000000000
    | 18 => 1249908167602679 / 4000000000000
    | 19 => 1059560996030719 / 4000000000000
    | 20 => 663024074321557 / 4000000000000
    | 21 => 356576552288619 / 4000000000000
    | 22 => 968174703482857 / 4000000000000
    | 23 => 1321959785804489 / 4000000000000
    | 24 => 558975925678443 / 4000000000000
    | 25 => 2272206104467403 / 4000000000000
    | _ => 1517728374519877 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-45639903767 / 1000000000000) (-45639903658 / 1000000000000), orderedInterval (-851680903 / 1000000000000) (-851680793 / 1000000000000))
    | 1 => (orderedInterval (-19724386471 / 1000000000000) (-19724385864 / 1000000000000), orderedInterval (49440168562 / 1000000000000) (49440169169 / 1000000000000))
    | 2 => (orderedInterval (8742819217 / 1000000000000) (8742819218 / 1000000000000), orderedInterval (40893239842 / 1000000000000) (40893239843 / 1000000000000))
    | 3 => (orderedInterval (-44874754804 / 1000000000000) (-44874754803 / 1000000000000), orderedInterval (-87303363660 / 1000000000000) (-87303363659 / 1000000000000))
    | 4 => (orderedInterval (56742259263 / 1000000000000) (56742259264 / 1000000000000), orderedInterval (19578934507 / 1000000000000) (19578934508 / 1000000000000))
    | 5 => (orderedInterval (30098823620 / 1000000000000) (30098893317 / 1000000000000), orderedInterval (-20607548564 / 1000000000000) (-20607478867 / 1000000000000))
    | 6 => (orderedInterval (42191609349 / 1000000000000) (42191610235 / 1000000000000), orderedInterval (-5013945391 / 1000000000000) (-5013944505 / 1000000000000))
    | 7 => (orderedInterval (28624916199 / 1000000000000) (28625018550 / 1000000000000), orderedInterval (-15314627447 / 1000000000000) (-15314525096 / 1000000000000))
    | 8 => (orderedInterval (-2910908661 / 1000000000000) (-2910908659 / 1000000000000), orderedInterval (37704061968 / 1000000000000) (37704061969 / 1000000000000))
    | 9 => (orderedInterval (-25064100747 / 1000000000000) (-25064074960 / 1000000000000), orderedInterval (17445974475 / 1000000000000) (17446000262 / 1000000000000))
    | 10 => (orderedInterval (-24530851375 / 1000000000000) (-24530846044 / 1000000000000), orderedInterval (31849175683 / 1000000000000) (31849181014 / 1000000000000))
    | 11 => (orderedInterval (-2339776664 / 1000000000000) (-2339776663 / 1000000000000), orderedInterval (-30067491082 / 1000000000000) (-30067491081 / 1000000000000))
    | 12 => (orderedInterval (29520747638 / 1000000000000) (29520747653 / 1000000000000), orderedInterval (10081301057 / 1000000000000) (10081301072 / 1000000000000))
    | 13 => (orderedInterval (22447132295 / 1000000000000) (22447135771 / 1000000000000), orderedInterval (-29355505599 / 1000000000000) (-29355502122 / 1000000000000))
    | 14 => (orderedInterval (29233503765 / 1000000000000) (29233577059 / 1000000000000), orderedInterval (-18696295889 / 1000000000000) (-18696222596 / 1000000000000))
    | 15 => (orderedInterval (32692085666 / 1000000000000) (32692175956 / 1000000000000), orderedInterval (-19384920460 / 1000000000000) (-19384830170 / 1000000000000))
    | 16 => (orderedInterval (33806324709 / 1000000000000) (33806324710 / 1000000000000), orderedInterval (22103455794 / 1000000000000) (22103455795 / 1000000000000))
    | 17 => (orderedInterval (4731504970 / 1000000000000) (4731504971 / 1000000000000), orderedInterval (33232648373 / 1000000000000) (33232648374 / 1000000000000))
    | 18 => (orderedInterval (-35278916925 / 1000000000000) (-35278840770 / 1000000000000), orderedInterval (28211925310 / 1000000000000) (28212001465 / 1000000000000))
    | 19 => (orderedInterval (47940660026 / 1000000000000) (47940661605 / 1000000000000), orderedInterval (-10338577009 / 1000000000000) (-10338575430 / 1000000000000))
    | 20 => (orderedInterval (-2246162803 / 1000000000000) (-2246162801 / 1000000000000), orderedInterval (-61926059069 / 1000000000000) (-61926059066 / 1000000000000))
    | 21 => (orderedInterval (78072412128 / 1000000000000) (78072416581 / 1000000000000), orderedInterval (-32781110526 / 1000000000000) (-32781106073 / 1000000000000))
    | 22 => (orderedInterval (-40985968906 / 1000000000000) (-40985968905 / 1000000000000), orderedInterval (-30742826813 / 1000000000000) (-30742826812 / 1000000000000))
    | 23 => (orderedInterval (-43307327856 / 1000000000000) (-43307327840 / 1000000000000), orderedInterval (-7059377055 / 1000000000000) (-7059377039 / 1000000000000))
    | 24 => (orderedInterval (50402892826 / 1000000000000) (50402993507 / 1000000000000), orderedInterval (-45070860224 / 1000000000000) (-45070759544 / 1000000000000))
    | 25 => (orderedInterval (-6927321293 / 1000000000000) (-6927321292 / 1000000000000), orderedInterval (-32746313316 / 1000000000000) (-32746313315 / 1000000000000))
    | _ => (orderedInterval (-3455116329 / 1000000000000) (-3455116327 / 1000000000000), orderedInterval (-40810717273 / 1000000000000) (-40810717272 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-17760814566 / 1000000000000) (-17760814495 / 1000000000000)
      | 1 => orderedInterval (418898692 / 1000000000000) (418903684 / 1000000000000)
      | 2 => orderedInterval (-953261029 / 1000000000000) (-953257854 / 1000000000000)
      | 3 => orderedInterval (2303436175 / 1000000000000) (2303441273 / 1000000000000)
      | 4 => orderedInterval (1441785810 / 1000000000000) (1441786547 / 1000000000000)
      | 5 => orderedInterval (-1435961006 / 1000000000000) (-1435959934 / 1000000000000)
      | 6 => orderedInterval (2854256187 / 1000000000000) (2854268530 / 1000000000000)
      | 7 => orderedInterval (2807251364 / 1000000000000) (2807251484 / 1000000000000)
      | _ => orderedInterval (1516012867 / 1000000000000) (1516013560 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (2859758517 / 1000000000000) (2859758589 / 1000000000000)
      | 1 => orderedInterval (2912835636 / 1000000000000) (2912843445 / 1000000000000)
      | 2 => orderedInterval (2262668829 / 1000000000000) (2262675105 / 1000000000000)
      | 3 => orderedInterval (-13677139899 / 1000000000000) (-13677128892 / 1000000000000)
      | 4 => orderedInterval (-4466002564 / 1000000000000) (-4466001359 / 1000000000000)
      | 5 => orderedInterval (-363820074 / 1000000000000) (-363818526 / 1000000000000)
      | 6 => orderedInterval (-5200365638 / 1000000000000) (-5200353035 / 1000000000000)
      | 7 => orderedInterval (1314492575 / 1000000000000) (1314492634 / 1000000000000)
      | _ => orderedInterval (14342426371 / 1000000000000) (14342426769 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17452685735 / 1000000000000) (17452685809 / 1000000000000)
      | 1 => orderedInterval (4535579728 / 1000000000000) (4535591987 / 1000000000000)
      | 2 => orderedInterval (3598477428 / 1000000000000) (3598489861 / 1000000000000)
      | 3 => orderedInterval (-17448332356 / 1000000000000) (-17448308214 / 1000000000000)
      | 4 => orderedInterval (-2052773963 / 1000000000000) (-2052771980 / 1000000000000)
      | 5 => orderedInterval (1948900452 / 1000000000000) (1948902695 / 1000000000000)
      | 6 => orderedInterval (-3822879611 / 1000000000000) (-3822866695 / 1000000000000)
      | 7 => orderedInterval (-4349461649 / 1000000000000) (-4349461607 / 1000000000000)
      | _ => orderedInterval (-3060160265 / 1000000000000) (-3060159960 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3957644526 / 1000000000000) (-3957644447 / 1000000000000)
      | 1 => orderedInterval (-5805361636 / 1000000000000) (-5805342422 / 1000000000000)
      | 2 => orderedInterval (-6491568923 / 1000000000000) (-6491544333 / 1000000000000)
      | 3 => orderedInterval (81027637984 / 1000000000000) (81027691321 / 1000000000000)
      | 4 => orderedInterval (11193891434 / 1000000000000) (11193894708 / 1000000000000)
      | 5 => orderedInterval (-2083583727 / 1000000000000) (-2083580482 / 1000000000000)
      | 6 => orderedInterval (4780059547 / 1000000000000) (4780072743 / 1000000000000)
      | 7 => orderedInterval (-1032603444 / 1000000000000) (-1032603406 / 1000000000000)
      | _ => orderedInterval (-31770704371 / 1000000000000) (-31770704041 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-17085793688 / 1000000000000) (-17085793605 / 1000000000000)
      | 1 => orderedInterval (-12652366440 / 1000000000000) (-12652336261 / 1000000000000)
      | 2 => orderedInterval (-13806425203 / 1000000000000) (-13806376481 / 1000000000000)
      | 3 => orderedInterval (96598915849 / 1000000000000) (96599034458 / 1000000000000)
      | 4 => orderedInterval (-1034621424 / 1000000000000) (-1034615982 / 1000000000000)
      | 5 => orderedInterval (-2054976681 / 1000000000000) (-2054971973 / 1000000000000)
      | 6 => orderedInterval (4602678813 / 1000000000000) (4602692342 / 1000000000000)
      | 7 => orderedInterval (4908326341 / 1000000000000) (4908326380 / 1000000000000)
      | _ => orderedInterval (8504547263 / 1000000000000) (8504547726 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-8808395506 / 1000000000000) (-8808367205 / 1000000000000)
    | 1 => orderedInterval (-15146247 / 1000000000000) (-15105270 / 1000000000000)
    | 2 => orderedInterval (-3197964501 / 1000000000000) (-3197898104 / 1000000000000)
    | 3 => orderedInterval (45860122338 / 1000000000000) (45860239641 / 1000000000000)
    | _ => orderedInterval (67980284830 / 1000000000000) (67980506604 / 1000000000000)

theorem compactCertificate434_stateChecks0 :
    compactCertificate434.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (611 / 2)) (orderedInterval (-45639903767 / 1000000000000) (-45639903658 / 1000000000000), orderedInterval (-851680903 / 1000000000000) (-851680793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (900119669167511 / 4000000000000)) (orderedInterval (-19724386471 / 1000000000000) (-19724385864 / 1000000000000), orderedInterval (49440168562 / 1000000000000) (49440169169 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (291080206883063 / 800000000000)) (orderedInterval (8742819217 / 1000000000000) (8742819218 / 1000000000000), orderedInterval (40893239842 / 1000000000000) (40893239843 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_stateChecks1 :
    compactCertificate434.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (262652674532677 / 4000000000000)) (orderedInterval (-44874754804 / 1000000000000) (-44874754803 / 1000000000000), orderedInterval (-87303363660 / 1000000000000) (-87303363659 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (705522028949569 / 4000000000000)) (orderedInterval (56742259263 / 1000000000000) (56742259264 / 1000000000000), orderedInterval (19578934507 / 1000000000000) (19578934508 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1915629552178173 / 4000000000000)) (orderedInterval (30098823620 / 1000000000000) (30098893317 / 1000000000000), orderedInterval (-20607548564 / 1000000000000) (-20607478867 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_stateChecks2 :
    compactCertificate434.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1411044057899749 / 4000000000000)) (orderedInterval (42191609349 / 1000000000000) (42191610235 / 1000000000000), orderedInterval (-5013945391 / 1000000000000) (-5013944505 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2417848043686777 / 4000000000000)) (orderedInterval (28624916199 / 1000000000000) (28625018550 / 1000000000000), orderedInterval (-15314627447 / 1000000000000) (-15314525096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1780975925678443 / 4000000000000)) (orderedInterval (-2910908661 / 1000000000000) (-2910908659 / 1000000000000), orderedInterval (37704061968 / 1000000000000) (37704061969 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_stateChecks3 :
    compactCertificate434.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2732475068504389 / 4000000000000)) (orderedInterval (-25064100747 / 1000000000000) (-25064074960 / 1000000000000), orderedInterval (17445974475 / 1000000000000) (17446000262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1577595216354781 / 4000000000000)) (orderedInterval (-24530851375 / 1000000000000) (-24530846044 / 1000000000000), orderedInterval (31849175683 / 1000000000000) (31849181014 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2799470395572929 / 4000000000000)) (orderedInterval (-2339776664 / 1000000000000) (-2339776663 / 1000000000000), orderedInterval (-30067491082 / 1000000000000) (-30067491081 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_stateChecks4 :
    compactCertificate434.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2615628381292901 / 4000000000000)) (orderedInterval (29520747638 / 1000000000000) (29520747653 / 1000000000000), orderedInterval (10081301057 / 1000000000000) (10081301072 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1866635833078133 / 4000000000000)) (orderedInterval (22447132295 / 1000000000000) (22447135771 / 1000000000000), orderedInterval (-29355505599 / 1000000000000) (-29355502122 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2116566086848707 / 4000000000000)) (orderedInterval (29233503765 / 1000000000000) (29233577059 / 1000000000000), orderedInterval (-18696295889 / 1000000000000) (-18696222596 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_stateChecks5 :
    compactCertificate434.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1764572140107283 / 4000000000000)) (orderedInterval (32692085666 / 1000000000000) (32692175956 / 1000000000000), orderedInterval (-19384920460 / 1000000000000) (-19384830170 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1559052999888943 / 4000000000000)) (orderedInterval (33806324709 / 1000000000000) (33806324710 / 1000000000000), orderedInterval (22103455794 / 1000000000000) (22103455795 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (451874326377357 / 800000000000)) (orderedInterval (4731504970 / 1000000000000) (4731504971 / 1000000000000), orderedInterval (33232648373 / 1000000000000) (33232648374 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_stateChecks6 :
    compactCertificate434.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1249908167602679 / 4000000000000)) (orderedInterval (-35278916925 / 1000000000000) (-35278840770 / 1000000000000), orderedInterval (28211925310 / 1000000000000) (28212001465 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1059560996030719 / 4000000000000)) (orderedInterval (47940660026 / 1000000000000) (47940661605 / 1000000000000), orderedInterval (-10338577009 / 1000000000000) (-10338575430 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (663024074321557 / 4000000000000)) (orderedInterval (-2246162803 / 1000000000000) (-2246162801 / 1000000000000), orderedInterval (-61926059069 / 1000000000000) (-61926059066 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_stateChecks7 :
    compactCertificate434.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (356576552288619 / 4000000000000)) (orderedInterval (78072412128 / 1000000000000) (78072416581 / 1000000000000), orderedInterval (-32781110526 / 1000000000000) (-32781106073 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (968174703482857 / 4000000000000)) (orderedInterval (-40985968906 / 1000000000000) (-40985968905 / 1000000000000), orderedInterval (-30742826813 / 1000000000000) (-30742826812 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1321959785804489 / 4000000000000)) (orderedInterval (-43307327856 / 1000000000000) (-43307327840 / 1000000000000), orderedInterval (-7059377055 / 1000000000000) (-7059377039 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_stateChecks8 :
    compactCertificate434.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (558975925678443 / 4000000000000)) (orderedInterval (50402892826 / 1000000000000) (50402993507 / 1000000000000), orderedInterval (-45070860224 / 1000000000000) (-45070759544 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2272206104467403 / 4000000000000)) (orderedInterval (-6927321293 / 1000000000000) (-6927321292 / 1000000000000), orderedInterval (-32746313316 / 1000000000000) (-32746313315 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1517728374519877 / 4000000000000)) (orderedInterval (-3455116329 / 1000000000000) (-3455116327 / 1000000000000), orderedInterval (-40810717273 / 1000000000000) (-40810717272 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_states : ∀ j,
    BesselStateValid (compactCertificate434.point j) (compactCertificate434.state j) :=
  compactCertificate434.statesValid_of_checks3 compactCertificate434_stateChecks0
    compactCertificate434_stateChecks1 compactCertificate434_stateChecks2
    compactCertificate434_stateChecks3 compactCertificate434_stateChecks4
    compactCertificate434_stateChecks5 compactCertificate434_stateChecks6
    compactCertificate434_stateChecks7 compactCertificate434_stateChecks8

theorem compactCertificate434_chunkChecks0_0 :
    compactCertificate434.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (611 / 2) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45639903767 / 1000000000000) (-45639903658 / 1000000000000), orderedInterval (-851680903 / 1000000000000) (-851680793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (900119669167511 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19724386471 / 1000000000000) (-19724385864 / 1000000000000), orderedInterval (49440168562 / 1000000000000) (49440169169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (291080206883063 / 800000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8742819217 / 1000000000000) (8742819218 / 1000000000000), orderedInterval (40893239842 / 1000000000000) (40893239843 / 1000000000000)))) (orderedInterval (-17760814566 / 1000000000000) (-17760814495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (262652674532677 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44874754804 / 1000000000000) (-44874754803 / 1000000000000), orderedInterval (-87303363660 / 1000000000000) (-87303363659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (705522028949569 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56742259263 / 1000000000000) (56742259264 / 1000000000000), orderedInterval (19578934507 / 1000000000000) (19578934508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1915629552178173 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30098823620 / 1000000000000) (30098893317 / 1000000000000), orderedInterval (-20607548564 / 1000000000000) (-20607478867 / 1000000000000)))) (orderedInterval (418898692 / 1000000000000) (418903684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1411044057899749 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (42191609349 / 1000000000000) (42191610235 / 1000000000000), orderedInterval (-5013945391 / 1000000000000) (-5013944505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2417848043686777 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28624916199 / 1000000000000) (28625018550 / 1000000000000), orderedInterval (-15314627447 / 1000000000000) (-15314525096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1780975925678443 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2910908661 / 1000000000000) (-2910908659 / 1000000000000), orderedInterval (37704061968 / 1000000000000) (37704061969 / 1000000000000)))) (orderedInterval (-953261029 / 1000000000000) (-953257854 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_chunkChecks0_1 :
    compactCertificate434.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2732475068504389 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25064100747 / 1000000000000) (-25064074960 / 1000000000000), orderedInterval (17445974475 / 1000000000000) (17446000262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1577595216354781 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24530851375 / 1000000000000) (-24530846044 / 1000000000000), orderedInterval (31849175683 / 1000000000000) (31849181014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2799470395572929 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2339776664 / 1000000000000) (-2339776663 / 1000000000000), orderedInterval (-30067491082 / 1000000000000) (-30067491081 / 1000000000000)))) (orderedInterval (2303436175 / 1000000000000) (2303441273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2615628381292901 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29520747638 / 1000000000000) (29520747653 / 1000000000000), orderedInterval (10081301057 / 1000000000000) (10081301072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1866635833078133 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22447132295 / 1000000000000) (22447135771 / 1000000000000), orderedInterval (-29355505599 / 1000000000000) (-29355502122 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2116566086848707 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29233503765 / 1000000000000) (29233577059 / 1000000000000), orderedInterval (-18696295889 / 1000000000000) (-18696222596 / 1000000000000)))) (orderedInterval (1441785810 / 1000000000000) (1441786547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1764572140107283 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32692085666 / 1000000000000) (32692175956 / 1000000000000), orderedInterval (-19384920460 / 1000000000000) (-19384830170 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1559052999888943 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33806324709 / 1000000000000) (33806324710 / 1000000000000), orderedInterval (22103455794 / 1000000000000) (22103455795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (451874326377357 / 800000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4731504970 / 1000000000000) (4731504971 / 1000000000000), orderedInterval (33232648373 / 1000000000000) (33232648374 / 1000000000000)))) (orderedInterval (-1435961006 / 1000000000000) (-1435959934 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_chunkChecks0_2 :
    compactCertificate434.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1249908167602679 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35278916925 / 1000000000000) (-35278840770 / 1000000000000), orderedInterval (28211925310 / 1000000000000) (28212001465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1059560996030719 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47940660026 / 1000000000000) (47940661605 / 1000000000000), orderedInterval (-10338577009 / 1000000000000) (-10338575430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (663024074321557 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2246162803 / 1000000000000) (-2246162801 / 1000000000000), orderedInterval (-61926059069 / 1000000000000) (-61926059066 / 1000000000000)))) (orderedInterval (2854256187 / 1000000000000) (2854268530 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (356576552288619 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78072412128 / 1000000000000) (78072416581 / 1000000000000), orderedInterval (-32781110526 / 1000000000000) (-32781106073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (968174703482857 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40985968906 / 1000000000000) (-40985968905 / 1000000000000), orderedInterval (-30742826813 / 1000000000000) (-30742826812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1321959785804489 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43307327856 / 1000000000000) (-43307327840 / 1000000000000), orderedInterval (-7059377055 / 1000000000000) (-7059377039 / 1000000000000)))) (orderedInterval (2807251364 / 1000000000000) (2807251484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (558975925678443 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50402892826 / 1000000000000) (50402993507 / 1000000000000), orderedInterval (-45070860224 / 1000000000000) (-45070759544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2272206104467403 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6927321293 / 1000000000000) (-6927321292 / 1000000000000), orderedInterval (-32746313316 / 1000000000000) (-32746313315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1517728374519877 / 4000000000000) 0 (IntervalRat.scale (611 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-3455116329 / 1000000000000) (-3455116327 / 1000000000000), orderedInterval (-40810717273 / 1000000000000) (-40810717272 / 1000000000000)))) (orderedInterval (1516012867 / 1000000000000) (1516013560 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_chunkChecks0 :
    compactCertificate434.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate434.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate434_chunkChecks0_0
    compactCertificate434_chunkChecks0_1 compactCertificate434_chunkChecks0_2

theorem compactCertificate434_chunkChecks1_0 :
    compactCertificate434.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (611 / 2) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45639903767 / 1000000000000) (-45639903658 / 1000000000000), orderedInterval (-851680903 / 1000000000000) (-851680793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (900119669167511 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19724386471 / 1000000000000) (-19724385864 / 1000000000000), orderedInterval (49440168562 / 1000000000000) (49440169169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (291080206883063 / 800000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8742819217 / 1000000000000) (8742819218 / 1000000000000), orderedInterval (40893239842 / 1000000000000) (40893239843 / 1000000000000)))) (orderedInterval (2859758517 / 1000000000000) (2859758589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (262652674532677 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44874754804 / 1000000000000) (-44874754803 / 1000000000000), orderedInterval (-87303363660 / 1000000000000) (-87303363659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (705522028949569 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56742259263 / 1000000000000) (56742259264 / 1000000000000), orderedInterval (19578934507 / 1000000000000) (19578934508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1915629552178173 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30098823620 / 1000000000000) (30098893317 / 1000000000000), orderedInterval (-20607548564 / 1000000000000) (-20607478867 / 1000000000000)))) (orderedInterval (2912835636 / 1000000000000) (2912843445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1411044057899749 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (42191609349 / 1000000000000) (42191610235 / 1000000000000), orderedInterval (-5013945391 / 1000000000000) (-5013944505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2417848043686777 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28624916199 / 1000000000000) (28625018550 / 1000000000000), orderedInterval (-15314627447 / 1000000000000) (-15314525096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1780975925678443 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2910908661 / 1000000000000) (-2910908659 / 1000000000000), orderedInterval (37704061968 / 1000000000000) (37704061969 / 1000000000000)))) (orderedInterval (2262668829 / 1000000000000) (2262675105 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_chunkChecks1_1 :
    compactCertificate434.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2732475068504389 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25064100747 / 1000000000000) (-25064074960 / 1000000000000), orderedInterval (17445974475 / 1000000000000) (17446000262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1577595216354781 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24530851375 / 1000000000000) (-24530846044 / 1000000000000), orderedInterval (31849175683 / 1000000000000) (31849181014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2799470395572929 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2339776664 / 1000000000000) (-2339776663 / 1000000000000), orderedInterval (-30067491082 / 1000000000000) (-30067491081 / 1000000000000)))) (orderedInterval (-13677139899 / 1000000000000) (-13677128892 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2615628381292901 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29520747638 / 1000000000000) (29520747653 / 1000000000000), orderedInterval (10081301057 / 1000000000000) (10081301072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1866635833078133 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22447132295 / 1000000000000) (22447135771 / 1000000000000), orderedInterval (-29355505599 / 1000000000000) (-29355502122 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2116566086848707 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29233503765 / 1000000000000) (29233577059 / 1000000000000), orderedInterval (-18696295889 / 1000000000000) (-18696222596 / 1000000000000)))) (orderedInterval (-4466002564 / 1000000000000) (-4466001359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1764572140107283 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32692085666 / 1000000000000) (32692175956 / 1000000000000), orderedInterval (-19384920460 / 1000000000000) (-19384830170 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1559052999888943 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33806324709 / 1000000000000) (33806324710 / 1000000000000), orderedInterval (22103455794 / 1000000000000) (22103455795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (451874326377357 / 800000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4731504970 / 1000000000000) (4731504971 / 1000000000000), orderedInterval (33232648373 / 1000000000000) (33232648374 / 1000000000000)))) (orderedInterval (-363820074 / 1000000000000) (-363818526 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_chunkChecks1_2 :
    compactCertificate434.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1249908167602679 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35278916925 / 1000000000000) (-35278840770 / 1000000000000), orderedInterval (28211925310 / 1000000000000) (28212001465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1059560996030719 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47940660026 / 1000000000000) (47940661605 / 1000000000000), orderedInterval (-10338577009 / 1000000000000) (-10338575430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (663024074321557 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2246162803 / 1000000000000) (-2246162801 / 1000000000000), orderedInterval (-61926059069 / 1000000000000) (-61926059066 / 1000000000000)))) (orderedInterval (-5200365638 / 1000000000000) (-5200353035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (356576552288619 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78072412128 / 1000000000000) (78072416581 / 1000000000000), orderedInterval (-32781110526 / 1000000000000) (-32781106073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (968174703482857 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40985968906 / 1000000000000) (-40985968905 / 1000000000000), orderedInterval (-30742826813 / 1000000000000) (-30742826812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1321959785804489 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43307327856 / 1000000000000) (-43307327840 / 1000000000000), orderedInterval (-7059377055 / 1000000000000) (-7059377039 / 1000000000000)))) (orderedInterval (1314492575 / 1000000000000) (1314492634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (558975925678443 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50402892826 / 1000000000000) (50402993507 / 1000000000000), orderedInterval (-45070860224 / 1000000000000) (-45070759544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2272206104467403 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6927321293 / 1000000000000) (-6927321292 / 1000000000000), orderedInterval (-32746313316 / 1000000000000) (-32746313315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1517728374519877 / 4000000000000) 1 (IntervalRat.scale (611 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-3455116329 / 1000000000000) (-3455116327 / 1000000000000), orderedInterval (-40810717273 / 1000000000000) (-40810717272 / 1000000000000)))) (orderedInterval (14342426371 / 1000000000000) (14342426769 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_chunkChecks1 :
    compactCertificate434.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate434.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate434_chunkChecks1_0
    compactCertificate434_chunkChecks1_1 compactCertificate434_chunkChecks1_2

theorem compactCertificate434_chunkChecks2_0 :
    compactCertificate434.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (611 / 2) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45639903767 / 1000000000000) (-45639903658 / 1000000000000), orderedInterval (-851680903 / 1000000000000) (-851680793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (900119669167511 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19724386471 / 1000000000000) (-19724385864 / 1000000000000), orderedInterval (49440168562 / 1000000000000) (49440169169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (291080206883063 / 800000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8742819217 / 1000000000000) (8742819218 / 1000000000000), orderedInterval (40893239842 / 1000000000000) (40893239843 / 1000000000000)))) (orderedInterval (17452685735 / 1000000000000) (17452685809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (262652674532677 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44874754804 / 1000000000000) (-44874754803 / 1000000000000), orderedInterval (-87303363660 / 1000000000000) (-87303363659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (705522028949569 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56742259263 / 1000000000000) (56742259264 / 1000000000000), orderedInterval (19578934507 / 1000000000000) (19578934508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1915629552178173 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30098823620 / 1000000000000) (30098893317 / 1000000000000), orderedInterval (-20607548564 / 1000000000000) (-20607478867 / 1000000000000)))) (orderedInterval (4535579728 / 1000000000000) (4535591987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1411044057899749 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (42191609349 / 1000000000000) (42191610235 / 1000000000000), orderedInterval (-5013945391 / 1000000000000) (-5013944505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2417848043686777 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28624916199 / 1000000000000) (28625018550 / 1000000000000), orderedInterval (-15314627447 / 1000000000000) (-15314525096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1780975925678443 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2910908661 / 1000000000000) (-2910908659 / 1000000000000), orderedInterval (37704061968 / 1000000000000) (37704061969 / 1000000000000)))) (orderedInterval (3598477428 / 1000000000000) (3598489861 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_chunkChecks2_1 :
    compactCertificate434.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2732475068504389 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25064100747 / 1000000000000) (-25064074960 / 1000000000000), orderedInterval (17445974475 / 1000000000000) (17446000262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1577595216354781 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24530851375 / 1000000000000) (-24530846044 / 1000000000000), orderedInterval (31849175683 / 1000000000000) (31849181014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2799470395572929 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2339776664 / 1000000000000) (-2339776663 / 1000000000000), orderedInterval (-30067491082 / 1000000000000) (-30067491081 / 1000000000000)))) (orderedInterval (-17448332356 / 1000000000000) (-17448308214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2615628381292901 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29520747638 / 1000000000000) (29520747653 / 1000000000000), orderedInterval (10081301057 / 1000000000000) (10081301072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1866635833078133 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22447132295 / 1000000000000) (22447135771 / 1000000000000), orderedInterval (-29355505599 / 1000000000000) (-29355502122 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2116566086848707 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29233503765 / 1000000000000) (29233577059 / 1000000000000), orderedInterval (-18696295889 / 1000000000000) (-18696222596 / 1000000000000)))) (orderedInterval (-2052773963 / 1000000000000) (-2052771980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1764572140107283 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32692085666 / 1000000000000) (32692175956 / 1000000000000), orderedInterval (-19384920460 / 1000000000000) (-19384830170 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1559052999888943 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33806324709 / 1000000000000) (33806324710 / 1000000000000), orderedInterval (22103455794 / 1000000000000) (22103455795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (451874326377357 / 800000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4731504970 / 1000000000000) (4731504971 / 1000000000000), orderedInterval (33232648373 / 1000000000000) (33232648374 / 1000000000000)))) (orderedInterval (1948900452 / 1000000000000) (1948902695 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_chunkChecks2_2 :
    compactCertificate434.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1249908167602679 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35278916925 / 1000000000000) (-35278840770 / 1000000000000), orderedInterval (28211925310 / 1000000000000) (28212001465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1059560996030719 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47940660026 / 1000000000000) (47940661605 / 1000000000000), orderedInterval (-10338577009 / 1000000000000) (-10338575430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (663024074321557 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2246162803 / 1000000000000) (-2246162801 / 1000000000000), orderedInterval (-61926059069 / 1000000000000) (-61926059066 / 1000000000000)))) (orderedInterval (-3822879611 / 1000000000000) (-3822866695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (356576552288619 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78072412128 / 1000000000000) (78072416581 / 1000000000000), orderedInterval (-32781110526 / 1000000000000) (-32781106073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (968174703482857 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40985968906 / 1000000000000) (-40985968905 / 1000000000000), orderedInterval (-30742826813 / 1000000000000) (-30742826812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1321959785804489 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43307327856 / 1000000000000) (-43307327840 / 1000000000000), orderedInterval (-7059377055 / 1000000000000) (-7059377039 / 1000000000000)))) (orderedInterval (-4349461649 / 1000000000000) (-4349461607 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (558975925678443 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50402892826 / 1000000000000) (50402993507 / 1000000000000), orderedInterval (-45070860224 / 1000000000000) (-45070759544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2272206104467403 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6927321293 / 1000000000000) (-6927321292 / 1000000000000), orderedInterval (-32746313316 / 1000000000000) (-32746313315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1517728374519877 / 4000000000000) 2 (IntervalRat.scale (611 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-3455116329 / 1000000000000) (-3455116327 / 1000000000000), orderedInterval (-40810717273 / 1000000000000) (-40810717272 / 1000000000000)))) (orderedInterval (-3060160265 / 1000000000000) (-3060159960 / 1000000000000))) = true
  rfl'

theorem compactCertificate434_chunkChecks2 :
    compactCertificate434.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate434.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate434_chunkChecks2_0
    compactCertificate434_chunkChecks2_1 compactCertificate434_chunkChecks2_2

theorem compactCertificate434_chunkChecks3_0 :
    compactCertificate434.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (611 / 2) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45639903767 / 1000000000000) (-45639903658 / 1000000000000), orderedInterval (-851680903 / 1000000000000) (-851680793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (900119669167511 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19724386471 / 1000000000000) (-19724385864 / 1000000000000), orderedInterval (49440168562 / 1000000000000) (49440169169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (291080206883063 / 800000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8742819217 / 1000000000000) (8742819218 / 1000000000000), orderedInterval (40893239842 / 1000000000000) (40893239843 / 1000000000000)))) (orderedInterval (-3957644526 / 1000000000000) (-3957644447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (262652674532677 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44874754804 / 1000000000000) (-44874754803 / 1000000000000), orderedInterval (-87303363660 / 1000000000000) (-87303363659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (705522028949569 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56742259263 / 1000000000000) (56742259264 / 1000000000000), orderedInterval (19578934507 / 1000000000000) (19578934508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1915629552178173 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30098823620 / 1000000000000) (30098893317 / 1000000000000), orderedInterval (-20607548564 / 1000000000000) (-20607478867 / 1000000000000)))) (orderedInterval (-5805361636 / 1000000000000) (-5805342422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1411044057899749 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (42191609349 / 1000000000000) (42191610235 / 1000000000000), orderedInterval (-5013945391 / 1000000000000) (-5013944505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2417848043686777 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28624916199 / 1000000000000) (28625018550 / 1000000000000), orderedInterval (-15314627447 / 1000000000000) (-15314525096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1780975925678443 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2910908661 / 1000000000000) (-2910908659 / 1000000000000), orderedInterval (37704061968 / 1000000000000) (37704061969 / 1000000000000)))) (orderedInterval (-6491568923 / 1000000000000) (-6491544333 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate434_chunkChecks3_1 :
    compactCertificate434.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2732475068504389 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25064100747 / 1000000000000) (-25064074960 / 1000000000000), orderedInterval (17445974475 / 1000000000000) (17446000262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1577595216354781 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24530851375 / 1000000000000) (-24530846044 / 1000000000000), orderedInterval (31849175683 / 1000000000000) (31849181014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2799470395572929 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2339776664 / 1000000000000) (-2339776663 / 1000000000000), orderedInterval (-30067491082 / 1000000000000) (-30067491081 / 1000000000000)))) (orderedInterval (81027637984 / 1000000000000) (81027691321 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2615628381292901 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29520747638 / 1000000000000) (29520747653 / 1000000000000), orderedInterval (10081301057 / 1000000000000) (10081301072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1866635833078133 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22447132295 / 1000000000000) (22447135771 / 1000000000000), orderedInterval (-29355505599 / 1000000000000) (-29355502122 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2116566086848707 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29233503765 / 1000000000000) (29233577059 / 1000000000000), orderedInterval (-18696295889 / 1000000000000) (-18696222596 / 1000000000000)))) (orderedInterval (11193891434 / 1000000000000) (11193894708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1764572140107283 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32692085666 / 1000000000000) (32692175956 / 1000000000000), orderedInterval (-19384920460 / 1000000000000) (-19384830170 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1559052999888943 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33806324709 / 1000000000000) (33806324710 / 1000000000000), orderedInterval (22103455794 / 1000000000000) (22103455795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (451874326377357 / 800000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4731504970 / 1000000000000) (4731504971 / 1000000000000), orderedInterval (33232648373 / 1000000000000) (33232648374 / 1000000000000)))) (orderedInterval (-2083583727 / 1000000000000) (-2083580482 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate434_chunkChecks3_2 :
    compactCertificate434.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1249908167602679 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35278916925 / 1000000000000) (-35278840770 / 1000000000000), orderedInterval (28211925310 / 1000000000000) (28212001465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1059560996030719 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47940660026 / 1000000000000) (47940661605 / 1000000000000), orderedInterval (-10338577009 / 1000000000000) (-10338575430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (663024074321557 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2246162803 / 1000000000000) (-2246162801 / 1000000000000), orderedInterval (-61926059069 / 1000000000000) (-61926059066 / 1000000000000)))) (orderedInterval (4780059547 / 1000000000000) (4780072743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (356576552288619 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78072412128 / 1000000000000) (78072416581 / 1000000000000), orderedInterval (-32781110526 / 1000000000000) (-32781106073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (968174703482857 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40985968906 / 1000000000000) (-40985968905 / 1000000000000), orderedInterval (-30742826813 / 1000000000000) (-30742826812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1321959785804489 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43307327856 / 1000000000000) (-43307327840 / 1000000000000), orderedInterval (-7059377055 / 1000000000000) (-7059377039 / 1000000000000)))) (orderedInterval (-1032603444 / 1000000000000) (-1032603406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (558975925678443 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50402892826 / 1000000000000) (50402993507 / 1000000000000), orderedInterval (-45070860224 / 1000000000000) (-45070759544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2272206104467403 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6927321293 / 1000000000000) (-6927321292 / 1000000000000), orderedInterval (-32746313316 / 1000000000000) (-32746313315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1517728374519877 / 4000000000000) 3 (IntervalRat.scale (611 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-3455116329 / 1000000000000) (-3455116327 / 1000000000000), orderedInterval (-40810717273 / 1000000000000) (-40810717272 / 1000000000000)))) (orderedInterval (-31770704371 / 1000000000000) (-31770704041 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate434_chunkChecks3 :
    compactCertificate434.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate434.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate434_chunkChecks3_0
    compactCertificate434_chunkChecks3_1 compactCertificate434_chunkChecks3_2

theorem compactCertificate434_chunkChecks4_0 :
    compactCertificate434.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (611 / 2) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45639903767 / 1000000000000) (-45639903658 / 1000000000000), orderedInterval (-851680903 / 1000000000000) (-851680793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (900119669167511 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19724386471 / 1000000000000) (-19724385864 / 1000000000000), orderedInterval (49440168562 / 1000000000000) (49440169169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (291080206883063 / 800000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (8742819217 / 1000000000000) (8742819218 / 1000000000000), orderedInterval (40893239842 / 1000000000000) (40893239843 / 1000000000000)))) (orderedInterval (-17085793688 / 1000000000000) (-17085793605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (262652674532677 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44874754804 / 1000000000000) (-44874754803 / 1000000000000), orderedInterval (-87303363660 / 1000000000000) (-87303363659 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (705522028949569 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56742259263 / 1000000000000) (56742259264 / 1000000000000), orderedInterval (19578934507 / 1000000000000) (19578934508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1915629552178173 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30098823620 / 1000000000000) (30098893317 / 1000000000000), orderedInterval (-20607548564 / 1000000000000) (-20607478867 / 1000000000000)))) (orderedInterval (-12652366440 / 1000000000000) (-12652336261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1411044057899749 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (42191609349 / 1000000000000) (42191610235 / 1000000000000), orderedInterval (-5013945391 / 1000000000000) (-5013944505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2417848043686777 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28624916199 / 1000000000000) (28625018550 / 1000000000000), orderedInterval (-15314627447 / 1000000000000) (-15314525096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1780975925678443 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2910908661 / 1000000000000) (-2910908659 / 1000000000000), orderedInterval (37704061968 / 1000000000000) (37704061969 / 1000000000000)))) (orderedInterval (-13806425203 / 1000000000000) (-13806376481 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate434_chunkChecks4_1 :
    compactCertificate434.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2732475068504389 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25064100747 / 1000000000000) (-25064074960 / 1000000000000), orderedInterval (17445974475 / 1000000000000) (17446000262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1577595216354781 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-24530851375 / 1000000000000) (-24530846044 / 1000000000000), orderedInterval (31849175683 / 1000000000000) (31849181014 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2799470395572929 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-2339776664 / 1000000000000) (-2339776663 / 1000000000000), orderedInterval (-30067491082 / 1000000000000) (-30067491081 / 1000000000000)))) (orderedInterval (96598915849 / 1000000000000) (96599034458 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2615628381292901 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29520747638 / 1000000000000) (29520747653 / 1000000000000), orderedInterval (10081301057 / 1000000000000) (10081301072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1866635833078133 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22447132295 / 1000000000000) (22447135771 / 1000000000000), orderedInterval (-29355505599 / 1000000000000) (-29355502122 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2116566086848707 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29233503765 / 1000000000000) (29233577059 / 1000000000000), orderedInterval (-18696295889 / 1000000000000) (-18696222596 / 1000000000000)))) (orderedInterval (-1034621424 / 1000000000000) (-1034615982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1764572140107283 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (32692085666 / 1000000000000) (32692175956 / 1000000000000), orderedInterval (-19384920460 / 1000000000000) (-19384830170 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1559052999888943 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (33806324709 / 1000000000000) (33806324710 / 1000000000000), orderedInterval (22103455794 / 1000000000000) (22103455795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (451874326377357 / 800000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4731504970 / 1000000000000) (4731504971 / 1000000000000), orderedInterval (33232648373 / 1000000000000) (33232648374 / 1000000000000)))) (orderedInterval (-2054976681 / 1000000000000) (-2054971973 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate434_chunkChecks4_2 :
    compactCertificate434.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1249908167602679 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35278916925 / 1000000000000) (-35278840770 / 1000000000000), orderedInterval (28211925310 / 1000000000000) (28212001465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1059560996030719 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (47940660026 / 1000000000000) (47940661605 / 1000000000000), orderedInterval (-10338577009 / 1000000000000) (-10338575430 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (663024074321557 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-2246162803 / 1000000000000) (-2246162801 / 1000000000000), orderedInterval (-61926059069 / 1000000000000) (-61926059066 / 1000000000000)))) (orderedInterval (4602678813 / 1000000000000) (4602692342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (356576552288619 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (78072412128 / 1000000000000) (78072416581 / 1000000000000), orderedInterval (-32781110526 / 1000000000000) (-32781106073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (968174703482857 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40985968906 / 1000000000000) (-40985968905 / 1000000000000), orderedInterval (-30742826813 / 1000000000000) (-30742826812 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1321959785804489 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-43307327856 / 1000000000000) (-43307327840 / 1000000000000), orderedInterval (-7059377055 / 1000000000000) (-7059377039 / 1000000000000)))) (orderedInterval (4908326341 / 1000000000000) (4908326380 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (558975925678443 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50402892826 / 1000000000000) (50402993507 / 1000000000000), orderedInterval (-45070860224 / 1000000000000) (-45070759544 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2272206104467403 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-6927321293 / 1000000000000) (-6927321292 / 1000000000000), orderedInterval (-32746313316 / 1000000000000) (-32746313315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1517728374519877 / 4000000000000) 4 (IntervalRat.scale (611 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-3455116329 / 1000000000000) (-3455116327 / 1000000000000), orderedInterval (-40810717273 / 1000000000000) (-40810717272 / 1000000000000)))) (orderedInterval (8504547263 / 1000000000000) (8504547726 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate434_chunkChecks4 :
    compactCertificate434.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate434.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate434_chunkChecks4_0
    compactCertificate434_chunkChecks4_1 compactCertificate434_chunkChecks4_2

theorem compactCertificate434_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate434.chunkCheck r b = true :=
  compactCertificate434.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate434_chunkChecks0
    · exact compactCertificate434_chunkChecks1
    · exact compactCertificate434_chunkChecks2
    · exact compactCertificate434_chunkChecks3
    · exact compactCertificate434_chunkChecks4)

theorem compactCertificate434_coefficient0 :
    compactCertificate434.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate434_coefficient1 :
    compactCertificate434.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate434_coefficient2 :
    compactCertificate434.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate434_coefficient3 :
    compactCertificate434.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate434_coefficient4 :
    compactCertificate434.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate434_coefficients : ∀ r : Fin 5,
    compactCertificate434.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate434_coefficient0
  · exact compactCertificate434_coefficient1
  · exact compactCertificate434_coefficient2
  · exact compactCertificate434_coefficient3
  · exact compactCertificate434_coefficient4

theorem compactCertificate434_lower : (1 : ℚ) ≤ compactCertificate434.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate434, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate434_proves {t : ℝ} (ht : t ∈ compactCertificate434.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate434.proves compactCertificate434_states compactCertificate434_chunks
    compactCertificate434_coefficients compactCertificate434_lower ht

end Erdos232
