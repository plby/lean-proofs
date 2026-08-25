/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate520 : CompactCertificate where
  left := 391
  right := 392
  center := 783 / 2
  grid := fun i =>
    match i.val with
    | 0 => 125
    | 1 => 92
    | 2 => 148
    | 3 => 27
    | 4 => 72
    | 5 => 195
    | 6 => 144
    | 7 => 247
    | 8 => 182
    | 9 => 279
    | 10 => 161
    | 11 => 286
    | 12 => 267
    | 13 => 190
    | 14 => 216
    | 15 => 180
    | 16 => 159
    | 17 => 231
    | 18 => 128
    | 19 => 108
    | 20 => 68
    | 21 => 36
    | 22 => 99
    | 23 => 135
    | 24 => 57
    | 25 => 232
    | _ => 155
  point := fun i =>
    match i.val with
    | 0 => 783 / 2
    | 1 => 1153508512206483 / 4000000000000
    | 2 => 373020952519539 / 800000000000
    | 3 => 336590906970681 / 4000000000000
    | 4 => 904130521550757 / 4000000000000
    | 5 => 2454890244444369 / 4000000000000
    | 6 => 1808261043102297 / 4000000000000
    | 7 => 3098486118177981 / 4000000000000
    | 8 => 2282330850746679 / 4000000000000
    | 9 => 3501682452764217 / 4000000000000
    | 10 => 2021697306719793 / 4000000000000
    | 11 => 3587537348172837 / 4000000000000
    | 12 => 3351942753768153 / 4000000000000
    | 13 => 2392104512766249 / 4000000000000
    | 14 => 2712391564652271 / 4000000000000
    | 15 => 2261309305571199 / 4000000000000
    | 16 => 1997935350103179 / 4000000000000
    | 17 => 579079537730721 / 800000000000
    | 18 => 1601764476649587 / 4000000000000
    | 19 => 1357833485911707 / 4000000000000
    | 20 => 849669149253321 / 4000000000000
    | 21 => 456954894340407 / 4000000000000
    | 22 => 1240721428522221 / 4000000000000
    | 23 => 1694099038109517 / 4000000000000
    | 24 => 716330850746679 / 4000000000000
    | 25 => 2911845138785559 / 4000000000000
    | _ => 1944977605972281 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (16221813660 / 1000000000000) (16221813982 / 1000000000000), orderedInterval (-36938975955 / 1000000000000) (-36938975632 / 1000000000000))
    | 1 => (orderedInterval (6350200032 / 1000000000000) (6350200033 / 1000000000000), orderedInterval (46542965923 / 1000000000000) (46542965924 / 1000000000000))
    | 2 => (orderedInterval (31790704812 / 1000000000000) (31790805638 / 1000000000000), orderedInterval (-18866957850 / 1000000000000) (-18866857024 / 1000000000000))
    | 3 => (orderedInterval (-9430652277 / 1000000000000) (-9430652275 / 1000000000000), orderedInterval (-86411849418 / 1000000000000) (-86411849416 / 1000000000000))
    | 4 => (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000))
    | 5 => (orderedInterval (-30506917106 / 1000000000000) (-30506885724 / 1000000000000), orderedInterval (10351376630 / 1000000000000) (10351408012 / 1000000000000))
    | 6 => (orderedInterval (16694840910 / 1000000000000) (16694840911 / 1000000000000), orderedInterval (33590020558 / 1000000000000) (33590020559 / 1000000000000))
    | 7 => (orderedInterval (15388406475 / 1000000000000) (15388406661 / 1000000000000), orderedInterval (-24197599864 / 1000000000000) (-24197599678 / 1000000000000))
    | 8 => (orderedInterval (-13068216809 / 1000000000000) (-13068216730 / 1000000000000), orderedInterval (30751623695 / 1000000000000) (30751623774 / 1000000000000))
    | 9 => (orderedInterval (7930153013 / 1000000000000) (7930153015 / 1000000000000), orderedInterval (-25779103091 / 1000000000000) (-25779103089 / 1000000000000))
    | 10 => (orderedInterval (-14246380209 / 1000000000000) (-14246380208 / 1000000000000), orderedInterval (-32491535618 / 1000000000000) (-32491535617 / 1000000000000))
    | 11 => (orderedInterval (-19586366019 / 1000000000000) (-19586363911 / 1000000000000), orderedInterval (18071562090 / 1000000000000) (18071564197 / 1000000000000))
    | 12 => (orderedInterval (945244645 / 1000000000000) (945244646 / 1000000000000), orderedInterval (-27547053569 / 1000000000000) (-27547053568 / 1000000000000))
    | 13 => (orderedInterval (30782035275 / 1000000000000) (30782067696 / 1000000000000), orderedInterval (-10842407765 / 1000000000000) (-10842375344 / 1000000000000))
    | 14 => (orderedInterval (9028256239 / 1000000000000) (9028256240 / 1000000000000), orderedInterval (29273412382 / 1000000000000) (29273412383 / 1000000000000))
    | 15 => (orderedInterval (19656885841 / 1000000000000) (19656885842 / 1000000000000), orderedInterval (27180321097 / 1000000000000) (27180321098 / 1000000000000))
    | 16 => (orderedInterval (-24485010369 / 1000000000000) (-24485010368 / 1000000000000), orderedInterval (-25957014014 / 1000000000000) (-25957014013 / 1000000000000))
    | 17 => (orderedInterval (26060641261 / 1000000000000) (26060698853 / 1000000000000), orderedInterval (-14171945145 / 1000000000000) (-14171887553 / 1000000000000))
    | 18 => (orderedInterval (-31174798863 / 1000000000000) (-31174746877 / 1000000000000), orderedInterval (24897084995 / 1000000000000) (24897136981 / 1000000000000))
    | 19 => (orderedInterval (35260751261 / 1000000000000) (35260751262 / 1000000000000), orderedInterval (25089213059 / 1000000000000) (25089213060 / 1000000000000))
    | 20 => (orderedInterval (-22632509663 / 1000000000000) (-22632508517 / 1000000000000), orderedInterval (49901034027 / 1000000000000) (49901035173 / 1000000000000))
    | 21 => (orderedInterval (69998255203 / 1000000000000) (69998258594 / 1000000000000), orderedInterval (-26247024679 / 1000000000000) (-26247021289 / 1000000000000))
    | 22 => (orderedInterval (2369220787 / 1000000000000) (2369220790 / 1000000000000), orderedInterval (-45245476033 / 1000000000000) (-45245476030 / 1000000000000))
    | 23 => (orderedInterval (-7506868675 / 1000000000000) (-7506868674 / 1000000000000), orderedInterval (-38027888566 / 1000000000000) (-38027888565 / 1000000000000))
    | 24 => (orderedInterval (-42630616102 / 1000000000000) (-42630616101 / 1000000000000), orderedInterval (-41564577672 / 1000000000000) (-41564577671 / 1000000000000))
    | 25 => (orderedInterval (-3040113000 / 1000000000000) (-3040112999 / 1000000000000), orderedInterval (29417766430 / 1000000000000) (29417766431 / 1000000000000))
    | _ => (orderedInterval (-2988304776 / 1000000000000) (-2988304775 / 1000000000000), orderedInterval (-36057009516 / 1000000000000) (-36057009515 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (8354445389 / 1000000000000) (8354451461 / 1000000000000)
      | 1 => orderedInterval (3401329691 / 1000000000000) (3401331969 / 1000000000000)
      | 2 => orderedInterval (-790473058 / 1000000000000) (-790473028 / 1000000000000)
      | 3 => orderedInterval (-5248949392 / 1000000000000) (-5248948937 / 1000000000000)
      | 4 => orderedInterval (2848084694 / 1000000000000) (2848087807 / 1000000000000)
      | 5 => orderedInterval (2295442347 / 1000000000000) (2295443860 / 1000000000000)
      | 6 => orderedInterval (2252041902 / 1000000000000) (2252050350 / 1000000000000)
      | 7 => orderedInterval (-770958311 / 1000000000000) (-770958201 / 1000000000000)
      | _ => orderedInterval (551164456 / 1000000000000) (551164565 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15640459188 / 1000000000000) (-15640451983 / 1000000000000)
      | 1 => orderedInterval (-44827157 / 1000000000000) (-44823606 / 1000000000000)
      | 2 => orderedInterval (2559897621 / 1000000000000) (2559897673 / 1000000000000)
      | 3 => orderedInterval (13019983696 / 1000000000000) (13019984705 / 1000000000000)
      | 4 => orderedInterval (-758276532 / 1000000000000) (-758271773 / 1000000000000)
      | 5 => orderedInterval (1677483112 / 1000000000000) (1677485894 / 1000000000000)
      | 6 => orderedInterval (-4421630216 / 1000000000000) (-4421621603 / 1000000000000)
      | 7 => orderedInterval (4107499914 / 1000000000000) (4107499975 / 1000000000000)
      | _ => orderedInterval (3835185511 / 1000000000000) (3835185664 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9068116191 / 1000000000000) (-9068107616 / 1000000000000)
      | 1 => orderedInterval (-5710861270 / 1000000000000) (-5710855705 / 1000000000000)
      | 2 => orderedInterval (2522466716 / 1000000000000) (2522466811 / 1000000000000)
      | 3 => orderedInterval (23384055749 / 1000000000000) (23384058014 / 1000000000000)
      | 4 => orderedInterval (-6574778219 / 1000000000000) (-6574770927 / 1000000000000)
      | 5 => orderedInterval (-5039350696 / 1000000000000) (-5039345567 / 1000000000000)
      | 6 => orderedInterval (-3486258663 / 1000000000000) (-3486249848 / 1000000000000)
      | 7 => orderedInterval (-539988313 / 1000000000000) (-539988265 / 1000000000000)
      | _ => orderedInterval (-1676532916 / 1000000000000) (-1676532690 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (16361441538 / 1000000000000) (16361451724 / 1000000000000)
      | 1 => orderedInterval (2537682525 / 1000000000000) (2537691244 / 1000000000000)
      | 2 => orderedInterval (-8088356944 / 1000000000000) (-8088356770 / 1000000000000)
      | 3 => orderedInterval (-76979823191 / 1000000000000) (-76979818072 / 1000000000000)
      | 4 => orderedInterval (-435969903 / 1000000000000) (-435958745 / 1000000000000)
      | 5 => orderedInterval (-1723508516 / 1000000000000) (-1723499059 / 1000000000000)
      | 6 => orderedInterval (4934966884 / 1000000000000) (4934975891 / 1000000000000)
      | 7 => orderedInterval (-4210848593 / 1000000000000) (-4210848548 / 1000000000000)
      | _ => orderedInterval (2461639445 / 1000000000000) (2461639793 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10117106590 / 1000000000000) (10117118722 / 1000000000000)
      | 1 => orderedInterval (13209613638 / 1000000000000) (13209627325 / 1000000000000)
      | 2 => orderedInterval (-8658003929 / 1000000000000) (-8658003604 / 1000000000000)
      | 3 => orderedInterval (-114455726891 / 1000000000000) (-114455715255 / 1000000000000)
      | 4 => orderedInterval (15080692104 / 1000000000000) (15080709220 / 1000000000000)
      | 5 => orderedInterval (12505660787 / 1000000000000) (12505678264 / 1000000000000)
      | 6 => orderedInterval (4238667644 / 1000000000000) (4238676874 / 1000000000000)
      | 7 => orderedInterval (778903248 / 1000000000000) (778903294 / 1000000000000)
      | _ => orderedInterval (4268544512 / 1000000000000) (4268545070 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (12892127718 / 1000000000000) (12892149846 / 1000000000000)
    | 1 => orderedInterval (4334856761 / 1000000000000) (4334884946 / 1000000000000)
    | 2 => orderedInterval (-6189363803 / 1000000000000) (-6189325793 / 1000000000000)
    | 3 => orderedInterval (-65142776755 / 1000000000000) (-65142722542 / 1000000000000)
    | _ => orderedInterval (-62914542297 / 1000000000000) (-62914460090 / 1000000000000)

theorem compactCertificate520_stateChecks0 :
    compactCertificate520.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (783 / 2)) (orderedInterval (16221813660 / 1000000000000) (16221813982 / 1000000000000), orderedInterval (-36938975955 / 1000000000000) (-36938975632 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1153508512206483 / 4000000000000)) (orderedInterval (6350200032 / 1000000000000) (6350200033 / 1000000000000), orderedInterval (46542965923 / 1000000000000) (46542965924 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (373020952519539 / 800000000000)) (orderedInterval (31790704812 / 1000000000000) (31790805638 / 1000000000000), orderedInterval (-18866957850 / 1000000000000) (-18866857024 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_stateChecks1 :
    compactCertificate520.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (336590906970681 / 4000000000000)) (orderedInterval (-9430652277 / 1000000000000) (-9430652275 / 1000000000000), orderedInterval (-86411849418 / 1000000000000) (-86411849416 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (904130521550757 / 4000000000000)) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2454890244444369 / 4000000000000)) (orderedInterval (-30506917106 / 1000000000000) (-30506885724 / 1000000000000), orderedInterval (10351376630 / 1000000000000) (10351408012 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_stateChecks2 :
    compactCertificate520.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1808261043102297 / 4000000000000)) (orderedInterval (16694840910 / 1000000000000) (16694840911 / 1000000000000), orderedInterval (33590020558 / 1000000000000) (33590020559 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (3098486118177981 / 4000000000000)) (orderedInterval (15388406475 / 1000000000000) (15388406661 / 1000000000000), orderedInterval (-24197599864 / 1000000000000) (-24197599678 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2282330850746679 / 4000000000000)) (orderedInterval (-13068216809 / 1000000000000) (-13068216730 / 1000000000000), orderedInterval (30751623695 / 1000000000000) (30751623774 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_stateChecks3 :
    compactCertificate520.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 279 12 (3501682452764217 / 4000000000000)) (orderedInterval (7930153013 / 1000000000000) (7930153015 / 1000000000000), orderedInterval (-25779103091 / 1000000000000) (-25779103089 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2021697306719793 / 4000000000000)) (orderedInterval (-14246380209 / 1000000000000) (-14246380208 / 1000000000000), orderedInterval (-32491535618 / 1000000000000) (-32491535617 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 286 12 (3587537348172837 / 4000000000000)) (orderedInterval (-19586366019 / 1000000000000) (-19586363911 / 1000000000000), orderedInterval (18071562090 / 1000000000000) (18071564197 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_stateChecks4 :
    compactCertificate520.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3351942753768153 / 4000000000000)) (orderedInterval (945244645 / 1000000000000) (945244646 / 1000000000000), orderedInterval (-27547053569 / 1000000000000) (-27547053568 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2392104512766249 / 4000000000000)) (orderedInterval (30782035275 / 1000000000000) (30782067696 / 1000000000000), orderedInterval (-10842407765 / 1000000000000) (-10842375344 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2712391564652271 / 4000000000000)) (orderedInterval (9028256239 / 1000000000000) (9028256240 / 1000000000000), orderedInterval (29273412382 / 1000000000000) (29273412383 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_stateChecks5 :
    compactCertificate520.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2261309305571199 / 4000000000000)) (orderedInterval (19656885841 / 1000000000000) (19656885842 / 1000000000000), orderedInterval (27180321097 / 1000000000000) (27180321098 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1997935350103179 / 4000000000000)) (orderedInterval (-24485010369 / 1000000000000) (-24485010368 / 1000000000000), orderedInterval (-25957014014 / 1000000000000) (-25957014013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (579079537730721 / 800000000000)) (orderedInterval (26060641261 / 1000000000000) (26060698853 / 1000000000000), orderedInterval (-14171945145 / 1000000000000) (-14171887553 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_stateChecks6 :
    compactCertificate520.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1601764476649587 / 4000000000000)) (orderedInterval (-31174798863 / 1000000000000) (-31174746877 / 1000000000000), orderedInterval (24897084995 / 1000000000000) (24897136981 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1357833485911707 / 4000000000000)) (orderedInterval (35260751261 / 1000000000000) (35260751262 / 1000000000000), orderedInterval (25089213059 / 1000000000000) (25089213060 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (849669149253321 / 4000000000000)) (orderedInterval (-22632509663 / 1000000000000) (-22632508517 / 1000000000000), orderedInterval (49901034027 / 1000000000000) (49901035173 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_stateChecks7 :
    compactCertificate520.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (456954894340407 / 4000000000000)) (orderedInterval (69998255203 / 1000000000000) (69998258594 / 1000000000000), orderedInterval (-26247024679 / 1000000000000) (-26247021289 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1240721428522221 / 4000000000000)) (orderedInterval (2369220787 / 1000000000000) (2369220790 / 1000000000000), orderedInterval (-45245476033 / 1000000000000) (-45245476030 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1694099038109517 / 4000000000000)) (orderedInterval (-7506868675 / 1000000000000) (-7506868674 / 1000000000000), orderedInterval (-38027888566 / 1000000000000) (-38027888565 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_stateChecks8 :
    compactCertificate520.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (716330850746679 / 4000000000000)) (orderedInterval (-42630616102 / 1000000000000) (-42630616101 / 1000000000000), orderedInterval (-41564577672 / 1000000000000) (-41564577671 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (2911845138785559 / 4000000000000)) (orderedInterval (-3040113000 / 1000000000000) (-3040112999 / 1000000000000), orderedInterval (29417766430 / 1000000000000) (29417766431 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1944977605972281 / 4000000000000)) (orderedInterval (-2988304776 / 1000000000000) (-2988304775 / 1000000000000), orderedInterval (-36057009516 / 1000000000000) (-36057009515 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_states : ∀ j,
    BesselStateValid (compactCertificate520.point j) (compactCertificate520.state j) :=
  compactCertificate520.statesValid_of_checks3 compactCertificate520_stateChecks0
    compactCertificate520_stateChecks1 compactCertificate520_stateChecks2
    compactCertificate520_stateChecks3 compactCertificate520_stateChecks4
    compactCertificate520_stateChecks5 compactCertificate520_stateChecks6
    compactCertificate520_stateChecks7 compactCertificate520_stateChecks8

theorem compactCertificate520_chunkChecks0_0 :
    compactCertificate520.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (783 / 2) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16221813660 / 1000000000000) (16221813982 / 1000000000000), orderedInterval (-36938975955 / 1000000000000) (-36938975632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1153508512206483 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (6350200032 / 1000000000000) (6350200033 / 1000000000000), orderedInterval (46542965923 / 1000000000000) (46542965924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (373020952519539 / 800000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31790704812 / 1000000000000) (31790805638 / 1000000000000), orderedInterval (-18866957850 / 1000000000000) (-18866857024 / 1000000000000)))) (orderedInterval (8354445389 / 1000000000000) (8354451461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (336590906970681 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9430652277 / 1000000000000) (-9430652275 / 1000000000000), orderedInterval (-86411849418 / 1000000000000) (-86411849416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (904130521550757 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2454890244444369 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30506917106 / 1000000000000) (-30506885724 / 1000000000000), orderedInterval (10351376630 / 1000000000000) (10351408012 / 1000000000000)))) (orderedInterval (3401329691 / 1000000000000) (3401331969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1808261043102297 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16694840910 / 1000000000000) (16694840911 / 1000000000000), orderedInterval (33590020558 / 1000000000000) (33590020559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3098486118177981 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15388406475 / 1000000000000) (15388406661 / 1000000000000), orderedInterval (-24197599864 / 1000000000000) (-24197599678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2282330850746679 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-13068216809 / 1000000000000) (-13068216730 / 1000000000000), orderedInterval (30751623695 / 1000000000000) (30751623774 / 1000000000000)))) (orderedInterval (-790473058 / 1000000000000) (-790473028 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_chunkChecks0_1 :
    compactCertificate520.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3501682452764217 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7930153013 / 1000000000000) (7930153015 / 1000000000000), orderedInterval (-25779103091 / 1000000000000) (-25779103089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2021697306719793 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-14246380209 / 1000000000000) (-14246380208 / 1000000000000), orderedInterval (-32491535618 / 1000000000000) (-32491535617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3587537348172837 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19586366019 / 1000000000000) (-19586363911 / 1000000000000), orderedInterval (18071562090 / 1000000000000) (18071564197 / 1000000000000)))) (orderedInterval (-5248949392 / 1000000000000) (-5248948937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3351942753768153 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (945244645 / 1000000000000) (945244646 / 1000000000000), orderedInterval (-27547053569 / 1000000000000) (-27547053568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2392104512766249 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30782035275 / 1000000000000) (30782067696 / 1000000000000), orderedInterval (-10842407765 / 1000000000000) (-10842375344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2712391564652271 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9028256239 / 1000000000000) (9028256240 / 1000000000000), orderedInterval (29273412382 / 1000000000000) (29273412383 / 1000000000000)))) (orderedInterval (2848084694 / 1000000000000) (2848087807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2261309305571199 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19656885841 / 1000000000000) (19656885842 / 1000000000000), orderedInterval (27180321097 / 1000000000000) (27180321098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1997935350103179 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24485010369 / 1000000000000) (-24485010368 / 1000000000000), orderedInterval (-25957014014 / 1000000000000) (-25957014013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (579079537730721 / 800000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26060641261 / 1000000000000) (26060698853 / 1000000000000), orderedInterval (-14171945145 / 1000000000000) (-14171887553 / 1000000000000)))) (orderedInterval (2295442347 / 1000000000000) (2295443860 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_chunkChecks0_2 :
    compactCertificate520.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1601764476649587 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31174798863 / 1000000000000) (-31174746877 / 1000000000000), orderedInterval (24897084995 / 1000000000000) (24897136981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1357833485911707 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35260751261 / 1000000000000) (35260751262 / 1000000000000), orderedInterval (25089213059 / 1000000000000) (25089213060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (849669149253321 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22632509663 / 1000000000000) (-22632508517 / 1000000000000), orderedInterval (49901034027 / 1000000000000) (49901035173 / 1000000000000)))) (orderedInterval (2252041902 / 1000000000000) (2252050350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (456954894340407 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69998255203 / 1000000000000) (69998258594 / 1000000000000), orderedInterval (-26247024679 / 1000000000000) (-26247021289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1240721428522221 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (2369220787 / 1000000000000) (2369220790 / 1000000000000), orderedInterval (-45245476033 / 1000000000000) (-45245476030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1694099038109517 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7506868675 / 1000000000000) (-7506868674 / 1000000000000), orderedInterval (-38027888566 / 1000000000000) (-38027888565 / 1000000000000)))) (orderedInterval (-770958311 / 1000000000000) (-770958201 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (716330850746679 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42630616102 / 1000000000000) (-42630616101 / 1000000000000), orderedInterval (-41564577672 / 1000000000000) (-41564577671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2911845138785559 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-3040113000 / 1000000000000) (-3040112999 / 1000000000000), orderedInterval (29417766430 / 1000000000000) (29417766431 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1944977605972281 / 4000000000000) 0 (IntervalRat.scale (783 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2988304776 / 1000000000000) (-2988304775 / 1000000000000), orderedInterval (-36057009516 / 1000000000000) (-36057009515 / 1000000000000)))) (orderedInterval (551164456 / 1000000000000) (551164565 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_chunkChecks0 :
    compactCertificate520.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate520.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate520_chunkChecks0_0
    compactCertificate520_chunkChecks0_1 compactCertificate520_chunkChecks0_2

theorem compactCertificate520_chunkChecks1_0 :
    compactCertificate520.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (783 / 2) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16221813660 / 1000000000000) (16221813982 / 1000000000000), orderedInterval (-36938975955 / 1000000000000) (-36938975632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1153508512206483 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (6350200032 / 1000000000000) (6350200033 / 1000000000000), orderedInterval (46542965923 / 1000000000000) (46542965924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (373020952519539 / 800000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31790704812 / 1000000000000) (31790805638 / 1000000000000), orderedInterval (-18866957850 / 1000000000000) (-18866857024 / 1000000000000)))) (orderedInterval (-15640459188 / 1000000000000) (-15640451983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (336590906970681 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9430652277 / 1000000000000) (-9430652275 / 1000000000000), orderedInterval (-86411849418 / 1000000000000) (-86411849416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (904130521550757 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2454890244444369 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30506917106 / 1000000000000) (-30506885724 / 1000000000000), orderedInterval (10351376630 / 1000000000000) (10351408012 / 1000000000000)))) (orderedInterval (-44827157 / 1000000000000) (-44823606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1808261043102297 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16694840910 / 1000000000000) (16694840911 / 1000000000000), orderedInterval (33590020558 / 1000000000000) (33590020559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3098486118177981 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15388406475 / 1000000000000) (15388406661 / 1000000000000), orderedInterval (-24197599864 / 1000000000000) (-24197599678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2282330850746679 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-13068216809 / 1000000000000) (-13068216730 / 1000000000000), orderedInterval (30751623695 / 1000000000000) (30751623774 / 1000000000000)))) (orderedInterval (2559897621 / 1000000000000) (2559897673 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_chunkChecks1_1 :
    compactCertificate520.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3501682452764217 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7930153013 / 1000000000000) (7930153015 / 1000000000000), orderedInterval (-25779103091 / 1000000000000) (-25779103089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2021697306719793 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-14246380209 / 1000000000000) (-14246380208 / 1000000000000), orderedInterval (-32491535618 / 1000000000000) (-32491535617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3587537348172837 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19586366019 / 1000000000000) (-19586363911 / 1000000000000), orderedInterval (18071562090 / 1000000000000) (18071564197 / 1000000000000)))) (orderedInterval (13019983696 / 1000000000000) (13019984705 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3351942753768153 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (945244645 / 1000000000000) (945244646 / 1000000000000), orderedInterval (-27547053569 / 1000000000000) (-27547053568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2392104512766249 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30782035275 / 1000000000000) (30782067696 / 1000000000000), orderedInterval (-10842407765 / 1000000000000) (-10842375344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2712391564652271 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9028256239 / 1000000000000) (9028256240 / 1000000000000), orderedInterval (29273412382 / 1000000000000) (29273412383 / 1000000000000)))) (orderedInterval (-758276532 / 1000000000000) (-758271773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2261309305571199 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19656885841 / 1000000000000) (19656885842 / 1000000000000), orderedInterval (27180321097 / 1000000000000) (27180321098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1997935350103179 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24485010369 / 1000000000000) (-24485010368 / 1000000000000), orderedInterval (-25957014014 / 1000000000000) (-25957014013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (579079537730721 / 800000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26060641261 / 1000000000000) (26060698853 / 1000000000000), orderedInterval (-14171945145 / 1000000000000) (-14171887553 / 1000000000000)))) (orderedInterval (1677483112 / 1000000000000) (1677485894 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_chunkChecks1_2 :
    compactCertificate520.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1601764476649587 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31174798863 / 1000000000000) (-31174746877 / 1000000000000), orderedInterval (24897084995 / 1000000000000) (24897136981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1357833485911707 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35260751261 / 1000000000000) (35260751262 / 1000000000000), orderedInterval (25089213059 / 1000000000000) (25089213060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (849669149253321 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22632509663 / 1000000000000) (-22632508517 / 1000000000000), orderedInterval (49901034027 / 1000000000000) (49901035173 / 1000000000000)))) (orderedInterval (-4421630216 / 1000000000000) (-4421621603 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (456954894340407 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69998255203 / 1000000000000) (69998258594 / 1000000000000), orderedInterval (-26247024679 / 1000000000000) (-26247021289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1240721428522221 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (2369220787 / 1000000000000) (2369220790 / 1000000000000), orderedInterval (-45245476033 / 1000000000000) (-45245476030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1694099038109517 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7506868675 / 1000000000000) (-7506868674 / 1000000000000), orderedInterval (-38027888566 / 1000000000000) (-38027888565 / 1000000000000)))) (orderedInterval (4107499914 / 1000000000000) (4107499975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (716330850746679 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42630616102 / 1000000000000) (-42630616101 / 1000000000000), orderedInterval (-41564577672 / 1000000000000) (-41564577671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2911845138785559 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-3040113000 / 1000000000000) (-3040112999 / 1000000000000), orderedInterval (29417766430 / 1000000000000) (29417766431 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1944977605972281 / 4000000000000) 1 (IntervalRat.scale (783 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2988304776 / 1000000000000) (-2988304775 / 1000000000000), orderedInterval (-36057009516 / 1000000000000) (-36057009515 / 1000000000000)))) (orderedInterval (3835185511 / 1000000000000) (3835185664 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_chunkChecks1 :
    compactCertificate520.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate520.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate520_chunkChecks1_0
    compactCertificate520_chunkChecks1_1 compactCertificate520_chunkChecks1_2

theorem compactCertificate520_chunkChecks2_0 :
    compactCertificate520.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (783 / 2) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16221813660 / 1000000000000) (16221813982 / 1000000000000), orderedInterval (-36938975955 / 1000000000000) (-36938975632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1153508512206483 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (6350200032 / 1000000000000) (6350200033 / 1000000000000), orderedInterval (46542965923 / 1000000000000) (46542965924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (373020952519539 / 800000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31790704812 / 1000000000000) (31790805638 / 1000000000000), orderedInterval (-18866957850 / 1000000000000) (-18866857024 / 1000000000000)))) (orderedInterval (-9068116191 / 1000000000000) (-9068107616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (336590906970681 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9430652277 / 1000000000000) (-9430652275 / 1000000000000), orderedInterval (-86411849418 / 1000000000000) (-86411849416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (904130521550757 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2454890244444369 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30506917106 / 1000000000000) (-30506885724 / 1000000000000), orderedInterval (10351376630 / 1000000000000) (10351408012 / 1000000000000)))) (orderedInterval (-5710861270 / 1000000000000) (-5710855705 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1808261043102297 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16694840910 / 1000000000000) (16694840911 / 1000000000000), orderedInterval (33590020558 / 1000000000000) (33590020559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3098486118177981 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15388406475 / 1000000000000) (15388406661 / 1000000000000), orderedInterval (-24197599864 / 1000000000000) (-24197599678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2282330850746679 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-13068216809 / 1000000000000) (-13068216730 / 1000000000000), orderedInterval (30751623695 / 1000000000000) (30751623774 / 1000000000000)))) (orderedInterval (2522466716 / 1000000000000) (2522466811 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_chunkChecks2_1 :
    compactCertificate520.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3501682452764217 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7930153013 / 1000000000000) (7930153015 / 1000000000000), orderedInterval (-25779103091 / 1000000000000) (-25779103089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2021697306719793 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-14246380209 / 1000000000000) (-14246380208 / 1000000000000), orderedInterval (-32491535618 / 1000000000000) (-32491535617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3587537348172837 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19586366019 / 1000000000000) (-19586363911 / 1000000000000), orderedInterval (18071562090 / 1000000000000) (18071564197 / 1000000000000)))) (orderedInterval (23384055749 / 1000000000000) (23384058014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3351942753768153 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (945244645 / 1000000000000) (945244646 / 1000000000000), orderedInterval (-27547053569 / 1000000000000) (-27547053568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2392104512766249 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30782035275 / 1000000000000) (30782067696 / 1000000000000), orderedInterval (-10842407765 / 1000000000000) (-10842375344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2712391564652271 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9028256239 / 1000000000000) (9028256240 / 1000000000000), orderedInterval (29273412382 / 1000000000000) (29273412383 / 1000000000000)))) (orderedInterval (-6574778219 / 1000000000000) (-6574770927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2261309305571199 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19656885841 / 1000000000000) (19656885842 / 1000000000000), orderedInterval (27180321097 / 1000000000000) (27180321098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1997935350103179 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24485010369 / 1000000000000) (-24485010368 / 1000000000000), orderedInterval (-25957014014 / 1000000000000) (-25957014013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (579079537730721 / 800000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26060641261 / 1000000000000) (26060698853 / 1000000000000), orderedInterval (-14171945145 / 1000000000000) (-14171887553 / 1000000000000)))) (orderedInterval (-5039350696 / 1000000000000) (-5039345567 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_chunkChecks2_2 :
    compactCertificate520.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1601764476649587 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31174798863 / 1000000000000) (-31174746877 / 1000000000000), orderedInterval (24897084995 / 1000000000000) (24897136981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1357833485911707 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35260751261 / 1000000000000) (35260751262 / 1000000000000), orderedInterval (25089213059 / 1000000000000) (25089213060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (849669149253321 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22632509663 / 1000000000000) (-22632508517 / 1000000000000), orderedInterval (49901034027 / 1000000000000) (49901035173 / 1000000000000)))) (orderedInterval (-3486258663 / 1000000000000) (-3486249848 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (456954894340407 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69998255203 / 1000000000000) (69998258594 / 1000000000000), orderedInterval (-26247024679 / 1000000000000) (-26247021289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1240721428522221 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (2369220787 / 1000000000000) (2369220790 / 1000000000000), orderedInterval (-45245476033 / 1000000000000) (-45245476030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1694099038109517 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7506868675 / 1000000000000) (-7506868674 / 1000000000000), orderedInterval (-38027888566 / 1000000000000) (-38027888565 / 1000000000000)))) (orderedInterval (-539988313 / 1000000000000) (-539988265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (716330850746679 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42630616102 / 1000000000000) (-42630616101 / 1000000000000), orderedInterval (-41564577672 / 1000000000000) (-41564577671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2911845138785559 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-3040113000 / 1000000000000) (-3040112999 / 1000000000000), orderedInterval (29417766430 / 1000000000000) (29417766431 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1944977605972281 / 4000000000000) 2 (IntervalRat.scale (783 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2988304776 / 1000000000000) (-2988304775 / 1000000000000), orderedInterval (-36057009516 / 1000000000000) (-36057009515 / 1000000000000)))) (orderedInterval (-1676532916 / 1000000000000) (-1676532690 / 1000000000000))) = true
  rfl'

theorem compactCertificate520_chunkChecks2 :
    compactCertificate520.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate520.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate520_chunkChecks2_0
    compactCertificate520_chunkChecks2_1 compactCertificate520_chunkChecks2_2

theorem compactCertificate520_chunkChecks3_0 :
    compactCertificate520.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (783 / 2) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16221813660 / 1000000000000) (16221813982 / 1000000000000), orderedInterval (-36938975955 / 1000000000000) (-36938975632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1153508512206483 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (6350200032 / 1000000000000) (6350200033 / 1000000000000), orderedInterval (46542965923 / 1000000000000) (46542965924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (373020952519539 / 800000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31790704812 / 1000000000000) (31790805638 / 1000000000000), orderedInterval (-18866957850 / 1000000000000) (-18866857024 / 1000000000000)))) (orderedInterval (16361441538 / 1000000000000) (16361451724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (336590906970681 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9430652277 / 1000000000000) (-9430652275 / 1000000000000), orderedInterval (-86411849418 / 1000000000000) (-86411849416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (904130521550757 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2454890244444369 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30506917106 / 1000000000000) (-30506885724 / 1000000000000), orderedInterval (10351376630 / 1000000000000) (10351408012 / 1000000000000)))) (orderedInterval (2537682525 / 1000000000000) (2537691244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1808261043102297 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16694840910 / 1000000000000) (16694840911 / 1000000000000), orderedInterval (33590020558 / 1000000000000) (33590020559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3098486118177981 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15388406475 / 1000000000000) (15388406661 / 1000000000000), orderedInterval (-24197599864 / 1000000000000) (-24197599678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2282330850746679 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-13068216809 / 1000000000000) (-13068216730 / 1000000000000), orderedInterval (30751623695 / 1000000000000) (30751623774 / 1000000000000)))) (orderedInterval (-8088356944 / 1000000000000) (-8088356770 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate520_chunkChecks3_1 :
    compactCertificate520.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3501682452764217 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7930153013 / 1000000000000) (7930153015 / 1000000000000), orderedInterval (-25779103091 / 1000000000000) (-25779103089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2021697306719793 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-14246380209 / 1000000000000) (-14246380208 / 1000000000000), orderedInterval (-32491535618 / 1000000000000) (-32491535617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3587537348172837 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19586366019 / 1000000000000) (-19586363911 / 1000000000000), orderedInterval (18071562090 / 1000000000000) (18071564197 / 1000000000000)))) (orderedInterval (-76979823191 / 1000000000000) (-76979818072 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3351942753768153 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (945244645 / 1000000000000) (945244646 / 1000000000000), orderedInterval (-27547053569 / 1000000000000) (-27547053568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2392104512766249 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30782035275 / 1000000000000) (30782067696 / 1000000000000), orderedInterval (-10842407765 / 1000000000000) (-10842375344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2712391564652271 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9028256239 / 1000000000000) (9028256240 / 1000000000000), orderedInterval (29273412382 / 1000000000000) (29273412383 / 1000000000000)))) (orderedInterval (-435969903 / 1000000000000) (-435958745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2261309305571199 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19656885841 / 1000000000000) (19656885842 / 1000000000000), orderedInterval (27180321097 / 1000000000000) (27180321098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1997935350103179 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24485010369 / 1000000000000) (-24485010368 / 1000000000000), orderedInterval (-25957014014 / 1000000000000) (-25957014013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (579079537730721 / 800000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26060641261 / 1000000000000) (26060698853 / 1000000000000), orderedInterval (-14171945145 / 1000000000000) (-14171887553 / 1000000000000)))) (orderedInterval (-1723508516 / 1000000000000) (-1723499059 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate520_chunkChecks3_2 :
    compactCertificate520.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1601764476649587 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31174798863 / 1000000000000) (-31174746877 / 1000000000000), orderedInterval (24897084995 / 1000000000000) (24897136981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1357833485911707 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35260751261 / 1000000000000) (35260751262 / 1000000000000), orderedInterval (25089213059 / 1000000000000) (25089213060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (849669149253321 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22632509663 / 1000000000000) (-22632508517 / 1000000000000), orderedInterval (49901034027 / 1000000000000) (49901035173 / 1000000000000)))) (orderedInterval (4934966884 / 1000000000000) (4934975891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (456954894340407 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69998255203 / 1000000000000) (69998258594 / 1000000000000), orderedInterval (-26247024679 / 1000000000000) (-26247021289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1240721428522221 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (2369220787 / 1000000000000) (2369220790 / 1000000000000), orderedInterval (-45245476033 / 1000000000000) (-45245476030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1694099038109517 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7506868675 / 1000000000000) (-7506868674 / 1000000000000), orderedInterval (-38027888566 / 1000000000000) (-38027888565 / 1000000000000)))) (orderedInterval (-4210848593 / 1000000000000) (-4210848548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (716330850746679 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42630616102 / 1000000000000) (-42630616101 / 1000000000000), orderedInterval (-41564577672 / 1000000000000) (-41564577671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2911845138785559 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-3040113000 / 1000000000000) (-3040112999 / 1000000000000), orderedInterval (29417766430 / 1000000000000) (29417766431 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1944977605972281 / 4000000000000) 3 (IntervalRat.scale (783 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2988304776 / 1000000000000) (-2988304775 / 1000000000000), orderedInterval (-36057009516 / 1000000000000) (-36057009515 / 1000000000000)))) (orderedInterval (2461639445 / 1000000000000) (2461639793 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate520_chunkChecks3 :
    compactCertificate520.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate520.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate520_chunkChecks3_0
    compactCertificate520_chunkChecks3_1 compactCertificate520_chunkChecks3_2

theorem compactCertificate520_chunkChecks4_0 :
    compactCertificate520.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (783 / 2) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (16221813660 / 1000000000000) (16221813982 / 1000000000000), orderedInterval (-36938975955 / 1000000000000) (-36938975632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1153508512206483 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (6350200032 / 1000000000000) (6350200033 / 1000000000000), orderedInterval (46542965923 / 1000000000000) (46542965924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (373020952519539 / 800000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (31790704812 / 1000000000000) (31790805638 / 1000000000000), orderedInterval (-18866957850 / 1000000000000) (-18866857024 / 1000000000000)))) (orderedInterval (10117106590 / 1000000000000) (10117118722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (336590906970681 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-9430652277 / 1000000000000) (-9430652275 / 1000000000000), orderedInterval (-86411849418 / 1000000000000) (-86411849416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (904130521550757 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (30956894522 / 1000000000000) (30956894523 / 1000000000000), orderedInterval (43037992943 / 1000000000000) (43037992944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2454890244444369 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30506917106 / 1000000000000) (-30506885724 / 1000000000000), orderedInterval (10351376630 / 1000000000000) (10351408012 / 1000000000000)))) (orderedInterval (13209613638 / 1000000000000) (13209627325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1808261043102297 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16694840910 / 1000000000000) (16694840911 / 1000000000000), orderedInterval (33590020558 / 1000000000000) (33590020559 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3098486118177981 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (15388406475 / 1000000000000) (15388406661 / 1000000000000), orderedInterval (-24197599864 / 1000000000000) (-24197599678 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2282330850746679 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-13068216809 / 1000000000000) (-13068216730 / 1000000000000), orderedInterval (30751623695 / 1000000000000) (30751623774 / 1000000000000)))) (orderedInterval (-8658003929 / 1000000000000) (-8658003604 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate520_chunkChecks4_1 :
    compactCertificate520.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3501682452764217 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7930153013 / 1000000000000) (7930153015 / 1000000000000), orderedInterval (-25779103091 / 1000000000000) (-25779103089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2021697306719793 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-14246380209 / 1000000000000) (-14246380208 / 1000000000000), orderedInterval (-32491535618 / 1000000000000) (-32491535617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3587537348172837 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19586366019 / 1000000000000) (-19586363911 / 1000000000000), orderedInterval (18071562090 / 1000000000000) (18071564197 / 1000000000000)))) (orderedInterval (-114455726891 / 1000000000000) (-114455715255 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3351942753768153 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (945244645 / 1000000000000) (945244646 / 1000000000000), orderedInterval (-27547053569 / 1000000000000) (-27547053568 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2392104512766249 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (30782035275 / 1000000000000) (30782067696 / 1000000000000), orderedInterval (-10842407765 / 1000000000000) (-10842375344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2712391564652271 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9028256239 / 1000000000000) (9028256240 / 1000000000000), orderedInterval (29273412382 / 1000000000000) (29273412383 / 1000000000000)))) (orderedInterval (15080692104 / 1000000000000) (15080709220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2261309305571199 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19656885841 / 1000000000000) (19656885842 / 1000000000000), orderedInterval (27180321097 / 1000000000000) (27180321098 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1997935350103179 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24485010369 / 1000000000000) (-24485010368 / 1000000000000), orderedInterval (-25957014014 / 1000000000000) (-25957014013 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (579079537730721 / 800000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26060641261 / 1000000000000) (26060698853 / 1000000000000), orderedInterval (-14171945145 / 1000000000000) (-14171887553 / 1000000000000)))) (orderedInterval (12505660787 / 1000000000000) (12505678264 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate520_chunkChecks4_2 :
    compactCertificate520.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1601764476649587 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31174798863 / 1000000000000) (-31174746877 / 1000000000000), orderedInterval (24897084995 / 1000000000000) (24897136981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1357833485911707 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35260751261 / 1000000000000) (35260751262 / 1000000000000), orderedInterval (25089213059 / 1000000000000) (25089213060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (849669149253321 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22632509663 / 1000000000000) (-22632508517 / 1000000000000), orderedInterval (49901034027 / 1000000000000) (49901035173 / 1000000000000)))) (orderedInterval (4238667644 / 1000000000000) (4238676874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (456954894340407 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69998255203 / 1000000000000) (69998258594 / 1000000000000), orderedInterval (-26247024679 / 1000000000000) (-26247021289 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1240721428522221 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (2369220787 / 1000000000000) (2369220790 / 1000000000000), orderedInterval (-45245476033 / 1000000000000) (-45245476030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1694099038109517 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-7506868675 / 1000000000000) (-7506868674 / 1000000000000), orderedInterval (-38027888566 / 1000000000000) (-38027888565 / 1000000000000)))) (orderedInterval (778903248 / 1000000000000) (778903294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (716330850746679 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-42630616102 / 1000000000000) (-42630616101 / 1000000000000), orderedInterval (-41564577672 / 1000000000000) (-41564577671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2911845138785559 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-3040113000 / 1000000000000) (-3040112999 / 1000000000000), orderedInterval (29417766430 / 1000000000000) (29417766431 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1944977605972281 / 4000000000000) 4 (IntervalRat.scale (783 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-2988304776 / 1000000000000) (-2988304775 / 1000000000000), orderedInterval (-36057009516 / 1000000000000) (-36057009515 / 1000000000000)))) (orderedInterval (4268544512 / 1000000000000) (4268545070 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate520_chunkChecks4 :
    compactCertificate520.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate520.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate520_chunkChecks4_0
    compactCertificate520_chunkChecks4_1 compactCertificate520_chunkChecks4_2

theorem compactCertificate520_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate520.chunkCheck r b = true :=
  compactCertificate520.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate520_chunkChecks0
    · exact compactCertificate520_chunkChecks1
    · exact compactCertificate520_chunkChecks2
    · exact compactCertificate520_chunkChecks3
    · exact compactCertificate520_chunkChecks4)

theorem compactCertificate520_coefficient0 :
    compactCertificate520.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate520_coefficient1 :
    compactCertificate520.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate520_coefficient2 :
    compactCertificate520.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate520_coefficient3 :
    compactCertificate520.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate520_coefficient4 :
    compactCertificate520.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate520_coefficients : ∀ r : Fin 5,
    compactCertificate520.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate520_coefficient0
  · exact compactCertificate520_coefficient1
  · exact compactCertificate520_coefficient2
  · exact compactCertificate520_coefficient3
  · exact compactCertificate520_coefficient4

theorem compactCertificate520_lower : (1 : ℚ) ≤ compactCertificate520.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate520, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate520_proves {t : ℝ} (ht : t ∈ compactCertificate520.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate520.proves compactCertificate520_states compactCertificate520_chunks
    compactCertificate520_coefficients compactCertificate520_lower ht

end Erdos232
