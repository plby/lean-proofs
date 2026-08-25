/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate294 : CompactCertificate where
  left := 167
  right := 168
  center := 335 / 2
  grid := fun i =>
    match i.val with
    | 0 => 53
    | 1 => 39
    | 2 => 64
    | 3 => 11
    | 4 => 31
    | 5 => 84
    | 6 => 62
    | 7 => 106
    | 8 => 78
    | 9 => 119
    | 10 => 69
    | 11 => 122
    | 12 => 114
    | 13 => 81
    | 14 => 92
    | 15 => 77
    | 16 => 68
    | 17 => 99
    | 18 => 55
    | 19 => 46
    | 20 => 29
    | 21 => 16
    | 22 => 42
    | 23 => 58
    | 24 => 24
    | 25 => 99
    | _ => 66
  point := fun i =>
    match i.val with
    | 0 => 335 / 2
    | 1 => 98703793509367 / 800000000000
    | 2 => 31918778823511 / 160000000000
    | 3 => 28801520775269 / 800000000000
    | 4 => 77364936071393 / 800000000000
    | 5 => 210060851057181 / 800000000000
    | 6 => 154729872142853 / 800000000000
    | 7 => 265132273202969 / 800000000000
    | 8 => 195295232439371 / 800000000000
    | 9 => 299633108984933 / 800000000000
    | 10 => 172993256130557 / 800000000000
    | 11 => 306979568745313 / 800000000000
    | 12 => 286820133464197 / 800000000000
    | 13 => 204688381041301 / 800000000000
    | 14 => 232094808214179 / 800000000000
    | 15 => 193496453988851 / 800000000000
    | 16 => 170959985257871 / 800000000000
    | 17 => 49550867213229 / 160000000000
    | 18 => 137060306431063 / 800000000000
    | 19 => 116187539662943 / 800000000000
    | 20 => 72704767560629 / 800000000000
    | 21 => 39100865799243 / 800000000000
    | 22 => 106166456846729 / 800000000000
    | 23 => 144961220374633 / 800000000000
    | 24 => 61295232439371 / 800000000000
    | 25 => 249161716856491 / 800000000000
    | _ => 166428479693669 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-60302537029 / 1000000000000) (-60302536155 / 1000000000000), orderedInterval (12998104778 / 1000000000000) (12998105652 / 1000000000000))
    | 1 => (orderedInterval (-71649649978 / 1000000000000) (-71649649869 / 1000000000000), orderedInterval (5401726547 / 1000000000000) (5401726656 / 1000000000000))
    | 2 => (orderedInterval (-39920636992 / 1000000000000) (-39920589918 / 1000000000000), orderedInterval (40069308617 / 1000000000000) (40069355691 / 1000000000000))
    | 3 => (orderedInterval (-105410709644 / 1000000000000) (-105410664905 / 1000000000000), orderedInterval (82525963553 / 1000000000000) (82526008293 / 1000000000000))
    | 4 => (orderedInterval (-8172953617 / 1000000000000) (-8172953615 / 1000000000000), orderedInterval (-80681474624 / 1000000000000) (-80681474623 / 1000000000000))
    | 5 => (orderedInterval (-25010851329 / 1000000000000) (-25010848444 / 1000000000000), orderedInterval (42461951418 / 1000000000000) (42461954303 / 1000000000000))
    | 6 => (orderedInterval (-31520291302 / 1000000000000) (-31520284290 / 1000000000000), orderedInterval (48018852154 / 1000000000000) (48018859166 / 1000000000000))
    | 7 => (orderedInterval (-31697596948 / 1000000000000) (-31697564958 / 1000000000000), orderedInterval (30316194889 / 1000000000000) (30316226878 / 1000000000000))
    | 8 => (orderedInterval (-7141207956 / 1000000000000) (-7141207937 / 1000000000000), orderedInterval (50579768067 / 1000000000000) (50579768086 / 1000000000000))
    | 9 => (orderedInterval (-41046267962 / 1000000000000) (-41046267899 / 1000000000000), orderedInterval (-3809638476 / 1000000000000) (-3809638413 / 1000000000000))
    | 10 => (orderedInterval (-13765116621 / 1000000000000) (-13765116620 / 1000000000000), orderedInterval (-52451975730 / 1000000000000) (-52451975729 / 1000000000000))
    | 11 => (orderedInterval (38459629378 / 1000000000000) (38459629381 / 1000000000000), orderedInterval (13362949128 / 1000000000000) (13362949130 / 1000000000000))
    | 12 => (orderedInterval (38776967690 / 1000000000000) (38776967691 / 1000000000000), orderedInterval (16438595714 / 1000000000000) (16438595715 / 1000000000000))
    | 13 => (orderedInterval (-41010942441 / 1000000000000) (-41010867883 / 1000000000000), orderedInterval (28474750589 / 1000000000000) (28474825146 / 1000000000000))
    | 14 => (orderedInterval (44665496126 / 1000000000000) (44665501308 / 1000000000000), orderedInterval (-14195564230 / 1000000000000) (-14195559047 / 1000000000000))
    | 15 => (orderedInterval (-35076055725 / 1000000000000) (-35076055724 / 1000000000000), orderedInterval (-37367290633 / 1000000000000) (-37367290632 / 1000000000000))
    | 16 => (orderedInterval (41238308129 / 1000000000000) (41238308130 / 1000000000000), orderedInterval (35658737614 / 1000000000000) (35658737615 / 1000000000000))
    | 17 => (orderedInterval (23301120398 / 1000000000000) (23301122792 / 1000000000000), orderedInterval (-38931160718 / 1000000000000) (-38931158323 / 1000000000000))
    | 18 => (orderedInterval (38213228883 / 1000000000000) (38213248980 / 1000000000000), orderedInterval (-47604728028 / 1000000000000) (-47604707931 / 1000000000000))
    | 19 => (orderedInterval (66066784823 / 1000000000000) (66066784840 / 1000000000000), orderedInterval (4079368178 / 1000000000000) (4079368195 / 1000000000000))
    | 20 => (orderedInterval (-44372254392 / 1000000000000) (-44372254391 / 1000000000000), orderedInterval (-70721612877 / 1000000000000) (-70721612876 / 1000000000000))
    | 21 => (orderedInterval (-65056197915 / 1000000000000) (-65056179759 / 1000000000000), orderedInterval (94437030506 / 1000000000000) (94437048662 / 1000000000000))
    | 22 => (orderedInterval (69239252852 / 1000000000000) (69239252881 / 1000000000000), orderedInterval (1481603628 / 1000000000000) (1481603657 / 1000000000000))
    | 23 => (orderedInterval (-13290091832 / 1000000000000) (-13290091725 / 1000000000000), orderedInterval (57800934665 / 1000000000000) (57800934772 / 1000000000000))
    | 24 => (orderedInterval (82709700982 / 1000000000000) (82709707399 / 1000000000000), orderedInterval (-38852755000 / 1000000000000) (-38852748583 / 1000000000000))
    | 25 => (orderedInterval (-42449383994 / 1000000000000) (-42449383993 / 1000000000000), orderedInterval (-15490933212 / 1000000000000) (-15490933210 / 1000000000000))
    | _ => (orderedInterval (55066382262 / 1000000000000) (55066382280 / 1000000000000), orderedInterval (5143360609 / 1000000000000) (5143360627 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-26912038899 / 1000000000000) (-26912035777 / 1000000000000)
      | 1 => orderedInterval (2623234398 / 1000000000000) (2623235109 / 1000000000000)
      | 2 => orderedInterval (805090813 / 1000000000000) (805091811 / 1000000000000)
      | 3 => orderedInterval (11740807231 / 1000000000000) (11740807310 / 1000000000000)
      | 4 => orderedInterval (-4804189361 / 1000000000000) (-4804182264 / 1000000000000)
      | 5 => orderedInterval (-2168377343 / 1000000000000) (-2168377264 / 1000000000000)
      | 6 => orderedInterval (-11293937599 / 1000000000000) (-11293934342 / 1000000000000)
      | 7 => orderedInterval (648986197 / 1000000000000) (648986562 / 1000000000000)
      | _ => orderedInterval (-6377857589 / 1000000000000) (-6377857500 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (7989480791 / 1000000000000) (7989484442 / 1000000000000)
      | 1 => orderedInterval (-6625234713 / 1000000000000) (-6625234263 / 1000000000000)
      | 2 => orderedInterval (-68557875 / 1000000000000) (-68555905 / 1000000000000)
      | 3 => orderedInterval (848343674 / 1000000000000) (848343838 / 1000000000000)
      | 4 => orderedInterval (3602308127 / 1000000000000) (3602318975 / 1000000000000)
      | 5 => orderedInterval (-5069555124 / 1000000000000) (-5069554986 / 1000000000000)
      | 6 => orderedInterval (6336069608 / 1000000000000) (6336072935 / 1000000000000)
      | 7 => orderedInterval (-5327621514 / 1000000000000) (-5327621388 / 1000000000000)
      | _ => orderedInterval (1038994651 / 1000000000000) (1038994739 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (27539265885 / 1000000000000) (27539270188 / 1000000000000)
      | 1 => orderedInterval (-4283146001 / 1000000000000) (-4283145440 / 1000000000000)
      | 2 => orderedInterval (-3460473161 / 1000000000000) (-3460469256 / 1000000000000)
      | 3 => orderedInterval (-63465614080 / 1000000000000) (-63465613726 / 1000000000000)
      | 4 => orderedInterval (12912771042 / 1000000000000) (12912787691 / 1000000000000)
      | 5 => orderedInterval (2676684434 / 1000000000000) (2676684680 / 1000000000000)
      | 6 => orderedInterval (9591012835 / 1000000000000) (9591016254 / 1000000000000)
      | 7 => orderedInterval (-276428492 / 1000000000000) (-276428434 / 1000000000000)
      | _ => orderedInterval (3880215657 / 1000000000000) (3880215767 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9308569031 / 1000000000000) (-9308563974 / 1000000000000)
      | 1 => orderedInterval (12229743702 / 1000000000000) (12229744548 / 1000000000000)
      | 2 => orderedInterval (3479423104 / 1000000000000) (3479430824 / 1000000000000)
      | 3 => orderedInterval (-21666658910 / 1000000000000) (-21666658134 / 1000000000000)
      | 4 => orderedInterval (-7137241594 / 1000000000000) (-7137216139 / 1000000000000)
      | 5 => orderedInterval (11821005655 / 1000000000000) (11821006097 / 1000000000000)
      | 6 => orderedInterval (-7683918617 / 1000000000000) (-7683915121 / 1000000000000)
      | 7 => orderedInterval (5669722649 / 1000000000000) (5669722687 / 1000000000000)
      | _ => orderedInterval (-6258469169 / 1000000000000) (-6258469008 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-28699712439 / 1000000000000) (-28699706453 / 1000000000000)
      | 1 => orderedInterval (10560429579 / 1000000000000) (10560430902 / 1000000000000)
      | 2 => orderedInterval (14163650112 / 1000000000000) (14163665426 / 1000000000000)
      | 3 => orderedInterval (330346499676 / 1000000000000) (330346501406 / 1000000000000)
      | 4 => orderedInterval (-37756940976 / 1000000000000) (-37756901895 / 1000000000000)
      | 5 => orderedInterval (-1182812415 / 1000000000000) (-1182811609 / 1000000000000)
      | 6 => orderedInterval (-8834265904 / 1000000000000) (-8834262309 / 1000000000000)
      | 7 => orderedInterval (717021301 / 1000000000000) (717021335 / 1000000000000)
      | _ => orderedInterval (16817413247 / 1000000000000) (16817413496 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-35738282152 / 1000000000000) (-35738266355 / 1000000000000)
    | 1 => orderedInterval (2724227625 / 1000000000000) (2724248387 / 1000000000000)
    | 2 => orderedInterval (-14885711881 / 1000000000000) (-14885682276 / 1000000000000)
    | 3 => orderedInterval (-18854962211 / 1000000000000) (-18854918220 / 1000000000000)
    | _ => orderedInterval (296131282181 / 1000000000000) (296131350299 / 1000000000000)

theorem compactCertificate294_stateChecks0 :
    compactCertificate294.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (335 / 2)) (orderedInterval (-60302537029 / 1000000000000) (-60302536155 / 1000000000000), orderedInterval (12998104778 / 1000000000000) (12998105652 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (98703793509367 / 800000000000)) (orderedInterval (-71649649978 / 1000000000000) (-71649649869 / 1000000000000), orderedInterval (5401726547 / 1000000000000) (5401726656 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (31918778823511 / 160000000000)) (orderedInterval (-39920636992 / 1000000000000) (-39920589918 / 1000000000000), orderedInterval (40069308617 / 1000000000000) (40069355691 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_stateChecks1 :
    compactCertificate294.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (28801520775269 / 800000000000)) (orderedInterval (-105410709644 / 1000000000000) (-105410664905 / 1000000000000), orderedInterval (82525963553 / 1000000000000) (82526008293 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (77364936071393 / 800000000000)) (orderedInterval (-8172953617 / 1000000000000) (-8172953615 / 1000000000000), orderedInterval (-80681474624 / 1000000000000) (-80681474623 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (210060851057181 / 800000000000)) (orderedInterval (-25010851329 / 1000000000000) (-25010848444 / 1000000000000), orderedInterval (42461951418 / 1000000000000) (42461954303 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_stateChecks2 :
    compactCertificate294.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (154729872142853 / 800000000000)) (orderedInterval (-31520291302 / 1000000000000) (-31520284290 / 1000000000000), orderedInterval (48018852154 / 1000000000000) (48018859166 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (265132273202969 / 800000000000)) (orderedInterval (-31697596948 / 1000000000000) (-31697564958 / 1000000000000), orderedInterval (30316194889 / 1000000000000) (30316226878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (195295232439371 / 800000000000)) (orderedInterval (-7141207956 / 1000000000000) (-7141207937 / 1000000000000), orderedInterval (50579768067 / 1000000000000) (50579768086 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_stateChecks3 :
    compactCertificate294.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (299633108984933 / 800000000000)) (orderedInterval (-41046267962 / 1000000000000) (-41046267899 / 1000000000000), orderedInterval (-3809638476 / 1000000000000) (-3809638413 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (172993256130557 / 800000000000)) (orderedInterval (-13765116621 / 1000000000000) (-13765116620 / 1000000000000), orderedInterval (-52451975730 / 1000000000000) (-52451975729 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (306979568745313 / 800000000000)) (orderedInterval (38459629378 / 1000000000000) (38459629381 / 1000000000000), orderedInterval (13362949128 / 1000000000000) (13362949130 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_stateChecks4 :
    compactCertificate294.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (286820133464197 / 800000000000)) (orderedInterval (38776967690 / 1000000000000) (38776967691 / 1000000000000), orderedInterval (16438595714 / 1000000000000) (16438595715 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (204688381041301 / 800000000000)) (orderedInterval (-41010942441 / 1000000000000) (-41010867883 / 1000000000000), orderedInterval (28474750589 / 1000000000000) (28474825146 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (232094808214179 / 800000000000)) (orderedInterval (44665496126 / 1000000000000) (44665501308 / 1000000000000), orderedInterval (-14195564230 / 1000000000000) (-14195559047 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_stateChecks5 :
    compactCertificate294.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (193496453988851 / 800000000000)) (orderedInterval (-35076055725 / 1000000000000) (-35076055724 / 1000000000000), orderedInterval (-37367290633 / 1000000000000) (-37367290632 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (170959985257871 / 800000000000)) (orderedInterval (41238308129 / 1000000000000) (41238308130 / 1000000000000), orderedInterval (35658737614 / 1000000000000) (35658737615 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (49550867213229 / 160000000000)) (orderedInterval (23301120398 / 1000000000000) (23301122792 / 1000000000000), orderedInterval (-38931160718 / 1000000000000) (-38931158323 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_stateChecks6 :
    compactCertificate294.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (137060306431063 / 800000000000)) (orderedInterval (38213228883 / 1000000000000) (38213248980 / 1000000000000), orderedInterval (-47604728028 / 1000000000000) (-47604707931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (116187539662943 / 800000000000)) (orderedInterval (66066784823 / 1000000000000) (66066784840 / 1000000000000), orderedInterval (4079368178 / 1000000000000) (4079368195 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (72704767560629 / 800000000000)) (orderedInterval (-44372254392 / 1000000000000) (-44372254391 / 1000000000000), orderedInterval (-70721612877 / 1000000000000) (-70721612876 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_stateChecks7 :
    compactCertificate294.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (39100865799243 / 800000000000)) (orderedInterval (-65056197915 / 1000000000000) (-65056179759 / 1000000000000), orderedInterval (94437030506 / 1000000000000) (94437048662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (106166456846729 / 800000000000)) (orderedInterval (69239252852 / 1000000000000) (69239252881 / 1000000000000), orderedInterval (1481603628 / 1000000000000) (1481603657 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (144961220374633 / 800000000000)) (orderedInterval (-13290091832 / 1000000000000) (-13290091725 / 1000000000000), orderedInterval (57800934665 / 1000000000000) (57800934772 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_stateChecks8 :
    compactCertificate294.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (61295232439371 / 800000000000)) (orderedInterval (82709700982 / 1000000000000) (82709707399 / 1000000000000), orderedInterval (-38852755000 / 1000000000000) (-38852748583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (249161716856491 / 800000000000)) (orderedInterval (-42449383994 / 1000000000000) (-42449383993 / 1000000000000), orderedInterval (-15490933212 / 1000000000000) (-15490933210 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (166428479693669 / 800000000000)) (orderedInterval (55066382262 / 1000000000000) (55066382280 / 1000000000000), orderedInterval (5143360609 / 1000000000000) (5143360627 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_states : ∀ j,
    BesselStateValid (compactCertificate294.point j) (compactCertificate294.state j) :=
  compactCertificate294.statesValid_of_checks3 compactCertificate294_stateChecks0
    compactCertificate294_stateChecks1 compactCertificate294_stateChecks2
    compactCertificate294_stateChecks3 compactCertificate294_stateChecks4
    compactCertificate294_stateChecks5 compactCertificate294_stateChecks6
    compactCertificate294_stateChecks7 compactCertificate294_stateChecks8

theorem compactCertificate294_chunkChecks0_0 :
    compactCertificate294.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (335 / 2) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-60302537029 / 1000000000000) (-60302536155 / 1000000000000), orderedInterval (12998104778 / 1000000000000) (12998105652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (98703793509367 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-71649649978 / 1000000000000) (-71649649869 / 1000000000000), orderedInterval (5401726547 / 1000000000000) (5401726656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (31918778823511 / 160000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39920636992 / 1000000000000) (-39920589918 / 1000000000000), orderedInterval (40069308617 / 1000000000000) (40069355691 / 1000000000000)))) (orderedInterval (-26912038899 / 1000000000000) (-26912035777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (28801520775269 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-105410709644 / 1000000000000) (-105410664905 / 1000000000000), orderedInterval (82525963553 / 1000000000000) (82526008293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (77364936071393 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8172953617 / 1000000000000) (-8172953615 / 1000000000000), orderedInterval (-80681474624 / 1000000000000) (-80681474623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (210060851057181 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25010851329 / 1000000000000) (-25010848444 / 1000000000000), orderedInterval (42461951418 / 1000000000000) (42461954303 / 1000000000000)))) (orderedInterval (2623234398 / 1000000000000) (2623235109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (154729872142853 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31520291302 / 1000000000000) (-31520284290 / 1000000000000), orderedInterval (48018852154 / 1000000000000) (48018859166 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (265132273202969 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31697596948 / 1000000000000) (-31697564958 / 1000000000000), orderedInterval (30316194889 / 1000000000000) (30316226878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (195295232439371 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-7141207956 / 1000000000000) (-7141207937 / 1000000000000), orderedInterval (50579768067 / 1000000000000) (50579768086 / 1000000000000)))) (orderedInterval (805090813 / 1000000000000) (805091811 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_chunkChecks0_1 :
    compactCertificate294.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (299633108984933 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-41046267962 / 1000000000000) (-41046267899 / 1000000000000), orderedInterval (-3809638476 / 1000000000000) (-3809638413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (172993256130557 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13765116621 / 1000000000000) (-13765116620 / 1000000000000), orderedInterval (-52451975730 / 1000000000000) (-52451975729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (306979568745313 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38459629378 / 1000000000000) (38459629381 / 1000000000000), orderedInterval (13362949128 / 1000000000000) (13362949130 / 1000000000000)))) (orderedInterval (11740807231 / 1000000000000) (11740807310 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (286820133464197 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38776967690 / 1000000000000) (38776967691 / 1000000000000), orderedInterval (16438595714 / 1000000000000) (16438595715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (204688381041301 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41010942441 / 1000000000000) (-41010867883 / 1000000000000), orderedInterval (28474750589 / 1000000000000) (28474825146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (232094808214179 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44665496126 / 1000000000000) (44665501308 / 1000000000000), orderedInterval (-14195564230 / 1000000000000) (-14195559047 / 1000000000000)))) (orderedInterval (-4804189361 / 1000000000000) (-4804182264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (193496453988851 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35076055725 / 1000000000000) (-35076055724 / 1000000000000), orderedInterval (-37367290633 / 1000000000000) (-37367290632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (170959985257871 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41238308129 / 1000000000000) (41238308130 / 1000000000000), orderedInterval (35658737614 / 1000000000000) (35658737615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (49550867213229 / 160000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23301120398 / 1000000000000) (23301122792 / 1000000000000), orderedInterval (-38931160718 / 1000000000000) (-38931158323 / 1000000000000)))) (orderedInterval (-2168377343 / 1000000000000) (-2168377264 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_chunkChecks0_2 :
    compactCertificate294.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (137060306431063 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38213228883 / 1000000000000) (38213248980 / 1000000000000), orderedInterval (-47604728028 / 1000000000000) (-47604707931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (116187539662943 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (66066784823 / 1000000000000) (66066784840 / 1000000000000), orderedInterval (4079368178 / 1000000000000) (4079368195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (72704767560629 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-44372254392 / 1000000000000) (-44372254391 / 1000000000000), orderedInterval (-70721612877 / 1000000000000) (-70721612876 / 1000000000000)))) (orderedInterval (-11293937599 / 1000000000000) (-11293934342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (39100865799243 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-65056197915 / 1000000000000) (-65056179759 / 1000000000000), orderedInterval (94437030506 / 1000000000000) (94437048662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (106166456846729 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69239252852 / 1000000000000) (69239252881 / 1000000000000), orderedInterval (1481603628 / 1000000000000) (1481603657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (144961220374633 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13290091832 / 1000000000000) (-13290091725 / 1000000000000), orderedInterval (57800934665 / 1000000000000) (57800934772 / 1000000000000)))) (orderedInterval (648986197 / 1000000000000) (648986562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (61295232439371 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82709700982 / 1000000000000) (82709707399 / 1000000000000), orderedInterval (-38852755000 / 1000000000000) (-38852748583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (249161716856491 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42449383994 / 1000000000000) (-42449383993 / 1000000000000), orderedInterval (-15490933212 / 1000000000000) (-15490933210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (166428479693669 / 800000000000) 0 (IntervalRat.scale (335 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (55066382262 / 1000000000000) (55066382280 / 1000000000000), orderedInterval (5143360609 / 1000000000000) (5143360627 / 1000000000000)))) (orderedInterval (-6377857589 / 1000000000000) (-6377857500 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_chunkChecks0 :
    compactCertificate294.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate294.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate294_chunkChecks0_0
    compactCertificate294_chunkChecks0_1 compactCertificate294_chunkChecks0_2

theorem compactCertificate294_chunkChecks1_0 :
    compactCertificate294.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (335 / 2) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-60302537029 / 1000000000000) (-60302536155 / 1000000000000), orderedInterval (12998104778 / 1000000000000) (12998105652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (98703793509367 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-71649649978 / 1000000000000) (-71649649869 / 1000000000000), orderedInterval (5401726547 / 1000000000000) (5401726656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (31918778823511 / 160000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39920636992 / 1000000000000) (-39920589918 / 1000000000000), orderedInterval (40069308617 / 1000000000000) (40069355691 / 1000000000000)))) (orderedInterval (7989480791 / 1000000000000) (7989484442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (28801520775269 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-105410709644 / 1000000000000) (-105410664905 / 1000000000000), orderedInterval (82525963553 / 1000000000000) (82526008293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (77364936071393 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8172953617 / 1000000000000) (-8172953615 / 1000000000000), orderedInterval (-80681474624 / 1000000000000) (-80681474623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (210060851057181 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25010851329 / 1000000000000) (-25010848444 / 1000000000000), orderedInterval (42461951418 / 1000000000000) (42461954303 / 1000000000000)))) (orderedInterval (-6625234713 / 1000000000000) (-6625234263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (154729872142853 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31520291302 / 1000000000000) (-31520284290 / 1000000000000), orderedInterval (48018852154 / 1000000000000) (48018859166 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (265132273202969 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31697596948 / 1000000000000) (-31697564958 / 1000000000000), orderedInterval (30316194889 / 1000000000000) (30316226878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (195295232439371 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-7141207956 / 1000000000000) (-7141207937 / 1000000000000), orderedInterval (50579768067 / 1000000000000) (50579768086 / 1000000000000)))) (orderedInterval (-68557875 / 1000000000000) (-68555905 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_chunkChecks1_1 :
    compactCertificate294.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (299633108984933 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-41046267962 / 1000000000000) (-41046267899 / 1000000000000), orderedInterval (-3809638476 / 1000000000000) (-3809638413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (172993256130557 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13765116621 / 1000000000000) (-13765116620 / 1000000000000), orderedInterval (-52451975730 / 1000000000000) (-52451975729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (306979568745313 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38459629378 / 1000000000000) (38459629381 / 1000000000000), orderedInterval (13362949128 / 1000000000000) (13362949130 / 1000000000000)))) (orderedInterval (848343674 / 1000000000000) (848343838 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (286820133464197 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38776967690 / 1000000000000) (38776967691 / 1000000000000), orderedInterval (16438595714 / 1000000000000) (16438595715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (204688381041301 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41010942441 / 1000000000000) (-41010867883 / 1000000000000), orderedInterval (28474750589 / 1000000000000) (28474825146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (232094808214179 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44665496126 / 1000000000000) (44665501308 / 1000000000000), orderedInterval (-14195564230 / 1000000000000) (-14195559047 / 1000000000000)))) (orderedInterval (3602308127 / 1000000000000) (3602318975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (193496453988851 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35076055725 / 1000000000000) (-35076055724 / 1000000000000), orderedInterval (-37367290633 / 1000000000000) (-37367290632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (170959985257871 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41238308129 / 1000000000000) (41238308130 / 1000000000000), orderedInterval (35658737614 / 1000000000000) (35658737615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (49550867213229 / 160000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23301120398 / 1000000000000) (23301122792 / 1000000000000), orderedInterval (-38931160718 / 1000000000000) (-38931158323 / 1000000000000)))) (orderedInterval (-5069555124 / 1000000000000) (-5069554986 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_chunkChecks1_2 :
    compactCertificate294.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (137060306431063 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38213228883 / 1000000000000) (38213248980 / 1000000000000), orderedInterval (-47604728028 / 1000000000000) (-47604707931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (116187539662943 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (66066784823 / 1000000000000) (66066784840 / 1000000000000), orderedInterval (4079368178 / 1000000000000) (4079368195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (72704767560629 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-44372254392 / 1000000000000) (-44372254391 / 1000000000000), orderedInterval (-70721612877 / 1000000000000) (-70721612876 / 1000000000000)))) (orderedInterval (6336069608 / 1000000000000) (6336072935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (39100865799243 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-65056197915 / 1000000000000) (-65056179759 / 1000000000000), orderedInterval (94437030506 / 1000000000000) (94437048662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (106166456846729 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69239252852 / 1000000000000) (69239252881 / 1000000000000), orderedInterval (1481603628 / 1000000000000) (1481603657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (144961220374633 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13290091832 / 1000000000000) (-13290091725 / 1000000000000), orderedInterval (57800934665 / 1000000000000) (57800934772 / 1000000000000)))) (orderedInterval (-5327621514 / 1000000000000) (-5327621388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (61295232439371 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82709700982 / 1000000000000) (82709707399 / 1000000000000), orderedInterval (-38852755000 / 1000000000000) (-38852748583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (249161716856491 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42449383994 / 1000000000000) (-42449383993 / 1000000000000), orderedInterval (-15490933212 / 1000000000000) (-15490933210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (166428479693669 / 800000000000) 1 (IntervalRat.scale (335 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (55066382262 / 1000000000000) (55066382280 / 1000000000000), orderedInterval (5143360609 / 1000000000000) (5143360627 / 1000000000000)))) (orderedInterval (1038994651 / 1000000000000) (1038994739 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_chunkChecks1 :
    compactCertificate294.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate294.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate294_chunkChecks1_0
    compactCertificate294_chunkChecks1_1 compactCertificate294_chunkChecks1_2

theorem compactCertificate294_chunkChecks2_0 :
    compactCertificate294.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (335 / 2) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-60302537029 / 1000000000000) (-60302536155 / 1000000000000), orderedInterval (12998104778 / 1000000000000) (12998105652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (98703793509367 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-71649649978 / 1000000000000) (-71649649869 / 1000000000000), orderedInterval (5401726547 / 1000000000000) (5401726656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (31918778823511 / 160000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39920636992 / 1000000000000) (-39920589918 / 1000000000000), orderedInterval (40069308617 / 1000000000000) (40069355691 / 1000000000000)))) (orderedInterval (27539265885 / 1000000000000) (27539270188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (28801520775269 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-105410709644 / 1000000000000) (-105410664905 / 1000000000000), orderedInterval (82525963553 / 1000000000000) (82526008293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (77364936071393 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8172953617 / 1000000000000) (-8172953615 / 1000000000000), orderedInterval (-80681474624 / 1000000000000) (-80681474623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (210060851057181 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25010851329 / 1000000000000) (-25010848444 / 1000000000000), orderedInterval (42461951418 / 1000000000000) (42461954303 / 1000000000000)))) (orderedInterval (-4283146001 / 1000000000000) (-4283145440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (154729872142853 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31520291302 / 1000000000000) (-31520284290 / 1000000000000), orderedInterval (48018852154 / 1000000000000) (48018859166 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (265132273202969 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31697596948 / 1000000000000) (-31697564958 / 1000000000000), orderedInterval (30316194889 / 1000000000000) (30316226878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (195295232439371 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-7141207956 / 1000000000000) (-7141207937 / 1000000000000), orderedInterval (50579768067 / 1000000000000) (50579768086 / 1000000000000)))) (orderedInterval (-3460473161 / 1000000000000) (-3460469256 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_chunkChecks2_1 :
    compactCertificate294.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (299633108984933 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-41046267962 / 1000000000000) (-41046267899 / 1000000000000), orderedInterval (-3809638476 / 1000000000000) (-3809638413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (172993256130557 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13765116621 / 1000000000000) (-13765116620 / 1000000000000), orderedInterval (-52451975730 / 1000000000000) (-52451975729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (306979568745313 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38459629378 / 1000000000000) (38459629381 / 1000000000000), orderedInterval (13362949128 / 1000000000000) (13362949130 / 1000000000000)))) (orderedInterval (-63465614080 / 1000000000000) (-63465613726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (286820133464197 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38776967690 / 1000000000000) (38776967691 / 1000000000000), orderedInterval (16438595714 / 1000000000000) (16438595715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (204688381041301 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41010942441 / 1000000000000) (-41010867883 / 1000000000000), orderedInterval (28474750589 / 1000000000000) (28474825146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (232094808214179 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44665496126 / 1000000000000) (44665501308 / 1000000000000), orderedInterval (-14195564230 / 1000000000000) (-14195559047 / 1000000000000)))) (orderedInterval (12912771042 / 1000000000000) (12912787691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (193496453988851 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35076055725 / 1000000000000) (-35076055724 / 1000000000000), orderedInterval (-37367290633 / 1000000000000) (-37367290632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (170959985257871 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41238308129 / 1000000000000) (41238308130 / 1000000000000), orderedInterval (35658737614 / 1000000000000) (35658737615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (49550867213229 / 160000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23301120398 / 1000000000000) (23301122792 / 1000000000000), orderedInterval (-38931160718 / 1000000000000) (-38931158323 / 1000000000000)))) (orderedInterval (2676684434 / 1000000000000) (2676684680 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_chunkChecks2_2 :
    compactCertificate294.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (137060306431063 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38213228883 / 1000000000000) (38213248980 / 1000000000000), orderedInterval (-47604728028 / 1000000000000) (-47604707931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (116187539662943 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (66066784823 / 1000000000000) (66066784840 / 1000000000000), orderedInterval (4079368178 / 1000000000000) (4079368195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (72704767560629 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-44372254392 / 1000000000000) (-44372254391 / 1000000000000), orderedInterval (-70721612877 / 1000000000000) (-70721612876 / 1000000000000)))) (orderedInterval (9591012835 / 1000000000000) (9591016254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (39100865799243 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-65056197915 / 1000000000000) (-65056179759 / 1000000000000), orderedInterval (94437030506 / 1000000000000) (94437048662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (106166456846729 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69239252852 / 1000000000000) (69239252881 / 1000000000000), orderedInterval (1481603628 / 1000000000000) (1481603657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (144961220374633 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13290091832 / 1000000000000) (-13290091725 / 1000000000000), orderedInterval (57800934665 / 1000000000000) (57800934772 / 1000000000000)))) (orderedInterval (-276428492 / 1000000000000) (-276428434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (61295232439371 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82709700982 / 1000000000000) (82709707399 / 1000000000000), orderedInterval (-38852755000 / 1000000000000) (-38852748583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (249161716856491 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42449383994 / 1000000000000) (-42449383993 / 1000000000000), orderedInterval (-15490933212 / 1000000000000) (-15490933210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (166428479693669 / 800000000000) 2 (IntervalRat.scale (335 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (55066382262 / 1000000000000) (55066382280 / 1000000000000), orderedInterval (5143360609 / 1000000000000) (5143360627 / 1000000000000)))) (orderedInterval (3880215657 / 1000000000000) (3880215767 / 1000000000000))) = true
  rfl'

theorem compactCertificate294_chunkChecks2 :
    compactCertificate294.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate294.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate294_chunkChecks2_0
    compactCertificate294_chunkChecks2_1 compactCertificate294_chunkChecks2_2

theorem compactCertificate294_chunkChecks3_0 :
    compactCertificate294.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (335 / 2) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-60302537029 / 1000000000000) (-60302536155 / 1000000000000), orderedInterval (12998104778 / 1000000000000) (12998105652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (98703793509367 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-71649649978 / 1000000000000) (-71649649869 / 1000000000000), orderedInterval (5401726547 / 1000000000000) (5401726656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (31918778823511 / 160000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39920636992 / 1000000000000) (-39920589918 / 1000000000000), orderedInterval (40069308617 / 1000000000000) (40069355691 / 1000000000000)))) (orderedInterval (-9308569031 / 1000000000000) (-9308563974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (28801520775269 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-105410709644 / 1000000000000) (-105410664905 / 1000000000000), orderedInterval (82525963553 / 1000000000000) (82526008293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (77364936071393 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8172953617 / 1000000000000) (-8172953615 / 1000000000000), orderedInterval (-80681474624 / 1000000000000) (-80681474623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (210060851057181 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25010851329 / 1000000000000) (-25010848444 / 1000000000000), orderedInterval (42461951418 / 1000000000000) (42461954303 / 1000000000000)))) (orderedInterval (12229743702 / 1000000000000) (12229744548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (154729872142853 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31520291302 / 1000000000000) (-31520284290 / 1000000000000), orderedInterval (48018852154 / 1000000000000) (48018859166 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (265132273202969 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31697596948 / 1000000000000) (-31697564958 / 1000000000000), orderedInterval (30316194889 / 1000000000000) (30316226878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (195295232439371 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-7141207956 / 1000000000000) (-7141207937 / 1000000000000), orderedInterval (50579768067 / 1000000000000) (50579768086 / 1000000000000)))) (orderedInterval (3479423104 / 1000000000000) (3479430824 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate294_chunkChecks3_1 :
    compactCertificate294.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (299633108984933 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-41046267962 / 1000000000000) (-41046267899 / 1000000000000), orderedInterval (-3809638476 / 1000000000000) (-3809638413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (172993256130557 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13765116621 / 1000000000000) (-13765116620 / 1000000000000), orderedInterval (-52451975730 / 1000000000000) (-52451975729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (306979568745313 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38459629378 / 1000000000000) (38459629381 / 1000000000000), orderedInterval (13362949128 / 1000000000000) (13362949130 / 1000000000000)))) (orderedInterval (-21666658910 / 1000000000000) (-21666658134 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (286820133464197 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38776967690 / 1000000000000) (38776967691 / 1000000000000), orderedInterval (16438595714 / 1000000000000) (16438595715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (204688381041301 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41010942441 / 1000000000000) (-41010867883 / 1000000000000), orderedInterval (28474750589 / 1000000000000) (28474825146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (232094808214179 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44665496126 / 1000000000000) (44665501308 / 1000000000000), orderedInterval (-14195564230 / 1000000000000) (-14195559047 / 1000000000000)))) (orderedInterval (-7137241594 / 1000000000000) (-7137216139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (193496453988851 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35076055725 / 1000000000000) (-35076055724 / 1000000000000), orderedInterval (-37367290633 / 1000000000000) (-37367290632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (170959985257871 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41238308129 / 1000000000000) (41238308130 / 1000000000000), orderedInterval (35658737614 / 1000000000000) (35658737615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (49550867213229 / 160000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23301120398 / 1000000000000) (23301122792 / 1000000000000), orderedInterval (-38931160718 / 1000000000000) (-38931158323 / 1000000000000)))) (orderedInterval (11821005655 / 1000000000000) (11821006097 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate294_chunkChecks3_2 :
    compactCertificate294.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (137060306431063 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38213228883 / 1000000000000) (38213248980 / 1000000000000), orderedInterval (-47604728028 / 1000000000000) (-47604707931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (116187539662943 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (66066784823 / 1000000000000) (66066784840 / 1000000000000), orderedInterval (4079368178 / 1000000000000) (4079368195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (72704767560629 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-44372254392 / 1000000000000) (-44372254391 / 1000000000000), orderedInterval (-70721612877 / 1000000000000) (-70721612876 / 1000000000000)))) (orderedInterval (-7683918617 / 1000000000000) (-7683915121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (39100865799243 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-65056197915 / 1000000000000) (-65056179759 / 1000000000000), orderedInterval (94437030506 / 1000000000000) (94437048662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (106166456846729 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69239252852 / 1000000000000) (69239252881 / 1000000000000), orderedInterval (1481603628 / 1000000000000) (1481603657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (144961220374633 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13290091832 / 1000000000000) (-13290091725 / 1000000000000), orderedInterval (57800934665 / 1000000000000) (57800934772 / 1000000000000)))) (orderedInterval (5669722649 / 1000000000000) (5669722687 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (61295232439371 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82709700982 / 1000000000000) (82709707399 / 1000000000000), orderedInterval (-38852755000 / 1000000000000) (-38852748583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (249161716856491 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42449383994 / 1000000000000) (-42449383993 / 1000000000000), orderedInterval (-15490933212 / 1000000000000) (-15490933210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (166428479693669 / 800000000000) 3 (IntervalRat.scale (335 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (55066382262 / 1000000000000) (55066382280 / 1000000000000), orderedInterval (5143360609 / 1000000000000) (5143360627 / 1000000000000)))) (orderedInterval (-6258469169 / 1000000000000) (-6258469008 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate294_chunkChecks3 :
    compactCertificate294.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate294.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate294_chunkChecks3_0
    compactCertificate294_chunkChecks3_1 compactCertificate294_chunkChecks3_2

theorem compactCertificate294_chunkChecks4_0 :
    compactCertificate294.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (335 / 2) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-60302537029 / 1000000000000) (-60302536155 / 1000000000000), orderedInterval (12998104778 / 1000000000000) (12998105652 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (98703793509367 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-71649649978 / 1000000000000) (-71649649869 / 1000000000000), orderedInterval (5401726547 / 1000000000000) (5401726656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (31918778823511 / 160000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-39920636992 / 1000000000000) (-39920589918 / 1000000000000), orderedInterval (40069308617 / 1000000000000) (40069355691 / 1000000000000)))) (orderedInterval (-28699712439 / 1000000000000) (-28699706453 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (28801520775269 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-105410709644 / 1000000000000) (-105410664905 / 1000000000000), orderedInterval (82525963553 / 1000000000000) (82526008293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (77364936071393 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8172953617 / 1000000000000) (-8172953615 / 1000000000000), orderedInterval (-80681474624 / 1000000000000) (-80681474623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (210060851057181 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25010851329 / 1000000000000) (-25010848444 / 1000000000000), orderedInterval (42461951418 / 1000000000000) (42461954303 / 1000000000000)))) (orderedInterval (10560429579 / 1000000000000) (10560430902 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (154729872142853 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31520291302 / 1000000000000) (-31520284290 / 1000000000000), orderedInterval (48018852154 / 1000000000000) (48018859166 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (265132273202969 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-31697596948 / 1000000000000) (-31697564958 / 1000000000000), orderedInterval (30316194889 / 1000000000000) (30316226878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (195295232439371 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-7141207956 / 1000000000000) (-7141207937 / 1000000000000), orderedInterval (50579768067 / 1000000000000) (50579768086 / 1000000000000)))) (orderedInterval (14163650112 / 1000000000000) (14163665426 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate294_chunkChecks4_1 :
    compactCertificate294.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (299633108984933 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-41046267962 / 1000000000000) (-41046267899 / 1000000000000), orderedInterval (-3809638476 / 1000000000000) (-3809638413 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (172993256130557 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13765116621 / 1000000000000) (-13765116620 / 1000000000000), orderedInterval (-52451975730 / 1000000000000) (-52451975729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (306979568745313 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38459629378 / 1000000000000) (38459629381 / 1000000000000), orderedInterval (13362949128 / 1000000000000) (13362949130 / 1000000000000)))) (orderedInterval (330346499676 / 1000000000000) (330346501406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (286820133464197 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (38776967690 / 1000000000000) (38776967691 / 1000000000000), orderedInterval (16438595714 / 1000000000000) (16438595715 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (204688381041301 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-41010942441 / 1000000000000) (-41010867883 / 1000000000000), orderedInterval (28474750589 / 1000000000000) (28474825146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (232094808214179 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (44665496126 / 1000000000000) (44665501308 / 1000000000000), orderedInterval (-14195564230 / 1000000000000) (-14195559047 / 1000000000000)))) (orderedInterval (-37756940976 / 1000000000000) (-37756901895 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (193496453988851 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35076055725 / 1000000000000) (-35076055724 / 1000000000000), orderedInterval (-37367290633 / 1000000000000) (-37367290632 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (170959985257871 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (41238308129 / 1000000000000) (41238308130 / 1000000000000), orderedInterval (35658737614 / 1000000000000) (35658737615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (49550867213229 / 160000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23301120398 / 1000000000000) (23301122792 / 1000000000000), orderedInterval (-38931160718 / 1000000000000) (-38931158323 / 1000000000000)))) (orderedInterval (-1182812415 / 1000000000000) (-1182811609 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate294_chunkChecks4_2 :
    compactCertificate294.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (137060306431063 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38213228883 / 1000000000000) (38213248980 / 1000000000000), orderedInterval (-47604728028 / 1000000000000) (-47604707931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (116187539662943 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (66066784823 / 1000000000000) (66066784840 / 1000000000000), orderedInterval (4079368178 / 1000000000000) (4079368195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (72704767560629 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-44372254392 / 1000000000000) (-44372254391 / 1000000000000), orderedInterval (-70721612877 / 1000000000000) (-70721612876 / 1000000000000)))) (orderedInterval (-8834265904 / 1000000000000) (-8834262309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (39100865799243 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-65056197915 / 1000000000000) (-65056179759 / 1000000000000), orderedInterval (94437030506 / 1000000000000) (94437048662 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (106166456846729 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (69239252852 / 1000000000000) (69239252881 / 1000000000000), orderedInterval (1481603628 / 1000000000000) (1481603657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (144961220374633 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13290091832 / 1000000000000) (-13290091725 / 1000000000000), orderedInterval (57800934665 / 1000000000000) (57800934772 / 1000000000000)))) (orderedInterval (717021301 / 1000000000000) (717021335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (61295232439371 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (82709700982 / 1000000000000) (82709707399 / 1000000000000), orderedInterval (-38852755000 / 1000000000000) (-38852748583 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (249161716856491 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42449383994 / 1000000000000) (-42449383993 / 1000000000000), orderedInterval (-15490933212 / 1000000000000) (-15490933210 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (166428479693669 / 800000000000) 4 (IntervalRat.scale (335 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (55066382262 / 1000000000000) (55066382280 / 1000000000000), orderedInterval (5143360609 / 1000000000000) (5143360627 / 1000000000000)))) (orderedInterval (16817413247 / 1000000000000) (16817413496 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate294_chunkChecks4 :
    compactCertificate294.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate294.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate294_chunkChecks4_0
    compactCertificate294_chunkChecks4_1 compactCertificate294_chunkChecks4_2

theorem compactCertificate294_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate294.chunkCheck r b = true :=
  compactCertificate294.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate294_chunkChecks0
    · exact compactCertificate294_chunkChecks1
    · exact compactCertificate294_chunkChecks2
    · exact compactCertificate294_chunkChecks3
    · exact compactCertificate294_chunkChecks4)

theorem compactCertificate294_coefficient0 :
    compactCertificate294.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate294_coefficient1 :
    compactCertificate294.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate294_coefficient2 :
    compactCertificate294.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate294_coefficient3 :
    compactCertificate294.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate294_coefficient4 :
    compactCertificate294.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate294_coefficients : ∀ r : Fin 5,
    compactCertificate294.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate294_coefficient0
  · exact compactCertificate294_coefficient1
  · exact compactCertificate294_coefficient2
  · exact compactCertificate294_coefficient3
  · exact compactCertificate294_coefficient4

theorem compactCertificate294_lower : (1 : ℚ) ≤ compactCertificate294.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate294, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate294_proves {t : ℝ} (ht : t ∈ compactCertificate294.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate294.proves compactCertificate294_states compactCertificate294_chunks
    compactCertificate294_coefficients compactCertificate294_lower ht

end Erdos232
