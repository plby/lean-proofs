/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate340 : CompactCertificate where
  left := 212
  right := 213
  center := 425 / 2
  grid := fun i =>
    match i.val with
    | 0 => 68
    | 1 => 50
    | 2 => 81
    | 3 => 15
    | 4 => 39
    | 5 => 106
    | 6 => 78
    | 7 => 134
    | 8 => 99
    | 9 => 151
    | 10 => 87
    | 11 => 155
    | 12 => 145
    | 13 => 103
    | 14 => 117
    | 15 => 98
    | 16 => 86
    | 17 => 125
    | 18 => 69
    | 19 => 59
    | 20 => 37
    | 21 => 20
    | 22 => 54
    | 23 => 73
    | 24 => 31
    | 25 => 126
    | _ => 84
  point := fun i =>
    match i.val with
    | 0 => 425 / 2
    | 1 => 25044246114317 / 160000000000
    | 2 => 8098794626861 / 32000000000
    | 3 => 7307848554919 / 160000000000
    | 4 => 19629909152443 / 160000000000
    | 5 => 53299021910031 / 160000000000
    | 6 => 39259818304903 / 160000000000
    | 7 => 67272367827619 / 160000000000
    | 8 => 49552521663721 / 160000000000
    | 9 => 76026311234983 / 160000000000
    | 10 => 43893811257007 / 160000000000
    | 11 => 77890338338363 / 160000000000
    | 12 => 72775257744647 / 160000000000
    | 13 => 51935857876151 / 160000000000
    | 14 => 58889727457329 / 160000000000
    | 15 => 49096115191201 / 160000000000
    | 16 => 43377906707221 / 160000000000
    | 17 => 12572608098879 / 32000000000
    | 18 => 34776495661613 / 160000000000
    | 19 => 29480420511493 / 160000000000
    | 20 => 18447478336279 / 160000000000
    | 21 => 9921115202793 / 160000000000
    | 22 => 26937757707379 / 160000000000
    | 23 => 36781205169683 / 160000000000
    | 24 => 15552521663721 / 160000000000
    | 25 => 63220137112841 / 160000000000
    | _ => 42228121713319 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-18433203048 / 1000000000000) (-18433202631 / 1000000000000), orderedInterval (51580554449 / 1000000000000) (51580554865 / 1000000000000))
    | 1 => (orderedInterval (14632526454 / 1000000000000) (14632526455 / 1000000000000), orderedInterval (62026409685 / 1000000000000) (62026409686 / 1000000000000))
    | 2 => (orderedInterval (28185092934 / 1000000000000) (28185098942 / 1000000000000), orderedInterval (-41540834005 / 1000000000000) (-41540827997 / 1000000000000))
    | 3 => (orderedInterval (73050043162 / 1000000000000) (73050075530 / 1000000000000), orderedInterval (-93547699745 / 1000000000000) (-93547667378 / 1000000000000))
    | 4 => (orderedInterval (-58560163644 / 1000000000000) (-58560163643 / 1000000000000), orderedInterval (-41709782196 / 1000000000000) (-41709782195 / 1000000000000))
    | 5 => (orderedInterval (34110024352 / 1000000000000) (34110024353 / 1000000000000), orderedInterval (27290977723 / 1000000000000) (27290977724 / 1000000000000))
    | 6 => (orderedInterval (45725420531 / 1000000000000) (45725420532 / 1000000000000), orderedInterval (22349453167 / 1000000000000) (22349453168 / 1000000000000))
    | 7 => (orderedInterval (10153214410 / 1000000000000) (10153214411 / 1000000000000), orderedInterval (37551790863 / 1000000000000) (37551790864 / 1000000000000))
    | 8 => (orderedInterval (22897328274 / 1000000000000) (22897330407 / 1000000000000), orderedInterval (-39168712163 / 1000000000000) (-39168710030 / 1000000000000))
    | 9 => (orderedInterval (-36603055724 / 1000000000000) (-36603055284 / 1000000000000), orderedInterval (-23954711 / 1000000000000) (-23954270 / 1000000000000))
    | 10 => (orderedInterval (-46882808562 / 1000000000000) (-46882806439 / 1000000000000), orderedInterval (11157047223 / 1000000000000) (11157049347 / 1000000000000))
    | 11 => (orderedInterval (-21968279992 / 1000000000000) (-21968279991 / 1000000000000), orderedInterval (-28702340961 / 1000000000000) (-28702340960 / 1000000000000))
    | 12 => (orderedInterval (-3718172057 / 1000000000000) (-3718172056 / 1000000000000), orderedInterval (-37222463059 / 1000000000000) (-37222463058 / 1000000000000))
    | 13 => (orderedInterval (-43126966193 / 1000000000000) (-43126963457 / 1000000000000), orderedInterval (10131820220 / 1000000000000) (10131822956 / 1000000000000))
    | 14 => (orderedInterval (-39837276909 / 1000000000000) (-39837276906 / 1000000000000), orderedInterval (-11889471200 / 1000000000000) (-11889471197 / 1000000000000))
    | 15 => (orderedInterval (-10843389484 / 1000000000000) (-10843389431 / 1000000000000), orderedInterval (44256929759 / 1000000000000) (44256929812 / 1000000000000))
    | 16 => (orderedInterval (47920431345 / 1000000000000) (47920432138 / 1000000000000), orderedInterval (-7286232125 / 1000000000000) (-7286231332 / 1000000000000))
    | 17 => (orderedInterval (-33430344826 / 1000000000000) (-33430344825 / 1000000000000), orderedInterval (-22379459174 / 1000000000000) (-22379459173 / 1000000000000))
    | 18 => (orderedInterval (-53011084715 / 1000000000000) (-53011084712 / 1000000000000), orderedInterval (-10776837796 / 1000000000000) (-10776837792 / 1000000000000))
    | 19 => (orderedInterval (18301567981 / 1000000000000) (18301568336 / 1000000000000), orderedInterval (-55908495852 / 1000000000000) (-55908495498 / 1000000000000))
    | 20 => (orderedInterval (11682505671 / 1000000000000) (11682505736 / 1000000000000), orderedInterval (-73434208696 / 1000000000000) (-73434208631 / 1000000000000))
    | 21 => (orderedInterval (-4203795911 / 1000000000000) (-4203795894 / 1000000000000), orderedInterval (101274041968 / 1000000000000) (101274041984 / 1000000000000))
    | 22 => (orderedInterval (-29500347880 / 1000000000000) (-29500344479 / 1000000000000), orderedInterval (54041449724 / 1000000000000) (54041453125 / 1000000000000))
    | 23 => (orderedInterval (-51120091768 / 1000000000000) (-51120091765 / 1000000000000), orderedInterval (-12381084120 / 1000000000000) (-12381084117 / 1000000000000))
    | 24 => (orderedInterval (-45561522978 / 1000000000000) (-45561522977 / 1000000000000), orderedInterval (-66650214710 / 1000000000000) (-66650214709 / 1000000000000))
    | 25 => (orderedInterval (2818059538 / 1000000000000) (2818059539 / 1000000000000), orderedInterval (40036939477 / 1000000000000) (40036939478 / 1000000000000))
    | _ => (orderedInterval (35804994637 / 1000000000000) (35804994638 / 1000000000000), orderedInterval (33549410210 / 1000000000000) (33549410211 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-5515996261 / 1000000000000) (-5515995728 / 1000000000000)
      | 1 => orderedInterval (-5355544747 / 1000000000000) (-5355544369 / 1000000000000)
      | 2 => orderedInterval (240217486 / 1000000000000) (240217550 / 1000000000000)
      | 3 => orderedInterval (-92629817 / 1000000000000) (-92629497 / 1000000000000)
      | 4 => orderedInterval (-3809485491 / 1000000000000) (-3809485206 / 1000000000000)
      | 5 => orderedInterval (-3723491863 / 1000000000000) (-3723491796 / 1000000000000)
      | 6 => orderedInterval (7820530936 / 1000000000000) (7820531013 / 1000000000000)
      | 7 => orderedInterval (4664679881 / 1000000000000) (4664679985 / 1000000000000)
      | _ => orderedInterval (-7222021682 / 1000000000000) (-7222021622 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (17967197794 / 1000000000000) (17967198397 / 1000000000000)
      | 1 => orderedInterval (-3702445507 / 1000000000000) (-3702445402 / 1000000000000)
      | 2 => orderedInterval (-3671352310 / 1000000000000) (-3671352214 / 1000000000000)
      | 3 => orderedInterval (-8270602460 / 1000000000000) (-8270601906 / 1000000000000)
      | 4 => orderedInterval (3006065422 / 1000000000000) (3006065859 / 1000000000000)
      | 5 => orderedInterval (210521813 / 1000000000000) (210521902 / 1000000000000)
      | 6 => orderedInterval (3209151004 / 1000000000000) (3209151073 / 1000000000000)
      | 7 => orderedInterval (-490550364 / 1000000000000) (-490550279 / 1000000000000)
      | _ => orderedInterval (-14061884149 / 1000000000000) (-14061884065 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (4801676176 / 1000000000000) (4801676864 / 1000000000000)
      | 1 => orderedInterval (6725687941 / 1000000000000) (6725687999 / 1000000000000)
      | 2 => orderedInterval (67837189 / 1000000000000) (67837337 / 1000000000000)
      | 3 => orderedInterval (-10301629236 / 1000000000000) (-10301628206 / 1000000000000)
      | 4 => orderedInterval (8589344486 / 1000000000000) (8589345161 / 1000000000000)
      | 5 => orderedInterval (7649882971 / 1000000000000) (7649883091 / 1000000000000)
      | 6 => orderedInterval (-8215933841 / 1000000000000) (-8215933777 / 1000000000000)
      | 7 => orderedInterval (-5009366345 / 1000000000000) (-5009366272 / 1000000000000)
      | _ => orderedInterval (11279713352 / 1000000000000) (11279713475 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16579706027 / 1000000000000) (-16579705241 / 1000000000000)
      | 1 => orderedInterval (7725156042 / 1000000000000) (7725156107 / 1000000000000)
      | 2 => orderedInterval (11901794711 / 1000000000000) (11901794939 / 1000000000000)
      | 3 => orderedInterval (47278507773 / 1000000000000) (47278509813 / 1000000000000)
      | 4 => orderedInterval (-10357639940 / 1000000000000) (-10357638899 / 1000000000000)
      | 5 => orderedInterval (1180951922 / 1000000000000) (1180952087 / 1000000000000)
      | 6 => orderedInterval (-3486130771 / 1000000000000) (-3486130711 / 1000000000000)
      | 7 => orderedInterval (-521522474 / 1000000000000) (-521522411 / 1000000000000)
      | _ => orderedInterval (32997016734 / 1000000000000) (32997016924 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-3782137917 / 1000000000000) (-3782137009 / 1000000000000)
      | 1 => orderedInterval (-14955480068 / 1000000000000) (-14955479973 / 1000000000000)
      | 2 => orderedInterval (-2414879246 / 1000000000000) (-2414878887 / 1000000000000)
      | 3 => orderedInterval (66487775627 / 1000000000000) (66487779855 / 1000000000000)
      | 4 => orderedInterval (-18882550399 / 1000000000000) (-18882548781 / 1000000000000)
      | 5 => orderedInterval (-17823689511 / 1000000000000) (-17823689279 / 1000000000000)
      | 6 => orderedInterval (8757406580 / 1000000000000) (8757406638 / 1000000000000)
      | 7 => orderedInterval (5634804028 / 1000000000000) (5634804084 / 1000000000000)
      | _ => orderedInterval (-19050088190 / 1000000000000) (-19050087886 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-12993741558 / 1000000000000) (-12993739670 / 1000000000000)
    | 1 => orderedInterval (-5803898757 / 1000000000000) (-5803896635 / 1000000000000)
    | 2 => orderedInterval (15587212693 / 1000000000000) (15587215672 / 1000000000000)
    | 3 => orderedInterval (70138427970 / 1000000000000) (70138432608 / 1000000000000)
    | _ => orderedInterval (3971160904 / 1000000000000) (3971168762 / 1000000000000)

theorem compactCertificate340_stateChecks0 :
    compactCertificate340.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (425 / 2)) (orderedInterval (-18433203048 / 1000000000000) (-18433202631 / 1000000000000), orderedInterval (51580554449 / 1000000000000) (51580554865 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (25044246114317 / 160000000000)) (orderedInterval (14632526454 / 1000000000000) (14632526455 / 1000000000000), orderedInterval (62026409685 / 1000000000000) (62026409686 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (8098794626861 / 32000000000)) (orderedInterval (28185092934 / 1000000000000) (28185098942 / 1000000000000), orderedInterval (-41540834005 / 1000000000000) (-41540827997 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_stateChecks1 :
    compactCertificate340.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (7307848554919 / 160000000000)) (orderedInterval (73050043162 / 1000000000000) (73050075530 / 1000000000000), orderedInterval (-93547699745 / 1000000000000) (-93547667378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (19629909152443 / 160000000000)) (orderedInterval (-58560163644 / 1000000000000) (-58560163643 / 1000000000000), orderedInterval (-41709782196 / 1000000000000) (-41709782195 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (53299021910031 / 160000000000)) (orderedInterval (34110024352 / 1000000000000) (34110024353 / 1000000000000), orderedInterval (27290977723 / 1000000000000) (27290977724 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_stateChecks2 :
    compactCertificate340.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (39259818304903 / 160000000000)) (orderedInterval (45725420531 / 1000000000000) (45725420532 / 1000000000000), orderedInterval (22349453167 / 1000000000000) (22349453168 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (67272367827619 / 160000000000)) (orderedInterval (10153214410 / 1000000000000) (10153214411 / 1000000000000), orderedInterval (37551790863 / 1000000000000) (37551790864 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (49552521663721 / 160000000000)) (orderedInterval (22897328274 / 1000000000000) (22897330407 / 1000000000000), orderedInterval (-39168712163 / 1000000000000) (-39168710030 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_stateChecks3 :
    compactCertificate340.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (76026311234983 / 160000000000)) (orderedInterval (-36603055724 / 1000000000000) (-36603055284 / 1000000000000), orderedInterval (-23954711 / 1000000000000) (-23954270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (43893811257007 / 160000000000)) (orderedInterval (-46882808562 / 1000000000000) (-46882806439 / 1000000000000), orderedInterval (11157047223 / 1000000000000) (11157049347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (77890338338363 / 160000000000)) (orderedInterval (-21968279992 / 1000000000000) (-21968279991 / 1000000000000), orderedInterval (-28702340961 / 1000000000000) (-28702340960 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_stateChecks4 :
    compactCertificate340.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (72775257744647 / 160000000000)) (orderedInterval (-3718172057 / 1000000000000) (-3718172056 / 1000000000000), orderedInterval (-37222463059 / 1000000000000) (-37222463058 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (51935857876151 / 160000000000)) (orderedInterval (-43126966193 / 1000000000000) (-43126963457 / 1000000000000), orderedInterval (10131820220 / 1000000000000) (10131822956 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (58889727457329 / 160000000000)) (orderedInterval (-39837276909 / 1000000000000) (-39837276906 / 1000000000000), orderedInterval (-11889471200 / 1000000000000) (-11889471197 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_stateChecks5 :
    compactCertificate340.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (49096115191201 / 160000000000)) (orderedInterval (-10843389484 / 1000000000000) (-10843389431 / 1000000000000), orderedInterval (44256929759 / 1000000000000) (44256929812 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (43377906707221 / 160000000000)) (orderedInterval (47920431345 / 1000000000000) (47920432138 / 1000000000000), orderedInterval (-7286232125 / 1000000000000) (-7286231332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (12572608098879 / 32000000000)) (orderedInterval (-33430344826 / 1000000000000) (-33430344825 / 1000000000000), orderedInterval (-22379459174 / 1000000000000) (-22379459173 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_stateChecks6 :
    compactCertificate340.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (34776495661613 / 160000000000)) (orderedInterval (-53011084715 / 1000000000000) (-53011084712 / 1000000000000), orderedInterval (-10776837796 / 1000000000000) (-10776837792 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (29480420511493 / 160000000000)) (orderedInterval (18301567981 / 1000000000000) (18301568336 / 1000000000000), orderedInterval (-55908495852 / 1000000000000) (-55908495498 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (18447478336279 / 160000000000)) (orderedInterval (11682505671 / 1000000000000) (11682505736 / 1000000000000), orderedInterval (-73434208696 / 1000000000000) (-73434208631 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_stateChecks7 :
    compactCertificate340.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (9921115202793 / 160000000000)) (orderedInterval (-4203795911 / 1000000000000) (-4203795894 / 1000000000000), orderedInterval (101274041968 / 1000000000000) (101274041984 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (26937757707379 / 160000000000)) (orderedInterval (-29500347880 / 1000000000000) (-29500344479 / 1000000000000), orderedInterval (54041449724 / 1000000000000) (54041453125 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (36781205169683 / 160000000000)) (orderedInterval (-51120091768 / 1000000000000) (-51120091765 / 1000000000000), orderedInterval (-12381084120 / 1000000000000) (-12381084117 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_stateChecks8 :
    compactCertificate340.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (15552521663721 / 160000000000)) (orderedInterval (-45561522978 / 1000000000000) (-45561522977 / 1000000000000), orderedInterval (-66650214710 / 1000000000000) (-66650214709 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (63220137112841 / 160000000000)) (orderedInterval (2818059538 / 1000000000000) (2818059539 / 1000000000000), orderedInterval (40036939477 / 1000000000000) (40036939478 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (42228121713319 / 160000000000)) (orderedInterval (35804994637 / 1000000000000) (35804994638 / 1000000000000), orderedInterval (33549410210 / 1000000000000) (33549410211 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_states : ∀ j,
    BesselStateValid (compactCertificate340.point j) (compactCertificate340.state j) :=
  compactCertificate340.statesValid_of_checks3 compactCertificate340_stateChecks0
    compactCertificate340_stateChecks1 compactCertificate340_stateChecks2
    compactCertificate340_stateChecks3 compactCertificate340_stateChecks4
    compactCertificate340_stateChecks5 compactCertificate340_stateChecks6
    compactCertificate340_stateChecks7 compactCertificate340_stateChecks8

theorem compactCertificate340_chunkChecks0_0 :
    compactCertificate340.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (425 / 2) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18433203048 / 1000000000000) (-18433202631 / 1000000000000), orderedInterval (51580554449 / 1000000000000) (51580554865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (25044246114317 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (14632526454 / 1000000000000) (14632526455 / 1000000000000), orderedInterval (62026409685 / 1000000000000) (62026409686 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (8098794626861 / 32000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28185092934 / 1000000000000) (28185098942 / 1000000000000), orderedInterval (-41540834005 / 1000000000000) (-41540827997 / 1000000000000)))) (orderedInterval (-5515996261 / 1000000000000) (-5515995728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (7307848554919 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73050043162 / 1000000000000) (73050075530 / 1000000000000), orderedInterval (-93547699745 / 1000000000000) (-93547667378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (19629909152443 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58560163644 / 1000000000000) (-58560163643 / 1000000000000), orderedInterval (-41709782196 / 1000000000000) (-41709782195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (53299021910031 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (34110024352 / 1000000000000) (34110024353 / 1000000000000), orderedInterval (27290977723 / 1000000000000) (27290977724 / 1000000000000)))) (orderedInterval (-5355544747 / 1000000000000) (-5355544369 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (39259818304903 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45725420531 / 1000000000000) (45725420532 / 1000000000000), orderedInterval (22349453167 / 1000000000000) (22349453168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (67272367827619 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10153214410 / 1000000000000) (10153214411 / 1000000000000), orderedInterval (37551790863 / 1000000000000) (37551790864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (49552521663721 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22897328274 / 1000000000000) (22897330407 / 1000000000000), orderedInterval (-39168712163 / 1000000000000) (-39168710030 / 1000000000000)))) (orderedInterval (240217486 / 1000000000000) (240217550 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_chunkChecks0_1 :
    compactCertificate340.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (76026311234983 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36603055724 / 1000000000000) (-36603055284 / 1000000000000), orderedInterval (-23954711 / 1000000000000) (-23954270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (43893811257007 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-46882808562 / 1000000000000) (-46882806439 / 1000000000000), orderedInterval (11157047223 / 1000000000000) (11157049347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (77890338338363 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21968279992 / 1000000000000) (-21968279991 / 1000000000000), orderedInterval (-28702340961 / 1000000000000) (-28702340960 / 1000000000000)))) (orderedInterval (-92629817 / 1000000000000) (-92629497 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (72775257744647 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3718172057 / 1000000000000) (-3718172056 / 1000000000000), orderedInterval (-37222463059 / 1000000000000) (-37222463058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (51935857876151 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43126966193 / 1000000000000) (-43126963457 / 1000000000000), orderedInterval (10131820220 / 1000000000000) (10131822956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (58889727457329 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-39837276909 / 1000000000000) (-39837276906 / 1000000000000), orderedInterval (-11889471200 / 1000000000000) (-11889471197 / 1000000000000)))) (orderedInterval (-3809485491 / 1000000000000) (-3809485206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (49096115191201 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10843389484 / 1000000000000) (-10843389431 / 1000000000000), orderedInterval (44256929759 / 1000000000000) (44256929812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (43377906707221 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (47920431345 / 1000000000000) (47920432138 / 1000000000000), orderedInterval (-7286232125 / 1000000000000) (-7286231332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (12572608098879 / 32000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33430344826 / 1000000000000) (-33430344825 / 1000000000000), orderedInterval (-22379459174 / 1000000000000) (-22379459173 / 1000000000000)))) (orderedInterval (-3723491863 / 1000000000000) (-3723491796 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_chunkChecks0_2 :
    compactCertificate340.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (34776495661613 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53011084715 / 1000000000000) (-53011084712 / 1000000000000), orderedInterval (-10776837796 / 1000000000000) (-10776837792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (29480420511493 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (18301567981 / 1000000000000) (18301568336 / 1000000000000), orderedInterval (-55908495852 / 1000000000000) (-55908495498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (18447478336279 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11682505671 / 1000000000000) (11682505736 / 1000000000000), orderedInterval (-73434208696 / 1000000000000) (-73434208631 / 1000000000000)))) (orderedInterval (7820530936 / 1000000000000) (7820531013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (9921115202793 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4203795911 / 1000000000000) (-4203795894 / 1000000000000), orderedInterval (101274041968 / 1000000000000) (101274041984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (26937757707379 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-29500347880 / 1000000000000) (-29500344479 / 1000000000000), orderedInterval (54041449724 / 1000000000000) (54041453125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (36781205169683 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51120091768 / 1000000000000) (-51120091765 / 1000000000000), orderedInterval (-12381084120 / 1000000000000) (-12381084117 / 1000000000000)))) (orderedInterval (4664679881 / 1000000000000) (4664679985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (15552521663721 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45561522978 / 1000000000000) (-45561522977 / 1000000000000), orderedInterval (-66650214710 / 1000000000000) (-66650214709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (63220137112841 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2818059538 / 1000000000000) (2818059539 / 1000000000000), orderedInterval (40036939477 / 1000000000000) (40036939478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (42228121713319 / 160000000000) 0 (IntervalRat.scale (425 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35804994637 / 1000000000000) (35804994638 / 1000000000000), orderedInterval (33549410210 / 1000000000000) (33549410211 / 1000000000000)))) (orderedInterval (-7222021682 / 1000000000000) (-7222021622 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_chunkChecks0 :
    compactCertificate340.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate340.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate340_chunkChecks0_0
    compactCertificate340_chunkChecks0_1 compactCertificate340_chunkChecks0_2

theorem compactCertificate340_chunkChecks1_0 :
    compactCertificate340.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (425 / 2) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18433203048 / 1000000000000) (-18433202631 / 1000000000000), orderedInterval (51580554449 / 1000000000000) (51580554865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (25044246114317 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (14632526454 / 1000000000000) (14632526455 / 1000000000000), orderedInterval (62026409685 / 1000000000000) (62026409686 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (8098794626861 / 32000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28185092934 / 1000000000000) (28185098942 / 1000000000000), orderedInterval (-41540834005 / 1000000000000) (-41540827997 / 1000000000000)))) (orderedInterval (17967197794 / 1000000000000) (17967198397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (7307848554919 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73050043162 / 1000000000000) (73050075530 / 1000000000000), orderedInterval (-93547699745 / 1000000000000) (-93547667378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (19629909152443 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58560163644 / 1000000000000) (-58560163643 / 1000000000000), orderedInterval (-41709782196 / 1000000000000) (-41709782195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (53299021910031 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (34110024352 / 1000000000000) (34110024353 / 1000000000000), orderedInterval (27290977723 / 1000000000000) (27290977724 / 1000000000000)))) (orderedInterval (-3702445507 / 1000000000000) (-3702445402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (39259818304903 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45725420531 / 1000000000000) (45725420532 / 1000000000000), orderedInterval (22349453167 / 1000000000000) (22349453168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (67272367827619 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10153214410 / 1000000000000) (10153214411 / 1000000000000), orderedInterval (37551790863 / 1000000000000) (37551790864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (49552521663721 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22897328274 / 1000000000000) (22897330407 / 1000000000000), orderedInterval (-39168712163 / 1000000000000) (-39168710030 / 1000000000000)))) (orderedInterval (-3671352310 / 1000000000000) (-3671352214 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_chunkChecks1_1 :
    compactCertificate340.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (76026311234983 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36603055724 / 1000000000000) (-36603055284 / 1000000000000), orderedInterval (-23954711 / 1000000000000) (-23954270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (43893811257007 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-46882808562 / 1000000000000) (-46882806439 / 1000000000000), orderedInterval (11157047223 / 1000000000000) (11157049347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (77890338338363 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21968279992 / 1000000000000) (-21968279991 / 1000000000000), orderedInterval (-28702340961 / 1000000000000) (-28702340960 / 1000000000000)))) (orderedInterval (-8270602460 / 1000000000000) (-8270601906 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (72775257744647 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3718172057 / 1000000000000) (-3718172056 / 1000000000000), orderedInterval (-37222463059 / 1000000000000) (-37222463058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (51935857876151 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43126966193 / 1000000000000) (-43126963457 / 1000000000000), orderedInterval (10131820220 / 1000000000000) (10131822956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (58889727457329 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-39837276909 / 1000000000000) (-39837276906 / 1000000000000), orderedInterval (-11889471200 / 1000000000000) (-11889471197 / 1000000000000)))) (orderedInterval (3006065422 / 1000000000000) (3006065859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (49096115191201 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10843389484 / 1000000000000) (-10843389431 / 1000000000000), orderedInterval (44256929759 / 1000000000000) (44256929812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (43377906707221 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (47920431345 / 1000000000000) (47920432138 / 1000000000000), orderedInterval (-7286232125 / 1000000000000) (-7286231332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (12572608098879 / 32000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33430344826 / 1000000000000) (-33430344825 / 1000000000000), orderedInterval (-22379459174 / 1000000000000) (-22379459173 / 1000000000000)))) (orderedInterval (210521813 / 1000000000000) (210521902 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_chunkChecks1_2 :
    compactCertificate340.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (34776495661613 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53011084715 / 1000000000000) (-53011084712 / 1000000000000), orderedInterval (-10776837796 / 1000000000000) (-10776837792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (29480420511493 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (18301567981 / 1000000000000) (18301568336 / 1000000000000), orderedInterval (-55908495852 / 1000000000000) (-55908495498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (18447478336279 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11682505671 / 1000000000000) (11682505736 / 1000000000000), orderedInterval (-73434208696 / 1000000000000) (-73434208631 / 1000000000000)))) (orderedInterval (3209151004 / 1000000000000) (3209151073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (9921115202793 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4203795911 / 1000000000000) (-4203795894 / 1000000000000), orderedInterval (101274041968 / 1000000000000) (101274041984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (26937757707379 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-29500347880 / 1000000000000) (-29500344479 / 1000000000000), orderedInterval (54041449724 / 1000000000000) (54041453125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (36781205169683 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51120091768 / 1000000000000) (-51120091765 / 1000000000000), orderedInterval (-12381084120 / 1000000000000) (-12381084117 / 1000000000000)))) (orderedInterval (-490550364 / 1000000000000) (-490550279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (15552521663721 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45561522978 / 1000000000000) (-45561522977 / 1000000000000), orderedInterval (-66650214710 / 1000000000000) (-66650214709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (63220137112841 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2818059538 / 1000000000000) (2818059539 / 1000000000000), orderedInterval (40036939477 / 1000000000000) (40036939478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (42228121713319 / 160000000000) 1 (IntervalRat.scale (425 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35804994637 / 1000000000000) (35804994638 / 1000000000000), orderedInterval (33549410210 / 1000000000000) (33549410211 / 1000000000000)))) (orderedInterval (-14061884149 / 1000000000000) (-14061884065 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_chunkChecks1 :
    compactCertificate340.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate340.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate340_chunkChecks1_0
    compactCertificate340_chunkChecks1_1 compactCertificate340_chunkChecks1_2

theorem compactCertificate340_chunkChecks2_0 :
    compactCertificate340.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (425 / 2) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18433203048 / 1000000000000) (-18433202631 / 1000000000000), orderedInterval (51580554449 / 1000000000000) (51580554865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (25044246114317 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (14632526454 / 1000000000000) (14632526455 / 1000000000000), orderedInterval (62026409685 / 1000000000000) (62026409686 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (8098794626861 / 32000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28185092934 / 1000000000000) (28185098942 / 1000000000000), orderedInterval (-41540834005 / 1000000000000) (-41540827997 / 1000000000000)))) (orderedInterval (4801676176 / 1000000000000) (4801676864 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (7307848554919 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73050043162 / 1000000000000) (73050075530 / 1000000000000), orderedInterval (-93547699745 / 1000000000000) (-93547667378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (19629909152443 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58560163644 / 1000000000000) (-58560163643 / 1000000000000), orderedInterval (-41709782196 / 1000000000000) (-41709782195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (53299021910031 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (34110024352 / 1000000000000) (34110024353 / 1000000000000), orderedInterval (27290977723 / 1000000000000) (27290977724 / 1000000000000)))) (orderedInterval (6725687941 / 1000000000000) (6725687999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (39259818304903 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45725420531 / 1000000000000) (45725420532 / 1000000000000), orderedInterval (22349453167 / 1000000000000) (22349453168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (67272367827619 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10153214410 / 1000000000000) (10153214411 / 1000000000000), orderedInterval (37551790863 / 1000000000000) (37551790864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (49552521663721 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22897328274 / 1000000000000) (22897330407 / 1000000000000), orderedInterval (-39168712163 / 1000000000000) (-39168710030 / 1000000000000)))) (orderedInterval (67837189 / 1000000000000) (67837337 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_chunkChecks2_1 :
    compactCertificate340.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (76026311234983 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36603055724 / 1000000000000) (-36603055284 / 1000000000000), orderedInterval (-23954711 / 1000000000000) (-23954270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (43893811257007 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-46882808562 / 1000000000000) (-46882806439 / 1000000000000), orderedInterval (11157047223 / 1000000000000) (11157049347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (77890338338363 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21968279992 / 1000000000000) (-21968279991 / 1000000000000), orderedInterval (-28702340961 / 1000000000000) (-28702340960 / 1000000000000)))) (orderedInterval (-10301629236 / 1000000000000) (-10301628206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (72775257744647 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3718172057 / 1000000000000) (-3718172056 / 1000000000000), orderedInterval (-37222463059 / 1000000000000) (-37222463058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (51935857876151 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43126966193 / 1000000000000) (-43126963457 / 1000000000000), orderedInterval (10131820220 / 1000000000000) (10131822956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (58889727457329 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-39837276909 / 1000000000000) (-39837276906 / 1000000000000), orderedInterval (-11889471200 / 1000000000000) (-11889471197 / 1000000000000)))) (orderedInterval (8589344486 / 1000000000000) (8589345161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (49096115191201 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10843389484 / 1000000000000) (-10843389431 / 1000000000000), orderedInterval (44256929759 / 1000000000000) (44256929812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (43377906707221 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (47920431345 / 1000000000000) (47920432138 / 1000000000000), orderedInterval (-7286232125 / 1000000000000) (-7286231332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (12572608098879 / 32000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33430344826 / 1000000000000) (-33430344825 / 1000000000000), orderedInterval (-22379459174 / 1000000000000) (-22379459173 / 1000000000000)))) (orderedInterval (7649882971 / 1000000000000) (7649883091 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_chunkChecks2_2 :
    compactCertificate340.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (34776495661613 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53011084715 / 1000000000000) (-53011084712 / 1000000000000), orderedInterval (-10776837796 / 1000000000000) (-10776837792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (29480420511493 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (18301567981 / 1000000000000) (18301568336 / 1000000000000), orderedInterval (-55908495852 / 1000000000000) (-55908495498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (18447478336279 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11682505671 / 1000000000000) (11682505736 / 1000000000000), orderedInterval (-73434208696 / 1000000000000) (-73434208631 / 1000000000000)))) (orderedInterval (-8215933841 / 1000000000000) (-8215933777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (9921115202793 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4203795911 / 1000000000000) (-4203795894 / 1000000000000), orderedInterval (101274041968 / 1000000000000) (101274041984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (26937757707379 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-29500347880 / 1000000000000) (-29500344479 / 1000000000000), orderedInterval (54041449724 / 1000000000000) (54041453125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (36781205169683 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51120091768 / 1000000000000) (-51120091765 / 1000000000000), orderedInterval (-12381084120 / 1000000000000) (-12381084117 / 1000000000000)))) (orderedInterval (-5009366345 / 1000000000000) (-5009366272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (15552521663721 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45561522978 / 1000000000000) (-45561522977 / 1000000000000), orderedInterval (-66650214710 / 1000000000000) (-66650214709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (63220137112841 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2818059538 / 1000000000000) (2818059539 / 1000000000000), orderedInterval (40036939477 / 1000000000000) (40036939478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (42228121713319 / 160000000000) 2 (IntervalRat.scale (425 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35804994637 / 1000000000000) (35804994638 / 1000000000000), orderedInterval (33549410210 / 1000000000000) (33549410211 / 1000000000000)))) (orderedInterval (11279713352 / 1000000000000) (11279713475 / 1000000000000))) = true
  rfl'

theorem compactCertificate340_chunkChecks2 :
    compactCertificate340.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate340.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate340_chunkChecks2_0
    compactCertificate340_chunkChecks2_1 compactCertificate340_chunkChecks2_2

theorem compactCertificate340_chunkChecks3_0 :
    compactCertificate340.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (425 / 2) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18433203048 / 1000000000000) (-18433202631 / 1000000000000), orderedInterval (51580554449 / 1000000000000) (51580554865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (25044246114317 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (14632526454 / 1000000000000) (14632526455 / 1000000000000), orderedInterval (62026409685 / 1000000000000) (62026409686 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (8098794626861 / 32000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28185092934 / 1000000000000) (28185098942 / 1000000000000), orderedInterval (-41540834005 / 1000000000000) (-41540827997 / 1000000000000)))) (orderedInterval (-16579706027 / 1000000000000) (-16579705241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (7307848554919 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73050043162 / 1000000000000) (73050075530 / 1000000000000), orderedInterval (-93547699745 / 1000000000000) (-93547667378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (19629909152443 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58560163644 / 1000000000000) (-58560163643 / 1000000000000), orderedInterval (-41709782196 / 1000000000000) (-41709782195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (53299021910031 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (34110024352 / 1000000000000) (34110024353 / 1000000000000), orderedInterval (27290977723 / 1000000000000) (27290977724 / 1000000000000)))) (orderedInterval (7725156042 / 1000000000000) (7725156107 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (39259818304903 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45725420531 / 1000000000000) (45725420532 / 1000000000000), orderedInterval (22349453167 / 1000000000000) (22349453168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (67272367827619 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10153214410 / 1000000000000) (10153214411 / 1000000000000), orderedInterval (37551790863 / 1000000000000) (37551790864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (49552521663721 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22897328274 / 1000000000000) (22897330407 / 1000000000000), orderedInterval (-39168712163 / 1000000000000) (-39168710030 / 1000000000000)))) (orderedInterval (11901794711 / 1000000000000) (11901794939 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate340_chunkChecks3_1 :
    compactCertificate340.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (76026311234983 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36603055724 / 1000000000000) (-36603055284 / 1000000000000), orderedInterval (-23954711 / 1000000000000) (-23954270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (43893811257007 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-46882808562 / 1000000000000) (-46882806439 / 1000000000000), orderedInterval (11157047223 / 1000000000000) (11157049347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (77890338338363 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21968279992 / 1000000000000) (-21968279991 / 1000000000000), orderedInterval (-28702340961 / 1000000000000) (-28702340960 / 1000000000000)))) (orderedInterval (47278507773 / 1000000000000) (47278509813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (72775257744647 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3718172057 / 1000000000000) (-3718172056 / 1000000000000), orderedInterval (-37222463059 / 1000000000000) (-37222463058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (51935857876151 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43126966193 / 1000000000000) (-43126963457 / 1000000000000), orderedInterval (10131820220 / 1000000000000) (10131822956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (58889727457329 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-39837276909 / 1000000000000) (-39837276906 / 1000000000000), orderedInterval (-11889471200 / 1000000000000) (-11889471197 / 1000000000000)))) (orderedInterval (-10357639940 / 1000000000000) (-10357638899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (49096115191201 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10843389484 / 1000000000000) (-10843389431 / 1000000000000), orderedInterval (44256929759 / 1000000000000) (44256929812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (43377906707221 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (47920431345 / 1000000000000) (47920432138 / 1000000000000), orderedInterval (-7286232125 / 1000000000000) (-7286231332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (12572608098879 / 32000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33430344826 / 1000000000000) (-33430344825 / 1000000000000), orderedInterval (-22379459174 / 1000000000000) (-22379459173 / 1000000000000)))) (orderedInterval (1180951922 / 1000000000000) (1180952087 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate340_chunkChecks3_2 :
    compactCertificate340.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (34776495661613 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53011084715 / 1000000000000) (-53011084712 / 1000000000000), orderedInterval (-10776837796 / 1000000000000) (-10776837792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (29480420511493 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (18301567981 / 1000000000000) (18301568336 / 1000000000000), orderedInterval (-55908495852 / 1000000000000) (-55908495498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (18447478336279 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11682505671 / 1000000000000) (11682505736 / 1000000000000), orderedInterval (-73434208696 / 1000000000000) (-73434208631 / 1000000000000)))) (orderedInterval (-3486130771 / 1000000000000) (-3486130711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (9921115202793 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4203795911 / 1000000000000) (-4203795894 / 1000000000000), orderedInterval (101274041968 / 1000000000000) (101274041984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (26937757707379 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-29500347880 / 1000000000000) (-29500344479 / 1000000000000), orderedInterval (54041449724 / 1000000000000) (54041453125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (36781205169683 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51120091768 / 1000000000000) (-51120091765 / 1000000000000), orderedInterval (-12381084120 / 1000000000000) (-12381084117 / 1000000000000)))) (orderedInterval (-521522474 / 1000000000000) (-521522411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (15552521663721 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45561522978 / 1000000000000) (-45561522977 / 1000000000000), orderedInterval (-66650214710 / 1000000000000) (-66650214709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (63220137112841 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2818059538 / 1000000000000) (2818059539 / 1000000000000), orderedInterval (40036939477 / 1000000000000) (40036939478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (42228121713319 / 160000000000) 3 (IntervalRat.scale (425 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35804994637 / 1000000000000) (35804994638 / 1000000000000), orderedInterval (33549410210 / 1000000000000) (33549410211 / 1000000000000)))) (orderedInterval (32997016734 / 1000000000000) (32997016924 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate340_chunkChecks3 :
    compactCertificate340.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate340.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate340_chunkChecks3_0
    compactCertificate340_chunkChecks3_1 compactCertificate340_chunkChecks3_2

theorem compactCertificate340_chunkChecks4_0 :
    compactCertificate340.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (425 / 2) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-18433203048 / 1000000000000) (-18433202631 / 1000000000000), orderedInterval (51580554449 / 1000000000000) (51580554865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (25044246114317 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (14632526454 / 1000000000000) (14632526455 / 1000000000000), orderedInterval (62026409685 / 1000000000000) (62026409686 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (8098794626861 / 32000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (28185092934 / 1000000000000) (28185098942 / 1000000000000), orderedInterval (-41540834005 / 1000000000000) (-41540827997 / 1000000000000)))) (orderedInterval (-3782137917 / 1000000000000) (-3782137009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (7307848554919 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73050043162 / 1000000000000) (73050075530 / 1000000000000), orderedInterval (-93547699745 / 1000000000000) (-93547667378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (19629909152443 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58560163644 / 1000000000000) (-58560163643 / 1000000000000), orderedInterval (-41709782196 / 1000000000000) (-41709782195 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (53299021910031 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (34110024352 / 1000000000000) (34110024353 / 1000000000000), orderedInterval (27290977723 / 1000000000000) (27290977724 / 1000000000000)))) (orderedInterval (-14955480068 / 1000000000000) (-14955479973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (39259818304903 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45725420531 / 1000000000000) (45725420532 / 1000000000000), orderedInterval (22349453167 / 1000000000000) (22349453168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (67272367827619 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10153214410 / 1000000000000) (10153214411 / 1000000000000), orderedInterval (37551790863 / 1000000000000) (37551790864 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (49552521663721 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (22897328274 / 1000000000000) (22897330407 / 1000000000000), orderedInterval (-39168712163 / 1000000000000) (-39168710030 / 1000000000000)))) (orderedInterval (-2414879246 / 1000000000000) (-2414878887 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate340_chunkChecks4_1 :
    compactCertificate340.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (76026311234983 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36603055724 / 1000000000000) (-36603055284 / 1000000000000), orderedInterval (-23954711 / 1000000000000) (-23954270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (43893811257007 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-46882808562 / 1000000000000) (-46882806439 / 1000000000000), orderedInterval (11157047223 / 1000000000000) (11157049347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (77890338338363 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21968279992 / 1000000000000) (-21968279991 / 1000000000000), orderedInterval (-28702340961 / 1000000000000) (-28702340960 / 1000000000000)))) (orderedInterval (66487775627 / 1000000000000) (66487779855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (72775257744647 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-3718172057 / 1000000000000) (-3718172056 / 1000000000000), orderedInterval (-37222463059 / 1000000000000) (-37222463058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (51935857876151 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43126966193 / 1000000000000) (-43126963457 / 1000000000000), orderedInterval (10131820220 / 1000000000000) (10131822956 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (58889727457329 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-39837276909 / 1000000000000) (-39837276906 / 1000000000000), orderedInterval (-11889471200 / 1000000000000) (-11889471197 / 1000000000000)))) (orderedInterval (-18882550399 / 1000000000000) (-18882548781 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (49096115191201 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-10843389484 / 1000000000000) (-10843389431 / 1000000000000), orderedInterval (44256929759 / 1000000000000) (44256929812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (43377906707221 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (47920431345 / 1000000000000) (47920432138 / 1000000000000), orderedInterval (-7286232125 / 1000000000000) (-7286231332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (12572608098879 / 32000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-33430344826 / 1000000000000) (-33430344825 / 1000000000000), orderedInterval (-22379459174 / 1000000000000) (-22379459173 / 1000000000000)))) (orderedInterval (-17823689511 / 1000000000000) (-17823689279 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate340_chunkChecks4_2 :
    compactCertificate340.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (34776495661613 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-53011084715 / 1000000000000) (-53011084712 / 1000000000000), orderedInterval (-10776837796 / 1000000000000) (-10776837792 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (29480420511493 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (18301567981 / 1000000000000) (18301568336 / 1000000000000), orderedInterval (-55908495852 / 1000000000000) (-55908495498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (18447478336279 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11682505671 / 1000000000000) (11682505736 / 1000000000000), orderedInterval (-73434208696 / 1000000000000) (-73434208631 / 1000000000000)))) (orderedInterval (8757406580 / 1000000000000) (8757406638 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (9921115202793 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-4203795911 / 1000000000000) (-4203795894 / 1000000000000), orderedInterval (101274041968 / 1000000000000) (101274041984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (26937757707379 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-29500347880 / 1000000000000) (-29500344479 / 1000000000000), orderedInterval (54041449724 / 1000000000000) (54041453125 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (36781205169683 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51120091768 / 1000000000000) (-51120091765 / 1000000000000), orderedInterval (-12381084120 / 1000000000000) (-12381084117 / 1000000000000)))) (orderedInterval (5634804028 / 1000000000000) (5634804084 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (15552521663721 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45561522978 / 1000000000000) (-45561522977 / 1000000000000), orderedInterval (-66650214710 / 1000000000000) (-66650214709 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (63220137112841 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2818059538 / 1000000000000) (2818059539 / 1000000000000), orderedInterval (40036939477 / 1000000000000) (40036939478 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (42228121713319 / 160000000000) 4 (IntervalRat.scale (425 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35804994637 / 1000000000000) (35804994638 / 1000000000000), orderedInterval (33549410210 / 1000000000000) (33549410211 / 1000000000000)))) (orderedInterval (-19050088190 / 1000000000000) (-19050087886 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate340_chunkChecks4 :
    compactCertificate340.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate340.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate340_chunkChecks4_0
    compactCertificate340_chunkChecks4_1 compactCertificate340_chunkChecks4_2

theorem compactCertificate340_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate340.chunkCheck r b = true :=
  compactCertificate340.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate340_chunkChecks0
    · exact compactCertificate340_chunkChecks1
    · exact compactCertificate340_chunkChecks2
    · exact compactCertificate340_chunkChecks3
    · exact compactCertificate340_chunkChecks4)

theorem compactCertificate340_coefficient0 :
    compactCertificate340.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate340_coefficient1 :
    compactCertificate340.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate340_coefficient2 :
    compactCertificate340.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate340_coefficient3 :
    compactCertificate340.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate340_coefficient4 :
    compactCertificate340.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate340_coefficients : ∀ r : Fin 5,
    compactCertificate340.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate340_coefficient0
  · exact compactCertificate340_coefficient1
  · exact compactCertificate340_coefficient2
  · exact compactCertificate340_coefficient3
  · exact compactCertificate340_coefficient4

theorem compactCertificate340_lower : (1 : ℚ) ≤ compactCertificate340.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate340, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate340_proves {t : ℝ} (ht : t ∈ compactCertificate340.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate340.proves compactCertificate340_states compactCertificate340_chunks
    compactCertificate340_coefficients compactCertificate340_lower ht

end Erdos232
