/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate470 : CompactCertificate where
  left := 341
  right := 342
  center := 683 / 2
  grid := fun i =>
    match i.val with
    | 0 => 109
    | 1 => 80
    | 2 => 130
    | 3 => 23
    | 4 => 63
    | 5 => 170
    | 6 => 126
    | 7 => 215
    | 8 => 159
    | 9 => 243
    | 10 => 140
    | 11 => 249
    | 12 => 233
    | 13 => 166
    | 14 => 188
    | 15 => 157
    | 16 => 139
    | 17 => 201
    | 18 => 111
    | 19 => 94
    | 20 => 59
    | 21 => 32
    | 22 => 86
    | 23 => 118
    | 24 => 50
    | 25 => 202
    | _ => 135
  point := fun i =>
    match i.val with
    | 0 => 683 / 2
    | 1 => 1006189417416383 / 4000000000000
    | 2 => 325380984126239 / 800000000000
    | 3 => 293603562529981 / 4000000000000
    | 4 => 788660467712857 / 4000000000000
    | 5 => 2141366586150069 / 4000000000000
    | 6 => 1577320935426397 / 4000000000000
    | 7 => 2702766307427281 / 4000000000000
    | 8 => 1990845429195379 / 4000000000000
    | 9 => 3054468857264317 / 4000000000000
    | 10 => 1763498416972693 / 4000000000000
    | 11 => 3129358887358937 / 4000000000000
    | 12 => 2923853002329053 / 4000000000000
    | 13 => 2086599466435949 / 4000000000000
    | 14 => 2365981403138571 / 4000000000000
    | 15 => 1972508627975899 / 4000000000000
    | 16 => 1742771193001879 / 4000000000000
    | 17 => 505123019502021 / 800000000000
    | 18 => 1397196855110687 / 4000000000000
    | 19 => 1184419247608807 / 4000000000000
    | 20 => 741154570804621 / 4000000000000
    | 21 => 398595393147507 / 4000000000000
    | 22 => 1082264030243521 / 4000000000000
    | 23 => 1477739007699617 / 4000000000000
    | 24 => 624845429195379 / 4000000000000
    | 25 => 2539961979298259 / 4000000000000
    | _ => 1696576890011581 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (6390992826 / 1000000000000) (6390992836 / 1000000000000), orderedInterval (-42709987932 / 1000000000000) (-42709987922 / 1000000000000))
    | 1 => (orderedInterval (42463160404 / 1000000000000) (42463160405 / 1000000000000), orderedInterval (26891376378 / 1000000000000) (26891376379 / 1000000000000))
    | 2 => (orderedInterval (-30885315203 / 1000000000000) (-30885265505 / 1000000000000), orderedInterval (24762985338 / 1000000000000) (24763035036 / 1000000000000))
    | 3 => (orderedInterval (-87251885091 / 1000000000000) (-87251882300 / 1000000000000), orderedInterval (33154197489 / 1000000000000) (33154200279 / 1000000000000))
    | 4 => (orderedInterval (-1678531592 / 1000000000000) (-1678531590 / 1000000000000), orderedInterval (-56794150449 / 1000000000000) (-56794150447 / 1000000000000))
    | 5 => (orderedInterval (30503322168 / 1000000000000) (30503411407 / 1000000000000), orderedInterval (-16113568068 / 1000000000000) (-16113478828 / 1000000000000))
    | 6 => (orderedInterval (-26655586984 / 1000000000000) (-26655576261 / 1000000000000), orderedInterval (30098942121 / 1000000000000) (30098952844 / 1000000000000))
    | 7 => (orderedInterval (-26383474815 / 1000000000000) (-26383474814 / 1000000000000), orderedInterval (-15667644185 / 1000000000000) (-15667644183 / 1000000000000))
    | 8 => (orderedInterval (30413684323 / 1000000000000) (30413778973 / 1000000000000), orderedInterval (-18848115176 / 1000000000000) (-18848020526 / 1000000000000))
    | 9 => (orderedInterval (-24224879546 / 1000000000000) (-24224879545 / 1000000000000), orderedInterval (-15695433180 / 1000000000000) (-15695433179 / 1000000000000))
    | 10 => (orderedInterval (36663926519 / 1000000000000) (36663934047 / 1000000000000), orderedInterval (-10028989035 / 1000000000000) (-10028981507 / 1000000000000))
    | 11 => (orderedInterval (-21773667240 / 1000000000000) (-21773667239 / 1000000000000), orderedInterval (-18415562238 / 1000000000000) (-18415562237 / 1000000000000))
    | 12 => (orderedInterval (7089785684 / 1000000000000) (7089785686 / 1000000000000), orderedInterval (-28652149401 / 1000000000000) (-28652149398 / 1000000000000))
    | 13 => (orderedInterval (28017383777 / 1000000000000) (28017383778 / 1000000000000), orderedInterval (20839930987 / 1000000000000) (20839930988 / 1000000000000))
    | 14 => (orderedInterval (32673101876 / 1000000000000) (32673104501 / 1000000000000), orderedInterval (-2986786553 / 1000000000000) (-2986783928 / 1000000000000))
    | 15 => (orderedInterval (-22655648862 / 1000000000000) (-22655648861 / 1000000000000), orderedInterval (-27864422365 / 1000000000000) (-27864422364 / 1000000000000))
    | 16 => (orderedInterval (7724100733 / 1000000000000) (7724100745 / 1000000000000), orderedInterval (-37445554298 / 1000000000000) (-37445554287 / 1000000000000))
    | 17 => (orderedInterval (-21147995165 / 1000000000000) (-21147995164 / 1000000000000), orderedInterval (-23669183435 / 1000000000000) (-23669183434 / 1000000000000))
    | 18 => (orderedInterval (-41812028144 / 1000000000000) (-41812028134 / 1000000000000), orderedInterval (-8560789351 / 1000000000000) (-8560789341 / 1000000000000))
    | 19 => (orderedInterval (46365858908 / 1000000000000) (46365859063 / 1000000000000), orderedInterval (-508680949 / 1000000000000) (-508680795 / 1000000000000))
    | 20 => (orderedInterval (-38623914304 / 1000000000000) (-38623914303 / 1000000000000), orderedInterval (-43986841149 / 1000000000000) (-43986841148 / 1000000000000))
    | 21 => (orderedInterval (-7818289118 / 1000000000000) (-7818289088 / 1000000000000), orderedInterval (79585345251 / 1000000000000) (79585345281 / 1000000000000))
    | 22 => (orderedInterval (44737595039 / 1000000000000) (44737595040 / 1000000000000), orderedInterval (18664680708 / 1000000000000) (18664680709 / 1000000000000))
    | 23 => (orderedInterval (-19467659633 / 1000000000000) (-19467658702 / 1000000000000), orderedInterval (36690194394 / 1000000000000) (36690195325 / 1000000000000))
    | 24 => (orderedInterval (-5335607582 / 1000000000000) (-5335607566 / 1000000000000), orderedInterval (63632534538 / 1000000000000) (63632534554 / 1000000000000))
    | 25 => (orderedInterval (29202953463 / 1000000000000) (29202953468 / 1000000000000), orderedInterval (12214370977 / 1000000000000) (12214370981 / 1000000000000))
    | _ => (orderedInterval (-28175480239 / 1000000000000) (-28175480238 / 1000000000000), orderedInterval (-26558014090 / 1000000000000) (-26558014089 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1116454586 / 1000000000000) (1116457530 / 1000000000000)
      | 1 => orderedInterval (-1283141645 / 1000000000000) (-1283135229 / 1000000000000)
      | 2 => orderedInterval (1548810658 / 1000000000000) (1548812965 / 1000000000000)
      | 3 => orderedInterval (3925708695 / 1000000000000) (3925709389 / 1000000000000)
      | 4 => orderedInterval (2356066848 / 1000000000000) (2356066903 / 1000000000000)
      | 5 => orderedInterval (-1245116803 / 1000000000000) (-1245116769 / 1000000000000)
      | 6 => orderedInterval (2803709660 / 1000000000000) (2803709757 / 1000000000000)
      | 7 => orderedInterval (621389322 / 1000000000000) (621389435 / 1000000000000)
      | _ => orderedInterval (2877130358 / 1000000000000) (2877130453 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15013506311 / 1000000000000) (-15013502807 / 1000000000000)
      | 1 => orderedInterval (521171856 / 1000000000000) (521181855 / 1000000000000)
      | 2 => orderedInterval (292273825 / 1000000000000) (292277193 / 1000000000000)
      | 3 => orderedInterval (-720431030 / 1000000000000) (-720430029 / 1000000000000)
      | 4 => orderedInterval (4143616493 / 1000000000000) (4143616583 / 1000000000000)
      | 5 => orderedInterval (1148814278 / 1000000000000) (1148814326 / 1000000000000)
      | 6 => orderedInterval (648064218 / 1000000000000) (648064307 / 1000000000000)
      | 7 => orderedInterval (-3806208801 / 1000000000000) (-3806208686 / 1000000000000)
      | _ => orderedInterval (4515592691 / 1000000000000) (4515592825 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-133057722 / 1000000000000) (-133053540 / 1000000000000)
      | 1 => orderedInterval (5304028219 / 1000000000000) (5304043904 / 1000000000000)
      | 2 => orderedInterval (-4747950417 / 1000000000000) (-4747945488 / 1000000000000)
      | 3 => orderedInterval (-9803247509 / 1000000000000) (-9803245975 / 1000000000000)
      | 4 => orderedInterval (-5111642044 / 1000000000000) (-5111641894 / 1000000000000)
      | 5 => orderedInterval (3112654861 / 1000000000000) (3112654934 / 1000000000000)
      | 6 => orderedInterval (-4653027749 / 1000000000000) (-4653027665 / 1000000000000)
      | 7 => orderedInterval (-1110090923 / 1000000000000) (-1110090803 / 1000000000000)
      | _ => orderedInterval (57645731 / 1000000000000) (57645930 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14373943635 / 1000000000000) (14373948614 / 1000000000000)
      | 1 => orderedInterval (-4025729074 / 1000000000000) (-4025704492 / 1000000000000)
      | 2 => orderedInterval (-2319178416 / 1000000000000) (-2319171211 / 1000000000000)
      | 3 => orderedInterval (1921658693 / 1000000000000) (1921661217 / 1000000000000)
      | 4 => orderedInterval (-12160009241 / 1000000000000) (-12160008985 / 1000000000000)
      | 5 => orderedInterval (340008914 / 1000000000000) (340009024 / 1000000000000)
      | 6 => orderedInterval (-1241156488 / 1000000000000) (-1241156407 / 1000000000000)
      | 7 => orderedInterval (3810241682 / 1000000000000) (3810241811 / 1000000000000)
      | _ => orderedInterval (-3191690040 / 1000000000000) (-3191689735 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-1081205580 / 1000000000000) (-1081199637 / 1000000000000)
      | 1 => orderedInterval (-13076484463 / 1000000000000) (-13076445860 / 1000000000000)
      | 2 => orderedInterval (15801806877 / 1000000000000) (15801817439 / 1000000000000)
      | 3 => orderedInterval (29892121930 / 1000000000000) (29892126420 / 1000000000000)
      | 4 => orderedInterval (10320996606 / 1000000000000) (10320997049 / 1000000000000)
      | 5 => orderedInterval (-8638218654 / 1000000000000) (-8638218480 / 1000000000000)
      | 6 => orderedInterval (5732342551 / 1000000000000) (5732342630 / 1000000000000)
      | 7 => orderedInterval (1622187333 / 1000000000000) (1622187471 / 1000000000000)
      | _ => orderedInterval (-15819649466 / 1000000000000) (-15819648975 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (12721011679 / 1000000000000) (12721024434 / 1000000000000)
    | 1 => orderedInterval (-8270612781 / 1000000000000) (-8270594433 / 1000000000000)
    | 2 => orderedInterval (-17084687553 / 1000000000000) (-17084660597 / 1000000000000)
    | 3 => orderedInterval (-2491910335 / 1000000000000) (-2491870164 / 1000000000000)
    | _ => orderedInterval (24753897134 / 1000000000000) (24753958057 / 1000000000000)

theorem compactCertificate470_stateChecks0 :
    compactCertificate470.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (683 / 2)) (orderedInterval (6390992826 / 1000000000000) (6390992836 / 1000000000000), orderedInterval (-42709987932 / 1000000000000) (-42709987922 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1006189417416383 / 4000000000000)) (orderedInterval (42463160404 / 1000000000000) (42463160405 / 1000000000000), orderedInterval (26891376378 / 1000000000000) (26891376379 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (325380984126239 / 800000000000)) (orderedInterval (-30885315203 / 1000000000000) (-30885265505 / 1000000000000), orderedInterval (24762985338 / 1000000000000) (24763035036 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_stateChecks1 :
    compactCertificate470.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (293603562529981 / 4000000000000)) (orderedInterval (-87251885091 / 1000000000000) (-87251882300 / 1000000000000), orderedInterval (33154197489 / 1000000000000) (33154200279 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (788660467712857 / 4000000000000)) (orderedInterval (-1678531592 / 1000000000000) (-1678531590 / 1000000000000), orderedInterval (-56794150449 / 1000000000000) (-56794150447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2141366586150069 / 4000000000000)) (orderedInterval (30503322168 / 1000000000000) (30503411407 / 1000000000000), orderedInterval (-16113568068 / 1000000000000) (-16113478828 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_stateChecks2 :
    compactCertificate470.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1577320935426397 / 4000000000000)) (orderedInterval (-26655586984 / 1000000000000) (-26655576261 / 1000000000000), orderedInterval (30098942121 / 1000000000000) (30098952844 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2702766307427281 / 4000000000000)) (orderedInterval (-26383474815 / 1000000000000) (-26383474814 / 1000000000000), orderedInterval (-15667644185 / 1000000000000) (-15667644183 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1990845429195379 / 4000000000000)) (orderedInterval (30413684323 / 1000000000000) (30413778973 / 1000000000000), orderedInterval (-18848115176 / 1000000000000) (-18848020526 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_stateChecks3 :
    compactCertificate470.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (3054468857264317 / 4000000000000)) (orderedInterval (-24224879546 / 1000000000000) (-24224879545 / 1000000000000), orderedInterval (-15695433180 / 1000000000000) (-15695433179 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1763498416972693 / 4000000000000)) (orderedInterval (36663926519 / 1000000000000) (36663934047 / 1000000000000), orderedInterval (-10028989035 / 1000000000000) (-10028981507 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (3129358887358937 / 4000000000000)) (orderedInterval (-21773667240 / 1000000000000) (-21773667239 / 1000000000000), orderedInterval (-18415562238 / 1000000000000) (-18415562237 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_stateChecks4 :
    compactCertificate470.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (2923853002329053 / 4000000000000)) (orderedInterval (7089785684 / 1000000000000) (7089785686 / 1000000000000), orderedInterval (-28652149401 / 1000000000000) (-28652149398 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2086599466435949 / 4000000000000)) (orderedInterval (28017383777 / 1000000000000) (28017383778 / 1000000000000), orderedInterval (20839930987 / 1000000000000) (20839930988 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2365981403138571 / 4000000000000)) (orderedInterval (32673101876 / 1000000000000) (32673104501 / 1000000000000), orderedInterval (-2986786553 / 1000000000000) (-2986783928 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_stateChecks5 :
    compactCertificate470.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1972508627975899 / 4000000000000)) (orderedInterval (-22655648862 / 1000000000000) (-22655648861 / 1000000000000), orderedInterval (-27864422365 / 1000000000000) (-27864422364 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1742771193001879 / 4000000000000)) (orderedInterval (7724100733 / 1000000000000) (7724100745 / 1000000000000), orderedInterval (-37445554298 / 1000000000000) (-37445554287 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (505123019502021 / 800000000000)) (orderedInterval (-21147995165 / 1000000000000) (-21147995164 / 1000000000000), orderedInterval (-23669183435 / 1000000000000) (-23669183434 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_stateChecks6 :
    compactCertificate470.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1397196855110687 / 4000000000000)) (orderedInterval (-41812028144 / 1000000000000) (-41812028134 / 1000000000000), orderedInterval (-8560789351 / 1000000000000) (-8560789341 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1184419247608807 / 4000000000000)) (orderedInterval (46365858908 / 1000000000000) (46365859063 / 1000000000000), orderedInterval (-508680949 / 1000000000000) (-508680795 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (741154570804621 / 4000000000000)) (orderedInterval (-38623914304 / 1000000000000) (-38623914303 / 1000000000000), orderedInterval (-43986841149 / 1000000000000) (-43986841148 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_stateChecks7 :
    compactCertificate470.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (398595393147507 / 4000000000000)) (orderedInterval (-7818289118 / 1000000000000) (-7818289088 / 1000000000000), orderedInterval (79585345251 / 1000000000000) (79585345281 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1082264030243521 / 4000000000000)) (orderedInterval (44737595039 / 1000000000000) (44737595040 / 1000000000000), orderedInterval (18664680708 / 1000000000000) (18664680709 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1477739007699617 / 4000000000000)) (orderedInterval (-19467659633 / 1000000000000) (-19467658702 / 1000000000000), orderedInterval (36690194394 / 1000000000000) (36690195325 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_stateChecks8 :
    compactCertificate470.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (624845429195379 / 4000000000000)) (orderedInterval (-5335607582 / 1000000000000) (-5335607566 / 1000000000000), orderedInterval (63632534538 / 1000000000000) (63632534554 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2539961979298259 / 4000000000000)) (orderedInterval (29202953463 / 1000000000000) (29202953468 / 1000000000000), orderedInterval (12214370977 / 1000000000000) (12214370981 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1696576890011581 / 4000000000000)) (orderedInterval (-28175480239 / 1000000000000) (-28175480238 / 1000000000000), orderedInterval (-26558014090 / 1000000000000) (-26558014089 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_states : ∀ j,
    BesselStateValid (compactCertificate470.point j) (compactCertificate470.state j) :=
  compactCertificate470.statesValid_of_checks3 compactCertificate470_stateChecks0
    compactCertificate470_stateChecks1 compactCertificate470_stateChecks2
    compactCertificate470_stateChecks3 compactCertificate470_stateChecks4
    compactCertificate470_stateChecks5 compactCertificate470_stateChecks6
    compactCertificate470_stateChecks7 compactCertificate470_stateChecks8

theorem compactCertificate470_chunkChecks0_0 :
    compactCertificate470.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (683 / 2) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6390992826 / 1000000000000) (6390992836 / 1000000000000), orderedInterval (-42709987932 / 1000000000000) (-42709987922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1006189417416383 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42463160404 / 1000000000000) (42463160405 / 1000000000000), orderedInterval (26891376378 / 1000000000000) (26891376379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (325380984126239 / 800000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30885315203 / 1000000000000) (-30885265505 / 1000000000000), orderedInterval (24762985338 / 1000000000000) (24763035036 / 1000000000000)))) (orderedInterval (1116454586 / 1000000000000) (1116457530 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (293603562529981 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-87251885091 / 1000000000000) (-87251882300 / 1000000000000), orderedInterval (33154197489 / 1000000000000) (33154200279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (788660467712857 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1678531592 / 1000000000000) (-1678531590 / 1000000000000), orderedInterval (-56794150449 / 1000000000000) (-56794150447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2141366586150069 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30503322168 / 1000000000000) (30503411407 / 1000000000000), orderedInterval (-16113568068 / 1000000000000) (-16113478828 / 1000000000000)))) (orderedInterval (-1283141645 / 1000000000000) (-1283135229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1577320935426397 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26655586984 / 1000000000000) (-26655576261 / 1000000000000), orderedInterval (30098942121 / 1000000000000) (30098952844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2702766307427281 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26383474815 / 1000000000000) (-26383474814 / 1000000000000), orderedInterval (-15667644185 / 1000000000000) (-15667644183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1990845429195379 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30413684323 / 1000000000000) (30413778973 / 1000000000000), orderedInterval (-18848115176 / 1000000000000) (-18848020526 / 1000000000000)))) (orderedInterval (1548810658 / 1000000000000) (1548812965 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_chunkChecks0_1 :
    compactCertificate470.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3054468857264317 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24224879546 / 1000000000000) (-24224879545 / 1000000000000), orderedInterval (-15695433180 / 1000000000000) (-15695433179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1763498416972693 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36663926519 / 1000000000000) (36663934047 / 1000000000000), orderedInterval (-10028989035 / 1000000000000) (-10028981507 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3129358887358937 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21773667240 / 1000000000000) (-21773667239 / 1000000000000), orderedInterval (-18415562238 / 1000000000000) (-18415562237 / 1000000000000)))) (orderedInterval (3925708695 / 1000000000000) (3925709389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2923853002329053 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7089785684 / 1000000000000) (7089785686 / 1000000000000), orderedInterval (-28652149401 / 1000000000000) (-28652149398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2086599466435949 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28017383777 / 1000000000000) (28017383778 / 1000000000000), orderedInterval (20839930987 / 1000000000000) (20839930988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2365981403138571 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32673101876 / 1000000000000) (32673104501 / 1000000000000), orderedInterval (-2986786553 / 1000000000000) (-2986783928 / 1000000000000)))) (orderedInterval (2356066848 / 1000000000000) (2356066903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1972508627975899 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22655648862 / 1000000000000) (-22655648861 / 1000000000000), orderedInterval (-27864422365 / 1000000000000) (-27864422364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1742771193001879 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7724100733 / 1000000000000) (7724100745 / 1000000000000), orderedInterval (-37445554298 / 1000000000000) (-37445554287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (505123019502021 / 800000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21147995165 / 1000000000000) (-21147995164 / 1000000000000), orderedInterval (-23669183435 / 1000000000000) (-23669183434 / 1000000000000)))) (orderedInterval (-1245116803 / 1000000000000) (-1245116769 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_chunkChecks0_2 :
    compactCertificate470.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1397196855110687 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41812028144 / 1000000000000) (-41812028134 / 1000000000000), orderedInterval (-8560789351 / 1000000000000) (-8560789341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1184419247608807 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46365858908 / 1000000000000) (46365859063 / 1000000000000), orderedInterval (-508680949 / 1000000000000) (-508680795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (741154570804621 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38623914304 / 1000000000000) (-38623914303 / 1000000000000), orderedInterval (-43986841149 / 1000000000000) (-43986841148 / 1000000000000)))) (orderedInterval (2803709660 / 1000000000000) (2803709757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (398595393147507 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-7818289118 / 1000000000000) (-7818289088 / 1000000000000), orderedInterval (79585345251 / 1000000000000) (79585345281 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1082264030243521 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44737595039 / 1000000000000) (44737595040 / 1000000000000), orderedInterval (18664680708 / 1000000000000) (18664680709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1477739007699617 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19467659633 / 1000000000000) (-19467658702 / 1000000000000), orderedInterval (36690194394 / 1000000000000) (36690195325 / 1000000000000)))) (orderedInterval (621389322 / 1000000000000) (621389435 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (624845429195379 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-5335607582 / 1000000000000) (-5335607566 / 1000000000000), orderedInterval (63632534538 / 1000000000000) (63632534554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2539961979298259 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29202953463 / 1000000000000) (29202953468 / 1000000000000), orderedInterval (12214370977 / 1000000000000) (12214370981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1696576890011581 / 4000000000000) 0 (IntervalRat.scale (683 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28175480239 / 1000000000000) (-28175480238 / 1000000000000), orderedInterval (-26558014090 / 1000000000000) (-26558014089 / 1000000000000)))) (orderedInterval (2877130358 / 1000000000000) (2877130453 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_chunkChecks0 :
    compactCertificate470.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate470.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate470_chunkChecks0_0
    compactCertificate470_chunkChecks0_1 compactCertificate470_chunkChecks0_2

theorem compactCertificate470_chunkChecks1_0 :
    compactCertificate470.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (683 / 2) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6390992826 / 1000000000000) (6390992836 / 1000000000000), orderedInterval (-42709987932 / 1000000000000) (-42709987922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1006189417416383 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42463160404 / 1000000000000) (42463160405 / 1000000000000), orderedInterval (26891376378 / 1000000000000) (26891376379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (325380984126239 / 800000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30885315203 / 1000000000000) (-30885265505 / 1000000000000), orderedInterval (24762985338 / 1000000000000) (24763035036 / 1000000000000)))) (orderedInterval (-15013506311 / 1000000000000) (-15013502807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (293603562529981 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-87251885091 / 1000000000000) (-87251882300 / 1000000000000), orderedInterval (33154197489 / 1000000000000) (33154200279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (788660467712857 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1678531592 / 1000000000000) (-1678531590 / 1000000000000), orderedInterval (-56794150449 / 1000000000000) (-56794150447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2141366586150069 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30503322168 / 1000000000000) (30503411407 / 1000000000000), orderedInterval (-16113568068 / 1000000000000) (-16113478828 / 1000000000000)))) (orderedInterval (521171856 / 1000000000000) (521181855 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1577320935426397 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26655586984 / 1000000000000) (-26655576261 / 1000000000000), orderedInterval (30098942121 / 1000000000000) (30098952844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2702766307427281 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26383474815 / 1000000000000) (-26383474814 / 1000000000000), orderedInterval (-15667644185 / 1000000000000) (-15667644183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1990845429195379 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30413684323 / 1000000000000) (30413778973 / 1000000000000), orderedInterval (-18848115176 / 1000000000000) (-18848020526 / 1000000000000)))) (orderedInterval (292273825 / 1000000000000) (292277193 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_chunkChecks1_1 :
    compactCertificate470.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3054468857264317 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24224879546 / 1000000000000) (-24224879545 / 1000000000000), orderedInterval (-15695433180 / 1000000000000) (-15695433179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1763498416972693 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36663926519 / 1000000000000) (36663934047 / 1000000000000), orderedInterval (-10028989035 / 1000000000000) (-10028981507 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3129358887358937 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21773667240 / 1000000000000) (-21773667239 / 1000000000000), orderedInterval (-18415562238 / 1000000000000) (-18415562237 / 1000000000000)))) (orderedInterval (-720431030 / 1000000000000) (-720430029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2923853002329053 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7089785684 / 1000000000000) (7089785686 / 1000000000000), orderedInterval (-28652149401 / 1000000000000) (-28652149398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2086599466435949 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28017383777 / 1000000000000) (28017383778 / 1000000000000), orderedInterval (20839930987 / 1000000000000) (20839930988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2365981403138571 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32673101876 / 1000000000000) (32673104501 / 1000000000000), orderedInterval (-2986786553 / 1000000000000) (-2986783928 / 1000000000000)))) (orderedInterval (4143616493 / 1000000000000) (4143616583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1972508627975899 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22655648862 / 1000000000000) (-22655648861 / 1000000000000), orderedInterval (-27864422365 / 1000000000000) (-27864422364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1742771193001879 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7724100733 / 1000000000000) (7724100745 / 1000000000000), orderedInterval (-37445554298 / 1000000000000) (-37445554287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (505123019502021 / 800000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21147995165 / 1000000000000) (-21147995164 / 1000000000000), orderedInterval (-23669183435 / 1000000000000) (-23669183434 / 1000000000000)))) (orderedInterval (1148814278 / 1000000000000) (1148814326 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_chunkChecks1_2 :
    compactCertificate470.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1397196855110687 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41812028144 / 1000000000000) (-41812028134 / 1000000000000), orderedInterval (-8560789351 / 1000000000000) (-8560789341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1184419247608807 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46365858908 / 1000000000000) (46365859063 / 1000000000000), orderedInterval (-508680949 / 1000000000000) (-508680795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (741154570804621 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38623914304 / 1000000000000) (-38623914303 / 1000000000000), orderedInterval (-43986841149 / 1000000000000) (-43986841148 / 1000000000000)))) (orderedInterval (648064218 / 1000000000000) (648064307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (398595393147507 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-7818289118 / 1000000000000) (-7818289088 / 1000000000000), orderedInterval (79585345251 / 1000000000000) (79585345281 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1082264030243521 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44737595039 / 1000000000000) (44737595040 / 1000000000000), orderedInterval (18664680708 / 1000000000000) (18664680709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1477739007699617 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19467659633 / 1000000000000) (-19467658702 / 1000000000000), orderedInterval (36690194394 / 1000000000000) (36690195325 / 1000000000000)))) (orderedInterval (-3806208801 / 1000000000000) (-3806208686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (624845429195379 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-5335607582 / 1000000000000) (-5335607566 / 1000000000000), orderedInterval (63632534538 / 1000000000000) (63632534554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2539961979298259 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29202953463 / 1000000000000) (29202953468 / 1000000000000), orderedInterval (12214370977 / 1000000000000) (12214370981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1696576890011581 / 4000000000000) 1 (IntervalRat.scale (683 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28175480239 / 1000000000000) (-28175480238 / 1000000000000), orderedInterval (-26558014090 / 1000000000000) (-26558014089 / 1000000000000)))) (orderedInterval (4515592691 / 1000000000000) (4515592825 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_chunkChecks1 :
    compactCertificate470.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate470.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate470_chunkChecks1_0
    compactCertificate470_chunkChecks1_1 compactCertificate470_chunkChecks1_2

theorem compactCertificate470_chunkChecks2_0 :
    compactCertificate470.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (683 / 2) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6390992826 / 1000000000000) (6390992836 / 1000000000000), orderedInterval (-42709987932 / 1000000000000) (-42709987922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1006189417416383 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42463160404 / 1000000000000) (42463160405 / 1000000000000), orderedInterval (26891376378 / 1000000000000) (26891376379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (325380984126239 / 800000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30885315203 / 1000000000000) (-30885265505 / 1000000000000), orderedInterval (24762985338 / 1000000000000) (24763035036 / 1000000000000)))) (orderedInterval (-133057722 / 1000000000000) (-133053540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (293603562529981 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-87251885091 / 1000000000000) (-87251882300 / 1000000000000), orderedInterval (33154197489 / 1000000000000) (33154200279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (788660467712857 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1678531592 / 1000000000000) (-1678531590 / 1000000000000), orderedInterval (-56794150449 / 1000000000000) (-56794150447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2141366586150069 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30503322168 / 1000000000000) (30503411407 / 1000000000000), orderedInterval (-16113568068 / 1000000000000) (-16113478828 / 1000000000000)))) (orderedInterval (5304028219 / 1000000000000) (5304043904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1577320935426397 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26655586984 / 1000000000000) (-26655576261 / 1000000000000), orderedInterval (30098942121 / 1000000000000) (30098952844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2702766307427281 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26383474815 / 1000000000000) (-26383474814 / 1000000000000), orderedInterval (-15667644185 / 1000000000000) (-15667644183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1990845429195379 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30413684323 / 1000000000000) (30413778973 / 1000000000000), orderedInterval (-18848115176 / 1000000000000) (-18848020526 / 1000000000000)))) (orderedInterval (-4747950417 / 1000000000000) (-4747945488 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_chunkChecks2_1 :
    compactCertificate470.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3054468857264317 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24224879546 / 1000000000000) (-24224879545 / 1000000000000), orderedInterval (-15695433180 / 1000000000000) (-15695433179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1763498416972693 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36663926519 / 1000000000000) (36663934047 / 1000000000000), orderedInterval (-10028989035 / 1000000000000) (-10028981507 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3129358887358937 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21773667240 / 1000000000000) (-21773667239 / 1000000000000), orderedInterval (-18415562238 / 1000000000000) (-18415562237 / 1000000000000)))) (orderedInterval (-9803247509 / 1000000000000) (-9803245975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2923853002329053 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7089785684 / 1000000000000) (7089785686 / 1000000000000), orderedInterval (-28652149401 / 1000000000000) (-28652149398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2086599466435949 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28017383777 / 1000000000000) (28017383778 / 1000000000000), orderedInterval (20839930987 / 1000000000000) (20839930988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2365981403138571 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32673101876 / 1000000000000) (32673104501 / 1000000000000), orderedInterval (-2986786553 / 1000000000000) (-2986783928 / 1000000000000)))) (orderedInterval (-5111642044 / 1000000000000) (-5111641894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1972508627975899 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22655648862 / 1000000000000) (-22655648861 / 1000000000000), orderedInterval (-27864422365 / 1000000000000) (-27864422364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1742771193001879 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7724100733 / 1000000000000) (7724100745 / 1000000000000), orderedInterval (-37445554298 / 1000000000000) (-37445554287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (505123019502021 / 800000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21147995165 / 1000000000000) (-21147995164 / 1000000000000), orderedInterval (-23669183435 / 1000000000000) (-23669183434 / 1000000000000)))) (orderedInterval (3112654861 / 1000000000000) (3112654934 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_chunkChecks2_2 :
    compactCertificate470.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1397196855110687 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41812028144 / 1000000000000) (-41812028134 / 1000000000000), orderedInterval (-8560789351 / 1000000000000) (-8560789341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1184419247608807 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46365858908 / 1000000000000) (46365859063 / 1000000000000), orderedInterval (-508680949 / 1000000000000) (-508680795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (741154570804621 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38623914304 / 1000000000000) (-38623914303 / 1000000000000), orderedInterval (-43986841149 / 1000000000000) (-43986841148 / 1000000000000)))) (orderedInterval (-4653027749 / 1000000000000) (-4653027665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (398595393147507 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-7818289118 / 1000000000000) (-7818289088 / 1000000000000), orderedInterval (79585345251 / 1000000000000) (79585345281 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1082264030243521 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44737595039 / 1000000000000) (44737595040 / 1000000000000), orderedInterval (18664680708 / 1000000000000) (18664680709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1477739007699617 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19467659633 / 1000000000000) (-19467658702 / 1000000000000), orderedInterval (36690194394 / 1000000000000) (36690195325 / 1000000000000)))) (orderedInterval (-1110090923 / 1000000000000) (-1110090803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (624845429195379 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-5335607582 / 1000000000000) (-5335607566 / 1000000000000), orderedInterval (63632534538 / 1000000000000) (63632534554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2539961979298259 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29202953463 / 1000000000000) (29202953468 / 1000000000000), orderedInterval (12214370977 / 1000000000000) (12214370981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1696576890011581 / 4000000000000) 2 (IntervalRat.scale (683 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28175480239 / 1000000000000) (-28175480238 / 1000000000000), orderedInterval (-26558014090 / 1000000000000) (-26558014089 / 1000000000000)))) (orderedInterval (57645731 / 1000000000000) (57645930 / 1000000000000))) = true
  rfl'

theorem compactCertificate470_chunkChecks2 :
    compactCertificate470.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate470.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate470_chunkChecks2_0
    compactCertificate470_chunkChecks2_1 compactCertificate470_chunkChecks2_2

theorem compactCertificate470_chunkChecks3_0 :
    compactCertificate470.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (683 / 2) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6390992826 / 1000000000000) (6390992836 / 1000000000000), orderedInterval (-42709987932 / 1000000000000) (-42709987922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1006189417416383 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42463160404 / 1000000000000) (42463160405 / 1000000000000), orderedInterval (26891376378 / 1000000000000) (26891376379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (325380984126239 / 800000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30885315203 / 1000000000000) (-30885265505 / 1000000000000), orderedInterval (24762985338 / 1000000000000) (24763035036 / 1000000000000)))) (orderedInterval (14373943635 / 1000000000000) (14373948614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (293603562529981 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-87251885091 / 1000000000000) (-87251882300 / 1000000000000), orderedInterval (33154197489 / 1000000000000) (33154200279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (788660467712857 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1678531592 / 1000000000000) (-1678531590 / 1000000000000), orderedInterval (-56794150449 / 1000000000000) (-56794150447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2141366586150069 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30503322168 / 1000000000000) (30503411407 / 1000000000000), orderedInterval (-16113568068 / 1000000000000) (-16113478828 / 1000000000000)))) (orderedInterval (-4025729074 / 1000000000000) (-4025704492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1577320935426397 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26655586984 / 1000000000000) (-26655576261 / 1000000000000), orderedInterval (30098942121 / 1000000000000) (30098952844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2702766307427281 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26383474815 / 1000000000000) (-26383474814 / 1000000000000), orderedInterval (-15667644185 / 1000000000000) (-15667644183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1990845429195379 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30413684323 / 1000000000000) (30413778973 / 1000000000000), orderedInterval (-18848115176 / 1000000000000) (-18848020526 / 1000000000000)))) (orderedInterval (-2319178416 / 1000000000000) (-2319171211 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate470_chunkChecks3_1 :
    compactCertificate470.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3054468857264317 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24224879546 / 1000000000000) (-24224879545 / 1000000000000), orderedInterval (-15695433180 / 1000000000000) (-15695433179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1763498416972693 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36663926519 / 1000000000000) (36663934047 / 1000000000000), orderedInterval (-10028989035 / 1000000000000) (-10028981507 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3129358887358937 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21773667240 / 1000000000000) (-21773667239 / 1000000000000), orderedInterval (-18415562238 / 1000000000000) (-18415562237 / 1000000000000)))) (orderedInterval (1921658693 / 1000000000000) (1921661217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2923853002329053 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7089785684 / 1000000000000) (7089785686 / 1000000000000), orderedInterval (-28652149401 / 1000000000000) (-28652149398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2086599466435949 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28017383777 / 1000000000000) (28017383778 / 1000000000000), orderedInterval (20839930987 / 1000000000000) (20839930988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2365981403138571 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32673101876 / 1000000000000) (32673104501 / 1000000000000), orderedInterval (-2986786553 / 1000000000000) (-2986783928 / 1000000000000)))) (orderedInterval (-12160009241 / 1000000000000) (-12160008985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1972508627975899 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22655648862 / 1000000000000) (-22655648861 / 1000000000000), orderedInterval (-27864422365 / 1000000000000) (-27864422364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1742771193001879 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7724100733 / 1000000000000) (7724100745 / 1000000000000), orderedInterval (-37445554298 / 1000000000000) (-37445554287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (505123019502021 / 800000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21147995165 / 1000000000000) (-21147995164 / 1000000000000), orderedInterval (-23669183435 / 1000000000000) (-23669183434 / 1000000000000)))) (orderedInterval (340008914 / 1000000000000) (340009024 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate470_chunkChecks3_2 :
    compactCertificate470.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1397196855110687 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41812028144 / 1000000000000) (-41812028134 / 1000000000000), orderedInterval (-8560789351 / 1000000000000) (-8560789341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1184419247608807 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46365858908 / 1000000000000) (46365859063 / 1000000000000), orderedInterval (-508680949 / 1000000000000) (-508680795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (741154570804621 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38623914304 / 1000000000000) (-38623914303 / 1000000000000), orderedInterval (-43986841149 / 1000000000000) (-43986841148 / 1000000000000)))) (orderedInterval (-1241156488 / 1000000000000) (-1241156407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (398595393147507 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-7818289118 / 1000000000000) (-7818289088 / 1000000000000), orderedInterval (79585345251 / 1000000000000) (79585345281 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1082264030243521 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44737595039 / 1000000000000) (44737595040 / 1000000000000), orderedInterval (18664680708 / 1000000000000) (18664680709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1477739007699617 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19467659633 / 1000000000000) (-19467658702 / 1000000000000), orderedInterval (36690194394 / 1000000000000) (36690195325 / 1000000000000)))) (orderedInterval (3810241682 / 1000000000000) (3810241811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (624845429195379 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-5335607582 / 1000000000000) (-5335607566 / 1000000000000), orderedInterval (63632534538 / 1000000000000) (63632534554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2539961979298259 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29202953463 / 1000000000000) (29202953468 / 1000000000000), orderedInterval (12214370977 / 1000000000000) (12214370981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1696576890011581 / 4000000000000) 3 (IntervalRat.scale (683 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28175480239 / 1000000000000) (-28175480238 / 1000000000000), orderedInterval (-26558014090 / 1000000000000) (-26558014089 / 1000000000000)))) (orderedInterval (-3191690040 / 1000000000000) (-3191689735 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate470_chunkChecks3 :
    compactCertificate470.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate470.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate470_chunkChecks3_0
    compactCertificate470_chunkChecks3_1 compactCertificate470_chunkChecks3_2

theorem compactCertificate470_chunkChecks4_0 :
    compactCertificate470.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (683 / 2) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6390992826 / 1000000000000) (6390992836 / 1000000000000), orderedInterval (-42709987932 / 1000000000000) (-42709987922 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1006189417416383 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42463160404 / 1000000000000) (42463160405 / 1000000000000), orderedInterval (26891376378 / 1000000000000) (26891376379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (325380984126239 / 800000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-30885315203 / 1000000000000) (-30885265505 / 1000000000000), orderedInterval (24762985338 / 1000000000000) (24763035036 / 1000000000000)))) (orderedInterval (-1081205580 / 1000000000000) (-1081199637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (293603562529981 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-87251885091 / 1000000000000) (-87251882300 / 1000000000000), orderedInterval (33154197489 / 1000000000000) (33154200279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (788660467712857 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-1678531592 / 1000000000000) (-1678531590 / 1000000000000), orderedInterval (-56794150449 / 1000000000000) (-56794150447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2141366586150069 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30503322168 / 1000000000000) (30503411407 / 1000000000000), orderedInterval (-16113568068 / 1000000000000) (-16113478828 / 1000000000000)))) (orderedInterval (-13076484463 / 1000000000000) (-13076445860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1577320935426397 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-26655586984 / 1000000000000) (-26655576261 / 1000000000000), orderedInterval (30098942121 / 1000000000000) (30098952844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2702766307427281 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-26383474815 / 1000000000000) (-26383474814 / 1000000000000), orderedInterval (-15667644185 / 1000000000000) (-15667644183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1990845429195379 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (30413684323 / 1000000000000) (30413778973 / 1000000000000), orderedInterval (-18848115176 / 1000000000000) (-18848020526 / 1000000000000)))) (orderedInterval (15801806877 / 1000000000000) (15801817439 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate470_chunkChecks4_1 :
    compactCertificate470.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3054468857264317 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24224879546 / 1000000000000) (-24224879545 / 1000000000000), orderedInterval (-15695433180 / 1000000000000) (-15695433179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1763498416972693 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (36663926519 / 1000000000000) (36663934047 / 1000000000000), orderedInterval (-10028989035 / 1000000000000) (-10028981507 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3129358887358937 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21773667240 / 1000000000000) (-21773667239 / 1000000000000), orderedInterval (-18415562238 / 1000000000000) (-18415562237 / 1000000000000)))) (orderedInterval (29892121930 / 1000000000000) (29892126420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2923853002329053 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7089785684 / 1000000000000) (7089785686 / 1000000000000), orderedInterval (-28652149401 / 1000000000000) (-28652149398 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2086599466435949 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28017383777 / 1000000000000) (28017383778 / 1000000000000), orderedInterval (20839930987 / 1000000000000) (20839930988 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2365981403138571 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32673101876 / 1000000000000) (32673104501 / 1000000000000), orderedInterval (-2986786553 / 1000000000000) (-2986783928 / 1000000000000)))) (orderedInterval (10320996606 / 1000000000000) (10320997049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1972508627975899 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22655648862 / 1000000000000) (-22655648861 / 1000000000000), orderedInterval (-27864422365 / 1000000000000) (-27864422364 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1742771193001879 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7724100733 / 1000000000000) (7724100745 / 1000000000000), orderedInterval (-37445554298 / 1000000000000) (-37445554287 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (505123019502021 / 800000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21147995165 / 1000000000000) (-21147995164 / 1000000000000), orderedInterval (-23669183435 / 1000000000000) (-23669183434 / 1000000000000)))) (orderedInterval (-8638218654 / 1000000000000) (-8638218480 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate470_chunkChecks4_2 :
    compactCertificate470.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1397196855110687 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-41812028144 / 1000000000000) (-41812028134 / 1000000000000), orderedInterval (-8560789351 / 1000000000000) (-8560789341 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1184419247608807 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (46365858908 / 1000000000000) (46365859063 / 1000000000000), orderedInterval (-508680949 / 1000000000000) (-508680795 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (741154570804621 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38623914304 / 1000000000000) (-38623914303 / 1000000000000), orderedInterval (-43986841149 / 1000000000000) (-43986841148 / 1000000000000)))) (orderedInterval (5732342551 / 1000000000000) (5732342630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (398595393147507 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-7818289118 / 1000000000000) (-7818289088 / 1000000000000), orderedInterval (79585345251 / 1000000000000) (79585345281 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1082264030243521 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44737595039 / 1000000000000) (44737595040 / 1000000000000), orderedInterval (18664680708 / 1000000000000) (18664680709 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1477739007699617 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-19467659633 / 1000000000000) (-19467658702 / 1000000000000), orderedInterval (36690194394 / 1000000000000) (36690195325 / 1000000000000)))) (orderedInterval (1622187333 / 1000000000000) (1622187471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (624845429195379 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-5335607582 / 1000000000000) (-5335607566 / 1000000000000), orderedInterval (63632534538 / 1000000000000) (63632534554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2539961979298259 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29202953463 / 1000000000000) (29202953468 / 1000000000000), orderedInterval (12214370977 / 1000000000000) (12214370981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1696576890011581 / 4000000000000) 4 (IntervalRat.scale (683 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28175480239 / 1000000000000) (-28175480238 / 1000000000000), orderedInterval (-26558014090 / 1000000000000) (-26558014089 / 1000000000000)))) (orderedInterval (-15819649466 / 1000000000000) (-15819648975 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate470_chunkChecks4 :
    compactCertificate470.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate470.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate470_chunkChecks4_0
    compactCertificate470_chunkChecks4_1 compactCertificate470_chunkChecks4_2

theorem compactCertificate470_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate470.chunkCheck r b = true :=
  compactCertificate470.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate470_chunkChecks0
    · exact compactCertificate470_chunkChecks1
    · exact compactCertificate470_chunkChecks2
    · exact compactCertificate470_chunkChecks3
    · exact compactCertificate470_chunkChecks4)

theorem compactCertificate470_coefficient0 :
    compactCertificate470.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate470_coefficient1 :
    compactCertificate470.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate470_coefficient2 :
    compactCertificate470.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate470_coefficient3 :
    compactCertificate470.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate470_coefficient4 :
    compactCertificate470.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate470_coefficients : ∀ r : Fin 5,
    compactCertificate470.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate470_coefficient0
  · exact compactCertificate470_coefficient1
  · exact compactCertificate470_coefficient2
  · exact compactCertificate470_coefficient3
  · exact compactCertificate470_coefficient4

theorem compactCertificate470_lower : (1 : ℚ) ≤ compactCertificate470.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate470, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate470_proves {t : ℝ} (ht : t ∈ compactCertificate470.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate470.proves compactCertificate470_states compactCertificate470_chunks
    compactCertificate470_coefficients compactCertificate470_lower ht

end Erdos232
