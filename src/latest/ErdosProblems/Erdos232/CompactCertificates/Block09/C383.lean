/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate383 : CompactCertificate where
  left := 254
  right := 255
  center := 509 / 2
  grid := fun i =>
    match i.val with
    | 0 => 81
    | 1 => 60
    | 2 => 97
    | 3 => 17
    | 4 => 47
    | 5 => 127
    | 6 => 94
    | 7 => 160
    | 8 => 118
    | 9 => 181
    | 10 => 105
    | 11 => 186
    | 12 => 173
    | 13 => 124
    | 14 => 140
    | 15 => 117
    | 16 => 103
    | 17 => 150
    | 18 => 83
    | 19 => 70
    | 20 => 44
    | 21 => 24
    | 22 => 64
    | 23 => 88
    | 24 => 37
    | 25 => 151
    | _ => 101
  point := fun i =>
    match i.val with
    | 0 => 509 / 2
    | 1 => 749854192481609 / 4000000000000
    | 2 => 242487439121897 / 800000000000
    | 3 => 218805583203163 / 4000000000000
    | 4 => 587742574034911 / 4000000000000
    | 5 => 1595835420717987 / 4000000000000
    | 6 => 1175485148070331 / 4000000000000
    | 7 => 2014213836721063 / 4000000000000
    | 8 => 1483660795696117 / 4000000000000
    | 9 => 2276317201094491 / 4000000000000
    | 10 => 1314232348812739 / 4000000000000
    | 11 => 2332128365542751 / 4000000000000
    | 12 => 2178976834825019 / 4000000000000
    | 13 => 1555020685821227 / 4000000000000
    | 14 => 1763227722104733 / 4000000000000
    | 15 => 1469995448960077 / 4000000000000
    | 16 => 1298785559645617 / 4000000000000
    | 17 => 376438677784083 / 800000000000
    | 18 => 1041249193633001 / 4000000000000
    | 19 => 882678472961761 / 4000000000000
    | 20 => 552339204303883 / 4000000000000
    | 21 => 297049861071861 / 4000000000000
    | 22 => 806548157238583 / 4000000000000
    | 23 => 1101272554786391 / 4000000000000
    | 24 => 465660795696117 / 4000000000000
    | 25 => 1892885281790357 / 4000000000000
    | _ => 1264359644239963 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-36427745789 / 1000000000000) (-36427745788 / 1000000000000), orderedInterval (-34199003156 / 1000000000000) (-34199003155 / 1000000000000))
    | 1 => (orderedInterval (-14263770055 / 1000000000000) (-14263769917 / 1000000000000), orderedInterval (56540443365 / 1000000000000) (56540443503 / 1000000000000))
    | 2 => (orderedInterval (34132405585 / 1000000000000) (34132453955 / 1000000000000), orderedInterval (-30638586709 / 1000000000000) (-30638538339 / 1000000000000))
    | 3 => (orderedInterval (-94326233303 / 1000000000000) (-94326221274 / 1000000000000), orderedInterval (53210903380 / 1000000000000) (53210915408 / 1000000000000))
    | 4 => (orderedInterval (-4297545393 / 1000000000000) (-4297545391 / 1000000000000), orderedInterval (-65667942839 / 1000000000000) (-65667942837 / 1000000000000))
    | 5 => (orderedInterval (-27568219862 / 1000000000000) (-27568219861 / 1000000000000), orderedInterval (-28873859326 / 1000000000000) (-28873859325 / 1000000000000))
    | 6 => (orderedInterval (-28295285428 / 1000000000000) (-28295276742 / 1000000000000), orderedInterval (37003511694 / 1000000000000) (37003520380 / 1000000000000))
    | 7 => (orderedInterval (35329627349 / 1000000000000) (35329629405 / 1000000000000), orderedInterval (-4043988853 / 1000000000000) (-4043986797 / 1000000000000))
    | 8 => (orderedInterval (34688370303 / 1000000000000) (34688370304 / 1000000000000), orderedInterval (22604175790 / 1000000000000) (22604175791 / 1000000000000))
    | 9 => (orderedInterval (-31591960249 / 1000000000000) (-31591960242 / 1000000000000), orderedInterval (-10955478849 / 1000000000000) (-10955478841 / 1000000000000))
    | 10 => (orderedInterval (22029180493 / 1000000000000) (22029182296 / 1000000000000), orderedInterval (-38143017066 / 1000000000000) (-38143015262 / 1000000000000))
    | 11 => (orderedInterval (-16389072773 / 1000000000000) (-16389072416 / 1000000000000), orderedInterval (28707443699 / 1000000000000) (28707444056 / 1000000000000))
    | 12 => (orderedInterval (-30585699768 / 1000000000000) (-30585622796 / 1000000000000), orderedInterval (15298107401 / 1000000000000) (15298184373 / 1000000000000))
    | 13 => (orderedInterval (-697656802 / 1000000000000) (-697656801 / 1000000000000), orderedInterval (40461989415 / 1000000000000) (40461989417 / 1000000000000))
    | 14 => (orderedInterval (37258233590 / 1000000000000) (37258237295 / 1000000000000), orderedInterval (-7528086887 / 1000000000000) (-7528083182 / 1000000000000))
    | 15 => (orderedInterval (-27368397879 / 1000000000000) (-27368397878 / 1000000000000), orderedInterval (-31319981355 / 1000000000000) (-31319981354 / 1000000000000))
    | 16 => (orderedInterval (-41939189527 / 1000000000000) (-41939181861 / 1000000000000), orderedInterval (14268962447 / 1000000000000) (14268970114 / 1000000000000))
    | 17 => (orderedInterval (3473739613 / 1000000000000) (3473739614 / 1000000000000), orderedInterval (36614140249 / 1000000000000) (36614140250 / 1000000000000))
    | 18 => (orderedInterval (-16726044049 / 1000000000000) (-16726044048 / 1000000000000), orderedInterval (-46506491490 / 1000000000000) (-46506491489 / 1000000000000))
    | 19 => (orderedInterval (53690815711 / 1000000000000) (53690815764 / 1000000000000), orderedInterval (1373065646 / 1000000000000) (1373065700 / 1000000000000))
    | 20 => (orderedInterval (40506548391 / 1000000000000) (40506548392 / 1000000000000), orderedInterval (54347199853 / 1000000000000) (54347199854 / 1000000000000))
    | 21 => (orderedInterval (-31925560980 / 1000000000000) (-31925559902 / 1000000000000), orderedInterval (87125648349 / 1000000000000) (87125649427 / 1000000000000))
    | 22 => (orderedInterval (54944285105 / 1000000000000) (54944285108 / 1000000000000), orderedInterval (11626951253 / 1000000000000) (11626951256 / 1000000000000))
    | 23 => (orderedInterval (-16807697210 / 1000000000000) (-16807696880 / 1000000000000), orderedInterval (45083938376 / 1000000000000) (45083938706 / 1000000000000))
    | 24 => (orderedInterval (-60603756981 / 1000000000000) (-60603756980 / 1000000000000), orderedInterval (-42115358572 / 1000000000000) (-42115358571 / 1000000000000))
    | 25 => (orderedInterval (13401310902 / 1000000000000) (13401311009 / 1000000000000), orderedInterval (-34156437362 / 1000000000000) (-34156437255 / 1000000000000))
    | _ => (orderedInterval (18542771237 / 1000000000000) (18542771845 / 1000000000000), orderedInterval (-40897580523 / 1000000000000) (-40897579916 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12568665408 / 1000000000000) (-12568662550 / 1000000000000)
      | 1 => orderedInterval (2826276575 / 1000000000000) (2826276737 / 1000000000000)
      | 2 => orderedInterval (-251357662 / 1000000000000) (-251357584 / 1000000000000)
      | 3 => orderedInterval (4915887580 / 1000000000000) (4915887867 / 1000000000000)
      | 4 => orderedInterval (297644295 / 1000000000000) (297645734 / 1000000000000)
      | 5 => orderedInterval (2172940230 / 1000000000000) (2172940693 / 1000000000000)
      | 6 => orderedInterval (954171846 / 1000000000000) (954171914 / 1000000000000)
      | 7 => orderedInterval (631118666 / 1000000000000) (631118742 / 1000000000000)
      | _ => orderedInterval (-4935345773 / 1000000000000) (-4935345579 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15308520412 / 1000000000000) (-15308517009 / 1000000000000)
      | 1 => orderedInterval (1709376196 / 1000000000000) (1709376260 / 1000000000000)
      | 2 => orderedInterval (1042986051 / 1000000000000) (1042986202 / 1000000000000)
      | 3 => orderedInterval (10053373713 / 1000000000000) (10053374215 / 1000000000000)
      | 4 => orderedInterval (5319456617 / 1000000000000) (5319459674 / 1000000000000)
      | 5 => orderedInterval (169245844 / 1000000000000) (169246440 / 1000000000000)
      | 6 => orderedInterval (8498444240 / 1000000000000) (8498444302 / 1000000000000)
      | 7 => orderedInterval (-4416244796 / 1000000000000) (-4416244735 / 1000000000000)
      | _ => orderedInterval (14584254092 / 1000000000000) (14584254349 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11729832023 / 1000000000000) (11729836087 / 1000000000000)
      | 1 => orderedInterval (-4817792712 / 1000000000000) (-4817792657 / 1000000000000)
      | 2 => orderedInterval (2481213192 / 1000000000000) (2481213486 / 1000000000000)
      | 3 => orderedInterval (-18600109845 / 1000000000000) (-18600108900 / 1000000000000)
      | 4 => orderedInterval (-1831082909 / 1000000000000) (-1831076392 / 1000000000000)
      | 5 => orderedInterval (-3552308187 / 1000000000000) (-3552307418 / 1000000000000)
      | 6 => orderedInterval (-934835902 / 1000000000000) (-934835842 / 1000000000000)
      | 7 => orderedInterval (-757861251 / 1000000000000) (-757861192 / 1000000000000)
      | _ => orderedInterval (9157601982 / 1000000000000) (9157602335 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (16335796623 / 1000000000000) (16335801462 / 1000000000000)
      | 1 => orderedInterval (-7421253816 / 1000000000000) (-7421253742 / 1000000000000)
      | 2 => orderedInterval (-2667086632 / 1000000000000) (-2667086059 / 1000000000000)
      | 3 => orderedInterval (-64675457721 / 1000000000000) (-64675455823 / 1000000000000)
      | 4 => orderedInterval (-11119780914 / 1000000000000) (-11119767025 / 1000000000000)
      | 5 => orderedInterval (-3126545240 / 1000000000000) (-3126544244 / 1000000000000)
      | 6 => orderedInterval (-8185370754 / 1000000000000) (-8185370696 / 1000000000000)
      | 7 => orderedInterval (4548401706 / 1000000000000) (4548401767 / 1000000000000)
      | _ => orderedInterval (-32587501913 / 1000000000000) (-32587501412 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10575945453 / 1000000000000) (-10575939672 / 1000000000000)
      | 1 => orderedInterval (11878215266 / 1000000000000) (11878215378 / 1000000000000)
      | 2 => orderedInterval (-12897501180 / 1000000000000) (-12897500055 / 1000000000000)
      | 3 => orderedInterval (81208677523 / 1000000000000) (81208681511 / 1000000000000)
      | 4 => orderedInterval (9621365008 / 1000000000000) (9621394693 / 1000000000000)
      | 5 => orderedInterval (6048619949 / 1000000000000) (6048621247 / 1000000000000)
      | 6 => orderedInterval (1388116213 / 1000000000000) (1388116269 / 1000000000000)
      | 7 => orderedInterval (1241544346 / 1000000000000) (1241544411 / 1000000000000)
      | _ => orderedInterval (-21078718452 / 1000000000000) (-21078717712 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-5957329651 / 1000000000000) (-5957324026 / 1000000000000)
    | 1 => orderedInterval (21652371545 / 1000000000000) (21652379698 / 1000000000000)
    | 2 => orderedInterval (-7125343609 / 1000000000000) (-7125330493 / 1000000000000)
    | 3 => orderedInterval (-108898798661 / 1000000000000) (-108898775772 / 1000000000000)
    | _ => orderedInterval (66834373220 / 1000000000000) (66834416070 / 1000000000000)

theorem compactCertificate383_stateChecks0 :
    compactCertificate383.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (509 / 2)) (orderedInterval (-36427745789 / 1000000000000) (-36427745788 / 1000000000000), orderedInterval (-34199003156 / 1000000000000) (-34199003155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (749854192481609 / 4000000000000)) (orderedInterval (-14263770055 / 1000000000000) (-14263769917 / 1000000000000), orderedInterval (56540443365 / 1000000000000) (56540443503 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (242487439121897 / 800000000000)) (orderedInterval (34132405585 / 1000000000000) (34132453955 / 1000000000000), orderedInterval (-30638586709 / 1000000000000) (-30638538339 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_stateChecks1 :
    compactCertificate383.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (218805583203163 / 4000000000000)) (orderedInterval (-94326233303 / 1000000000000) (-94326221274 / 1000000000000), orderedInterval (53210903380 / 1000000000000) (53210915408 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (587742574034911 / 4000000000000)) (orderedInterval (-4297545393 / 1000000000000) (-4297545391 / 1000000000000), orderedInterval (-65667942839 / 1000000000000) (-65667942837 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1595835420717987 / 4000000000000)) (orderedInterval (-27568219862 / 1000000000000) (-27568219861 / 1000000000000), orderedInterval (-28873859326 / 1000000000000) (-28873859325 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_stateChecks2 :
    compactCertificate383.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1175485148070331 / 4000000000000)) (orderedInterval (-28295285428 / 1000000000000) (-28295276742 / 1000000000000), orderedInterval (37003511694 / 1000000000000) (37003520380 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2014213836721063 / 4000000000000)) (orderedInterval (35329627349 / 1000000000000) (35329629405 / 1000000000000), orderedInterval (-4043988853 / 1000000000000) (-4043986797 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1483660795696117 / 4000000000000)) (orderedInterval (34688370303 / 1000000000000) (34688370304 / 1000000000000), orderedInterval (22604175790 / 1000000000000) (22604175791 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_stateChecks3 :
    compactCertificate383.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2276317201094491 / 4000000000000)) (orderedInterval (-31591960249 / 1000000000000) (-31591960242 / 1000000000000), orderedInterval (-10955478849 / 1000000000000) (-10955478841 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1314232348812739 / 4000000000000)) (orderedInterval (22029180493 / 1000000000000) (22029182296 / 1000000000000), orderedInterval (-38143017066 / 1000000000000) (-38143015262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2332128365542751 / 4000000000000)) (orderedInterval (-16389072773 / 1000000000000) (-16389072416 / 1000000000000), orderedInterval (28707443699 / 1000000000000) (28707444056 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_stateChecks4 :
    compactCertificate383.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2178976834825019 / 4000000000000)) (orderedInterval (-30585699768 / 1000000000000) (-30585622796 / 1000000000000), orderedInterval (15298107401 / 1000000000000) (15298184373 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1555020685821227 / 4000000000000)) (orderedInterval (-697656802 / 1000000000000) (-697656801 / 1000000000000), orderedInterval (40461989415 / 1000000000000) (40461989417 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1763227722104733 / 4000000000000)) (orderedInterval (37258233590 / 1000000000000) (37258237295 / 1000000000000), orderedInterval (-7528086887 / 1000000000000) (-7528083182 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_stateChecks5 :
    compactCertificate383.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1469995448960077 / 4000000000000)) (orderedInterval (-27368397879 / 1000000000000) (-27368397878 / 1000000000000), orderedInterval (-31319981355 / 1000000000000) (-31319981354 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1298785559645617 / 4000000000000)) (orderedInterval (-41939189527 / 1000000000000) (-41939181861 / 1000000000000), orderedInterval (14268962447 / 1000000000000) (14268970114 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (376438677784083 / 800000000000)) (orderedInterval (3473739613 / 1000000000000) (3473739614 / 1000000000000), orderedInterval (36614140249 / 1000000000000) (36614140250 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_stateChecks6 :
    compactCertificate383.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1041249193633001 / 4000000000000)) (orderedInterval (-16726044049 / 1000000000000) (-16726044048 / 1000000000000), orderedInterval (-46506491490 / 1000000000000) (-46506491489 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (882678472961761 / 4000000000000)) (orderedInterval (53690815711 / 1000000000000) (53690815764 / 1000000000000), orderedInterval (1373065646 / 1000000000000) (1373065700 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (552339204303883 / 4000000000000)) (orderedInterval (40506548391 / 1000000000000) (40506548392 / 1000000000000), orderedInterval (54347199853 / 1000000000000) (54347199854 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_stateChecks7 :
    compactCertificate383.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (297049861071861 / 4000000000000)) (orderedInterval (-31925560980 / 1000000000000) (-31925559902 / 1000000000000), orderedInterval (87125648349 / 1000000000000) (87125649427 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (806548157238583 / 4000000000000)) (orderedInterval (54944285105 / 1000000000000) (54944285108 / 1000000000000), orderedInterval (11626951253 / 1000000000000) (11626951256 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1101272554786391 / 4000000000000)) (orderedInterval (-16807697210 / 1000000000000) (-16807696880 / 1000000000000), orderedInterval (45083938376 / 1000000000000) (45083938706 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_stateChecks8 :
    compactCertificate383.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (465660795696117 / 4000000000000)) (orderedInterval (-60603756981 / 1000000000000) (-60603756980 / 1000000000000), orderedInterval (-42115358572 / 1000000000000) (-42115358571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1892885281790357 / 4000000000000)) (orderedInterval (13401310902 / 1000000000000) (13401311009 / 1000000000000), orderedInterval (-34156437362 / 1000000000000) (-34156437255 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1264359644239963 / 4000000000000)) (orderedInterval (18542771237 / 1000000000000) (18542771845 / 1000000000000), orderedInterval (-40897580523 / 1000000000000) (-40897579916 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_states : ∀ j,
    BesselStateValid (compactCertificate383.point j) (compactCertificate383.state j) :=
  compactCertificate383.statesValid_of_checks3 compactCertificate383_stateChecks0
    compactCertificate383_stateChecks1 compactCertificate383_stateChecks2
    compactCertificate383_stateChecks3 compactCertificate383_stateChecks4
    compactCertificate383_stateChecks5 compactCertificate383_stateChecks6
    compactCertificate383_stateChecks7 compactCertificate383_stateChecks8

theorem compactCertificate383_chunkChecks0_0 :
    compactCertificate383.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (509 / 2) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36427745789 / 1000000000000) (-36427745788 / 1000000000000), orderedInterval (-34199003156 / 1000000000000) (-34199003155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (749854192481609 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-14263770055 / 1000000000000) (-14263769917 / 1000000000000), orderedInterval (56540443365 / 1000000000000) (56540443503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (242487439121897 / 800000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34132405585 / 1000000000000) (34132453955 / 1000000000000), orderedInterval (-30638586709 / 1000000000000) (-30638538339 / 1000000000000)))) (orderedInterval (-12568665408 / 1000000000000) (-12568662550 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (218805583203163 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-94326233303 / 1000000000000) (-94326221274 / 1000000000000), orderedInterval (53210903380 / 1000000000000) (53210915408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (587742574034911 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-4297545393 / 1000000000000) (-4297545391 / 1000000000000), orderedInterval (-65667942839 / 1000000000000) (-65667942837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1595835420717987 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27568219862 / 1000000000000) (-27568219861 / 1000000000000), orderedInterval (-28873859326 / 1000000000000) (-28873859325 / 1000000000000)))) (orderedInterval (2826276575 / 1000000000000) (2826276737 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1175485148070331 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28295285428 / 1000000000000) (-28295276742 / 1000000000000), orderedInterval (37003511694 / 1000000000000) (37003520380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2014213836721063 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35329627349 / 1000000000000) (35329629405 / 1000000000000), orderedInterval (-4043988853 / 1000000000000) (-4043986797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1483660795696117 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34688370303 / 1000000000000) (34688370304 / 1000000000000), orderedInterval (22604175790 / 1000000000000) (22604175791 / 1000000000000)))) (orderedInterval (-251357662 / 1000000000000) (-251357584 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_chunkChecks0_1 :
    compactCertificate383.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2276317201094491 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31591960249 / 1000000000000) (-31591960242 / 1000000000000), orderedInterval (-10955478849 / 1000000000000) (-10955478841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1314232348812739 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22029180493 / 1000000000000) (22029182296 / 1000000000000), orderedInterval (-38143017066 / 1000000000000) (-38143015262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2332128365542751 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16389072773 / 1000000000000) (-16389072416 / 1000000000000), orderedInterval (28707443699 / 1000000000000) (28707444056 / 1000000000000)))) (orderedInterval (4915887580 / 1000000000000) (4915887867 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2178976834825019 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30585699768 / 1000000000000) (-30585622796 / 1000000000000), orderedInterval (15298107401 / 1000000000000) (15298184373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1555020685821227 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-697656802 / 1000000000000) (-697656801 / 1000000000000), orderedInterval (40461989415 / 1000000000000) (40461989417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1763227722104733 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37258233590 / 1000000000000) (37258237295 / 1000000000000), orderedInterval (-7528086887 / 1000000000000) (-7528083182 / 1000000000000)))) (orderedInterval (297644295 / 1000000000000) (297645734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1469995448960077 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27368397879 / 1000000000000) (-27368397878 / 1000000000000), orderedInterval (-31319981355 / 1000000000000) (-31319981354 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1298785559645617 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41939189527 / 1000000000000) (-41939181861 / 1000000000000), orderedInterval (14268962447 / 1000000000000) (14268970114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (376438677784083 / 800000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3473739613 / 1000000000000) (3473739614 / 1000000000000), orderedInterval (36614140249 / 1000000000000) (36614140250 / 1000000000000)))) (orderedInterval (2172940230 / 1000000000000) (2172940693 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_chunkChecks0_2 :
    compactCertificate383.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1041249193633001 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-16726044049 / 1000000000000) (-16726044048 / 1000000000000), orderedInterval (-46506491490 / 1000000000000) (-46506491489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (882678472961761 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53690815711 / 1000000000000) (53690815764 / 1000000000000), orderedInterval (1373065646 / 1000000000000) (1373065700 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (552339204303883 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40506548391 / 1000000000000) (40506548392 / 1000000000000), orderedInterval (54347199853 / 1000000000000) (54347199854 / 1000000000000)))) (orderedInterval (954171846 / 1000000000000) (954171914 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (297049861071861 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-31925560980 / 1000000000000) (-31925559902 / 1000000000000), orderedInterval (87125648349 / 1000000000000) (87125649427 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (806548157238583 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54944285105 / 1000000000000) (54944285108 / 1000000000000), orderedInterval (11626951253 / 1000000000000) (11626951256 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1101272554786391 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16807697210 / 1000000000000) (-16807696880 / 1000000000000), orderedInterval (45083938376 / 1000000000000) (45083938706 / 1000000000000)))) (orderedInterval (631118666 / 1000000000000) (631118742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (465660795696117 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60603756981 / 1000000000000) (-60603756980 / 1000000000000), orderedInterval (-42115358572 / 1000000000000) (-42115358571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1892885281790357 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13401310902 / 1000000000000) (13401311009 / 1000000000000), orderedInterval (-34156437362 / 1000000000000) (-34156437255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1264359644239963 / 4000000000000) 0 (IntervalRat.scale (509 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18542771237 / 1000000000000) (18542771845 / 1000000000000), orderedInterval (-40897580523 / 1000000000000) (-40897579916 / 1000000000000)))) (orderedInterval (-4935345773 / 1000000000000) (-4935345579 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_chunkChecks0 :
    compactCertificate383.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate383.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate383_chunkChecks0_0
    compactCertificate383_chunkChecks0_1 compactCertificate383_chunkChecks0_2

theorem compactCertificate383_chunkChecks1_0 :
    compactCertificate383.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (509 / 2) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36427745789 / 1000000000000) (-36427745788 / 1000000000000), orderedInterval (-34199003156 / 1000000000000) (-34199003155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (749854192481609 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-14263770055 / 1000000000000) (-14263769917 / 1000000000000), orderedInterval (56540443365 / 1000000000000) (56540443503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (242487439121897 / 800000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34132405585 / 1000000000000) (34132453955 / 1000000000000), orderedInterval (-30638586709 / 1000000000000) (-30638538339 / 1000000000000)))) (orderedInterval (-15308520412 / 1000000000000) (-15308517009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (218805583203163 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-94326233303 / 1000000000000) (-94326221274 / 1000000000000), orderedInterval (53210903380 / 1000000000000) (53210915408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (587742574034911 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-4297545393 / 1000000000000) (-4297545391 / 1000000000000), orderedInterval (-65667942839 / 1000000000000) (-65667942837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1595835420717987 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27568219862 / 1000000000000) (-27568219861 / 1000000000000), orderedInterval (-28873859326 / 1000000000000) (-28873859325 / 1000000000000)))) (orderedInterval (1709376196 / 1000000000000) (1709376260 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1175485148070331 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28295285428 / 1000000000000) (-28295276742 / 1000000000000), orderedInterval (37003511694 / 1000000000000) (37003520380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2014213836721063 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35329627349 / 1000000000000) (35329629405 / 1000000000000), orderedInterval (-4043988853 / 1000000000000) (-4043986797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1483660795696117 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34688370303 / 1000000000000) (34688370304 / 1000000000000), orderedInterval (22604175790 / 1000000000000) (22604175791 / 1000000000000)))) (orderedInterval (1042986051 / 1000000000000) (1042986202 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_chunkChecks1_1 :
    compactCertificate383.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2276317201094491 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31591960249 / 1000000000000) (-31591960242 / 1000000000000), orderedInterval (-10955478849 / 1000000000000) (-10955478841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1314232348812739 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22029180493 / 1000000000000) (22029182296 / 1000000000000), orderedInterval (-38143017066 / 1000000000000) (-38143015262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2332128365542751 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16389072773 / 1000000000000) (-16389072416 / 1000000000000), orderedInterval (28707443699 / 1000000000000) (28707444056 / 1000000000000)))) (orderedInterval (10053373713 / 1000000000000) (10053374215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2178976834825019 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30585699768 / 1000000000000) (-30585622796 / 1000000000000), orderedInterval (15298107401 / 1000000000000) (15298184373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1555020685821227 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-697656802 / 1000000000000) (-697656801 / 1000000000000), orderedInterval (40461989415 / 1000000000000) (40461989417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1763227722104733 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37258233590 / 1000000000000) (37258237295 / 1000000000000), orderedInterval (-7528086887 / 1000000000000) (-7528083182 / 1000000000000)))) (orderedInterval (5319456617 / 1000000000000) (5319459674 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1469995448960077 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27368397879 / 1000000000000) (-27368397878 / 1000000000000), orderedInterval (-31319981355 / 1000000000000) (-31319981354 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1298785559645617 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41939189527 / 1000000000000) (-41939181861 / 1000000000000), orderedInterval (14268962447 / 1000000000000) (14268970114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (376438677784083 / 800000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3473739613 / 1000000000000) (3473739614 / 1000000000000), orderedInterval (36614140249 / 1000000000000) (36614140250 / 1000000000000)))) (orderedInterval (169245844 / 1000000000000) (169246440 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_chunkChecks1_2 :
    compactCertificate383.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1041249193633001 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-16726044049 / 1000000000000) (-16726044048 / 1000000000000), orderedInterval (-46506491490 / 1000000000000) (-46506491489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (882678472961761 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53690815711 / 1000000000000) (53690815764 / 1000000000000), orderedInterval (1373065646 / 1000000000000) (1373065700 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (552339204303883 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40506548391 / 1000000000000) (40506548392 / 1000000000000), orderedInterval (54347199853 / 1000000000000) (54347199854 / 1000000000000)))) (orderedInterval (8498444240 / 1000000000000) (8498444302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (297049861071861 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-31925560980 / 1000000000000) (-31925559902 / 1000000000000), orderedInterval (87125648349 / 1000000000000) (87125649427 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (806548157238583 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54944285105 / 1000000000000) (54944285108 / 1000000000000), orderedInterval (11626951253 / 1000000000000) (11626951256 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1101272554786391 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16807697210 / 1000000000000) (-16807696880 / 1000000000000), orderedInterval (45083938376 / 1000000000000) (45083938706 / 1000000000000)))) (orderedInterval (-4416244796 / 1000000000000) (-4416244735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (465660795696117 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60603756981 / 1000000000000) (-60603756980 / 1000000000000), orderedInterval (-42115358572 / 1000000000000) (-42115358571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1892885281790357 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13401310902 / 1000000000000) (13401311009 / 1000000000000), orderedInterval (-34156437362 / 1000000000000) (-34156437255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1264359644239963 / 4000000000000) 1 (IntervalRat.scale (509 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18542771237 / 1000000000000) (18542771845 / 1000000000000), orderedInterval (-40897580523 / 1000000000000) (-40897579916 / 1000000000000)))) (orderedInterval (14584254092 / 1000000000000) (14584254349 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_chunkChecks1 :
    compactCertificate383.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate383.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate383_chunkChecks1_0
    compactCertificate383_chunkChecks1_1 compactCertificate383_chunkChecks1_2

theorem compactCertificate383_chunkChecks2_0 :
    compactCertificate383.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (509 / 2) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36427745789 / 1000000000000) (-36427745788 / 1000000000000), orderedInterval (-34199003156 / 1000000000000) (-34199003155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (749854192481609 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-14263770055 / 1000000000000) (-14263769917 / 1000000000000), orderedInterval (56540443365 / 1000000000000) (56540443503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (242487439121897 / 800000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34132405585 / 1000000000000) (34132453955 / 1000000000000), orderedInterval (-30638586709 / 1000000000000) (-30638538339 / 1000000000000)))) (orderedInterval (11729832023 / 1000000000000) (11729836087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (218805583203163 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-94326233303 / 1000000000000) (-94326221274 / 1000000000000), orderedInterval (53210903380 / 1000000000000) (53210915408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (587742574034911 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-4297545393 / 1000000000000) (-4297545391 / 1000000000000), orderedInterval (-65667942839 / 1000000000000) (-65667942837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1595835420717987 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27568219862 / 1000000000000) (-27568219861 / 1000000000000), orderedInterval (-28873859326 / 1000000000000) (-28873859325 / 1000000000000)))) (orderedInterval (-4817792712 / 1000000000000) (-4817792657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1175485148070331 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28295285428 / 1000000000000) (-28295276742 / 1000000000000), orderedInterval (37003511694 / 1000000000000) (37003520380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2014213836721063 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35329627349 / 1000000000000) (35329629405 / 1000000000000), orderedInterval (-4043988853 / 1000000000000) (-4043986797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1483660795696117 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34688370303 / 1000000000000) (34688370304 / 1000000000000), orderedInterval (22604175790 / 1000000000000) (22604175791 / 1000000000000)))) (orderedInterval (2481213192 / 1000000000000) (2481213486 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_chunkChecks2_1 :
    compactCertificate383.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2276317201094491 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31591960249 / 1000000000000) (-31591960242 / 1000000000000), orderedInterval (-10955478849 / 1000000000000) (-10955478841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1314232348812739 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22029180493 / 1000000000000) (22029182296 / 1000000000000), orderedInterval (-38143017066 / 1000000000000) (-38143015262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2332128365542751 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16389072773 / 1000000000000) (-16389072416 / 1000000000000), orderedInterval (28707443699 / 1000000000000) (28707444056 / 1000000000000)))) (orderedInterval (-18600109845 / 1000000000000) (-18600108900 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2178976834825019 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30585699768 / 1000000000000) (-30585622796 / 1000000000000), orderedInterval (15298107401 / 1000000000000) (15298184373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1555020685821227 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-697656802 / 1000000000000) (-697656801 / 1000000000000), orderedInterval (40461989415 / 1000000000000) (40461989417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1763227722104733 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37258233590 / 1000000000000) (37258237295 / 1000000000000), orderedInterval (-7528086887 / 1000000000000) (-7528083182 / 1000000000000)))) (orderedInterval (-1831082909 / 1000000000000) (-1831076392 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1469995448960077 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27368397879 / 1000000000000) (-27368397878 / 1000000000000), orderedInterval (-31319981355 / 1000000000000) (-31319981354 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1298785559645617 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41939189527 / 1000000000000) (-41939181861 / 1000000000000), orderedInterval (14268962447 / 1000000000000) (14268970114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (376438677784083 / 800000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3473739613 / 1000000000000) (3473739614 / 1000000000000), orderedInterval (36614140249 / 1000000000000) (36614140250 / 1000000000000)))) (orderedInterval (-3552308187 / 1000000000000) (-3552307418 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_chunkChecks2_2 :
    compactCertificate383.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1041249193633001 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-16726044049 / 1000000000000) (-16726044048 / 1000000000000), orderedInterval (-46506491490 / 1000000000000) (-46506491489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (882678472961761 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53690815711 / 1000000000000) (53690815764 / 1000000000000), orderedInterval (1373065646 / 1000000000000) (1373065700 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (552339204303883 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40506548391 / 1000000000000) (40506548392 / 1000000000000), orderedInterval (54347199853 / 1000000000000) (54347199854 / 1000000000000)))) (orderedInterval (-934835902 / 1000000000000) (-934835842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (297049861071861 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-31925560980 / 1000000000000) (-31925559902 / 1000000000000), orderedInterval (87125648349 / 1000000000000) (87125649427 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (806548157238583 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54944285105 / 1000000000000) (54944285108 / 1000000000000), orderedInterval (11626951253 / 1000000000000) (11626951256 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1101272554786391 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16807697210 / 1000000000000) (-16807696880 / 1000000000000), orderedInterval (45083938376 / 1000000000000) (45083938706 / 1000000000000)))) (orderedInterval (-757861251 / 1000000000000) (-757861192 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (465660795696117 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60603756981 / 1000000000000) (-60603756980 / 1000000000000), orderedInterval (-42115358572 / 1000000000000) (-42115358571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1892885281790357 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13401310902 / 1000000000000) (13401311009 / 1000000000000), orderedInterval (-34156437362 / 1000000000000) (-34156437255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1264359644239963 / 4000000000000) 2 (IntervalRat.scale (509 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18542771237 / 1000000000000) (18542771845 / 1000000000000), orderedInterval (-40897580523 / 1000000000000) (-40897579916 / 1000000000000)))) (orderedInterval (9157601982 / 1000000000000) (9157602335 / 1000000000000))) = true
  rfl'

theorem compactCertificate383_chunkChecks2 :
    compactCertificate383.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate383.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate383_chunkChecks2_0
    compactCertificate383_chunkChecks2_1 compactCertificate383_chunkChecks2_2

theorem compactCertificate383_chunkChecks3_0 :
    compactCertificate383.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (509 / 2) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36427745789 / 1000000000000) (-36427745788 / 1000000000000), orderedInterval (-34199003156 / 1000000000000) (-34199003155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (749854192481609 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-14263770055 / 1000000000000) (-14263769917 / 1000000000000), orderedInterval (56540443365 / 1000000000000) (56540443503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (242487439121897 / 800000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34132405585 / 1000000000000) (34132453955 / 1000000000000), orderedInterval (-30638586709 / 1000000000000) (-30638538339 / 1000000000000)))) (orderedInterval (16335796623 / 1000000000000) (16335801462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (218805583203163 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-94326233303 / 1000000000000) (-94326221274 / 1000000000000), orderedInterval (53210903380 / 1000000000000) (53210915408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (587742574034911 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-4297545393 / 1000000000000) (-4297545391 / 1000000000000), orderedInterval (-65667942839 / 1000000000000) (-65667942837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1595835420717987 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27568219862 / 1000000000000) (-27568219861 / 1000000000000), orderedInterval (-28873859326 / 1000000000000) (-28873859325 / 1000000000000)))) (orderedInterval (-7421253816 / 1000000000000) (-7421253742 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1175485148070331 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28295285428 / 1000000000000) (-28295276742 / 1000000000000), orderedInterval (37003511694 / 1000000000000) (37003520380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2014213836721063 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35329627349 / 1000000000000) (35329629405 / 1000000000000), orderedInterval (-4043988853 / 1000000000000) (-4043986797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1483660795696117 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34688370303 / 1000000000000) (34688370304 / 1000000000000), orderedInterval (22604175790 / 1000000000000) (22604175791 / 1000000000000)))) (orderedInterval (-2667086632 / 1000000000000) (-2667086059 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate383_chunkChecks3_1 :
    compactCertificate383.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2276317201094491 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31591960249 / 1000000000000) (-31591960242 / 1000000000000), orderedInterval (-10955478849 / 1000000000000) (-10955478841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1314232348812739 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22029180493 / 1000000000000) (22029182296 / 1000000000000), orderedInterval (-38143017066 / 1000000000000) (-38143015262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2332128365542751 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16389072773 / 1000000000000) (-16389072416 / 1000000000000), orderedInterval (28707443699 / 1000000000000) (28707444056 / 1000000000000)))) (orderedInterval (-64675457721 / 1000000000000) (-64675455823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2178976834825019 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30585699768 / 1000000000000) (-30585622796 / 1000000000000), orderedInterval (15298107401 / 1000000000000) (15298184373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1555020685821227 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-697656802 / 1000000000000) (-697656801 / 1000000000000), orderedInterval (40461989415 / 1000000000000) (40461989417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1763227722104733 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37258233590 / 1000000000000) (37258237295 / 1000000000000), orderedInterval (-7528086887 / 1000000000000) (-7528083182 / 1000000000000)))) (orderedInterval (-11119780914 / 1000000000000) (-11119767025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1469995448960077 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27368397879 / 1000000000000) (-27368397878 / 1000000000000), orderedInterval (-31319981355 / 1000000000000) (-31319981354 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1298785559645617 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41939189527 / 1000000000000) (-41939181861 / 1000000000000), orderedInterval (14268962447 / 1000000000000) (14268970114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (376438677784083 / 800000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3473739613 / 1000000000000) (3473739614 / 1000000000000), orderedInterval (36614140249 / 1000000000000) (36614140250 / 1000000000000)))) (orderedInterval (-3126545240 / 1000000000000) (-3126544244 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate383_chunkChecks3_2 :
    compactCertificate383.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1041249193633001 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-16726044049 / 1000000000000) (-16726044048 / 1000000000000), orderedInterval (-46506491490 / 1000000000000) (-46506491489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (882678472961761 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53690815711 / 1000000000000) (53690815764 / 1000000000000), orderedInterval (1373065646 / 1000000000000) (1373065700 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (552339204303883 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40506548391 / 1000000000000) (40506548392 / 1000000000000), orderedInterval (54347199853 / 1000000000000) (54347199854 / 1000000000000)))) (orderedInterval (-8185370754 / 1000000000000) (-8185370696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (297049861071861 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-31925560980 / 1000000000000) (-31925559902 / 1000000000000), orderedInterval (87125648349 / 1000000000000) (87125649427 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (806548157238583 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54944285105 / 1000000000000) (54944285108 / 1000000000000), orderedInterval (11626951253 / 1000000000000) (11626951256 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1101272554786391 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16807697210 / 1000000000000) (-16807696880 / 1000000000000), orderedInterval (45083938376 / 1000000000000) (45083938706 / 1000000000000)))) (orderedInterval (4548401706 / 1000000000000) (4548401767 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (465660795696117 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60603756981 / 1000000000000) (-60603756980 / 1000000000000), orderedInterval (-42115358572 / 1000000000000) (-42115358571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1892885281790357 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13401310902 / 1000000000000) (13401311009 / 1000000000000), orderedInterval (-34156437362 / 1000000000000) (-34156437255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1264359644239963 / 4000000000000) 3 (IntervalRat.scale (509 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18542771237 / 1000000000000) (18542771845 / 1000000000000), orderedInterval (-40897580523 / 1000000000000) (-40897579916 / 1000000000000)))) (orderedInterval (-32587501913 / 1000000000000) (-32587501412 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate383_chunkChecks3 :
    compactCertificate383.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate383.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate383_chunkChecks3_0
    compactCertificate383_chunkChecks3_1 compactCertificate383_chunkChecks3_2

theorem compactCertificate383_chunkChecks4_0 :
    compactCertificate383.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (509 / 2) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36427745789 / 1000000000000) (-36427745788 / 1000000000000), orderedInterval (-34199003156 / 1000000000000) (-34199003155 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (749854192481609 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-14263770055 / 1000000000000) (-14263769917 / 1000000000000), orderedInterval (56540443365 / 1000000000000) (56540443503 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (242487439121897 / 800000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34132405585 / 1000000000000) (34132453955 / 1000000000000), orderedInterval (-30638586709 / 1000000000000) (-30638538339 / 1000000000000)))) (orderedInterval (-10575945453 / 1000000000000) (-10575939672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (218805583203163 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-94326233303 / 1000000000000) (-94326221274 / 1000000000000), orderedInterval (53210903380 / 1000000000000) (53210915408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (587742574034911 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-4297545393 / 1000000000000) (-4297545391 / 1000000000000), orderedInterval (-65667942839 / 1000000000000) (-65667942837 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1595835420717987 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27568219862 / 1000000000000) (-27568219861 / 1000000000000), orderedInterval (-28873859326 / 1000000000000) (-28873859325 / 1000000000000)))) (orderedInterval (11878215266 / 1000000000000) (11878215378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1175485148070331 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-28295285428 / 1000000000000) (-28295276742 / 1000000000000), orderedInterval (37003511694 / 1000000000000) (37003520380 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2014213836721063 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (35329627349 / 1000000000000) (35329629405 / 1000000000000), orderedInterval (-4043988853 / 1000000000000) (-4043986797 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1483660795696117 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (34688370303 / 1000000000000) (34688370304 / 1000000000000), orderedInterval (22604175790 / 1000000000000) (22604175791 / 1000000000000)))) (orderedInterval (-12897501180 / 1000000000000) (-12897500055 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate383_chunkChecks4_1 :
    compactCertificate383.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2276317201094491 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-31591960249 / 1000000000000) (-31591960242 / 1000000000000), orderedInterval (-10955478849 / 1000000000000) (-10955478841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1314232348812739 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (22029180493 / 1000000000000) (22029182296 / 1000000000000), orderedInterval (-38143017066 / 1000000000000) (-38143015262 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2332128365542751 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16389072773 / 1000000000000) (-16389072416 / 1000000000000), orderedInterval (28707443699 / 1000000000000) (28707444056 / 1000000000000)))) (orderedInterval (81208677523 / 1000000000000) (81208681511 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2178976834825019 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30585699768 / 1000000000000) (-30585622796 / 1000000000000), orderedInterval (15298107401 / 1000000000000) (15298184373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1555020685821227 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-697656802 / 1000000000000) (-697656801 / 1000000000000), orderedInterval (40461989415 / 1000000000000) (40461989417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1763227722104733 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37258233590 / 1000000000000) (37258237295 / 1000000000000), orderedInterval (-7528086887 / 1000000000000) (-7528083182 / 1000000000000)))) (orderedInterval (9621365008 / 1000000000000) (9621394693 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1469995448960077 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27368397879 / 1000000000000) (-27368397878 / 1000000000000), orderedInterval (-31319981355 / 1000000000000) (-31319981354 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1298785559645617 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-41939189527 / 1000000000000) (-41939181861 / 1000000000000), orderedInterval (14268962447 / 1000000000000) (14268970114 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (376438677784083 / 800000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3473739613 / 1000000000000) (3473739614 / 1000000000000), orderedInterval (36614140249 / 1000000000000) (36614140250 / 1000000000000)))) (orderedInterval (6048619949 / 1000000000000) (6048621247 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate383_chunkChecks4_2 :
    compactCertificate383.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1041249193633001 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-16726044049 / 1000000000000) (-16726044048 / 1000000000000), orderedInterval (-46506491490 / 1000000000000) (-46506491489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (882678472961761 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (53690815711 / 1000000000000) (53690815764 / 1000000000000), orderedInterval (1373065646 / 1000000000000) (1373065700 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (552339204303883 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (40506548391 / 1000000000000) (40506548392 / 1000000000000), orderedInterval (54347199853 / 1000000000000) (54347199854 / 1000000000000)))) (orderedInterval (1388116213 / 1000000000000) (1388116269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (297049861071861 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-31925560980 / 1000000000000) (-31925559902 / 1000000000000), orderedInterval (87125648349 / 1000000000000) (87125649427 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (806548157238583 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54944285105 / 1000000000000) (54944285108 / 1000000000000), orderedInterval (11626951253 / 1000000000000) (11626951256 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1101272554786391 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-16807697210 / 1000000000000) (-16807696880 / 1000000000000), orderedInterval (45083938376 / 1000000000000) (45083938706 / 1000000000000)))) (orderedInterval (1241544346 / 1000000000000) (1241544411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (465660795696117 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-60603756981 / 1000000000000) (-60603756980 / 1000000000000), orderedInterval (-42115358572 / 1000000000000) (-42115358571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1892885281790357 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13401310902 / 1000000000000) (13401311009 / 1000000000000), orderedInterval (-34156437362 / 1000000000000) (-34156437255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1264359644239963 / 4000000000000) 4 (IntervalRat.scale (509 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (18542771237 / 1000000000000) (18542771845 / 1000000000000), orderedInterval (-40897580523 / 1000000000000) (-40897579916 / 1000000000000)))) (orderedInterval (-21078718452 / 1000000000000) (-21078717712 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate383_chunkChecks4 :
    compactCertificate383.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate383.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate383_chunkChecks4_0
    compactCertificate383_chunkChecks4_1 compactCertificate383_chunkChecks4_2

theorem compactCertificate383_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate383.chunkCheck r b = true :=
  compactCertificate383.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate383_chunkChecks0
    · exact compactCertificate383_chunkChecks1
    · exact compactCertificate383_chunkChecks2
    · exact compactCertificate383_chunkChecks3
    · exact compactCertificate383_chunkChecks4)

theorem compactCertificate383_coefficient0 :
    compactCertificate383.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate383_coefficient1 :
    compactCertificate383.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate383_coefficient2 :
    compactCertificate383.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate383_coefficient3 :
    compactCertificate383.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate383_coefficient4 :
    compactCertificate383.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate383_coefficients : ∀ r : Fin 5,
    compactCertificate383.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate383_coefficient0
  · exact compactCertificate383_coefficient1
  · exact compactCertificate383_coefficient2
  · exact compactCertificate383_coefficient3
  · exact compactCertificate383_coefficient4

theorem compactCertificate383_lower : (1 : ℚ) ≤ compactCertificate383.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate383, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate383_proves {t : ℝ} (ht : t ∈ compactCertificate383.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate383.proves compactCertificate383_states compactCertificate383_chunks
    compactCertificate383_coefficients compactCertificate383_lower ht

end Erdos232
