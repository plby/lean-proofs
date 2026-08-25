/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate319 : CompactCertificate where
  left := 383 / 2
  right := 192
  center := 767 / 4
  grid := fun i =>
    match i.val with
    | 0 => 61
    | 1 => 45
    | 2 => 73
    | 3 => 13
    | 4 => 35
    | 5 => 96
    | 6 => 71
    | 7 => 121
    | 8 => 89
    | 9 => 137
    | 10 => 79
    | 11 => 140
    | 12 => 131
    | 13 => 93
    | 14 => 106
    | 15 => 88
    | 16 => 78
    | 17 => 113
    | 18 => 62
    | 19 => 53
    | 20 => 33
    | 21 => 18
    | 22 => 48
    | 23 => 66
    | 24 => 28
    | 25 => 114
    | _ => 76
  point := fun i =>
    match i.val with
    | 0 => 767 / 4
    | 1 => 1129937457040067 / 8000000000000
    | 2 => 365398557576611 / 1600000000000
    | 3 => 329712931860169 / 8000000000000
    | 4 => 885655312936693 / 8000000000000
    | 5 => 2404726459117281 / 8000000000000
    | 6 => 1771310625874153 / 8000000000000
    | 7 => 3035170948457869 / 8000000000000
    | 8 => 2235693183298471 / 8000000000000
    | 9 => 3430128277484233 / 8000000000000
    | 10 => 1980385484360257 / 8000000000000
    | 11 => 3514228794442613 / 8000000000000
    | 12 => 3283448393537897 / 8000000000000
    | 13 => 2343223705353401 / 8000000000000
    | 14 => 2656965938810079 / 8000000000000
    | 15 => 2215101197155951 / 8000000000000
    | 16 => 1957109084966971 / 8000000000000
    | 17 => 567246494814129 / 1600000000000
    | 18 => 1569033657203363 / 8000000000000
    | 19 => 1330087207783243 / 8000000000000
    | 20 => 832306816701529 / 8000000000000
    | 21 => 447617374149543 / 8000000000000
    | 22 => 1215368244797629 / 8000000000000
    | 23 => 1659481433243933 / 8000000000000
    | 24 => 701693183298471 / 8000000000000
    | 25 => 2852343833267591 / 8000000000000
    | _ => 1905233491418569 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-45048836990 / 1000000000000) (-45048836989 / 1000000000000), orderedInterval (-35808161046 / 1000000000000) (-35808161045 / 1000000000000))
    | 1 => (orderedInterval (-40897990878 / 1000000000000) (-40897990877 / 1000000000000), orderedInterval (-53096688391 / 1000000000000) (-53096688390 / 1000000000000))
    | 2 => (orderedInterval (9312837294 / 1000000000000) (9312837331 / 1000000000000), orderedInterval (-51990529190 / 1000000000000) (-51990529153 / 1000000000000))
    | 3 => (orderedInterval (-113729706867 / 1000000000000) (-113729706866 / 1000000000000), orderedInterval (-48734641459 / 1000000000000) (-48734641458 / 1000000000000))
    | 4 => (orderedInterval (-75784252976 / 1000000000000) (-75784252955 / 1000000000000), orderedInterval (-2338303739 / 1000000000000) (-2338303718 / 1000000000000))
    | 5 => (orderedInterval (-9912991217 / 1000000000000) (-9912991178 / 1000000000000), orderedInterval (44956785930 / 1000000000000) (44956785970 / 1000000000000))
    | 6 => (orderedInterval (40440477106 / 1000000000000) (40440555377 / 1000000000000), orderedInterval (-35302324725 / 1000000000000) (-35302246454 / 1000000000000))
    | 7 => (orderedInterval (-1995187284 / 1000000000000) (-1995187283 / 1000000000000), orderedInterval (-40911932135 / 1000000000000) (-40911932133 / 1000000000000))
    | 8 => (orderedInterval (-28688732534 / 1000000000000) (-28688732533 / 1000000000000), orderedInterval (-38092866466 / 1000000000000) (-38092866465 / 1000000000000))
    | 9 => (orderedInterval (28873776135 / 1000000000000) (28873805140 / 1000000000000), orderedInterval (-25549875752 / 1000000000000) (-25549846747 / 1000000000000))
    | 10 => (orderedInterval (-7440826863 / 1000000000000) (-7440826862 / 1000000000000), orderedInterval (-50148100242 / 1000000000000) (-50148100241 / 1000000000000))
    | 11 => (orderedInterval (9076481702 / 1000000000000) (9076481703 / 1000000000000), orderedInterval (36960705214 / 1000000000000) (36960705215 / 1000000000000))
    | 12 => (orderedInterval (12855024375 / 1000000000000) (12855024469 / 1000000000000), orderedInterval (-37242662335 / 1000000000000) (-37242662241 / 1000000000000))
    | 13 => (orderedInterval (-46560034501 / 1000000000000) (-46560034436 / 1000000000000), orderedInterval (-2296144192 / 1000000000000) (-2296144127 / 1000000000000))
    | 14 => (orderedInterval (-4504025530 / 1000000000000) (-4504025525 / 1000000000000), orderedInterval (43556157239 / 1000000000000) (43556157245 / 1000000000000))
    | 15 => (orderedInterval (44903932142 / 1000000000000) (44903932143 / 1000000000000), orderedInterval (16736550698 / 1000000000000) (16736550699 / 1000000000000))
    | 16 => (orderedInterval (18888238505 / 1000000000000) (18888238506 / 1000000000000), orderedInterval (47348363423 / 1000000000000) (47348363424 / 1000000000000))
    | 17 => (orderedInterval (-13093743801 / 1000000000000) (-13093743800 / 1000000000000), orderedInterval (-40283302660 / 1000000000000) (-40283302659 / 1000000000000))
    | 18 => (orderedInterval (48136096095 / 1000000000000) (48136136040 / 1000000000000), orderedInterval (-30599446599 / 1000000000000) (-30599406655 / 1000000000000))
    | 19 => (orderedInterval (-31874582225 / 1000000000000) (-31874582224 / 1000000000000), orderedInterval (-52942431129 / 1000000000000) (-52942431128 / 1000000000000))
    | 20 => (orderedInterval (-71399899042 / 1000000000000) (-71399899041 / 1000000000000), orderedInterval (-31611439272 / 1000000000000) (-31611439271 / 1000000000000))
    | 21 => (orderedInterval (19795606890 / 1000000000000) (19795606892 / 1000000000000), orderedInterval (104639549271 / 1000000000000) (104639549272 / 1000000000000))
    | 22 => (orderedInterval (61063199244 / 1000000000000) (61063202720 / 1000000000000), orderedInterval (-21688939702 / 1000000000000) (-21688936226 / 1000000000000))
    | 23 => (orderedInterval (42515793841 / 1000000000000) (42515793842 / 1000000000000), orderedInterval (35413876395 / 1000000000000) (35413876396 / 1000000000000))
    | 24 => (orderedInterval (43143746483 / 1000000000000) (43143746484 / 1000000000000), orderedInterval (73216799096 / 1000000000000) (73216799097 / 1000000000000))
    | 25 => (orderedInterval (-30708001263 / 1000000000000) (-30707971433 / 1000000000000), orderedInterval (29069827094 / 1000000000000) (29069856924 / 1000000000000))
    | _ => (orderedInterval (9155419770 / 1000000000000) (9155419771 / 1000000000000), orderedInterval (50866189241 / 1000000000000) (50866189242 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-17690383989 / 1000000000000) (-17690383972 / 1000000000000)
      | 1 => orderedInterval (-828417738 / 1000000000000) (-828417711 / 1000000000000)
      | 2 => orderedInterval (-631810510 / 1000000000000) (-631810498 / 1000000000000)
      | 3 => orderedInterval (-4391555277 / 1000000000000) (-4391550046 / 1000000000000)
      | 4 => orderedInterval (-4612130214 / 1000000000000) (-4612130183 / 1000000000000)
      | 5 => orderedInterval (-897626905 / 1000000000000) (-897626886 / 1000000000000)
      | 6 => orderedInterval (-8216947476 / 1000000000000) (-8216941040 / 1000000000000)
      | 7 => orderedInterval (-5009223060 / 1000000000000) (-5009222957 / 1000000000000)
      | _ => orderedInterval (1041968456 / 1000000000000) (1041970938 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-18191114152 / 1000000000000) (-18191114134 / 1000000000000)
      | 1 => orderedInterval (-4945694900 / 1000000000000) (-4945694869 / 1000000000000)
      | 2 => orderedInterval (1155019471 / 1000000000000) (1155019490 / 1000000000000)
      | 3 => orderedInterval (17391519122 / 1000000000000) (17391530804 / 1000000000000)
      | 4 => orderedInterval (725671121 / 1000000000000) (725671172 / 1000000000000)
      | 5 => orderedInterval (-5084861128 / 1000000000000) (-5084861101 / 1000000000000)
      | 6 => orderedInterval (7044192693 / 1000000000000) (7044199271 / 1000000000000)
      | 7 => orderedInterval (-3110049435 / 1000000000000) (-3110049351 / 1000000000000)
      | _ => orderedInterval (-16051600912 / 1000000000000) (-16051596322 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17382238239 / 1000000000000) (17382238261 / 1000000000000)
      | 1 => orderedInterval (-840647868 / 1000000000000) (-840647824 / 1000000000000)
      | 2 => orderedInterval (1225798564 / 1000000000000) (1225798598 / 1000000000000)
      | 3 => orderedInterval (19709140856 / 1000000000000) (19709167024 / 1000000000000)
      | 4 => orderedInterval (11264400631 / 1000000000000) (11264400715 / 1000000000000)
      | 5 => orderedInterval (1850765130 / 1000000000000) (1850765171 / 1000000000000)
      | 6 => orderedInterval (7343364573 / 1000000000000) (7343371333 / 1000000000000)
      | 7 => orderedInterval (4730175514 / 1000000000000) (4730175585 / 1000000000000)
      | _ => orderedInterval (-5963359562 / 1000000000000) (-5963351032 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (19453841370 / 1000000000000) (19453841395 / 1000000000000)
      | 1 => orderedInterval (12327258029 / 1000000000000) (12327258095 / 1000000000000)
      | 2 => orderedInterval (-6930847515 / 1000000000000) (-6930847453 / 1000000000000)
      | 3 => orderedInterval (-106036573131 / 1000000000000) (-106036514634 / 1000000000000)
      | 4 => orderedInterval (-4732851674 / 1000000000000) (-4732851531 / 1000000000000)
      | 5 => orderedInterval (11554237363 / 1000000000000) (11554237425 / 1000000000000)
      | 6 => orderedInterval (-7062646020 / 1000000000000) (-7062639109 / 1000000000000)
      | 7 => orderedInterval (3214621008 / 1000000000000) (3214621070 / 1000000000000)
      | _ => orderedInterval (33485978093 / 1000000000000) (33485993918 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-17070823276 / 1000000000000) (-17070823247 / 1000000000000)
      | 1 => orderedInterval (3822301672 / 1000000000000) (3822301773 / 1000000000000)
      | 2 => orderedInterval (-2112755047 / 1000000000000) (-2112754934 / 1000000000000)
      | 3 => orderedInterval (-93149380263 / 1000000000000) (-93149249170 / 1000000000000)
      | 4 => orderedInterval (-28587553016 / 1000000000000) (-28587552765 / 1000000000000)
      | 5 => orderedInterval (-4647544665 / 1000000000000) (-4647544568 / 1000000000000)
      | 6 => orderedInterval (-7532024895 / 1000000000000) (-7532017792 / 1000000000000)
      | 7 => orderedInterval (-5044509441 / 1000000000000) (-5044509387 / 1000000000000)
      | _ => orderedInterval (25455123353 / 1000000000000) (25455152816 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-41236126713 / 1000000000000) (-41236112355 / 1000000000000)
    | 1 => orderedInterval (-21066918120 / 1000000000000) (-21066895040 / 1000000000000)
    | 2 => orderedInterval (56701876077 / 1000000000000) (56701917831 / 1000000000000)
    | 3 => orderedInterval (-44726982477 / 1000000000000) (-44726900824 / 1000000000000)
    | _ => orderedInterval (-128867165578 / 1000000000000) (-128866997274 / 1000000000000)

theorem compactCertificate319_stateChecks0 :
    compactCertificate319.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (767 / 4)) (orderedInterval (-45048836990 / 1000000000000) (-45048836989 / 1000000000000), orderedInterval (-35808161046 / 1000000000000) (-35808161045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (1129937457040067 / 8000000000000)) (orderedInterval (-40897990878 / 1000000000000) (-40897990877 / 1000000000000), orderedInterval (-53096688391 / 1000000000000) (-53096688390 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (365398557576611 / 1600000000000)) (orderedInterval (9312837294 / 1000000000000) (9312837331 / 1000000000000), orderedInterval (-51990529190 / 1000000000000) (-51990529153 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_stateChecks1 :
    compactCertificate319.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (329712931860169 / 8000000000000)) (orderedInterval (-113729706867 / 1000000000000) (-113729706866 / 1000000000000), orderedInterval (-48734641459 / 1000000000000) (-48734641458 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (885655312936693 / 8000000000000)) (orderedInterval (-75784252976 / 1000000000000) (-75784252955 / 1000000000000), orderedInterval (-2338303739 / 1000000000000) (-2338303718 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (2404726459117281 / 8000000000000)) (orderedInterval (-9912991217 / 1000000000000) (-9912991178 / 1000000000000), orderedInterval (44956785930 / 1000000000000) (44956785970 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_stateChecks2 :
    compactCertificate319.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (1771310625874153 / 8000000000000)) (orderedInterval (40440477106 / 1000000000000) (40440555377 / 1000000000000), orderedInterval (-35302324725 / 1000000000000) (-35302246454 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (3035170948457869 / 8000000000000)) (orderedInterval (-1995187284 / 1000000000000) (-1995187283 / 1000000000000), orderedInterval (-40911932135 / 1000000000000) (-40911932133 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (2235693183298471 / 8000000000000)) (orderedInterval (-28688732534 / 1000000000000) (-28688732533 / 1000000000000), orderedInterval (-38092866466 / 1000000000000) (-38092866465 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_stateChecks3 :
    compactCertificate319.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (3430128277484233 / 8000000000000)) (orderedInterval (28873776135 / 1000000000000) (28873805140 / 1000000000000), orderedInterval (-25549875752 / 1000000000000) (-25549846747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (1980385484360257 / 8000000000000)) (orderedInterval (-7440826863 / 1000000000000) (-7440826862 / 1000000000000), orderedInterval (-50148100242 / 1000000000000) (-50148100241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (3514228794442613 / 8000000000000)) (orderedInterval (9076481702 / 1000000000000) (9076481703 / 1000000000000), orderedInterval (36960705214 / 1000000000000) (36960705215 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_stateChecks4 :
    compactCertificate319.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (3283448393537897 / 8000000000000)) (orderedInterval (12855024375 / 1000000000000) (12855024469 / 1000000000000), orderedInterval (-37242662335 / 1000000000000) (-37242662241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (2343223705353401 / 8000000000000)) (orderedInterval (-46560034501 / 1000000000000) (-46560034436 / 1000000000000), orderedInterval (-2296144192 / 1000000000000) (-2296144127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (2656965938810079 / 8000000000000)) (orderedInterval (-4504025530 / 1000000000000) (-4504025525 / 1000000000000), orderedInterval (43556157239 / 1000000000000) (43556157245 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_stateChecks5 :
    compactCertificate319.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (2215101197155951 / 8000000000000)) (orderedInterval (44903932142 / 1000000000000) (44903932143 / 1000000000000), orderedInterval (16736550698 / 1000000000000) (16736550699 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (1957109084966971 / 8000000000000)) (orderedInterval (18888238505 / 1000000000000) (18888238506 / 1000000000000), orderedInterval (47348363423 / 1000000000000) (47348363424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (567246494814129 / 1600000000000)) (orderedInterval (-13093743801 / 1000000000000) (-13093743800 / 1000000000000), orderedInterval (-40283302660 / 1000000000000) (-40283302659 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_stateChecks6 :
    compactCertificate319.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (1569033657203363 / 8000000000000)) (orderedInterval (48136096095 / 1000000000000) (48136136040 / 1000000000000), orderedInterval (-30599446599 / 1000000000000) (-30599406655 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (1330087207783243 / 8000000000000)) (orderedInterval (-31874582225 / 1000000000000) (-31874582224 / 1000000000000), orderedInterval (-52942431129 / 1000000000000) (-52942431128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (832306816701529 / 8000000000000)) (orderedInterval (-71399899042 / 1000000000000) (-71399899041 / 1000000000000), orderedInterval (-31611439272 / 1000000000000) (-31611439271 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_stateChecks7 :
    compactCertificate319.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (447617374149543 / 8000000000000)) (orderedInterval (19795606890 / 1000000000000) (19795606892 / 1000000000000), orderedInterval (104639549271 / 1000000000000) (104639549272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (1215368244797629 / 8000000000000)) (orderedInterval (61063199244 / 1000000000000) (61063202720 / 1000000000000), orderedInterval (-21688939702 / 1000000000000) (-21688936226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (1659481433243933 / 8000000000000)) (orderedInterval (42515793841 / 1000000000000) (42515793842 / 1000000000000), orderedInterval (35413876395 / 1000000000000) (35413876396 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_stateChecks8 :
    compactCertificate319.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (701693183298471 / 8000000000000)) (orderedInterval (43143746483 / 1000000000000) (43143746484 / 1000000000000), orderedInterval (73216799096 / 1000000000000) (73216799097 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (2852343833267591 / 8000000000000)) (orderedInterval (-30708001263 / 1000000000000) (-30707971433 / 1000000000000), orderedInterval (29069827094 / 1000000000000) (29069856924 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (1905233491418569 / 8000000000000)) (orderedInterval (9155419770 / 1000000000000) (9155419771 / 1000000000000), orderedInterval (50866189241 / 1000000000000) (50866189242 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_states : ∀ j,
    BesselStateValid (compactCertificate319.point j) (compactCertificate319.state j) :=
  compactCertificate319.statesValid_of_checks3 compactCertificate319_stateChecks0
    compactCertificate319_stateChecks1 compactCertificate319_stateChecks2
    compactCertificate319_stateChecks3 compactCertificate319_stateChecks4
    compactCertificate319_stateChecks5 compactCertificate319_stateChecks6
    compactCertificate319_stateChecks7 compactCertificate319_stateChecks8

theorem compactCertificate319_chunkChecks0_0 :
    compactCertificate319.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (767 / 4) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45048836990 / 1000000000000) (-45048836989 / 1000000000000), orderedInterval (-35808161046 / 1000000000000) (-35808161045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1129937457040067 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40897990878 / 1000000000000) (-40897990877 / 1000000000000), orderedInterval (-53096688391 / 1000000000000) (-53096688390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (365398557576611 / 1600000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9312837294 / 1000000000000) (9312837331 / 1000000000000), orderedInterval (-51990529190 / 1000000000000) (-51990529153 / 1000000000000)))) (orderedInterval (-17690383989 / 1000000000000) (-17690383972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (329712931860169 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-113729706867 / 1000000000000) (-113729706866 / 1000000000000), orderedInterval (-48734641459 / 1000000000000) (-48734641458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (885655312936693 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-75784252976 / 1000000000000) (-75784252955 / 1000000000000), orderedInterval (-2338303739 / 1000000000000) (-2338303718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2404726459117281 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9912991217 / 1000000000000) (-9912991178 / 1000000000000), orderedInterval (44956785930 / 1000000000000) (44956785970 / 1000000000000)))) (orderedInterval (-828417738 / 1000000000000) (-828417711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1771310625874153 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40440477106 / 1000000000000) (40440555377 / 1000000000000), orderedInterval (-35302324725 / 1000000000000) (-35302246454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3035170948457869 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1995187284 / 1000000000000) (-1995187283 / 1000000000000), orderedInterval (-40911932135 / 1000000000000) (-40911932133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2235693183298471 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28688732534 / 1000000000000) (-28688732533 / 1000000000000), orderedInterval (-38092866466 / 1000000000000) (-38092866465 / 1000000000000)))) (orderedInterval (-631810510 / 1000000000000) (-631810498 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_chunkChecks0_1 :
    compactCertificate319.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3430128277484233 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28873776135 / 1000000000000) (28873805140 / 1000000000000), orderedInterval (-25549875752 / 1000000000000) (-25549846747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1980385484360257 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7440826863 / 1000000000000) (-7440826862 / 1000000000000), orderedInterval (-50148100242 / 1000000000000) (-50148100241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3514228794442613 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9076481702 / 1000000000000) (9076481703 / 1000000000000), orderedInterval (36960705214 / 1000000000000) (36960705215 / 1000000000000)))) (orderedInterval (-4391555277 / 1000000000000) (-4391550046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3283448393537897 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12855024375 / 1000000000000) (12855024469 / 1000000000000), orderedInterval (-37242662335 / 1000000000000) (-37242662241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2343223705353401 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-46560034501 / 1000000000000) (-46560034436 / 1000000000000), orderedInterval (-2296144192 / 1000000000000) (-2296144127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2656965938810079 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4504025530 / 1000000000000) (-4504025525 / 1000000000000), orderedInterval (43556157239 / 1000000000000) (43556157245 / 1000000000000)))) (orderedInterval (-4612130214 / 1000000000000) (-4612130183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2215101197155951 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44903932142 / 1000000000000) (44903932143 / 1000000000000), orderedInterval (16736550698 / 1000000000000) (16736550699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1957109084966971 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18888238505 / 1000000000000) (18888238506 / 1000000000000), orderedInterval (47348363423 / 1000000000000) (47348363424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (567246494814129 / 1600000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13093743801 / 1000000000000) (-13093743800 / 1000000000000), orderedInterval (-40283302660 / 1000000000000) (-40283302659 / 1000000000000)))) (orderedInterval (-897626905 / 1000000000000) (-897626886 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_chunkChecks0_2 :
    compactCertificate319.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1569033657203363 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48136096095 / 1000000000000) (48136136040 / 1000000000000), orderedInterval (-30599446599 / 1000000000000) (-30599406655 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1330087207783243 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31874582225 / 1000000000000) (-31874582224 / 1000000000000), orderedInterval (-52942431129 / 1000000000000) (-52942431128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (832306816701529 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71399899042 / 1000000000000) (-71399899041 / 1000000000000), orderedInterval (-31611439272 / 1000000000000) (-31611439271 / 1000000000000)))) (orderedInterval (-8216947476 / 1000000000000) (-8216941040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (447617374149543 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (19795606890 / 1000000000000) (19795606892 / 1000000000000), orderedInterval (104639549271 / 1000000000000) (104639549272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1215368244797629 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (61063199244 / 1000000000000) (61063202720 / 1000000000000), orderedInterval (-21688939702 / 1000000000000) (-21688936226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1659481433243933 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42515793841 / 1000000000000) (42515793842 / 1000000000000), orderedInterval (35413876395 / 1000000000000) (35413876396 / 1000000000000)))) (orderedInterval (-5009223060 / 1000000000000) (-5009222957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (701693183298471 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43143746483 / 1000000000000) (43143746484 / 1000000000000), orderedInterval (73216799096 / 1000000000000) (73216799097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2852343833267591 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30708001263 / 1000000000000) (-30707971433 / 1000000000000), orderedInterval (29069827094 / 1000000000000) (29069856924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1905233491418569 / 8000000000000) 0 (IntervalRat.scale (767 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9155419770 / 1000000000000) (9155419771 / 1000000000000), orderedInterval (50866189241 / 1000000000000) (50866189242 / 1000000000000)))) (orderedInterval (1041968456 / 1000000000000) (1041970938 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_chunkChecks0 :
    compactCertificate319.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate319.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate319_chunkChecks0_0
    compactCertificate319_chunkChecks0_1 compactCertificate319_chunkChecks0_2

theorem compactCertificate319_chunkChecks1_0 :
    compactCertificate319.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (767 / 4) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45048836990 / 1000000000000) (-45048836989 / 1000000000000), orderedInterval (-35808161046 / 1000000000000) (-35808161045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1129937457040067 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40897990878 / 1000000000000) (-40897990877 / 1000000000000), orderedInterval (-53096688391 / 1000000000000) (-53096688390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (365398557576611 / 1600000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9312837294 / 1000000000000) (9312837331 / 1000000000000), orderedInterval (-51990529190 / 1000000000000) (-51990529153 / 1000000000000)))) (orderedInterval (-18191114152 / 1000000000000) (-18191114134 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (329712931860169 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-113729706867 / 1000000000000) (-113729706866 / 1000000000000), orderedInterval (-48734641459 / 1000000000000) (-48734641458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (885655312936693 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-75784252976 / 1000000000000) (-75784252955 / 1000000000000), orderedInterval (-2338303739 / 1000000000000) (-2338303718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2404726459117281 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9912991217 / 1000000000000) (-9912991178 / 1000000000000), orderedInterval (44956785930 / 1000000000000) (44956785970 / 1000000000000)))) (orderedInterval (-4945694900 / 1000000000000) (-4945694869 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1771310625874153 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40440477106 / 1000000000000) (40440555377 / 1000000000000), orderedInterval (-35302324725 / 1000000000000) (-35302246454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3035170948457869 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1995187284 / 1000000000000) (-1995187283 / 1000000000000), orderedInterval (-40911932135 / 1000000000000) (-40911932133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2235693183298471 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28688732534 / 1000000000000) (-28688732533 / 1000000000000), orderedInterval (-38092866466 / 1000000000000) (-38092866465 / 1000000000000)))) (orderedInterval (1155019471 / 1000000000000) (1155019490 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_chunkChecks1_1 :
    compactCertificate319.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3430128277484233 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28873776135 / 1000000000000) (28873805140 / 1000000000000), orderedInterval (-25549875752 / 1000000000000) (-25549846747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1980385484360257 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7440826863 / 1000000000000) (-7440826862 / 1000000000000), orderedInterval (-50148100242 / 1000000000000) (-50148100241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3514228794442613 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9076481702 / 1000000000000) (9076481703 / 1000000000000), orderedInterval (36960705214 / 1000000000000) (36960705215 / 1000000000000)))) (orderedInterval (17391519122 / 1000000000000) (17391530804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3283448393537897 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12855024375 / 1000000000000) (12855024469 / 1000000000000), orderedInterval (-37242662335 / 1000000000000) (-37242662241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2343223705353401 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-46560034501 / 1000000000000) (-46560034436 / 1000000000000), orderedInterval (-2296144192 / 1000000000000) (-2296144127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2656965938810079 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4504025530 / 1000000000000) (-4504025525 / 1000000000000), orderedInterval (43556157239 / 1000000000000) (43556157245 / 1000000000000)))) (orderedInterval (725671121 / 1000000000000) (725671172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2215101197155951 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44903932142 / 1000000000000) (44903932143 / 1000000000000), orderedInterval (16736550698 / 1000000000000) (16736550699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1957109084966971 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18888238505 / 1000000000000) (18888238506 / 1000000000000), orderedInterval (47348363423 / 1000000000000) (47348363424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (567246494814129 / 1600000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13093743801 / 1000000000000) (-13093743800 / 1000000000000), orderedInterval (-40283302660 / 1000000000000) (-40283302659 / 1000000000000)))) (orderedInterval (-5084861128 / 1000000000000) (-5084861101 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_chunkChecks1_2 :
    compactCertificate319.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1569033657203363 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48136096095 / 1000000000000) (48136136040 / 1000000000000), orderedInterval (-30599446599 / 1000000000000) (-30599406655 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1330087207783243 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31874582225 / 1000000000000) (-31874582224 / 1000000000000), orderedInterval (-52942431129 / 1000000000000) (-52942431128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (832306816701529 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71399899042 / 1000000000000) (-71399899041 / 1000000000000), orderedInterval (-31611439272 / 1000000000000) (-31611439271 / 1000000000000)))) (orderedInterval (7044192693 / 1000000000000) (7044199271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (447617374149543 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (19795606890 / 1000000000000) (19795606892 / 1000000000000), orderedInterval (104639549271 / 1000000000000) (104639549272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1215368244797629 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (61063199244 / 1000000000000) (61063202720 / 1000000000000), orderedInterval (-21688939702 / 1000000000000) (-21688936226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1659481433243933 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42515793841 / 1000000000000) (42515793842 / 1000000000000), orderedInterval (35413876395 / 1000000000000) (35413876396 / 1000000000000)))) (orderedInterval (-3110049435 / 1000000000000) (-3110049351 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (701693183298471 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43143746483 / 1000000000000) (43143746484 / 1000000000000), orderedInterval (73216799096 / 1000000000000) (73216799097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2852343833267591 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30708001263 / 1000000000000) (-30707971433 / 1000000000000), orderedInterval (29069827094 / 1000000000000) (29069856924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1905233491418569 / 8000000000000) 1 (IntervalRat.scale (767 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9155419770 / 1000000000000) (9155419771 / 1000000000000), orderedInterval (50866189241 / 1000000000000) (50866189242 / 1000000000000)))) (orderedInterval (-16051600912 / 1000000000000) (-16051596322 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_chunkChecks1 :
    compactCertificate319.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate319.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate319_chunkChecks1_0
    compactCertificate319_chunkChecks1_1 compactCertificate319_chunkChecks1_2

theorem compactCertificate319_chunkChecks2_0 :
    compactCertificate319.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (767 / 4) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45048836990 / 1000000000000) (-45048836989 / 1000000000000), orderedInterval (-35808161046 / 1000000000000) (-35808161045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1129937457040067 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40897990878 / 1000000000000) (-40897990877 / 1000000000000), orderedInterval (-53096688391 / 1000000000000) (-53096688390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (365398557576611 / 1600000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9312837294 / 1000000000000) (9312837331 / 1000000000000), orderedInterval (-51990529190 / 1000000000000) (-51990529153 / 1000000000000)))) (orderedInterval (17382238239 / 1000000000000) (17382238261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (329712931860169 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-113729706867 / 1000000000000) (-113729706866 / 1000000000000), orderedInterval (-48734641459 / 1000000000000) (-48734641458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (885655312936693 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-75784252976 / 1000000000000) (-75784252955 / 1000000000000), orderedInterval (-2338303739 / 1000000000000) (-2338303718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2404726459117281 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9912991217 / 1000000000000) (-9912991178 / 1000000000000), orderedInterval (44956785930 / 1000000000000) (44956785970 / 1000000000000)))) (orderedInterval (-840647868 / 1000000000000) (-840647824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1771310625874153 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40440477106 / 1000000000000) (40440555377 / 1000000000000), orderedInterval (-35302324725 / 1000000000000) (-35302246454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3035170948457869 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1995187284 / 1000000000000) (-1995187283 / 1000000000000), orderedInterval (-40911932135 / 1000000000000) (-40911932133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2235693183298471 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28688732534 / 1000000000000) (-28688732533 / 1000000000000), orderedInterval (-38092866466 / 1000000000000) (-38092866465 / 1000000000000)))) (orderedInterval (1225798564 / 1000000000000) (1225798598 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_chunkChecks2_1 :
    compactCertificate319.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3430128277484233 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28873776135 / 1000000000000) (28873805140 / 1000000000000), orderedInterval (-25549875752 / 1000000000000) (-25549846747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1980385484360257 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7440826863 / 1000000000000) (-7440826862 / 1000000000000), orderedInterval (-50148100242 / 1000000000000) (-50148100241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3514228794442613 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9076481702 / 1000000000000) (9076481703 / 1000000000000), orderedInterval (36960705214 / 1000000000000) (36960705215 / 1000000000000)))) (orderedInterval (19709140856 / 1000000000000) (19709167024 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3283448393537897 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12855024375 / 1000000000000) (12855024469 / 1000000000000), orderedInterval (-37242662335 / 1000000000000) (-37242662241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2343223705353401 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-46560034501 / 1000000000000) (-46560034436 / 1000000000000), orderedInterval (-2296144192 / 1000000000000) (-2296144127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2656965938810079 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4504025530 / 1000000000000) (-4504025525 / 1000000000000), orderedInterval (43556157239 / 1000000000000) (43556157245 / 1000000000000)))) (orderedInterval (11264400631 / 1000000000000) (11264400715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2215101197155951 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44903932142 / 1000000000000) (44903932143 / 1000000000000), orderedInterval (16736550698 / 1000000000000) (16736550699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1957109084966971 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18888238505 / 1000000000000) (18888238506 / 1000000000000), orderedInterval (47348363423 / 1000000000000) (47348363424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (567246494814129 / 1600000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13093743801 / 1000000000000) (-13093743800 / 1000000000000), orderedInterval (-40283302660 / 1000000000000) (-40283302659 / 1000000000000)))) (orderedInterval (1850765130 / 1000000000000) (1850765171 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_chunkChecks2_2 :
    compactCertificate319.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1569033657203363 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48136096095 / 1000000000000) (48136136040 / 1000000000000), orderedInterval (-30599446599 / 1000000000000) (-30599406655 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1330087207783243 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31874582225 / 1000000000000) (-31874582224 / 1000000000000), orderedInterval (-52942431129 / 1000000000000) (-52942431128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (832306816701529 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71399899042 / 1000000000000) (-71399899041 / 1000000000000), orderedInterval (-31611439272 / 1000000000000) (-31611439271 / 1000000000000)))) (orderedInterval (7343364573 / 1000000000000) (7343371333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (447617374149543 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (19795606890 / 1000000000000) (19795606892 / 1000000000000), orderedInterval (104639549271 / 1000000000000) (104639549272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1215368244797629 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (61063199244 / 1000000000000) (61063202720 / 1000000000000), orderedInterval (-21688939702 / 1000000000000) (-21688936226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1659481433243933 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42515793841 / 1000000000000) (42515793842 / 1000000000000), orderedInterval (35413876395 / 1000000000000) (35413876396 / 1000000000000)))) (orderedInterval (4730175514 / 1000000000000) (4730175585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (701693183298471 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43143746483 / 1000000000000) (43143746484 / 1000000000000), orderedInterval (73216799096 / 1000000000000) (73216799097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2852343833267591 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30708001263 / 1000000000000) (-30707971433 / 1000000000000), orderedInterval (29069827094 / 1000000000000) (29069856924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1905233491418569 / 8000000000000) 2 (IntervalRat.scale (767 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9155419770 / 1000000000000) (9155419771 / 1000000000000), orderedInterval (50866189241 / 1000000000000) (50866189242 / 1000000000000)))) (orderedInterval (-5963359562 / 1000000000000) (-5963351032 / 1000000000000))) = true
  rfl'

theorem compactCertificate319_chunkChecks2 :
    compactCertificate319.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate319.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate319_chunkChecks2_0
    compactCertificate319_chunkChecks2_1 compactCertificate319_chunkChecks2_2

theorem compactCertificate319_chunkChecks3_0 :
    compactCertificate319.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (767 / 4) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45048836990 / 1000000000000) (-45048836989 / 1000000000000), orderedInterval (-35808161046 / 1000000000000) (-35808161045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1129937457040067 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40897990878 / 1000000000000) (-40897990877 / 1000000000000), orderedInterval (-53096688391 / 1000000000000) (-53096688390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (365398557576611 / 1600000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9312837294 / 1000000000000) (9312837331 / 1000000000000), orderedInterval (-51990529190 / 1000000000000) (-51990529153 / 1000000000000)))) (orderedInterval (19453841370 / 1000000000000) (19453841395 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (329712931860169 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-113729706867 / 1000000000000) (-113729706866 / 1000000000000), orderedInterval (-48734641459 / 1000000000000) (-48734641458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (885655312936693 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-75784252976 / 1000000000000) (-75784252955 / 1000000000000), orderedInterval (-2338303739 / 1000000000000) (-2338303718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2404726459117281 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9912991217 / 1000000000000) (-9912991178 / 1000000000000), orderedInterval (44956785930 / 1000000000000) (44956785970 / 1000000000000)))) (orderedInterval (12327258029 / 1000000000000) (12327258095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1771310625874153 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40440477106 / 1000000000000) (40440555377 / 1000000000000), orderedInterval (-35302324725 / 1000000000000) (-35302246454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3035170948457869 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1995187284 / 1000000000000) (-1995187283 / 1000000000000), orderedInterval (-40911932135 / 1000000000000) (-40911932133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2235693183298471 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28688732534 / 1000000000000) (-28688732533 / 1000000000000), orderedInterval (-38092866466 / 1000000000000) (-38092866465 / 1000000000000)))) (orderedInterval (-6930847515 / 1000000000000) (-6930847453 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate319_chunkChecks3_1 :
    compactCertificate319.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3430128277484233 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28873776135 / 1000000000000) (28873805140 / 1000000000000), orderedInterval (-25549875752 / 1000000000000) (-25549846747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1980385484360257 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7440826863 / 1000000000000) (-7440826862 / 1000000000000), orderedInterval (-50148100242 / 1000000000000) (-50148100241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3514228794442613 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9076481702 / 1000000000000) (9076481703 / 1000000000000), orderedInterval (36960705214 / 1000000000000) (36960705215 / 1000000000000)))) (orderedInterval (-106036573131 / 1000000000000) (-106036514634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3283448393537897 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12855024375 / 1000000000000) (12855024469 / 1000000000000), orderedInterval (-37242662335 / 1000000000000) (-37242662241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2343223705353401 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-46560034501 / 1000000000000) (-46560034436 / 1000000000000), orderedInterval (-2296144192 / 1000000000000) (-2296144127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2656965938810079 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4504025530 / 1000000000000) (-4504025525 / 1000000000000), orderedInterval (43556157239 / 1000000000000) (43556157245 / 1000000000000)))) (orderedInterval (-4732851674 / 1000000000000) (-4732851531 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2215101197155951 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44903932142 / 1000000000000) (44903932143 / 1000000000000), orderedInterval (16736550698 / 1000000000000) (16736550699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1957109084966971 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18888238505 / 1000000000000) (18888238506 / 1000000000000), orderedInterval (47348363423 / 1000000000000) (47348363424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (567246494814129 / 1600000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13093743801 / 1000000000000) (-13093743800 / 1000000000000), orderedInterval (-40283302660 / 1000000000000) (-40283302659 / 1000000000000)))) (orderedInterval (11554237363 / 1000000000000) (11554237425 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate319_chunkChecks3_2 :
    compactCertificate319.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1569033657203363 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48136096095 / 1000000000000) (48136136040 / 1000000000000), orderedInterval (-30599446599 / 1000000000000) (-30599406655 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1330087207783243 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31874582225 / 1000000000000) (-31874582224 / 1000000000000), orderedInterval (-52942431129 / 1000000000000) (-52942431128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (832306816701529 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71399899042 / 1000000000000) (-71399899041 / 1000000000000), orderedInterval (-31611439272 / 1000000000000) (-31611439271 / 1000000000000)))) (orderedInterval (-7062646020 / 1000000000000) (-7062639109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (447617374149543 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (19795606890 / 1000000000000) (19795606892 / 1000000000000), orderedInterval (104639549271 / 1000000000000) (104639549272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1215368244797629 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (61063199244 / 1000000000000) (61063202720 / 1000000000000), orderedInterval (-21688939702 / 1000000000000) (-21688936226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1659481433243933 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42515793841 / 1000000000000) (42515793842 / 1000000000000), orderedInterval (35413876395 / 1000000000000) (35413876396 / 1000000000000)))) (orderedInterval (3214621008 / 1000000000000) (3214621070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (701693183298471 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43143746483 / 1000000000000) (43143746484 / 1000000000000), orderedInterval (73216799096 / 1000000000000) (73216799097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2852343833267591 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30708001263 / 1000000000000) (-30707971433 / 1000000000000), orderedInterval (29069827094 / 1000000000000) (29069856924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1905233491418569 / 8000000000000) 3 (IntervalRat.scale (767 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9155419770 / 1000000000000) (9155419771 / 1000000000000), orderedInterval (50866189241 / 1000000000000) (50866189242 / 1000000000000)))) (orderedInterval (33485978093 / 1000000000000) (33485993918 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate319_chunkChecks3 :
    compactCertificate319.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate319.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate319_chunkChecks3_0
    compactCertificate319_chunkChecks3_1 compactCertificate319_chunkChecks3_2

theorem compactCertificate319_chunkChecks4_0 :
    compactCertificate319.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (767 / 4) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45048836990 / 1000000000000) (-45048836989 / 1000000000000), orderedInterval (-35808161046 / 1000000000000) (-35808161045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1129937457040067 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40897990878 / 1000000000000) (-40897990877 / 1000000000000), orderedInterval (-53096688391 / 1000000000000) (-53096688390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (365398557576611 / 1600000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (9312837294 / 1000000000000) (9312837331 / 1000000000000), orderedInterval (-51990529190 / 1000000000000) (-51990529153 / 1000000000000)))) (orderedInterval (-17070823276 / 1000000000000) (-17070823247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (329712931860169 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-113729706867 / 1000000000000) (-113729706866 / 1000000000000), orderedInterval (-48734641459 / 1000000000000) (-48734641458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (885655312936693 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-75784252976 / 1000000000000) (-75784252955 / 1000000000000), orderedInterval (-2338303739 / 1000000000000) (-2338303718 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2404726459117281 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-9912991217 / 1000000000000) (-9912991178 / 1000000000000), orderedInterval (44956785930 / 1000000000000) (44956785970 / 1000000000000)))) (orderedInterval (3822301672 / 1000000000000) (3822301773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1771310625874153 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40440477106 / 1000000000000) (40440555377 / 1000000000000), orderedInterval (-35302324725 / 1000000000000) (-35302246454 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3035170948457869 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1995187284 / 1000000000000) (-1995187283 / 1000000000000), orderedInterval (-40911932135 / 1000000000000) (-40911932133 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2235693183298471 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28688732534 / 1000000000000) (-28688732533 / 1000000000000), orderedInterval (-38092866466 / 1000000000000) (-38092866465 / 1000000000000)))) (orderedInterval (-2112755047 / 1000000000000) (-2112754934 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate319_chunkChecks4_1 :
    compactCertificate319.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3430128277484233 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28873776135 / 1000000000000) (28873805140 / 1000000000000), orderedInterval (-25549875752 / 1000000000000) (-25549846747 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1980385484360257 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7440826863 / 1000000000000) (-7440826862 / 1000000000000), orderedInterval (-50148100242 / 1000000000000) (-50148100241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3514228794442613 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (9076481702 / 1000000000000) (9076481703 / 1000000000000), orderedInterval (36960705214 / 1000000000000) (36960705215 / 1000000000000)))) (orderedInterval (-93149380263 / 1000000000000) (-93149249170 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3283448393537897 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12855024375 / 1000000000000) (12855024469 / 1000000000000), orderedInterval (-37242662335 / 1000000000000) (-37242662241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2343223705353401 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-46560034501 / 1000000000000) (-46560034436 / 1000000000000), orderedInterval (-2296144192 / 1000000000000) (-2296144127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2656965938810079 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-4504025530 / 1000000000000) (-4504025525 / 1000000000000), orderedInterval (43556157239 / 1000000000000) (43556157245 / 1000000000000)))) (orderedInterval (-28587553016 / 1000000000000) (-28587552765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2215101197155951 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (44903932142 / 1000000000000) (44903932143 / 1000000000000), orderedInterval (16736550698 / 1000000000000) (16736550699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1957109084966971 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18888238505 / 1000000000000) (18888238506 / 1000000000000), orderedInterval (47348363423 / 1000000000000) (47348363424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (567246494814129 / 1600000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13093743801 / 1000000000000) (-13093743800 / 1000000000000), orderedInterval (-40283302660 / 1000000000000) (-40283302659 / 1000000000000)))) (orderedInterval (-4647544665 / 1000000000000) (-4647544568 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate319_chunkChecks4_2 :
    compactCertificate319.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1569033657203363 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (48136096095 / 1000000000000) (48136136040 / 1000000000000), orderedInterval (-30599446599 / 1000000000000) (-30599406655 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1330087207783243 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-31874582225 / 1000000000000) (-31874582224 / 1000000000000), orderedInterval (-52942431129 / 1000000000000) (-52942431128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (832306816701529 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71399899042 / 1000000000000) (-71399899041 / 1000000000000), orderedInterval (-31611439272 / 1000000000000) (-31611439271 / 1000000000000)))) (orderedInterval (-7532024895 / 1000000000000) (-7532017792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (447617374149543 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (19795606890 / 1000000000000) (19795606892 / 1000000000000), orderedInterval (104639549271 / 1000000000000) (104639549272 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1215368244797629 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (61063199244 / 1000000000000) (61063202720 / 1000000000000), orderedInterval (-21688939702 / 1000000000000) (-21688936226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1659481433243933 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (42515793841 / 1000000000000) (42515793842 / 1000000000000), orderedInterval (35413876395 / 1000000000000) (35413876396 / 1000000000000)))) (orderedInterval (-5044509441 / 1000000000000) (-5044509387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (701693183298471 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (43143746483 / 1000000000000) (43143746484 / 1000000000000), orderedInterval (73216799096 / 1000000000000) (73216799097 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2852343833267591 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30708001263 / 1000000000000) (-30707971433 / 1000000000000), orderedInterval (29069827094 / 1000000000000) (29069856924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1905233491418569 / 8000000000000) 4 (IntervalRat.scale (767 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9155419770 / 1000000000000) (9155419771 / 1000000000000), orderedInterval (50866189241 / 1000000000000) (50866189242 / 1000000000000)))) (orderedInterval (25455123353 / 1000000000000) (25455152816 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate319_chunkChecks4 :
    compactCertificate319.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate319.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate319_chunkChecks4_0
    compactCertificate319_chunkChecks4_1 compactCertificate319_chunkChecks4_2

theorem compactCertificate319_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate319.chunkCheck r b = true :=
  compactCertificate319.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate319_chunkChecks0
    · exact compactCertificate319_chunkChecks1
    · exact compactCertificate319_chunkChecks2
    · exact compactCertificate319_chunkChecks3
    · exact compactCertificate319_chunkChecks4)

theorem compactCertificate319_coefficient0 :
    compactCertificate319.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate319_coefficient1 :
    compactCertificate319.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate319_coefficient2 :
    compactCertificate319.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate319_coefficient3 :
    compactCertificate319.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate319_coefficient4 :
    compactCertificate319.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate319_coefficients : ∀ r : Fin 5,
    compactCertificate319.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate319_coefficient0
  · exact compactCertificate319_coefficient1
  · exact compactCertificate319_coefficient2
  · exact compactCertificate319_coefficient3
  · exact compactCertificate319_coefficient4

theorem compactCertificate319_lower : (1 : ℚ) ≤ compactCertificate319.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate319, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate319_proves {t : ℝ} (ht : t ∈ compactCertificate319.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate319.proves compactCertificate319_states compactCertificate319_chunks
    compactCertificate319_coefficients compactCertificate319_lower ht

end Erdos232
