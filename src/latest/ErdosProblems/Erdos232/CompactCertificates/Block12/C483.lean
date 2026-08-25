/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate483 : CompactCertificate where
  left := 354
  right := 355
  center := 709 / 2
  grid := fun i =>
    match i.val with
    | 0 => 113
    | 1 => 83
    | 2 => 134
    | 3 => 24
    | 4 => 65
    | 5 => 177
    | 6 => 130
    | 7 => 223
    | 8 => 165
    | 9 => 252
    | 10 => 146
    | 11 => 259
    | 12 => 242
    | 13 => 172
    | 14 => 196
    | 15 => 163
    | 16 => 144
    | 17 => 209
    | 18 => 115
    | 19 => 98
    | 20 => 61
    | 21 => 33
    | 22 => 89
    | 23 => 122
    | 24 => 52
    | 25 => 210
    | _ => 140
  point := fun i =>
    match i.val with
    | 0 => 709 / 2
    | 1 => 1044492382061809 / 4000000000000
    | 2 => 337767375908497 / 800000000000
    | 3 => 304780272084563 / 4000000000000
    | 4 => 818682681710711 / 4000000000000
    | 5 => 2222882737306587 / 4000000000000
    | 6 => 1637365363422131 / 4000000000000
    | 7 => 2805653458222463 / 4000000000000
    | 8 => 2066631638798717 / 4000000000000
    | 9 => 3170744392094291 / 4000000000000
    | 10 => 1830630128306939 / 4000000000000
    | 11 => 3248485287170551 / 4000000000000
    | 12 => 3035156337703219 / 4000000000000
    | 13 => 2166030778481827 / 4000000000000
    | 14 => 2456048045132133 / 4000000000000
    | 15 => 2047596804150677 / 4000000000000
    | 16 => 1809113873848217 / 4000000000000
    | 17 => 524351714241483 / 800000000000
    | 18 => 1450384436710801 / 4000000000000
    | 19 => 1229506949567561 / 4000000000000
    | 20 => 769368361201283 / 4000000000000
    | 21 => 413768863457661 / 4000000000000
    | 22 => 1123462953795983 / 4000000000000
    | 23 => 1533992615606191 / 4000000000000
    | 24 => 648631638798717 / 4000000000000
    | 25 => 2636651600764957 / 4000000000000
    | _ => 1761161076161363 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-11917729450 / 1000000000000) (-11917729449 / 1000000000000), orderedInterval (-40650053159 / 1000000000000) (-40650053158 / 1000000000000))
    | 1 => (orderedInterval (-45185465075 / 1000000000000) (-45185465074 / 1000000000000), orderedInterval (-19820189051 / 1000000000000) (-19820189050 / 1000000000000))
    | 2 => (orderedInterval (34963178330 / 1000000000000) (34963218279 / 1000000000000), orderedInterval (-16935333762 / 1000000000000) (-16935293813 / 1000000000000))
    | 3 => (orderedInterval (91401027306 / 1000000000000) (91401027338 / 1000000000000), orderedInterval (-1496064829 / 1000000000000) (-1496064797 / 1000000000000))
    | 4 => (orderedInterval (-52960144592 / 1000000000000) (-52960144591 / 1000000000000), orderedInterval (-17354180987 / 1000000000000) (-17354180986 / 1000000000000))
    | 5 => (orderedInterval (-14537578110 / 1000000000000) (-14537578109 / 1000000000000), orderedInterval (-30552165117 / 1000000000000) (-30552165116 / 1000000000000))
    | 6 => (orderedInterval (39001812807 / 1000000000000) (39001814600 / 1000000000000), orderedInterval (-5886049778 / 1000000000000) (-5886047985 / 1000000000000))
    | 7 => (orderedInterval (-30085091348 / 1000000000000) (-30085088150 / 1000000000000), orderedInterval (1606178963 / 1000000000000) (1606182161 / 1000000000000))
    | 8 => (orderedInterval (27921695651 / 1000000000000) (27921733120 / 1000000000000), orderedInterval (-21300635399 / 1000000000000) (-21300597931 / 1000000000000))
    | 9 => (orderedInterval (27661233524 / 1000000000000) (27661260499 / 1000000000000), orderedInterval (-6179633262 / 1000000000000) (-6179606287 / 1000000000000))
    | 10 => (orderedInterval (-8498084411 / 1000000000000) (-8498084397 / 1000000000000), orderedInterval (36324886376 / 1000000000000) (36324886390 / 1000000000000))
    | 11 => (orderedInterval (19408564283 / 1000000000000) (19408566022 / 1000000000000), orderedInterval (-20191270729 / 1000000000000) (-20191268990 / 1000000000000))
    | 12 => (orderedInterval (-18462210870 / 1000000000000) (-18462209873 / 1000000000000), orderedInterval (22331242000 / 1000000000000) (22331242996 / 1000000000000))
    | 13 => (orderedInterval (31990431776 / 1000000000000) (31990464663 / 1000000000000), orderedInterval (-12368675089 / 1000000000000) (-12368642203 / 1000000000000))
    | 14 => (orderedInterval (-26284206056 / 1000000000000) (-26284173081 / 1000000000000), orderedInterval (18621413186 / 1000000000000) (18621446161 / 1000000000000))
    | 15 => (orderedInterval (-20050391951 / 1000000000000) (-20050391950 / 1000000000000), orderedInterval (-28991186546 / 1000000000000) (-28991186545 / 1000000000000))
    | 16 => (orderedInterval (23422722251 / 1000000000000) (23422722252 / 1000000000000), orderedInterval (29282123750 / 1000000000000) (29282123751 / 1000000000000))
    | 17 => (orderedInterval (11212195816 / 1000000000000) (11212195841 / 1000000000000), orderedInterval (-29087300077 / 1000000000000) (-29087300051 / 1000000000000))
    | 18 => (orderedInterval (-36211767738 / 1000000000000) (-36211707304 / 1000000000000), orderedInterval (21131557301 / 1000000000000) (21131617735 / 1000000000000))
    | 19 => (orderedInterval (12823734844 / 1000000000000) (12823734845 / 1000000000000), orderedInterval (43644830932 / 1000000000000) (43644830933 / 1000000000000))
    | 20 => (orderedInterval (-57341893746 / 1000000000000) (-57341893727 / 1000000000000), orderedInterval (-4512159099 / 1000000000000) (-4512159079 / 1000000000000))
    | 21 => (orderedInterval (-41261461438 / 1000000000000) (-41261461437 / 1000000000000), orderedInterval (-66522939390 / 1000000000000) (-66522939389 / 1000000000000))
    | 22 => (orderedInterval (-42269698534 / 1000000000000) (-42269671648 / 1000000000000), orderedInterval (21981978039 / 1000000000000) (21982004925 / 1000000000000))
    | 23 => (orderedInterval (34479513797 / 1000000000000) (34479513798 / 1000000000000), orderedInterval (21662095476 / 1000000000000) (21662095477 / 1000000000000))
    | 24 => (orderedInterval (-25565142002 / 1000000000000) (-25565140565 / 1000000000000), orderedInterval (57283379378 / 1000000000000) (57283380815 / 1000000000000))
    | 25 => (orderedInterval (6589317301 / 1000000000000) (6589317302 / 1000000000000), orderedInterval (30365736346 / 1000000000000) (30365736347 / 1000000000000))
    | _ => (orderedInterval (36114049014 / 1000000000000) (36114049017 / 1000000000000), orderedInterval (11862095713 / 1000000000000) (11862095717 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-3093132475 / 1000000000000) (-3093130105 / 1000000000000)
      | 1 => orderedInterval (-1891832503 / 1000000000000) (-1891832460 / 1000000000000)
      | 2 => orderedInterval (1602756773 / 1000000000000) (1602757798 / 1000000000000)
      | 3 => orderedInterval (-2785668435 / 1000000000000) (-2785663253 / 1000000000000)
      | 4 => orderedInterval (3491419810 / 1000000000000) (3491423147 / 1000000000000)
      | 5 => orderedInterval (-1284863387 / 1000000000000) (-1284863351 / 1000000000000)
      | 6 => orderedInterval (3197374547 / 1000000000000) (3197384300 / 1000000000000)
      | 7 => orderedInterval (-921607077 / 1000000000000) (-921606424 / 1000000000000)
      | _ => orderedInterval (-7466450841 / 1000000000000) (-7466450733 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17431893491 / 1000000000000) (-17431890670 / 1000000000000)
      | 1 => orderedInterval (3042438091 / 1000000000000) (3042438140 / 1000000000000)
      | 2 => orderedInterval (-848297173 / 1000000000000) (-848295623 / 1000000000000)
      | 3 => orderedInterval (-645721222 / 1000000000000) (-645709646 / 1000000000000)
      | 4 => orderedInterval (-2812757616 / 1000000000000) (-2812752469 / 1000000000000)
      | 5 => orderedInterval (-3998318605 / 1000000000000) (-3998318554 / 1000000000000)
      | 6 => orderedInterval (-5677574161 / 1000000000000) (-5677564195 / 1000000000000)
      | 7 => orderedInterval (-1832644837 / 1000000000000) (-1832644315 / 1000000000000)
      | _ => orderedInterval (-7202447828 / 1000000000000) (-7202447684 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (2091121900 / 1000000000000) (2091125266 / 1000000000000)
      | 1 => orderedInterval (-1857895339 / 1000000000000) (-1857895271 / 1000000000000)
      | 2 => orderedInterval (-5063741393 / 1000000000000) (-5063739017 / 1000000000000)
      | 3 => orderedInterval (11146584152 / 1000000000000) (11146610073 / 1000000000000)
      | 4 => orderedInterval (-8976715719 / 1000000000000) (-8976707752 / 1000000000000)
      | 5 => orderedInterval (1694500104 / 1000000000000) (1694500180 / 1000000000000)
      | 6 => orderedInterval (-4946221418 / 1000000000000) (-4946211202 / 1000000000000)
      | 7 => orderedInterval (2430797384 / 1000000000000) (2430797807 / 1000000000000)
      | _ => orderedInterval (12359468538 / 1000000000000) (12359468745 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17858934751 / 1000000000000) (17858938759 / 1000000000000)
      | 1 => orderedInterval (-8239944281 / 1000000000000) (-8239944180 / 1000000000000)
      | 2 => orderedInterval (1991670323 / 1000000000000) (1991674009 / 1000000000000)
      | 3 => orderedInterval (16410908252 / 1000000000000) (16410966254 / 1000000000000)
      | 4 => orderedInterval (8637202033 / 1000000000000) (8637214375 / 1000000000000)
      | 5 => orderedInterval (9190294260 / 1000000000000) (9190294377 / 1000000000000)
      | 6 => orderedInterval (5263291932 / 1000000000000) (5263302378 / 1000000000000)
      | 7 => orderedInterval (2312427291 / 1000000000000) (2312427635 / 1000000000000)
      | _ => orderedInterval (20086949866 / 1000000000000) (20086950183 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-820308872 / 1000000000000) (-820304089 / 1000000000000)
      | 1 => orderedInterval (6070583332 / 1000000000000) (6070583487 / 1000000000000)
      | 2 => orderedInterval (17255078655 / 1000000000000) (17255084479 / 1000000000000)
      | 3 => orderedInterval (-48724703161 / 1000000000000) (-48724573165 / 1000000000000)
      | 4 => orderedInterval (24614418801 / 1000000000000) (24614438014 / 1000000000000)
      | 5 => orderedInterval (-1255095966 / 1000000000000) (-1255095780 / 1000000000000)
      | 6 => orderedInterval (5735539117 / 1000000000000) (5735549827 / 1000000000000)
      | 7 => orderedInterval (-3248722627 / 1000000000000) (-3248722344 / 1000000000000)
      | _ => orderedInterval (-22655373087 / 1000000000000) (-22655372580 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-9152003588 / 1000000000000) (-9151981081 / 1000000000000)
    | 1 => orderedInterval (-37407216842 / 1000000000000) (-37407185016 / 1000000000000)
    | 2 => orderedInterval (8877898209 / 1000000000000) (8877948829 / 1000000000000)
    | 3 => orderedInterval (73511734427 / 1000000000000) (73511823790 / 1000000000000)
    | _ => orderedInterval (-23028583808 / 1000000000000) (-23028412151 / 1000000000000)

theorem compactCertificate483_stateChecks0 :
    compactCertificate483.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (709 / 2)) (orderedInterval (-11917729450 / 1000000000000) (-11917729449 / 1000000000000), orderedInterval (-40650053159 / 1000000000000) (-40650053158 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1044492382061809 / 4000000000000)) (orderedInterval (-45185465075 / 1000000000000) (-45185465074 / 1000000000000), orderedInterval (-19820189051 / 1000000000000) (-19820189050 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (337767375908497 / 800000000000)) (orderedInterval (34963178330 / 1000000000000) (34963218279 / 1000000000000), orderedInterval (-16935333762 / 1000000000000) (-16935293813 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_stateChecks1 :
    compactCertificate483.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (304780272084563 / 4000000000000)) (orderedInterval (91401027306 / 1000000000000) (91401027338 / 1000000000000), orderedInterval (-1496064829 / 1000000000000) (-1496064797 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (818682681710711 / 4000000000000)) (orderedInterval (-52960144592 / 1000000000000) (-52960144591 / 1000000000000), orderedInterval (-17354180987 / 1000000000000) (-17354180986 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2222882737306587 / 4000000000000)) (orderedInterval (-14537578110 / 1000000000000) (-14537578109 / 1000000000000), orderedInterval (-30552165117 / 1000000000000) (-30552165116 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_stateChecks2 :
    compactCertificate483.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1637365363422131 / 4000000000000)) (orderedInterval (39001812807 / 1000000000000) (39001814600 / 1000000000000), orderedInterval (-5886049778 / 1000000000000) (-5886047985 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2805653458222463 / 4000000000000)) (orderedInterval (-30085091348 / 1000000000000) (-30085088150 / 1000000000000), orderedInterval (1606178963 / 1000000000000) (1606182161 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2066631638798717 / 4000000000000)) (orderedInterval (27921695651 / 1000000000000) (27921733120 / 1000000000000), orderedInterval (-21300635399 / 1000000000000) (-21300597931 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_stateChecks3 :
    compactCertificate483.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (3170744392094291 / 4000000000000)) (orderedInterval (27661233524 / 1000000000000) (27661260499 / 1000000000000), orderedInterval (-6179633262 / 1000000000000) (-6179606287 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1830630128306939 / 4000000000000)) (orderedInterval (-8498084411 / 1000000000000) (-8498084397 / 1000000000000), orderedInterval (36324886376 / 1000000000000) (36324886390 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (3248485287170551 / 4000000000000)) (orderedInterval (19408564283 / 1000000000000) (19408566022 / 1000000000000), orderedInterval (-20191270729 / 1000000000000) (-20191268990 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_stateChecks4 :
    compactCertificate483.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3035156337703219 / 4000000000000)) (orderedInterval (-18462210870 / 1000000000000) (-18462209873 / 1000000000000), orderedInterval (22331242000 / 1000000000000) (22331242996 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2166030778481827 / 4000000000000)) (orderedInterval (31990431776 / 1000000000000) (31990464663 / 1000000000000), orderedInterval (-12368675089 / 1000000000000) (-12368642203 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2456048045132133 / 4000000000000)) (orderedInterval (-26284206056 / 1000000000000) (-26284173081 / 1000000000000), orderedInterval (18621413186 / 1000000000000) (18621446161 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_stateChecks5 :
    compactCertificate483.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2047596804150677 / 4000000000000)) (orderedInterval (-20050391951 / 1000000000000) (-20050391950 / 1000000000000), orderedInterval (-28991186546 / 1000000000000) (-28991186545 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1809113873848217 / 4000000000000)) (orderedInterval (23422722251 / 1000000000000) (23422722252 / 1000000000000), orderedInterval (29282123750 / 1000000000000) (29282123751 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (524351714241483 / 800000000000)) (orderedInterval (11212195816 / 1000000000000) (11212195841 / 1000000000000), orderedInterval (-29087300077 / 1000000000000) (-29087300051 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_stateChecks6 :
    compactCertificate483.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1450384436710801 / 4000000000000)) (orderedInterval (-36211767738 / 1000000000000) (-36211707304 / 1000000000000), orderedInterval (21131557301 / 1000000000000) (21131617735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1229506949567561 / 4000000000000)) (orderedInterval (12823734844 / 1000000000000) (12823734845 / 1000000000000), orderedInterval (43644830932 / 1000000000000) (43644830933 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (769368361201283 / 4000000000000)) (orderedInterval (-57341893746 / 1000000000000) (-57341893727 / 1000000000000), orderedInterval (-4512159099 / 1000000000000) (-4512159079 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_stateChecks7 :
    compactCertificate483.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (413768863457661 / 4000000000000)) (orderedInterval (-41261461438 / 1000000000000) (-41261461437 / 1000000000000), orderedInterval (-66522939390 / 1000000000000) (-66522939389 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1123462953795983 / 4000000000000)) (orderedInterval (-42269698534 / 1000000000000) (-42269671648 / 1000000000000), orderedInterval (21981978039 / 1000000000000) (21982004925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1533992615606191 / 4000000000000)) (orderedInterval (34479513797 / 1000000000000) (34479513798 / 1000000000000), orderedInterval (21662095476 / 1000000000000) (21662095477 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_stateChecks8 :
    compactCertificate483.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (648631638798717 / 4000000000000)) (orderedInterval (-25565142002 / 1000000000000) (-25565140565 / 1000000000000), orderedInterval (57283379378 / 1000000000000) (57283380815 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2636651600764957 / 4000000000000)) (orderedInterval (6589317301 / 1000000000000) (6589317302 / 1000000000000), orderedInterval (30365736346 / 1000000000000) (30365736347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1761161076161363 / 4000000000000)) (orderedInterval (36114049014 / 1000000000000) (36114049017 / 1000000000000), orderedInterval (11862095713 / 1000000000000) (11862095717 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_states : ∀ j,
    BesselStateValid (compactCertificate483.point j) (compactCertificate483.state j) :=
  compactCertificate483.statesValid_of_checks3 compactCertificate483_stateChecks0
    compactCertificate483_stateChecks1 compactCertificate483_stateChecks2
    compactCertificate483_stateChecks3 compactCertificate483_stateChecks4
    compactCertificate483_stateChecks5 compactCertificate483_stateChecks6
    compactCertificate483_stateChecks7 compactCertificate483_stateChecks8

theorem compactCertificate483_chunkChecks0_0 :
    compactCertificate483.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (709 / 2) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11917729450 / 1000000000000) (-11917729449 / 1000000000000), orderedInterval (-40650053159 / 1000000000000) (-40650053158 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1044492382061809 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45185465075 / 1000000000000) (-45185465074 / 1000000000000), orderedInterval (-19820189051 / 1000000000000) (-19820189050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (337767375908497 / 800000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34963178330 / 1000000000000) (34963218279 / 1000000000000), orderedInterval (-16935333762 / 1000000000000) (-16935293813 / 1000000000000)))) (orderedInterval (-3093132475 / 1000000000000) (-3093130105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (304780272084563 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91401027306 / 1000000000000) (91401027338 / 1000000000000), orderedInterval (-1496064829 / 1000000000000) (-1496064797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (818682681710711 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52960144592 / 1000000000000) (-52960144591 / 1000000000000), orderedInterval (-17354180987 / 1000000000000) (-17354180986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2222882737306587 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-14537578110 / 1000000000000) (-14537578109 / 1000000000000), orderedInterval (-30552165117 / 1000000000000) (-30552165116 / 1000000000000)))) (orderedInterval (-1891832503 / 1000000000000) (-1891832460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1637365363422131 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39001812807 / 1000000000000) (39001814600 / 1000000000000), orderedInterval (-5886049778 / 1000000000000) (-5886047985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2805653458222463 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30085091348 / 1000000000000) (-30085088150 / 1000000000000), orderedInterval (1606178963 / 1000000000000) (1606182161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2066631638798717 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27921695651 / 1000000000000) (27921733120 / 1000000000000), orderedInterval (-21300635399 / 1000000000000) (-21300597931 / 1000000000000)))) (orderedInterval (1602756773 / 1000000000000) (1602757798 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_chunkChecks0_1 :
    compactCertificate483.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3170744392094291 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27661233524 / 1000000000000) (27661260499 / 1000000000000), orderedInterval (-6179633262 / 1000000000000) (-6179606287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1830630128306939 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8498084411 / 1000000000000) (-8498084397 / 1000000000000), orderedInterval (36324886376 / 1000000000000) (36324886390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3248485287170551 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19408564283 / 1000000000000) (19408566022 / 1000000000000), orderedInterval (-20191270729 / 1000000000000) (-20191268990 / 1000000000000)))) (orderedInterval (-2785668435 / 1000000000000) (-2785663253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3035156337703219 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18462210870 / 1000000000000) (-18462209873 / 1000000000000), orderedInterval (22331242000 / 1000000000000) (22331242996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2166030778481827 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31990431776 / 1000000000000) (31990464663 / 1000000000000), orderedInterval (-12368675089 / 1000000000000) (-12368642203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2456048045132133 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26284206056 / 1000000000000) (-26284173081 / 1000000000000), orderedInterval (18621413186 / 1000000000000) (18621446161 / 1000000000000)))) (orderedInterval (3491419810 / 1000000000000) (3491423147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2047596804150677 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20050391951 / 1000000000000) (-20050391950 / 1000000000000), orderedInterval (-28991186546 / 1000000000000) (-28991186545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1809113873848217 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23422722251 / 1000000000000) (23422722252 / 1000000000000), orderedInterval (29282123750 / 1000000000000) (29282123751 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (524351714241483 / 800000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11212195816 / 1000000000000) (11212195841 / 1000000000000), orderedInterval (-29087300077 / 1000000000000) (-29087300051 / 1000000000000)))) (orderedInterval (-1284863387 / 1000000000000) (-1284863351 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_chunkChecks0_2 :
    compactCertificate483.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1450384436710801 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36211767738 / 1000000000000) (-36211707304 / 1000000000000), orderedInterval (21131557301 / 1000000000000) (21131617735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1229506949567561 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12823734844 / 1000000000000) (12823734845 / 1000000000000), orderedInterval (43644830932 / 1000000000000) (43644830933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (769368361201283 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57341893746 / 1000000000000) (-57341893727 / 1000000000000), orderedInterval (-4512159099 / 1000000000000) (-4512159079 / 1000000000000)))) (orderedInterval (3197374547 / 1000000000000) (3197384300 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (413768863457661 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41261461438 / 1000000000000) (-41261461437 / 1000000000000), orderedInterval (-66522939390 / 1000000000000) (-66522939389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1123462953795983 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42269698534 / 1000000000000) (-42269671648 / 1000000000000), orderedInterval (21981978039 / 1000000000000) (21982004925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1533992615606191 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34479513797 / 1000000000000) (34479513798 / 1000000000000), orderedInterval (21662095476 / 1000000000000) (21662095477 / 1000000000000)))) (orderedInterval (-921607077 / 1000000000000) (-921606424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (648631638798717 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25565142002 / 1000000000000) (-25565140565 / 1000000000000), orderedInterval (57283379378 / 1000000000000) (57283380815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2636651600764957 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6589317301 / 1000000000000) (6589317302 / 1000000000000), orderedInterval (30365736346 / 1000000000000) (30365736347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1761161076161363 / 4000000000000) 0 (IntervalRat.scale (709 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36114049014 / 1000000000000) (36114049017 / 1000000000000), orderedInterval (11862095713 / 1000000000000) (11862095717 / 1000000000000)))) (orderedInterval (-7466450841 / 1000000000000) (-7466450733 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_chunkChecks0 :
    compactCertificate483.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate483.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate483_chunkChecks0_0
    compactCertificate483_chunkChecks0_1 compactCertificate483_chunkChecks0_2

theorem compactCertificate483_chunkChecks1_0 :
    compactCertificate483.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (709 / 2) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11917729450 / 1000000000000) (-11917729449 / 1000000000000), orderedInterval (-40650053159 / 1000000000000) (-40650053158 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1044492382061809 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45185465075 / 1000000000000) (-45185465074 / 1000000000000), orderedInterval (-19820189051 / 1000000000000) (-19820189050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (337767375908497 / 800000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34963178330 / 1000000000000) (34963218279 / 1000000000000), orderedInterval (-16935333762 / 1000000000000) (-16935293813 / 1000000000000)))) (orderedInterval (-17431893491 / 1000000000000) (-17431890670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (304780272084563 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91401027306 / 1000000000000) (91401027338 / 1000000000000), orderedInterval (-1496064829 / 1000000000000) (-1496064797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (818682681710711 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52960144592 / 1000000000000) (-52960144591 / 1000000000000), orderedInterval (-17354180987 / 1000000000000) (-17354180986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2222882737306587 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-14537578110 / 1000000000000) (-14537578109 / 1000000000000), orderedInterval (-30552165117 / 1000000000000) (-30552165116 / 1000000000000)))) (orderedInterval (3042438091 / 1000000000000) (3042438140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1637365363422131 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39001812807 / 1000000000000) (39001814600 / 1000000000000), orderedInterval (-5886049778 / 1000000000000) (-5886047985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2805653458222463 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30085091348 / 1000000000000) (-30085088150 / 1000000000000), orderedInterval (1606178963 / 1000000000000) (1606182161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2066631638798717 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27921695651 / 1000000000000) (27921733120 / 1000000000000), orderedInterval (-21300635399 / 1000000000000) (-21300597931 / 1000000000000)))) (orderedInterval (-848297173 / 1000000000000) (-848295623 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_chunkChecks1_1 :
    compactCertificate483.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3170744392094291 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27661233524 / 1000000000000) (27661260499 / 1000000000000), orderedInterval (-6179633262 / 1000000000000) (-6179606287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1830630128306939 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8498084411 / 1000000000000) (-8498084397 / 1000000000000), orderedInterval (36324886376 / 1000000000000) (36324886390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3248485287170551 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19408564283 / 1000000000000) (19408566022 / 1000000000000), orderedInterval (-20191270729 / 1000000000000) (-20191268990 / 1000000000000)))) (orderedInterval (-645721222 / 1000000000000) (-645709646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3035156337703219 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18462210870 / 1000000000000) (-18462209873 / 1000000000000), orderedInterval (22331242000 / 1000000000000) (22331242996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2166030778481827 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31990431776 / 1000000000000) (31990464663 / 1000000000000), orderedInterval (-12368675089 / 1000000000000) (-12368642203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2456048045132133 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26284206056 / 1000000000000) (-26284173081 / 1000000000000), orderedInterval (18621413186 / 1000000000000) (18621446161 / 1000000000000)))) (orderedInterval (-2812757616 / 1000000000000) (-2812752469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2047596804150677 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20050391951 / 1000000000000) (-20050391950 / 1000000000000), orderedInterval (-28991186546 / 1000000000000) (-28991186545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1809113873848217 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23422722251 / 1000000000000) (23422722252 / 1000000000000), orderedInterval (29282123750 / 1000000000000) (29282123751 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (524351714241483 / 800000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11212195816 / 1000000000000) (11212195841 / 1000000000000), orderedInterval (-29087300077 / 1000000000000) (-29087300051 / 1000000000000)))) (orderedInterval (-3998318605 / 1000000000000) (-3998318554 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_chunkChecks1_2 :
    compactCertificate483.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1450384436710801 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36211767738 / 1000000000000) (-36211707304 / 1000000000000), orderedInterval (21131557301 / 1000000000000) (21131617735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1229506949567561 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12823734844 / 1000000000000) (12823734845 / 1000000000000), orderedInterval (43644830932 / 1000000000000) (43644830933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (769368361201283 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57341893746 / 1000000000000) (-57341893727 / 1000000000000), orderedInterval (-4512159099 / 1000000000000) (-4512159079 / 1000000000000)))) (orderedInterval (-5677574161 / 1000000000000) (-5677564195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (413768863457661 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41261461438 / 1000000000000) (-41261461437 / 1000000000000), orderedInterval (-66522939390 / 1000000000000) (-66522939389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1123462953795983 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42269698534 / 1000000000000) (-42269671648 / 1000000000000), orderedInterval (21981978039 / 1000000000000) (21982004925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1533992615606191 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34479513797 / 1000000000000) (34479513798 / 1000000000000), orderedInterval (21662095476 / 1000000000000) (21662095477 / 1000000000000)))) (orderedInterval (-1832644837 / 1000000000000) (-1832644315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (648631638798717 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25565142002 / 1000000000000) (-25565140565 / 1000000000000), orderedInterval (57283379378 / 1000000000000) (57283380815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2636651600764957 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6589317301 / 1000000000000) (6589317302 / 1000000000000), orderedInterval (30365736346 / 1000000000000) (30365736347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1761161076161363 / 4000000000000) 1 (IntervalRat.scale (709 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36114049014 / 1000000000000) (36114049017 / 1000000000000), orderedInterval (11862095713 / 1000000000000) (11862095717 / 1000000000000)))) (orderedInterval (-7202447828 / 1000000000000) (-7202447684 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_chunkChecks1 :
    compactCertificate483.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate483.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate483_chunkChecks1_0
    compactCertificate483_chunkChecks1_1 compactCertificate483_chunkChecks1_2

theorem compactCertificate483_chunkChecks2_0 :
    compactCertificate483.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (709 / 2) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11917729450 / 1000000000000) (-11917729449 / 1000000000000), orderedInterval (-40650053159 / 1000000000000) (-40650053158 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1044492382061809 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45185465075 / 1000000000000) (-45185465074 / 1000000000000), orderedInterval (-19820189051 / 1000000000000) (-19820189050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (337767375908497 / 800000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34963178330 / 1000000000000) (34963218279 / 1000000000000), orderedInterval (-16935333762 / 1000000000000) (-16935293813 / 1000000000000)))) (orderedInterval (2091121900 / 1000000000000) (2091125266 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (304780272084563 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91401027306 / 1000000000000) (91401027338 / 1000000000000), orderedInterval (-1496064829 / 1000000000000) (-1496064797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (818682681710711 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52960144592 / 1000000000000) (-52960144591 / 1000000000000), orderedInterval (-17354180987 / 1000000000000) (-17354180986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2222882737306587 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-14537578110 / 1000000000000) (-14537578109 / 1000000000000), orderedInterval (-30552165117 / 1000000000000) (-30552165116 / 1000000000000)))) (orderedInterval (-1857895339 / 1000000000000) (-1857895271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1637365363422131 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39001812807 / 1000000000000) (39001814600 / 1000000000000), orderedInterval (-5886049778 / 1000000000000) (-5886047985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2805653458222463 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30085091348 / 1000000000000) (-30085088150 / 1000000000000), orderedInterval (1606178963 / 1000000000000) (1606182161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2066631638798717 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27921695651 / 1000000000000) (27921733120 / 1000000000000), orderedInterval (-21300635399 / 1000000000000) (-21300597931 / 1000000000000)))) (orderedInterval (-5063741393 / 1000000000000) (-5063739017 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_chunkChecks2_1 :
    compactCertificate483.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3170744392094291 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27661233524 / 1000000000000) (27661260499 / 1000000000000), orderedInterval (-6179633262 / 1000000000000) (-6179606287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1830630128306939 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8498084411 / 1000000000000) (-8498084397 / 1000000000000), orderedInterval (36324886376 / 1000000000000) (36324886390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3248485287170551 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19408564283 / 1000000000000) (19408566022 / 1000000000000), orderedInterval (-20191270729 / 1000000000000) (-20191268990 / 1000000000000)))) (orderedInterval (11146584152 / 1000000000000) (11146610073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3035156337703219 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18462210870 / 1000000000000) (-18462209873 / 1000000000000), orderedInterval (22331242000 / 1000000000000) (22331242996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2166030778481827 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31990431776 / 1000000000000) (31990464663 / 1000000000000), orderedInterval (-12368675089 / 1000000000000) (-12368642203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2456048045132133 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26284206056 / 1000000000000) (-26284173081 / 1000000000000), orderedInterval (18621413186 / 1000000000000) (18621446161 / 1000000000000)))) (orderedInterval (-8976715719 / 1000000000000) (-8976707752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2047596804150677 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20050391951 / 1000000000000) (-20050391950 / 1000000000000), orderedInterval (-28991186546 / 1000000000000) (-28991186545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1809113873848217 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23422722251 / 1000000000000) (23422722252 / 1000000000000), orderedInterval (29282123750 / 1000000000000) (29282123751 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (524351714241483 / 800000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11212195816 / 1000000000000) (11212195841 / 1000000000000), orderedInterval (-29087300077 / 1000000000000) (-29087300051 / 1000000000000)))) (orderedInterval (1694500104 / 1000000000000) (1694500180 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_chunkChecks2_2 :
    compactCertificate483.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1450384436710801 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36211767738 / 1000000000000) (-36211707304 / 1000000000000), orderedInterval (21131557301 / 1000000000000) (21131617735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1229506949567561 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12823734844 / 1000000000000) (12823734845 / 1000000000000), orderedInterval (43644830932 / 1000000000000) (43644830933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (769368361201283 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57341893746 / 1000000000000) (-57341893727 / 1000000000000), orderedInterval (-4512159099 / 1000000000000) (-4512159079 / 1000000000000)))) (orderedInterval (-4946221418 / 1000000000000) (-4946211202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (413768863457661 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41261461438 / 1000000000000) (-41261461437 / 1000000000000), orderedInterval (-66522939390 / 1000000000000) (-66522939389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1123462953795983 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42269698534 / 1000000000000) (-42269671648 / 1000000000000), orderedInterval (21981978039 / 1000000000000) (21982004925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1533992615606191 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34479513797 / 1000000000000) (34479513798 / 1000000000000), orderedInterval (21662095476 / 1000000000000) (21662095477 / 1000000000000)))) (orderedInterval (2430797384 / 1000000000000) (2430797807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (648631638798717 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25565142002 / 1000000000000) (-25565140565 / 1000000000000), orderedInterval (57283379378 / 1000000000000) (57283380815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2636651600764957 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6589317301 / 1000000000000) (6589317302 / 1000000000000), orderedInterval (30365736346 / 1000000000000) (30365736347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1761161076161363 / 4000000000000) 2 (IntervalRat.scale (709 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36114049014 / 1000000000000) (36114049017 / 1000000000000), orderedInterval (11862095713 / 1000000000000) (11862095717 / 1000000000000)))) (orderedInterval (12359468538 / 1000000000000) (12359468745 / 1000000000000))) = true
  rfl'

theorem compactCertificate483_chunkChecks2 :
    compactCertificate483.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate483.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate483_chunkChecks2_0
    compactCertificate483_chunkChecks2_1 compactCertificate483_chunkChecks2_2

theorem compactCertificate483_chunkChecks3_0 :
    compactCertificate483.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (709 / 2) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11917729450 / 1000000000000) (-11917729449 / 1000000000000), orderedInterval (-40650053159 / 1000000000000) (-40650053158 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1044492382061809 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45185465075 / 1000000000000) (-45185465074 / 1000000000000), orderedInterval (-19820189051 / 1000000000000) (-19820189050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (337767375908497 / 800000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34963178330 / 1000000000000) (34963218279 / 1000000000000), orderedInterval (-16935333762 / 1000000000000) (-16935293813 / 1000000000000)))) (orderedInterval (17858934751 / 1000000000000) (17858938759 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (304780272084563 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91401027306 / 1000000000000) (91401027338 / 1000000000000), orderedInterval (-1496064829 / 1000000000000) (-1496064797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (818682681710711 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52960144592 / 1000000000000) (-52960144591 / 1000000000000), orderedInterval (-17354180987 / 1000000000000) (-17354180986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2222882737306587 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-14537578110 / 1000000000000) (-14537578109 / 1000000000000), orderedInterval (-30552165117 / 1000000000000) (-30552165116 / 1000000000000)))) (orderedInterval (-8239944281 / 1000000000000) (-8239944180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1637365363422131 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39001812807 / 1000000000000) (39001814600 / 1000000000000), orderedInterval (-5886049778 / 1000000000000) (-5886047985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2805653458222463 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30085091348 / 1000000000000) (-30085088150 / 1000000000000), orderedInterval (1606178963 / 1000000000000) (1606182161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2066631638798717 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27921695651 / 1000000000000) (27921733120 / 1000000000000), orderedInterval (-21300635399 / 1000000000000) (-21300597931 / 1000000000000)))) (orderedInterval (1991670323 / 1000000000000) (1991674009 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate483_chunkChecks3_1 :
    compactCertificate483.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3170744392094291 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27661233524 / 1000000000000) (27661260499 / 1000000000000), orderedInterval (-6179633262 / 1000000000000) (-6179606287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1830630128306939 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8498084411 / 1000000000000) (-8498084397 / 1000000000000), orderedInterval (36324886376 / 1000000000000) (36324886390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3248485287170551 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19408564283 / 1000000000000) (19408566022 / 1000000000000), orderedInterval (-20191270729 / 1000000000000) (-20191268990 / 1000000000000)))) (orderedInterval (16410908252 / 1000000000000) (16410966254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3035156337703219 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18462210870 / 1000000000000) (-18462209873 / 1000000000000), orderedInterval (22331242000 / 1000000000000) (22331242996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2166030778481827 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31990431776 / 1000000000000) (31990464663 / 1000000000000), orderedInterval (-12368675089 / 1000000000000) (-12368642203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2456048045132133 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26284206056 / 1000000000000) (-26284173081 / 1000000000000), orderedInterval (18621413186 / 1000000000000) (18621446161 / 1000000000000)))) (orderedInterval (8637202033 / 1000000000000) (8637214375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2047596804150677 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20050391951 / 1000000000000) (-20050391950 / 1000000000000), orderedInterval (-28991186546 / 1000000000000) (-28991186545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1809113873848217 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23422722251 / 1000000000000) (23422722252 / 1000000000000), orderedInterval (29282123750 / 1000000000000) (29282123751 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (524351714241483 / 800000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11212195816 / 1000000000000) (11212195841 / 1000000000000), orderedInterval (-29087300077 / 1000000000000) (-29087300051 / 1000000000000)))) (orderedInterval (9190294260 / 1000000000000) (9190294377 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate483_chunkChecks3_2 :
    compactCertificate483.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1450384436710801 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36211767738 / 1000000000000) (-36211707304 / 1000000000000), orderedInterval (21131557301 / 1000000000000) (21131617735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1229506949567561 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12823734844 / 1000000000000) (12823734845 / 1000000000000), orderedInterval (43644830932 / 1000000000000) (43644830933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (769368361201283 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57341893746 / 1000000000000) (-57341893727 / 1000000000000), orderedInterval (-4512159099 / 1000000000000) (-4512159079 / 1000000000000)))) (orderedInterval (5263291932 / 1000000000000) (5263302378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (413768863457661 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41261461438 / 1000000000000) (-41261461437 / 1000000000000), orderedInterval (-66522939390 / 1000000000000) (-66522939389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1123462953795983 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42269698534 / 1000000000000) (-42269671648 / 1000000000000), orderedInterval (21981978039 / 1000000000000) (21982004925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1533992615606191 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34479513797 / 1000000000000) (34479513798 / 1000000000000), orderedInterval (21662095476 / 1000000000000) (21662095477 / 1000000000000)))) (orderedInterval (2312427291 / 1000000000000) (2312427635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (648631638798717 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25565142002 / 1000000000000) (-25565140565 / 1000000000000), orderedInterval (57283379378 / 1000000000000) (57283380815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2636651600764957 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6589317301 / 1000000000000) (6589317302 / 1000000000000), orderedInterval (30365736346 / 1000000000000) (30365736347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1761161076161363 / 4000000000000) 3 (IntervalRat.scale (709 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36114049014 / 1000000000000) (36114049017 / 1000000000000), orderedInterval (11862095713 / 1000000000000) (11862095717 / 1000000000000)))) (orderedInterval (20086949866 / 1000000000000) (20086950183 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate483_chunkChecks3 :
    compactCertificate483.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate483.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate483_chunkChecks3_0
    compactCertificate483_chunkChecks3_1 compactCertificate483_chunkChecks3_2

theorem compactCertificate483_chunkChecks4_0 :
    compactCertificate483.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (709 / 2) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-11917729450 / 1000000000000) (-11917729449 / 1000000000000), orderedInterval (-40650053159 / 1000000000000) (-40650053158 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1044492382061809 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45185465075 / 1000000000000) (-45185465074 / 1000000000000), orderedInterval (-19820189051 / 1000000000000) (-19820189050 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (337767375908497 / 800000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (34963178330 / 1000000000000) (34963218279 / 1000000000000), orderedInterval (-16935333762 / 1000000000000) (-16935293813 / 1000000000000)))) (orderedInterval (-820308872 / 1000000000000) (-820304089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (304780272084563 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (91401027306 / 1000000000000) (91401027338 / 1000000000000), orderedInterval (-1496064829 / 1000000000000) (-1496064797 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (818682681710711 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-52960144592 / 1000000000000) (-52960144591 / 1000000000000), orderedInterval (-17354180987 / 1000000000000) (-17354180986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2222882737306587 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-14537578110 / 1000000000000) (-14537578109 / 1000000000000), orderedInterval (-30552165117 / 1000000000000) (-30552165116 / 1000000000000)))) (orderedInterval (6070583332 / 1000000000000) (6070583487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1637365363422131 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (39001812807 / 1000000000000) (39001814600 / 1000000000000), orderedInterval (-5886049778 / 1000000000000) (-5886047985 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2805653458222463 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30085091348 / 1000000000000) (-30085088150 / 1000000000000), orderedInterval (1606178963 / 1000000000000) (1606182161 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2066631638798717 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27921695651 / 1000000000000) (27921733120 / 1000000000000), orderedInterval (-21300635399 / 1000000000000) (-21300597931 / 1000000000000)))) (orderedInterval (17255078655 / 1000000000000) (17255084479 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate483_chunkChecks4_1 :
    compactCertificate483.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3170744392094291 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27661233524 / 1000000000000) (27661260499 / 1000000000000), orderedInterval (-6179633262 / 1000000000000) (-6179606287 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1830630128306939 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-8498084411 / 1000000000000) (-8498084397 / 1000000000000), orderedInterval (36324886376 / 1000000000000) (36324886390 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3248485287170551 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (19408564283 / 1000000000000) (19408566022 / 1000000000000), orderedInterval (-20191270729 / 1000000000000) (-20191268990 / 1000000000000)))) (orderedInterval (-48724703161 / 1000000000000) (-48724573165 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3035156337703219 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-18462210870 / 1000000000000) (-18462209873 / 1000000000000), orderedInterval (22331242000 / 1000000000000) (22331242996 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2166030778481827 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (31990431776 / 1000000000000) (31990464663 / 1000000000000), orderedInterval (-12368675089 / 1000000000000) (-12368642203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2456048045132133 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26284206056 / 1000000000000) (-26284173081 / 1000000000000), orderedInterval (18621413186 / 1000000000000) (18621446161 / 1000000000000)))) (orderedInterval (24614418801 / 1000000000000) (24614438014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2047596804150677 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20050391951 / 1000000000000) (-20050391950 / 1000000000000), orderedInterval (-28991186546 / 1000000000000) (-28991186545 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1809113873848217 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23422722251 / 1000000000000) (23422722252 / 1000000000000), orderedInterval (29282123750 / 1000000000000) (29282123751 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (524351714241483 / 800000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (11212195816 / 1000000000000) (11212195841 / 1000000000000), orderedInterval (-29087300077 / 1000000000000) (-29087300051 / 1000000000000)))) (orderedInterval (-1255095966 / 1000000000000) (-1255095780 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate483_chunkChecks4_2 :
    compactCertificate483.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1450384436710801 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36211767738 / 1000000000000) (-36211707304 / 1000000000000), orderedInterval (21131557301 / 1000000000000) (21131617735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1229506949567561 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12823734844 / 1000000000000) (12823734845 / 1000000000000), orderedInterval (43644830932 / 1000000000000) (43644830933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (769368361201283 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-57341893746 / 1000000000000) (-57341893727 / 1000000000000), orderedInterval (-4512159099 / 1000000000000) (-4512159079 / 1000000000000)))) (orderedInterval (5735539117 / 1000000000000) (5735549827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (413768863457661 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-41261461438 / 1000000000000) (-41261461437 / 1000000000000), orderedInterval (-66522939390 / 1000000000000) (-66522939389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1123462953795983 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42269698534 / 1000000000000) (-42269671648 / 1000000000000), orderedInterval (21981978039 / 1000000000000) (21982004925 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1533992615606191 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34479513797 / 1000000000000) (34479513798 / 1000000000000), orderedInterval (21662095476 / 1000000000000) (21662095477 / 1000000000000)))) (orderedInterval (-3248722627 / 1000000000000) (-3248722344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (648631638798717 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25565142002 / 1000000000000) (-25565140565 / 1000000000000), orderedInterval (57283379378 / 1000000000000) (57283380815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2636651600764957 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6589317301 / 1000000000000) (6589317302 / 1000000000000), orderedInterval (30365736346 / 1000000000000) (30365736347 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1761161076161363 / 4000000000000) 4 (IntervalRat.scale (709 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36114049014 / 1000000000000) (36114049017 / 1000000000000), orderedInterval (11862095713 / 1000000000000) (11862095717 / 1000000000000)))) (orderedInterval (-22655373087 / 1000000000000) (-22655372580 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate483_chunkChecks4 :
    compactCertificate483.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate483.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate483_chunkChecks4_0
    compactCertificate483_chunkChecks4_1 compactCertificate483_chunkChecks4_2

theorem compactCertificate483_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate483.chunkCheck r b = true :=
  compactCertificate483.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate483_chunkChecks0
    · exact compactCertificate483_chunkChecks1
    · exact compactCertificate483_chunkChecks2
    · exact compactCertificate483_chunkChecks3
    · exact compactCertificate483_chunkChecks4)

theorem compactCertificate483_coefficient0 :
    compactCertificate483.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate483_coefficient1 :
    compactCertificate483.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate483_coefficient2 :
    compactCertificate483.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate483_coefficient3 :
    compactCertificate483.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate483_coefficient4 :
    compactCertificate483.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate483_coefficients : ∀ r : Fin 5,
    compactCertificate483.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate483_coefficient0
  · exact compactCertificate483_coefficient1
  · exact compactCertificate483_coefficient2
  · exact compactCertificate483_coefficient3
  · exact compactCertificate483_coefficient4

theorem compactCertificate483_lower : (1 : ℚ) ≤ compactCertificate483.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate483, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate483_proves {t : ℝ} (ht : t ∈ compactCertificate483.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate483.proves compactCertificate483_states compactCertificate483_chunks
    compactCertificate483_coefficients compactCertificate483_lower ht

end Erdos232
