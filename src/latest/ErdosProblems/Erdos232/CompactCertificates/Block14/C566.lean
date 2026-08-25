/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate566 : CompactCertificate where
  left := 437
  right := 438
  center := 875 / 2
  grid := fun i =>
    match i.val with
    | 0 => 139
    | 1 => 103
    | 2 => 166
    | 3 => 30
    | 4 => 80
    | 5 => 218
    | 6 => 161
    | 7 => 276
    | 8 => 203
    | 9 => 312
    | 10 => 180
    | 11 => 319
    | 12 => 298
    | 13 => 213
    | 14 => 241
    | 15 => 201
    | 16 => 178
    | 17 => 258
    | 18 => 143
    | 19 => 121
    | 20 => 76
    | 21 => 41
    | 22 => 110
    | 23 => 151
    | 24 => 64
    | 25 => 259
    | _ => 173
  point := fun i =>
    match i.val with
    | 0 => 875 / 2
    | 1 => 10312336635307 / 32000000000
    | 2 => 3334797787531 / 6400000000
    | 3 => 3009114110849 / 32000000000
    | 4 => 8082903768653 / 32000000000
    | 5 => 21946656080601 / 32000000000
    | 6 => 16165807537313 / 32000000000
    | 7 => 27700386752549 / 32000000000
    | 8 => 20403979508591 / 32000000000
    | 9 => 31304951684993 / 32000000000
    | 10 => 18073922282297 / 32000000000
    | 11 => 32072492256973 / 32000000000
    | 12 => 29966282600737 / 32000000000
    | 13 => 21385353243121 / 32000000000
    | 14 => 24248711305959 / 32000000000
    | 15 => 20216047431671 / 32000000000
    | 16 => 17861490997091 / 32000000000
    | 17 => 5176956276009 / 6400000000
    | 18 => 14319733507723 / 32000000000
    | 19 => 12138996681203 / 32000000000
    | 20 => 7596020491409 / 32000000000
    | 21 => 4085165083503 / 32000000000
    | 22 => 11092017879509 / 32000000000
    | 23 => 15145202128693 / 32000000000
    | 24 => 6403979508591 / 32000000000
    | 25 => 26031821164111 / 32000000000
    | _ => 17388050117249 / 32000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-38125476134 / 1000000000000) (-38125475598 / 1000000000000), orderedInterval (1299776014 / 1000000000000) (1299776550 / 1000000000000))
    | 1 => (orderedInterval (22794769195 / 1000000000000) (22794771394 / 1000000000000), orderedInterval (-38191380769 / 1000000000000) (-38191378569 / 1000000000000))
    | 2 => (orderedInterval (11753232758 / 1000000000000) (11753232759 / 1000000000000), orderedInterval (32907335877 / 1000000000000) (32907335878 / 1000000000000))
    | 3 => (orderedInterval (44477297019 / 1000000000000) (44477297020 / 1000000000000), orderedInterval (68986724908 / 1000000000000) (68986724909 / 1000000000000))
    | 4 => (orderedInterval (44589182929 / 1000000000000) (44589206317 / 1000000000000), orderedInterval (-23156900487 / 1000000000000) (-23156877100 / 1000000000000))
    | 5 => (orderedInterval (29973617056 / 1000000000000) (29973628129 / 1000000000000), orderedInterval (-5483069595 / 1000000000000) (-5483058523 / 1000000000000))
    | 6 => (orderedInterval (-6013469422 / 1000000000000) (-6013469421 / 1000000000000), orderedInterval (-34980032548 / 1000000000000) (-34980032547 / 1000000000000))
    | 7 => (orderedInterval (-16567704514 / 1000000000000) (-16567704179 / 1000000000000), orderedInterval (21479226210 / 1000000000000) (21479226544 / 1000000000000))
    | 8 => (orderedInterval (-19528885002 / 1000000000000) (-19528885001 / 1000000000000), orderedInterval (-24825121149 / 1000000000000) (-24825121148 / 1000000000000))
    | 9 => (orderedInterval (-22870664355 / 1000000000000) (-22870638799 / 1000000000000), orderedInterval (11311568218 / 1000000000000) (11311593773 / 1000000000000))
    | 10 => (orderedInterval (3637869828 / 1000000000000) (3637869829 / 1000000000000), orderedInterval (33372008243 / 1000000000000) (33372008244 / 1000000000000))
    | 11 => (orderedInterval (-19466457043 / 1000000000000) (-19466457041 / 1000000000000), orderedInterval (-15997720780 / 1000000000000) (-15997720778 / 1000000000000))
    | 12 => (orderedInterval (22445963425 / 1000000000000) (22445963431 / 1000000000000), orderedInterval (13254659015 / 1000000000000) (13254659021 / 1000000000000))
    | 13 => (orderedInterval (2519895249 / 1000000000000) (2519895250 / 1000000000000), orderedInterval (-30763178883 / 1000000000000) (-30763178882 / 1000000000000))
    | 14 => (orderedInterval (-28712590746 / 1000000000000) (-28712590260 / 1000000000000), orderedInterval (-3944284830 / 1000000000000) (-3944284343 / 1000000000000))
    | 15 => (orderedInterval (-27945556938 / 1000000000000) (-27945556937 / 1000000000000), orderedInterval (-15036159111 / 1000000000000) (-15036159110 / 1000000000000))
    | 16 => (orderedInterval (-8248086601 / 1000000000000) (-8248086593 / 1000000000000), orderedInterval (32756653882 / 1000000000000) (32756653891 / 1000000000000))
    | 17 => (orderedInterval (-21006611645 / 1000000000000) (-21006607357 / 1000000000000), orderedInterval (18607122199 / 1000000000000) (18607126486 / 1000000000000))
    | 18 => (orderedInterval (31133334660 / 1000000000000) (31133414380 / 1000000000000), orderedInterval (-21326915238 / 1000000000000) (-21326835517 / 1000000000000))
    | 19 => (orderedInterval (163705756 / 1000000000000) (163705757 / 1000000000000), orderedInterval (-40965915303 / 1000000000000) (-40965915302 / 1000000000000))
    | 20 => (orderedInterval (-29263831520 / 1000000000000) (-29263824742 / 1000000000000), orderedInterval (42787964630 / 1000000000000) (42787971408 / 1000000000000))
    | 21 => (orderedInterval (24841537848 / 1000000000000) (24841538708 / 1000000000000), orderedInterval (-66201075438 / 1000000000000) (-66201074578 / 1000000000000))
    | 22 => (orderedInterval (41364199035 / 1000000000000) (41364203556 / 1000000000000), orderedInterval (-11267798821 / 1000000000000) (-11267794301 / 1000000000000))
    | 23 => (orderedInterval (11110999974 / 1000000000000) (11111000015 / 1000000000000), orderedInterval (-34963815312 / 1000000000000) (-34963815271 / 1000000000000))
    | 24 => (orderedInterval (-8584439751 / 1000000000000) (-8584439719 / 1000000000000), orderedInterval (55765843827 / 1000000000000) (55765843859 / 1000000000000))
    | 25 => (orderedInterval (-15960479826 / 1000000000000) (-15960479825 / 1000000000000), orderedInterval (-22964901869 / 1000000000000) (-22964901868 / 1000000000000))
    | _ => (orderedInterval (-21153535939 / 1000000000000) (-21153535938 / 1000000000000), orderedInterval (-26890155024 / 1000000000000) (-26890155023 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14209507972 / 1000000000000) (-14209507709 / 1000000000000)
      | 1 => orderedInterval (-985332706 / 1000000000000) (-985331012 / 1000000000000)
      | 2 => orderedInterval (39039652 / 1000000000000) (39039687 / 1000000000000)
      | 3 => orderedInterval (1566100941 / 1000000000000) (1566105656 / 1000000000000)
      | 4 => orderedInterval (-21628172 / 1000000000000) (-21628117 / 1000000000000)
      | 5 => orderedInterval (-388547738 / 1000000000000) (-388547585 / 1000000000000)
      | 6 => orderedInterval (-5939955412 / 1000000000000) (-5939942335 / 1000000000000)
      | 7 => orderedInterval (-2248660409 / 1000000000000) (-2248660234 / 1000000000000)
      | _ => orderedInterval (5216426022 / 1000000000000) (5216426144 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (2552920868 / 1000000000000) (2552921130 / 1000000000000)
      | 1 => orderedInterval (-37980099 / 1000000000000) (-37978312 / 1000000000000)
      | 2 => orderedInterval (-2185251012 / 1000000000000) (-2185250948 / 1000000000000)
      | 3 => orderedInterval (-6512126083 / 1000000000000) (-6512115570 / 1000000000000)
      | 4 => orderedInterval (-4921264270 / 1000000000000) (-4921264181 / 1000000000000)
      | 5 => orderedInterval (-1761470238 / 1000000000000) (-1761469973 / 1000000000000)
      | 6 => orderedInterval (6254118614 / 1000000000000) (6254131873 / 1000000000000)
      | 7 => orderedInterval (3458007310 / 1000000000000) (3458007447 / 1000000000000)
      | _ => orderedInterval (9896025795 / 1000000000000) (9896025966 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14012209209 / 1000000000000) (14012209473 / 1000000000000)
      | 1 => orderedInterval (4716022077 / 1000000000000) (4716024383 / 1000000000000)
      | 2 => orderedInterval (-993033292 / 1000000000000) (-993033175 / 1000000000000)
      | 3 => orderedInterval (-6230386987 / 1000000000000) (-6230363487 / 1000000000000)
      | 4 => orderedInterval (875854141 / 1000000000000) (875854289 / 1000000000000)
      | 5 => orderedInterval (1747251179 / 1000000000000) (1747251646 / 1000000000000)
      | 6 => orderedInterval (5481086208 / 1000000000000) (5481099735 / 1000000000000)
      | 7 => orderedInterval (1616762312 / 1000000000000) (1616762428 / 1000000000000)
      | _ => orderedInterval (-10626137305 / 1000000000000) (-10626137053 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3667288298 / 1000000000000) (-3667288030 / 1000000000000)
      | 1 => orderedInterval (-1342220585 / 1000000000000) (-1342217259 / 1000000000000)
      | 2 => orderedInterval (6991322930 / 1000000000000) (6991323148 / 1000000000000)
      | 3 => orderedInterval (44508150196 / 1000000000000) (44508202707 / 1000000000000)
      | 4 => orderedInterval (12609356452 / 1000000000000) (12609356704 / 1000000000000)
      | 5 => orderedInterval (1400469339 / 1000000000000) (1400470174 / 1000000000000)
      | 6 => orderedInterval (-5395494900 / 1000000000000) (-5395481100 / 1000000000000)
      | 7 => orderedInterval (-3553597814 / 1000000000000) (-3553597710 / 1000000000000)
      | _ => orderedInterval (-21691927609 / 1000000000000) (-21691927221 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13644518087 / 1000000000000) (-13644517814 / 1000000000000)
      | 1 => orderedInterval (-12681855092 / 1000000000000) (-12681850038 / 1000000000000)
      | 2 => orderedInterval (5670438991 / 1000000000000) (5670439405 / 1000000000000)
      | 3 => orderedInterval (25920852284 / 1000000000000) (25920969796 / 1000000000000)
      | 4 => orderedInterval (-5958249608 / 1000000000000) (-5958249171 / 1000000000000)
      | 5 => orderedInterval (-6444229129 / 1000000000000) (-6444227621 / 1000000000000)
      | 6 => orderedInterval (-5511673416 / 1000000000000) (-5511659290 / 1000000000000)
      | 7 => orderedInterval (-1523086600 / 1000000000000) (-1523086504 / 1000000000000)
      | _ => orderedInterval (25071632345 / 1000000000000) (25071632968 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-16972065794 / 1000000000000) (-16972045505 / 1000000000000)
    | 1 => orderedInterval (6742980885 / 1000000000000) (6743007432 / 1000000000000)
    | 2 => orderedInterval (10599627542 / 1000000000000) (10599668239 / 1000000000000)
    | 3 => orderedInterval (29858769711 / 1000000000000) (29858841413 / 1000000000000)
    | _ => orderedInterval (10899311688 / 1000000000000) (10899451731 / 1000000000000)

theorem compactCertificate566_stateChecks0 :
    compactCertificate566.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (875 / 2)) (orderedInterval (-38125476134 / 1000000000000) (-38125475598 / 1000000000000), orderedInterval (1299776014 / 1000000000000) (1299776550 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (10312336635307 / 32000000000)) (orderedInterval (22794769195 / 1000000000000) (22794771394 / 1000000000000), orderedInterval (-38191380769 / 1000000000000) (-38191378569 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (3334797787531 / 6400000000)) (orderedInterval (11753232758 / 1000000000000) (11753232759 / 1000000000000), orderedInterval (32907335877 / 1000000000000) (32907335878 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_stateChecks1 :
    compactCertificate566.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (3009114110849 / 32000000000)) (orderedInterval (44477297019 / 1000000000000) (44477297020 / 1000000000000), orderedInterval (68986724908 / 1000000000000) (68986724909 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (8082903768653 / 32000000000)) (orderedInterval (44589182929 / 1000000000000) (44589206317 / 1000000000000), orderedInterval (-23156900487 / 1000000000000) (-23156877100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (21946656080601 / 32000000000)) (orderedInterval (29973617056 / 1000000000000) (29973628129 / 1000000000000), orderedInterval (-5483069595 / 1000000000000) (-5483058523 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_stateChecks2 :
    compactCertificate566.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (16165807537313 / 32000000000)) (orderedInterval (-6013469422 / 1000000000000) (-6013469421 / 1000000000000), orderedInterval (-34980032548 / 1000000000000) (-34980032547 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (27700386752549 / 32000000000)) (orderedInterval (-16567704514 / 1000000000000) (-16567704179 / 1000000000000), orderedInterval (21479226210 / 1000000000000) (21479226544 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (20403979508591 / 32000000000)) (orderedInterval (-19528885002 / 1000000000000) (-19528885001 / 1000000000000), orderedInterval (-24825121149 / 1000000000000) (-24825121148 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_stateChecks3 :
    compactCertificate566.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 312 12 (31304951684993 / 32000000000)) (orderedInterval (-22870664355 / 1000000000000) (-22870638799 / 1000000000000), orderedInterval (11311568218 / 1000000000000) (11311593773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (18073922282297 / 32000000000)) (orderedInterval (3637869828 / 1000000000000) (3637869829 / 1000000000000), orderedInterval (33372008243 / 1000000000000) (33372008244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 319 12 (32072492256973 / 32000000000)) (orderedInterval (-19466457043 / 1000000000000) (-19466457041 / 1000000000000), orderedInterval (-15997720780 / 1000000000000) (-15997720778 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_stateChecks4 :
    compactCertificate566.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 298 12 (29966282600737 / 32000000000)) (orderedInterval (22445963425 / 1000000000000) (22445963431 / 1000000000000), orderedInterval (13254659015 / 1000000000000) (13254659021 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (21385353243121 / 32000000000)) (orderedInterval (2519895249 / 1000000000000) (2519895250 / 1000000000000), orderedInterval (-30763178883 / 1000000000000) (-30763178882 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (24248711305959 / 32000000000)) (orderedInterval (-28712590746 / 1000000000000) (-28712590260 / 1000000000000), orderedInterval (-3944284830 / 1000000000000) (-3944284343 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_stateChecks5 :
    compactCertificate566.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (20216047431671 / 32000000000)) (orderedInterval (-27945556938 / 1000000000000) (-27945556937 / 1000000000000), orderedInterval (-15036159111 / 1000000000000) (-15036159110 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (17861490997091 / 32000000000)) (orderedInterval (-8248086601 / 1000000000000) (-8248086593 / 1000000000000), orderedInterval (32756653882 / 1000000000000) (32756653891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 258 12 (5176956276009 / 6400000000)) (orderedInterval (-21006611645 / 1000000000000) (-21006607357 / 1000000000000), orderedInterval (18607122199 / 1000000000000) (18607126486 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_stateChecks6 :
    compactCertificate566.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (14319733507723 / 32000000000)) (orderedInterval (31133334660 / 1000000000000) (31133414380 / 1000000000000), orderedInterval (-21326915238 / 1000000000000) (-21326835517 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (12138996681203 / 32000000000)) (orderedInterval (163705756 / 1000000000000) (163705757 / 1000000000000), orderedInterval (-40965915303 / 1000000000000) (-40965915302 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (7596020491409 / 32000000000)) (orderedInterval (-29263831520 / 1000000000000) (-29263824742 / 1000000000000), orderedInterval (42787964630 / 1000000000000) (42787971408 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_stateChecks7 :
    compactCertificate566.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (4085165083503 / 32000000000)) (orderedInterval (24841537848 / 1000000000000) (24841538708 / 1000000000000), orderedInterval (-66201075438 / 1000000000000) (-66201074578 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (11092017879509 / 32000000000)) (orderedInterval (41364199035 / 1000000000000) (41364203556 / 1000000000000), orderedInterval (-11267798821 / 1000000000000) (-11267794301 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (15145202128693 / 32000000000)) (orderedInterval (11110999974 / 1000000000000) (11111000015 / 1000000000000), orderedInterval (-34963815312 / 1000000000000) (-34963815271 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_stateChecks8 :
    compactCertificate566.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (6403979508591 / 32000000000)) (orderedInterval (-8584439751 / 1000000000000) (-8584439719 / 1000000000000), orderedInterval (55765843827 / 1000000000000) (55765843859 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (26031821164111 / 32000000000)) (orderedInterval (-15960479826 / 1000000000000) (-15960479825 / 1000000000000), orderedInterval (-22964901869 / 1000000000000) (-22964901868 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (17388050117249 / 32000000000)) (orderedInterval (-21153535939 / 1000000000000) (-21153535938 / 1000000000000), orderedInterval (-26890155024 / 1000000000000) (-26890155023 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_states : ∀ j,
    BesselStateValid (compactCertificate566.point j) (compactCertificate566.state j) :=
  compactCertificate566.statesValid_of_checks3 compactCertificate566_stateChecks0
    compactCertificate566_stateChecks1 compactCertificate566_stateChecks2
    compactCertificate566_stateChecks3 compactCertificate566_stateChecks4
    compactCertificate566_stateChecks5 compactCertificate566_stateChecks6
    compactCertificate566_stateChecks7 compactCertificate566_stateChecks8

theorem compactCertificate566_chunkChecks0_0 :
    compactCertificate566.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (875 / 2) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38125476134 / 1000000000000) (-38125475598 / 1000000000000), orderedInterval (1299776014 / 1000000000000) (1299776550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (10312336635307 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (22794769195 / 1000000000000) (22794771394 / 1000000000000), orderedInterval (-38191380769 / 1000000000000) (-38191378569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (3334797787531 / 6400000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11753232758 / 1000000000000) (11753232759 / 1000000000000), orderedInterval (32907335877 / 1000000000000) (32907335878 / 1000000000000)))) (orderedInterval (-14209507972 / 1000000000000) (-14209507709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (3009114110849 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44477297019 / 1000000000000) (44477297020 / 1000000000000), orderedInterval (68986724908 / 1000000000000) (68986724909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (8082903768653 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44589182929 / 1000000000000) (44589206317 / 1000000000000), orderedInterval (-23156900487 / 1000000000000) (-23156877100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (21946656080601 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29973617056 / 1000000000000) (29973628129 / 1000000000000), orderedInterval (-5483069595 / 1000000000000) (-5483058523 / 1000000000000)))) (orderedInterval (-985332706 / 1000000000000) (-985331012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (16165807537313 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6013469422 / 1000000000000) (-6013469421 / 1000000000000), orderedInterval (-34980032548 / 1000000000000) (-34980032547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (27700386752549 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16567704514 / 1000000000000) (-16567704179 / 1000000000000), orderedInterval (21479226210 / 1000000000000) (21479226544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (20403979508591 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19528885002 / 1000000000000) (-19528885001 / 1000000000000), orderedInterval (-24825121149 / 1000000000000) (-24825121148 / 1000000000000)))) (orderedInterval (39039652 / 1000000000000) (39039687 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_chunkChecks0_1 :
    compactCertificate566.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (31304951684993 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22870664355 / 1000000000000) (-22870638799 / 1000000000000), orderedInterval (11311568218 / 1000000000000) (11311593773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (18073922282297 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3637869828 / 1000000000000) (3637869829 / 1000000000000), orderedInterval (33372008243 / 1000000000000) (33372008244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (32072492256973 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19466457043 / 1000000000000) (-19466457041 / 1000000000000), orderedInterval (-15997720780 / 1000000000000) (-15997720778 / 1000000000000)))) (orderedInterval (1566100941 / 1000000000000) (1566105656 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (29966282600737 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22445963425 / 1000000000000) (22445963431 / 1000000000000), orderedInterval (13254659015 / 1000000000000) (13254659021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (21385353243121 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2519895249 / 1000000000000) (2519895250 / 1000000000000), orderedInterval (-30763178883 / 1000000000000) (-30763178882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (24248711305959 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28712590746 / 1000000000000) (-28712590260 / 1000000000000), orderedInterval (-3944284830 / 1000000000000) (-3944284343 / 1000000000000)))) (orderedInterval (-21628172 / 1000000000000) (-21628117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (20216047431671 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27945556938 / 1000000000000) (-27945556937 / 1000000000000), orderedInterval (-15036159111 / 1000000000000) (-15036159110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (17861490997091 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8248086601 / 1000000000000) (-8248086593 / 1000000000000), orderedInterval (32756653882 / 1000000000000) (32756653891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (5176956276009 / 6400000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21006611645 / 1000000000000) (-21006607357 / 1000000000000), orderedInterval (18607122199 / 1000000000000) (18607126486 / 1000000000000)))) (orderedInterval (-388547738 / 1000000000000) (-388547585 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_chunkChecks0_2 :
    compactCertificate566.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (14319733507723 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31133334660 / 1000000000000) (31133414380 / 1000000000000), orderedInterval (-21326915238 / 1000000000000) (-21326835517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (12138996681203 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (163705756 / 1000000000000) (163705757 / 1000000000000), orderedInterval (-40965915303 / 1000000000000) (-40965915302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (7596020491409 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-29263831520 / 1000000000000) (-29263824742 / 1000000000000), orderedInterval (42787964630 / 1000000000000) (42787971408 / 1000000000000)))) (orderedInterval (-5939955412 / 1000000000000) (-5939942335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (4085165083503 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24841537848 / 1000000000000) (24841538708 / 1000000000000), orderedInterval (-66201075438 / 1000000000000) (-66201074578 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (11092017879509 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41364199035 / 1000000000000) (41364203556 / 1000000000000), orderedInterval (-11267798821 / 1000000000000) (-11267794301 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (15145202128693 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11110999974 / 1000000000000) (11111000015 / 1000000000000), orderedInterval (-34963815312 / 1000000000000) (-34963815271 / 1000000000000)))) (orderedInterval (-2248660409 / 1000000000000) (-2248660234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (6403979508591 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-8584439751 / 1000000000000) (-8584439719 / 1000000000000), orderedInterval (55765843827 / 1000000000000) (55765843859 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (26031821164111 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15960479826 / 1000000000000) (-15960479825 / 1000000000000), orderedInterval (-22964901869 / 1000000000000) (-22964901868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (17388050117249 / 32000000000) 0 (IntervalRat.scale (875 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21153535939 / 1000000000000) (-21153535938 / 1000000000000), orderedInterval (-26890155024 / 1000000000000) (-26890155023 / 1000000000000)))) (orderedInterval (5216426022 / 1000000000000) (5216426144 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_chunkChecks0 :
    compactCertificate566.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate566.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate566_chunkChecks0_0
    compactCertificate566_chunkChecks0_1 compactCertificate566_chunkChecks0_2

theorem compactCertificate566_chunkChecks1_0 :
    compactCertificate566.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (875 / 2) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38125476134 / 1000000000000) (-38125475598 / 1000000000000), orderedInterval (1299776014 / 1000000000000) (1299776550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (10312336635307 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (22794769195 / 1000000000000) (22794771394 / 1000000000000), orderedInterval (-38191380769 / 1000000000000) (-38191378569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (3334797787531 / 6400000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11753232758 / 1000000000000) (11753232759 / 1000000000000), orderedInterval (32907335877 / 1000000000000) (32907335878 / 1000000000000)))) (orderedInterval (2552920868 / 1000000000000) (2552921130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (3009114110849 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44477297019 / 1000000000000) (44477297020 / 1000000000000), orderedInterval (68986724908 / 1000000000000) (68986724909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (8082903768653 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44589182929 / 1000000000000) (44589206317 / 1000000000000), orderedInterval (-23156900487 / 1000000000000) (-23156877100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (21946656080601 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29973617056 / 1000000000000) (29973628129 / 1000000000000), orderedInterval (-5483069595 / 1000000000000) (-5483058523 / 1000000000000)))) (orderedInterval (-37980099 / 1000000000000) (-37978312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (16165807537313 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6013469422 / 1000000000000) (-6013469421 / 1000000000000), orderedInterval (-34980032548 / 1000000000000) (-34980032547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (27700386752549 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16567704514 / 1000000000000) (-16567704179 / 1000000000000), orderedInterval (21479226210 / 1000000000000) (21479226544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (20403979508591 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19528885002 / 1000000000000) (-19528885001 / 1000000000000), orderedInterval (-24825121149 / 1000000000000) (-24825121148 / 1000000000000)))) (orderedInterval (-2185251012 / 1000000000000) (-2185250948 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_chunkChecks1_1 :
    compactCertificate566.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (31304951684993 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22870664355 / 1000000000000) (-22870638799 / 1000000000000), orderedInterval (11311568218 / 1000000000000) (11311593773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (18073922282297 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3637869828 / 1000000000000) (3637869829 / 1000000000000), orderedInterval (33372008243 / 1000000000000) (33372008244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (32072492256973 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19466457043 / 1000000000000) (-19466457041 / 1000000000000), orderedInterval (-15997720780 / 1000000000000) (-15997720778 / 1000000000000)))) (orderedInterval (-6512126083 / 1000000000000) (-6512115570 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (29966282600737 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22445963425 / 1000000000000) (22445963431 / 1000000000000), orderedInterval (13254659015 / 1000000000000) (13254659021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (21385353243121 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2519895249 / 1000000000000) (2519895250 / 1000000000000), orderedInterval (-30763178883 / 1000000000000) (-30763178882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (24248711305959 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28712590746 / 1000000000000) (-28712590260 / 1000000000000), orderedInterval (-3944284830 / 1000000000000) (-3944284343 / 1000000000000)))) (orderedInterval (-4921264270 / 1000000000000) (-4921264181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (20216047431671 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27945556938 / 1000000000000) (-27945556937 / 1000000000000), orderedInterval (-15036159111 / 1000000000000) (-15036159110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (17861490997091 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8248086601 / 1000000000000) (-8248086593 / 1000000000000), orderedInterval (32756653882 / 1000000000000) (32756653891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (5176956276009 / 6400000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21006611645 / 1000000000000) (-21006607357 / 1000000000000), orderedInterval (18607122199 / 1000000000000) (18607126486 / 1000000000000)))) (orderedInterval (-1761470238 / 1000000000000) (-1761469973 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_chunkChecks1_2 :
    compactCertificate566.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (14319733507723 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31133334660 / 1000000000000) (31133414380 / 1000000000000), orderedInterval (-21326915238 / 1000000000000) (-21326835517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (12138996681203 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (163705756 / 1000000000000) (163705757 / 1000000000000), orderedInterval (-40965915303 / 1000000000000) (-40965915302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (7596020491409 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-29263831520 / 1000000000000) (-29263824742 / 1000000000000), orderedInterval (42787964630 / 1000000000000) (42787971408 / 1000000000000)))) (orderedInterval (6254118614 / 1000000000000) (6254131873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (4085165083503 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24841537848 / 1000000000000) (24841538708 / 1000000000000), orderedInterval (-66201075438 / 1000000000000) (-66201074578 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (11092017879509 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41364199035 / 1000000000000) (41364203556 / 1000000000000), orderedInterval (-11267798821 / 1000000000000) (-11267794301 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (15145202128693 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11110999974 / 1000000000000) (11111000015 / 1000000000000), orderedInterval (-34963815312 / 1000000000000) (-34963815271 / 1000000000000)))) (orderedInterval (3458007310 / 1000000000000) (3458007447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (6403979508591 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-8584439751 / 1000000000000) (-8584439719 / 1000000000000), orderedInterval (55765843827 / 1000000000000) (55765843859 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (26031821164111 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15960479826 / 1000000000000) (-15960479825 / 1000000000000), orderedInterval (-22964901869 / 1000000000000) (-22964901868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (17388050117249 / 32000000000) 1 (IntervalRat.scale (875 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21153535939 / 1000000000000) (-21153535938 / 1000000000000), orderedInterval (-26890155024 / 1000000000000) (-26890155023 / 1000000000000)))) (orderedInterval (9896025795 / 1000000000000) (9896025966 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_chunkChecks1 :
    compactCertificate566.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate566.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate566_chunkChecks1_0
    compactCertificate566_chunkChecks1_1 compactCertificate566_chunkChecks1_2

theorem compactCertificate566_chunkChecks2_0 :
    compactCertificate566.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (875 / 2) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38125476134 / 1000000000000) (-38125475598 / 1000000000000), orderedInterval (1299776014 / 1000000000000) (1299776550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (10312336635307 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (22794769195 / 1000000000000) (22794771394 / 1000000000000), orderedInterval (-38191380769 / 1000000000000) (-38191378569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (3334797787531 / 6400000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11753232758 / 1000000000000) (11753232759 / 1000000000000), orderedInterval (32907335877 / 1000000000000) (32907335878 / 1000000000000)))) (orderedInterval (14012209209 / 1000000000000) (14012209473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (3009114110849 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44477297019 / 1000000000000) (44477297020 / 1000000000000), orderedInterval (68986724908 / 1000000000000) (68986724909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (8082903768653 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44589182929 / 1000000000000) (44589206317 / 1000000000000), orderedInterval (-23156900487 / 1000000000000) (-23156877100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (21946656080601 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29973617056 / 1000000000000) (29973628129 / 1000000000000), orderedInterval (-5483069595 / 1000000000000) (-5483058523 / 1000000000000)))) (orderedInterval (4716022077 / 1000000000000) (4716024383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (16165807537313 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6013469422 / 1000000000000) (-6013469421 / 1000000000000), orderedInterval (-34980032548 / 1000000000000) (-34980032547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (27700386752549 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16567704514 / 1000000000000) (-16567704179 / 1000000000000), orderedInterval (21479226210 / 1000000000000) (21479226544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (20403979508591 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19528885002 / 1000000000000) (-19528885001 / 1000000000000), orderedInterval (-24825121149 / 1000000000000) (-24825121148 / 1000000000000)))) (orderedInterval (-993033292 / 1000000000000) (-993033175 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_chunkChecks2_1 :
    compactCertificate566.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (31304951684993 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22870664355 / 1000000000000) (-22870638799 / 1000000000000), orderedInterval (11311568218 / 1000000000000) (11311593773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (18073922282297 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3637869828 / 1000000000000) (3637869829 / 1000000000000), orderedInterval (33372008243 / 1000000000000) (33372008244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (32072492256973 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19466457043 / 1000000000000) (-19466457041 / 1000000000000), orderedInterval (-15997720780 / 1000000000000) (-15997720778 / 1000000000000)))) (orderedInterval (-6230386987 / 1000000000000) (-6230363487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (29966282600737 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22445963425 / 1000000000000) (22445963431 / 1000000000000), orderedInterval (13254659015 / 1000000000000) (13254659021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (21385353243121 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2519895249 / 1000000000000) (2519895250 / 1000000000000), orderedInterval (-30763178883 / 1000000000000) (-30763178882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (24248711305959 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28712590746 / 1000000000000) (-28712590260 / 1000000000000), orderedInterval (-3944284830 / 1000000000000) (-3944284343 / 1000000000000)))) (orderedInterval (875854141 / 1000000000000) (875854289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (20216047431671 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27945556938 / 1000000000000) (-27945556937 / 1000000000000), orderedInterval (-15036159111 / 1000000000000) (-15036159110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (17861490997091 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8248086601 / 1000000000000) (-8248086593 / 1000000000000), orderedInterval (32756653882 / 1000000000000) (32756653891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (5176956276009 / 6400000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21006611645 / 1000000000000) (-21006607357 / 1000000000000), orderedInterval (18607122199 / 1000000000000) (18607126486 / 1000000000000)))) (orderedInterval (1747251179 / 1000000000000) (1747251646 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_chunkChecks2_2 :
    compactCertificate566.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (14319733507723 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31133334660 / 1000000000000) (31133414380 / 1000000000000), orderedInterval (-21326915238 / 1000000000000) (-21326835517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (12138996681203 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (163705756 / 1000000000000) (163705757 / 1000000000000), orderedInterval (-40965915303 / 1000000000000) (-40965915302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (7596020491409 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-29263831520 / 1000000000000) (-29263824742 / 1000000000000), orderedInterval (42787964630 / 1000000000000) (42787971408 / 1000000000000)))) (orderedInterval (5481086208 / 1000000000000) (5481099735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (4085165083503 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24841537848 / 1000000000000) (24841538708 / 1000000000000), orderedInterval (-66201075438 / 1000000000000) (-66201074578 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (11092017879509 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41364199035 / 1000000000000) (41364203556 / 1000000000000), orderedInterval (-11267798821 / 1000000000000) (-11267794301 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (15145202128693 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11110999974 / 1000000000000) (11111000015 / 1000000000000), orderedInterval (-34963815312 / 1000000000000) (-34963815271 / 1000000000000)))) (orderedInterval (1616762312 / 1000000000000) (1616762428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (6403979508591 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-8584439751 / 1000000000000) (-8584439719 / 1000000000000), orderedInterval (55765843827 / 1000000000000) (55765843859 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (26031821164111 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15960479826 / 1000000000000) (-15960479825 / 1000000000000), orderedInterval (-22964901869 / 1000000000000) (-22964901868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (17388050117249 / 32000000000) 2 (IntervalRat.scale (875 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21153535939 / 1000000000000) (-21153535938 / 1000000000000), orderedInterval (-26890155024 / 1000000000000) (-26890155023 / 1000000000000)))) (orderedInterval (-10626137305 / 1000000000000) (-10626137053 / 1000000000000))) = true
  rfl'

theorem compactCertificate566_chunkChecks2 :
    compactCertificate566.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate566.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate566_chunkChecks2_0
    compactCertificate566_chunkChecks2_1 compactCertificate566_chunkChecks2_2

theorem compactCertificate566_chunkChecks3_0 :
    compactCertificate566.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (875 / 2) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38125476134 / 1000000000000) (-38125475598 / 1000000000000), orderedInterval (1299776014 / 1000000000000) (1299776550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (10312336635307 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (22794769195 / 1000000000000) (22794771394 / 1000000000000), orderedInterval (-38191380769 / 1000000000000) (-38191378569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (3334797787531 / 6400000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11753232758 / 1000000000000) (11753232759 / 1000000000000), orderedInterval (32907335877 / 1000000000000) (32907335878 / 1000000000000)))) (orderedInterval (-3667288298 / 1000000000000) (-3667288030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (3009114110849 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44477297019 / 1000000000000) (44477297020 / 1000000000000), orderedInterval (68986724908 / 1000000000000) (68986724909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (8082903768653 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44589182929 / 1000000000000) (44589206317 / 1000000000000), orderedInterval (-23156900487 / 1000000000000) (-23156877100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (21946656080601 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29973617056 / 1000000000000) (29973628129 / 1000000000000), orderedInterval (-5483069595 / 1000000000000) (-5483058523 / 1000000000000)))) (orderedInterval (-1342220585 / 1000000000000) (-1342217259 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (16165807537313 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6013469422 / 1000000000000) (-6013469421 / 1000000000000), orderedInterval (-34980032548 / 1000000000000) (-34980032547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (27700386752549 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16567704514 / 1000000000000) (-16567704179 / 1000000000000), orderedInterval (21479226210 / 1000000000000) (21479226544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (20403979508591 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19528885002 / 1000000000000) (-19528885001 / 1000000000000), orderedInterval (-24825121149 / 1000000000000) (-24825121148 / 1000000000000)))) (orderedInterval (6991322930 / 1000000000000) (6991323148 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate566_chunkChecks3_1 :
    compactCertificate566.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (31304951684993 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22870664355 / 1000000000000) (-22870638799 / 1000000000000), orderedInterval (11311568218 / 1000000000000) (11311593773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (18073922282297 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3637869828 / 1000000000000) (3637869829 / 1000000000000), orderedInterval (33372008243 / 1000000000000) (33372008244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (32072492256973 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19466457043 / 1000000000000) (-19466457041 / 1000000000000), orderedInterval (-15997720780 / 1000000000000) (-15997720778 / 1000000000000)))) (orderedInterval (44508150196 / 1000000000000) (44508202707 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (29966282600737 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22445963425 / 1000000000000) (22445963431 / 1000000000000), orderedInterval (13254659015 / 1000000000000) (13254659021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (21385353243121 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2519895249 / 1000000000000) (2519895250 / 1000000000000), orderedInterval (-30763178883 / 1000000000000) (-30763178882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (24248711305959 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28712590746 / 1000000000000) (-28712590260 / 1000000000000), orderedInterval (-3944284830 / 1000000000000) (-3944284343 / 1000000000000)))) (orderedInterval (12609356452 / 1000000000000) (12609356704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (20216047431671 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27945556938 / 1000000000000) (-27945556937 / 1000000000000), orderedInterval (-15036159111 / 1000000000000) (-15036159110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (17861490997091 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8248086601 / 1000000000000) (-8248086593 / 1000000000000), orderedInterval (32756653882 / 1000000000000) (32756653891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (5176956276009 / 6400000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21006611645 / 1000000000000) (-21006607357 / 1000000000000), orderedInterval (18607122199 / 1000000000000) (18607126486 / 1000000000000)))) (orderedInterval (1400469339 / 1000000000000) (1400470174 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate566_chunkChecks3_2 :
    compactCertificate566.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (14319733507723 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31133334660 / 1000000000000) (31133414380 / 1000000000000), orderedInterval (-21326915238 / 1000000000000) (-21326835517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (12138996681203 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (163705756 / 1000000000000) (163705757 / 1000000000000), orderedInterval (-40965915303 / 1000000000000) (-40965915302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (7596020491409 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-29263831520 / 1000000000000) (-29263824742 / 1000000000000), orderedInterval (42787964630 / 1000000000000) (42787971408 / 1000000000000)))) (orderedInterval (-5395494900 / 1000000000000) (-5395481100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (4085165083503 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24841537848 / 1000000000000) (24841538708 / 1000000000000), orderedInterval (-66201075438 / 1000000000000) (-66201074578 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (11092017879509 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41364199035 / 1000000000000) (41364203556 / 1000000000000), orderedInterval (-11267798821 / 1000000000000) (-11267794301 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (15145202128693 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11110999974 / 1000000000000) (11111000015 / 1000000000000), orderedInterval (-34963815312 / 1000000000000) (-34963815271 / 1000000000000)))) (orderedInterval (-3553597814 / 1000000000000) (-3553597710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (6403979508591 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-8584439751 / 1000000000000) (-8584439719 / 1000000000000), orderedInterval (55765843827 / 1000000000000) (55765843859 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (26031821164111 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15960479826 / 1000000000000) (-15960479825 / 1000000000000), orderedInterval (-22964901869 / 1000000000000) (-22964901868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (17388050117249 / 32000000000) 3 (IntervalRat.scale (875 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21153535939 / 1000000000000) (-21153535938 / 1000000000000), orderedInterval (-26890155024 / 1000000000000) (-26890155023 / 1000000000000)))) (orderedInterval (-21691927609 / 1000000000000) (-21691927221 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate566_chunkChecks3 :
    compactCertificate566.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate566.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate566_chunkChecks3_0
    compactCertificate566_chunkChecks3_1 compactCertificate566_chunkChecks3_2

theorem compactCertificate566_chunkChecks4_0 :
    compactCertificate566.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (875 / 2) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38125476134 / 1000000000000) (-38125475598 / 1000000000000), orderedInterval (1299776014 / 1000000000000) (1299776550 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (10312336635307 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (22794769195 / 1000000000000) (22794771394 / 1000000000000), orderedInterval (-38191380769 / 1000000000000) (-38191378569 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (3334797787531 / 6400000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (11753232758 / 1000000000000) (11753232759 / 1000000000000), orderedInterval (32907335877 / 1000000000000) (32907335878 / 1000000000000)))) (orderedInterval (-13644518087 / 1000000000000) (-13644517814 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (3009114110849 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (44477297019 / 1000000000000) (44477297020 / 1000000000000), orderedInterval (68986724908 / 1000000000000) (68986724909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (8082903768653 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44589182929 / 1000000000000) (44589206317 / 1000000000000), orderedInterval (-23156900487 / 1000000000000) (-23156877100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (21946656080601 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29973617056 / 1000000000000) (29973628129 / 1000000000000), orderedInterval (-5483069595 / 1000000000000) (-5483058523 / 1000000000000)))) (orderedInterval (-12681855092 / 1000000000000) (-12681850038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (16165807537313 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-6013469422 / 1000000000000) (-6013469421 / 1000000000000), orderedInterval (-34980032548 / 1000000000000) (-34980032547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (27700386752549 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16567704514 / 1000000000000) (-16567704179 / 1000000000000), orderedInterval (21479226210 / 1000000000000) (21479226544 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (20403979508591 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-19528885002 / 1000000000000) (-19528885001 / 1000000000000), orderedInterval (-24825121149 / 1000000000000) (-24825121148 / 1000000000000)))) (orderedInterval (5670438991 / 1000000000000) (5670439405 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate566_chunkChecks4_1 :
    compactCertificate566.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (31304951684993 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-22870664355 / 1000000000000) (-22870638799 / 1000000000000), orderedInterval (11311568218 / 1000000000000) (11311593773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (18073922282297 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3637869828 / 1000000000000) (3637869829 / 1000000000000), orderedInterval (33372008243 / 1000000000000) (33372008244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (32072492256973 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19466457043 / 1000000000000) (-19466457041 / 1000000000000), orderedInterval (-15997720780 / 1000000000000) (-15997720778 / 1000000000000)))) (orderedInterval (25920852284 / 1000000000000) (25920969796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (29966282600737 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22445963425 / 1000000000000) (22445963431 / 1000000000000), orderedInterval (13254659015 / 1000000000000) (13254659021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (21385353243121 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (2519895249 / 1000000000000) (2519895250 / 1000000000000), orderedInterval (-30763178883 / 1000000000000) (-30763178882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (24248711305959 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28712590746 / 1000000000000) (-28712590260 / 1000000000000), orderedInterval (-3944284830 / 1000000000000) (-3944284343 / 1000000000000)))) (orderedInterval (-5958249608 / 1000000000000) (-5958249171 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (20216047431671 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-27945556938 / 1000000000000) (-27945556937 / 1000000000000), orderedInterval (-15036159111 / 1000000000000) (-15036159110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (17861490997091 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-8248086601 / 1000000000000) (-8248086593 / 1000000000000), orderedInterval (32756653882 / 1000000000000) (32756653891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (5176956276009 / 6400000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-21006611645 / 1000000000000) (-21006607357 / 1000000000000), orderedInterval (18607122199 / 1000000000000) (18607126486 / 1000000000000)))) (orderedInterval (-6444229129 / 1000000000000) (-6444227621 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate566_chunkChecks4_2 :
    compactCertificate566.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (14319733507723 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31133334660 / 1000000000000) (31133414380 / 1000000000000), orderedInterval (-21326915238 / 1000000000000) (-21326835517 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (12138996681203 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (163705756 / 1000000000000) (163705757 / 1000000000000), orderedInterval (-40965915303 / 1000000000000) (-40965915302 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (7596020491409 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-29263831520 / 1000000000000) (-29263824742 / 1000000000000), orderedInterval (42787964630 / 1000000000000) (42787971408 / 1000000000000)))) (orderedInterval (-5511673416 / 1000000000000) (-5511659290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (4085165083503 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (24841537848 / 1000000000000) (24841538708 / 1000000000000), orderedInterval (-66201075438 / 1000000000000) (-66201074578 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (11092017879509 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41364199035 / 1000000000000) (41364203556 / 1000000000000), orderedInterval (-11267798821 / 1000000000000) (-11267794301 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (15145202128693 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (11110999974 / 1000000000000) (11111000015 / 1000000000000), orderedInterval (-34963815312 / 1000000000000) (-34963815271 / 1000000000000)))) (orderedInterval (-1523086600 / 1000000000000) (-1523086504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (6403979508591 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-8584439751 / 1000000000000) (-8584439719 / 1000000000000), orderedInterval (55765843827 / 1000000000000) (55765843859 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (26031821164111 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-15960479826 / 1000000000000) (-15960479825 / 1000000000000), orderedInterval (-22964901869 / 1000000000000) (-22964901868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (17388050117249 / 32000000000) 4 (IntervalRat.scale (875 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21153535939 / 1000000000000) (-21153535938 / 1000000000000), orderedInterval (-26890155024 / 1000000000000) (-26890155023 / 1000000000000)))) (orderedInterval (25071632345 / 1000000000000) (25071632968 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate566_chunkChecks4 :
    compactCertificate566.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate566.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate566_chunkChecks4_0
    compactCertificate566_chunkChecks4_1 compactCertificate566_chunkChecks4_2

theorem compactCertificate566_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate566.chunkCheck r b = true :=
  compactCertificate566.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate566_chunkChecks0
    · exact compactCertificate566_chunkChecks1
    · exact compactCertificate566_chunkChecks2
    · exact compactCertificate566_chunkChecks3
    · exact compactCertificate566_chunkChecks4)

theorem compactCertificate566_coefficient0 :
    compactCertificate566.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate566_coefficient1 :
    compactCertificate566.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate566_coefficient2 :
    compactCertificate566.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate566_coefficient3 :
    compactCertificate566.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate566_coefficient4 :
    compactCertificate566.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate566_coefficients : ∀ r : Fin 5,
    compactCertificate566.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate566_coefficient0
  · exact compactCertificate566_coefficient1
  · exact compactCertificate566_coefficient2
  · exact compactCertificate566_coefficient3
  · exact compactCertificate566_coefficient4

theorem compactCertificate566_lower : (1 : ℚ) ≤ compactCertificate566.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate566, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate566_proves {t : ℝ} (ht : t ∈ compactCertificate566.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate566.proves compactCertificate566_states compactCertificate566_chunks
    compactCertificate566_coefficients compactCertificate566_lower ht

end Erdos232
