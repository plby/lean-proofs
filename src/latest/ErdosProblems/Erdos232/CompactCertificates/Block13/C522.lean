/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate522 : CompactCertificate where
  left := 393
  right := 394
  center := 787 / 2
  grid := fun i =>
    match i.val with
    | 0 => 125
    | 1 => 92
    | 2 => 149
    | 3 => 27
    | 4 => 72
    | 5 => 196
    | 6 => 145
    | 7 => 248
    | 8 => 183
    | 9 => 280
    | 10 => 162
    | 11 => 287
    | 12 => 268
    | 13 => 191
    | 14 => 217
    | 15 => 181
    | 16 => 160
    | 17 => 232
    | 18 => 128
    | 19 => 109
    | 20 => 68
    | 21 => 37
    | 22 => 99
    | 23 => 136
    | 24 => 57
    | 25 => 233
    | _ => 156
  point := fun i =>
    match i.val with
    | 0 => 787 / 2
    | 1 => 1159401275998087 / 4000000000000
    | 2 => 374926551255271 / 800000000000
    | 3 => 338310400748309 / 4000000000000
    | 4 => 908749323704273 / 4000000000000
    | 5 => 2467431190776141 / 4000000000000
    | 6 => 1817498647409333 / 4000000000000
    | 7 => 3114314910608009 / 4000000000000
    | 8 => 2293990267608731 / 4000000000000
    | 9 => 3519570996584213 / 4000000000000
    | 10 => 2032025262309677 / 4000000000000
    | 11 => 3605864486605393 / 4000000000000
    | 12 => 3369066343825717 / 4000000000000
    | 13 => 2404324714619461 / 4000000000000
    | 14 => 2726247971112819 / 4000000000000
    | 15 => 2272861332675011 / 4000000000000
    | 16 => 2008141916387231 / 4000000000000
    | 17 => 582037798459869 / 800000000000
    | 18 => 1609947181511143 / 4000000000000
    | 19 => 1364770055443823 / 4000000000000
    | 20 => 854009732391269 / 4000000000000
    | 21 => 459289274388123 / 4000000000000
    | 22 => 1247059724453369 / 4000000000000
    | 23 => 1702753439325913 / 4000000000000
    | 24 => 719990267608731 / 4000000000000
    | 25 => 2926720465165051 / 4000000000000
    | _ => 1954913634610709 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-40217709384 / 1000000000000) (-40217709062 / 1000000000000), orderedInterval (662558702 / 1000000000000) (662559025 / 1000000000000))
    | 1 => (orderedInterval (46831684585 / 1000000000000) (46831684803 / 1000000000000), orderedInterval (-1859629287 / 1000000000000) (-1859629068 / 1000000000000))
    | 2 => (orderedInterval (-35929110539 / 1000000000000) (-35929110521 / 1000000000000), orderedInterval (-8176688533 / 1000000000000) (-8176688515 / 1000000000000))
    | 3 => (orderedInterval (-44495050021 / 1000000000000) (-44495050020 / 1000000000000), orderedInterval (-74217180046 / 1000000000000) (-74217180045 / 1000000000000))
    | 4 => (orderedInterval (51808618226 / 1000000000000) (51808619436 / 1000000000000), orderedInterval (-10978675465 / 1000000000000) (-10978674255 / 1000000000000))
    | 5 => (orderedInterval (30494104240 / 1000000000000) (30494134283 / 1000000000000), orderedInterval (-10131408549 / 1000000000000) (-10131378505 / 1000000000000))
    | 6 => (orderedInterval (13575791133 / 1000000000000) (13575791251 / 1000000000000), orderedInterval (-34897434187 / 1000000000000) (-34897434069 / 1000000000000))
    | 7 => (orderedInterval (7046429326 / 1000000000000) (7046429327 / 1000000000000), orderedInterval (27708596040 / 1000000000000) (27708596041 / 1000000000000))
    | 8 => (orderedInterval (19594124788 / 1000000000000) (19594126230 / 1000000000000), orderedInterval (-26963989206 / 1000000000000) (-26963987764 / 1000000000000))
    | 9 => (orderedInterval (23088410978 / 1000000000000) (23088410981 / 1000000000000), orderedInterval (13787059780 / 1000000000000) (13787059784 / 1000000000000))
    | 10 => (orderedInterval (-5169072335 / 1000000000000) (-5169072332 / 1000000000000), orderedInterval (35025856022 / 1000000000000) (35025856025 / 1000000000000))
    | 11 => (orderedInterval (-15316968085 / 1000000000000) (-15316968084 / 1000000000000), orderedInterval (-21707751860 / 1000000000000) (-21707751859 / 1000000000000))
    | 12 => (orderedInterval (24563677199 / 1000000000000) (24563677208 / 1000000000000), orderedInterval (12333165491 / 1000000000000) (12333165499 / 1000000000000))
    | 13 => (orderedInterval (-31521367425 / 1000000000000) (-31521352834 / 1000000000000), orderedInterval (8121148032 / 1000000000000) (8121162623 / 1000000000000))
    | 14 => (orderedInterval (-17797641761 / 1000000000000) (-17797641760 / 1000000000000), orderedInterval (-24832546639 / 1000000000000) (-24832546638 / 1000000000000))
    | 15 => (orderedInterval (-12173948870 / 1000000000000) (-12173948869 / 1000000000000), orderedInterval (-31169088718 / 1000000000000) (-31169088717 / 1000000000000))
    | 16 => (orderedInterval (5877265156 / 1000000000000) (5877265157 / 1000000000000), orderedInterval (35115872099 / 1000000000000) (35115872100 / 1000000000000))
    | 17 => (orderedInterval (-14621561891 / 1000000000000) (-14621561760 / 1000000000000), orderedInterval (25724478870 / 1000000000000) (25724479000 / 1000000000000))
    | 18 => (orderedInterval (36269147217 / 1000000000000) (36269147218 / 1000000000000), orderedInterval (16272543813 / 1000000000000) (16272543814 / 1000000000000))
    | 19 => (orderedInterval (19023732160 / 1000000000000) (19023732912 / 1000000000000), orderedInterval (-38808873847 / 1000000000000) (-38808873096 / 1000000000000))
    | 20 => (orderedInterval (33434166329 / 1000000000000) (33434166330 / 1000000000000), orderedInterval (43095190928 / 1000000000000) (43095190929 / 1000000000000))
    | 21 => (orderedInterval (44006159638 / 1000000000000) (44006176744 / 1000000000000), orderedInterval (-60257124865 / 1000000000000) (-60257107759 / 1000000000000))
    | 22 => (orderedInterval (-45154758558 / 1000000000000) (-45154758470 / 1000000000000), orderedInterval (-1668742536 / 1000000000000) (-1668742447 / 1000000000000))
    | 23 => (orderedInterval (-27283162699 / 1000000000000) (-27283146556 / 1000000000000), orderedInterval (27438900161 / 1000000000000) (27438916303 / 1000000000000))
    | 24 => (orderedInterval (-58883460369 / 1000000000000) (-58883459965 / 1000000000000), orderedInterval (8503190043 / 1000000000000) (8503190447 / 1000000000000))
    | 25 => (orderedInterval (-13470622262 / 1000000000000) (-13470622261 / 1000000000000), orderedInterval (-26232399513 / 1000000000000) (-26232399512 / 1000000000000))
    | _ => (orderedInterval (-19624928501 / 1000000000000) (-19624927229 / 1000000000000), orderedInterval (30309792580 / 1000000000000) (30309793851 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-17612872831 / 1000000000000) (-17612872673 / 1000000000000)
      | 1 => orderedInterval (206545772 / 1000000000000) (206548000 / 1000000000000)
      | 2 => orderedInterval (256211252 / 1000000000000) (256211310 / 1000000000000)
      | 3 => orderedInterval (-6662914924 / 1000000000000) (-6662914768 / 1000000000000)
      | 4 => orderedInterval (-3334134726 / 1000000000000) (-3334133299 / 1000000000000)
      | 5 => orderedInterval (-851286858 / 1000000000000) (-851286816 / 1000000000000)
      | 6 => orderedInterval (-5787446668 / 1000000000000) (-5787446526 / 1000000000000)
      | 7 => orderedInterval (2302790070 / 1000000000000) (2302791673 / 1000000000000)
      | _ => orderedInterval (4423720660 / 1000000000000) (4423721011 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-321610917 / 1000000000000) (-321610755 / 1000000000000)
      | 1 => orderedInterval (1070691850 / 1000000000000) (1070695278 / 1000000000000)
      | 2 => orderedInterval (-2640754062 / 1000000000000) (-2640753973 / 1000000000000)
      | 3 => orderedInterval (-9197040555 / 1000000000000) (-9197040229 / 1000000000000)
      | 4 => orderedInterval (914163823 / 1000000000000) (914166008 / 1000000000000)
      | 5 => orderedInterval (-1865801728 / 1000000000000) (-1865801667 / 1000000000000)
      | 6 => orderedInterval (4529920 / 1000000000000) (4530049 / 1000000000000)
      | 7 => orderedInterval (-1920239440 / 1000000000000) (-1920237965 / 1000000000000)
      | _ => orderedInterval (-3069199600 / 1000000000000) (-3069199149 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (18695607344 / 1000000000000) (18695607510 / 1000000000000)
      | 1 => orderedInterval (4671683603 / 1000000000000) (4671688949 / 1000000000000)
      | 2 => orderedInterval (-148301916 / 1000000000000) (-148301773 / 1000000000000)
      | 3 => orderedInterval (32601730094 / 1000000000000) (32601730791 / 1000000000000)
      | 4 => orderedInterval (8714236143 / 1000000000000) (8714239495 / 1000000000000)
      | 5 => orderedInterval (2125108952 / 1000000000000) (2125109045 / 1000000000000)
      | 6 => orderedInterval (6556141642 / 1000000000000) (6556141762 / 1000000000000)
      | 7 => orderedInterval (-3016001932 / 1000000000000) (-3016000410 / 1000000000000)
      | _ => orderedInterval (-9389104198 / 1000000000000) (-9389103602 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (507404055 / 1000000000000) (507404228 / 1000000000000)
      | 1 => orderedInterval (-2717296051 / 1000000000000) (-2717287690 / 1000000000000)
      | 2 => orderedInterval (8637740732 / 1000000000000) (8637740965 / 1000000000000)
      | 3 => orderedInterval (58824487136 / 1000000000000) (58824488664 / 1000000000000)
      | 4 => orderedInterval (-1228872368 / 1000000000000) (-1228867227 / 1000000000000)
      | 5 => orderedInterval (1088572874 / 1000000000000) (1088573021 / 1000000000000)
      | 6 => orderedInterval (1111575569 / 1000000000000) (1111575682 / 1000000000000)
      | 7 => orderedInterval (2623479018 / 1000000000000) (2623480640 / 1000000000000)
      | _ => orderedInterval (-2813417371 / 1000000000000) (-2813416564 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-20057083974 / 1000000000000) (-20057083795 / 1000000000000)
      | 1 => orderedInterval (-12866282911 / 1000000000000) (-12866269795 / 1000000000000)
      | 2 => orderedInterval (-1238318478 / 1000000000000) (-1238318090 / 1000000000000)
      | 3 => orderedInterval (-163898999324 / 1000000000000) (-163898995935 / 1000000000000)
      | 4 => orderedInterval (-24719800744 / 1000000000000) (-24719792833 / 1000000000000)
      | 5 => orderedInterval (-5882737728 / 1000000000000) (-5882737491 / 1000000000000)
      | 6 => orderedInterval (-6867233430 / 1000000000000) (-6867233322 / 1000000000000)
      | 7 => orderedInterval (3248135861 / 1000000000000) (3248137612 / 1000000000000)
      | _ => orderedInterval (21868238364 / 1000000000000) (21868239495 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-27059388253 / 1000000000000) (-27059382088 / 1000000000000)
    | 1 => orderedInterval (-17025260709 / 1000000000000) (-17025252403 / 1000000000000)
    | 2 => orderedInterval (60811099732 / 1000000000000) (60811111767 / 1000000000000)
    | 3 => orderedInterval (66033673594 / 1000000000000) (66033691719 / 1000000000000)
    | _ => orderedInterval (-210414082364 / 1000000000000) (-210414054154 / 1000000000000)

theorem compactCertificate522_stateChecks0 :
    compactCertificate522.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (787 / 2)) (orderedInterval (-40217709384 / 1000000000000) (-40217709062 / 1000000000000), orderedInterval (662558702 / 1000000000000) (662559025 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1159401275998087 / 4000000000000)) (orderedInterval (46831684585 / 1000000000000) (46831684803 / 1000000000000), orderedInterval (-1859629287 / 1000000000000) (-1859629068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (374926551255271 / 800000000000)) (orderedInterval (-35929110539 / 1000000000000) (-35929110521 / 1000000000000), orderedInterval (-8176688533 / 1000000000000) (-8176688515 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_stateChecks1 :
    compactCertificate522.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (338310400748309 / 4000000000000)) (orderedInterval (-44495050021 / 1000000000000) (-44495050020 / 1000000000000), orderedInterval (-74217180046 / 1000000000000) (-74217180045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (908749323704273 / 4000000000000)) (orderedInterval (51808618226 / 1000000000000) (51808619436 / 1000000000000), orderedInterval (-10978675465 / 1000000000000) (-10978674255 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2467431190776141 / 4000000000000)) (orderedInterval (30494104240 / 1000000000000) (30494134283 / 1000000000000), orderedInterval (-10131408549 / 1000000000000) (-10131378505 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_stateChecks2 :
    compactCertificate522.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1817498647409333 / 4000000000000)) (orderedInterval (13575791133 / 1000000000000) (13575791251 / 1000000000000), orderedInterval (-34897434187 / 1000000000000) (-34897434069 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3114314910608009 / 4000000000000)) (orderedInterval (7046429326 / 1000000000000) (7046429327 / 1000000000000), orderedInterval (27708596040 / 1000000000000) (27708596041 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2293990267608731 / 4000000000000)) (orderedInterval (19594124788 / 1000000000000) (19594126230 / 1000000000000), orderedInterval (-26963989206 / 1000000000000) (-26963987764 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_stateChecks3 :
    compactCertificate522.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 280 12 (3519570996584213 / 4000000000000)) (orderedInterval (23088410978 / 1000000000000) (23088410981 / 1000000000000), orderedInterval (13787059780 / 1000000000000) (13787059784 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2032025262309677 / 4000000000000)) (orderedInterval (-5169072335 / 1000000000000) (-5169072332 / 1000000000000), orderedInterval (35025856022 / 1000000000000) (35025856025 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 287 12 (3605864486605393 / 4000000000000)) (orderedInterval (-15316968085 / 1000000000000) (-15316968084 / 1000000000000), orderedInterval (-21707751860 / 1000000000000) (-21707751859 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_stateChecks4 :
    compactCertificate522.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 268 12 (3369066343825717 / 4000000000000)) (orderedInterval (24563677199 / 1000000000000) (24563677208 / 1000000000000), orderedInterval (12333165491 / 1000000000000) (12333165499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2404324714619461 / 4000000000000)) (orderedInterval (-31521367425 / 1000000000000) (-31521352834 / 1000000000000), orderedInterval (8121148032 / 1000000000000) (8121162623 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (2726247971112819 / 4000000000000)) (orderedInterval (-17797641761 / 1000000000000) (-17797641760 / 1000000000000), orderedInterval (-24832546639 / 1000000000000) (-24832546638 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_stateChecks5 :
    compactCertificate522.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2272861332675011 / 4000000000000)) (orderedInterval (-12173948870 / 1000000000000) (-12173948869 / 1000000000000), orderedInterval (-31169088718 / 1000000000000) (-31169088717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2008141916387231 / 4000000000000)) (orderedInterval (5877265156 / 1000000000000) (5877265157 / 1000000000000), orderedInterval (35115872099 / 1000000000000) (35115872100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (582037798459869 / 800000000000)) (orderedInterval (-14621561891 / 1000000000000) (-14621561760 / 1000000000000), orderedInterval (25724478870 / 1000000000000) (25724479000 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_stateChecks6 :
    compactCertificate522.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1609947181511143 / 4000000000000)) (orderedInterval (36269147217 / 1000000000000) (36269147218 / 1000000000000), orderedInterval (16272543813 / 1000000000000) (16272543814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1364770055443823 / 4000000000000)) (orderedInterval (19023732160 / 1000000000000) (19023732912 / 1000000000000), orderedInterval (-38808873847 / 1000000000000) (-38808873096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (854009732391269 / 4000000000000)) (orderedInterval (33434166329 / 1000000000000) (33434166330 / 1000000000000), orderedInterval (43095190928 / 1000000000000) (43095190929 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_stateChecks7 :
    compactCertificate522.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (459289274388123 / 4000000000000)) (orderedInterval (44006159638 / 1000000000000) (44006176744 / 1000000000000), orderedInterval (-60257124865 / 1000000000000) (-60257107759 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1247059724453369 / 4000000000000)) (orderedInterval (-45154758558 / 1000000000000) (-45154758470 / 1000000000000), orderedInterval (-1668742536 / 1000000000000) (-1668742447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1702753439325913 / 4000000000000)) (orderedInterval (-27283162699 / 1000000000000) (-27283146556 / 1000000000000), orderedInterval (27438900161 / 1000000000000) (27438916303 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_stateChecks8 :
    compactCertificate522.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (719990267608731 / 4000000000000)) (orderedInterval (-58883460369 / 1000000000000) (-58883459965 / 1000000000000), orderedInterval (8503190043 / 1000000000000) (8503190447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (2926720465165051 / 4000000000000)) (orderedInterval (-13470622262 / 1000000000000) (-13470622261 / 1000000000000), orderedInterval (-26232399513 / 1000000000000) (-26232399512 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1954913634610709 / 4000000000000)) (orderedInterval (-19624928501 / 1000000000000) (-19624927229 / 1000000000000), orderedInterval (30309792580 / 1000000000000) (30309793851 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_states : ∀ j,
    BesselStateValid (compactCertificate522.point j) (compactCertificate522.state j) :=
  compactCertificate522.statesValid_of_checks3 compactCertificate522_stateChecks0
    compactCertificate522_stateChecks1 compactCertificate522_stateChecks2
    compactCertificate522_stateChecks3 compactCertificate522_stateChecks4
    compactCertificate522_stateChecks5 compactCertificate522_stateChecks6
    compactCertificate522_stateChecks7 compactCertificate522_stateChecks8

theorem compactCertificate522_chunkChecks0_0 :
    compactCertificate522.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (787 / 2) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40217709384 / 1000000000000) (-40217709062 / 1000000000000), orderedInterval (662558702 / 1000000000000) (662559025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1159401275998087 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46831684585 / 1000000000000) (46831684803 / 1000000000000), orderedInterval (-1859629287 / 1000000000000) (-1859629068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (374926551255271 / 800000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-35929110539 / 1000000000000) (-35929110521 / 1000000000000), orderedInterval (-8176688533 / 1000000000000) (-8176688515 / 1000000000000)))) (orderedInterval (-17612872831 / 1000000000000) (-17612872673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (338310400748309 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44495050021 / 1000000000000) (-44495050020 / 1000000000000), orderedInterval (-74217180046 / 1000000000000) (-74217180045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (908749323704273 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51808618226 / 1000000000000) (51808619436 / 1000000000000), orderedInterval (-10978675465 / 1000000000000) (-10978674255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2467431190776141 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30494104240 / 1000000000000) (30494134283 / 1000000000000), orderedInterval (-10131408549 / 1000000000000) (-10131378505 / 1000000000000)))) (orderedInterval (206545772 / 1000000000000) (206548000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1817498647409333 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (13575791133 / 1000000000000) (13575791251 / 1000000000000), orderedInterval (-34897434187 / 1000000000000) (-34897434069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3114314910608009 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7046429326 / 1000000000000) (7046429327 / 1000000000000), orderedInterval (27708596040 / 1000000000000) (27708596041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2293990267608731 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19594124788 / 1000000000000) (19594126230 / 1000000000000), orderedInterval (-26963989206 / 1000000000000) (-26963987764 / 1000000000000)))) (orderedInterval (256211252 / 1000000000000) (256211310 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_chunkChecks0_1 :
    compactCertificate522.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3519570996584213 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23088410978 / 1000000000000) (23088410981 / 1000000000000), orderedInterval (13787059780 / 1000000000000) (13787059784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2032025262309677 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5169072335 / 1000000000000) (-5169072332 / 1000000000000), orderedInterval (35025856022 / 1000000000000) (35025856025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3605864486605393 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15316968085 / 1000000000000) (-15316968084 / 1000000000000), orderedInterval (-21707751860 / 1000000000000) (-21707751859 / 1000000000000)))) (orderedInterval (-6662914924 / 1000000000000) (-6662914768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3369066343825717 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24563677199 / 1000000000000) (24563677208 / 1000000000000), orderedInterval (12333165491 / 1000000000000) (12333165499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2404324714619461 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-31521367425 / 1000000000000) (-31521352834 / 1000000000000), orderedInterval (8121148032 / 1000000000000) (8121162623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2726247971112819 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17797641761 / 1000000000000) (-17797641760 / 1000000000000), orderedInterval (-24832546639 / 1000000000000) (-24832546638 / 1000000000000)))) (orderedInterval (-3334134726 / 1000000000000) (-3334133299 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2272861332675011 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12173948870 / 1000000000000) (-12173948869 / 1000000000000), orderedInterval (-31169088718 / 1000000000000) (-31169088717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2008141916387231 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5877265156 / 1000000000000) (5877265157 / 1000000000000), orderedInterval (35115872099 / 1000000000000) (35115872100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (582037798459869 / 800000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-14621561891 / 1000000000000) (-14621561760 / 1000000000000), orderedInterval (25724478870 / 1000000000000) (25724479000 / 1000000000000)))) (orderedInterval (-851286858 / 1000000000000) (-851286816 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_chunkChecks0_2 :
    compactCertificate522.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1609947181511143 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36269147217 / 1000000000000) (36269147218 / 1000000000000), orderedInterval (16272543813 / 1000000000000) (16272543814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1364770055443823 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (19023732160 / 1000000000000) (19023732912 / 1000000000000), orderedInterval (-38808873847 / 1000000000000) (-38808873096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (854009732391269 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33434166329 / 1000000000000) (33434166330 / 1000000000000), orderedInterval (43095190928 / 1000000000000) (43095190929 / 1000000000000)))) (orderedInterval (-5787446668 / 1000000000000) (-5787446526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (459289274388123 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (44006159638 / 1000000000000) (44006176744 / 1000000000000), orderedInterval (-60257124865 / 1000000000000) (-60257107759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1247059724453369 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45154758558 / 1000000000000) (-45154758470 / 1000000000000), orderedInterval (-1668742536 / 1000000000000) (-1668742447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1702753439325913 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27283162699 / 1000000000000) (-27283146556 / 1000000000000), orderedInterval (27438900161 / 1000000000000) (27438916303 / 1000000000000)))) (orderedInterval (2302790070 / 1000000000000) (2302791673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (719990267608731 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58883460369 / 1000000000000) (-58883459965 / 1000000000000), orderedInterval (8503190043 / 1000000000000) (8503190447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2926720465165051 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13470622262 / 1000000000000) (-13470622261 / 1000000000000), orderedInterval (-26232399513 / 1000000000000) (-26232399512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1954913634610709 / 4000000000000) 0 (IntervalRat.scale (787 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19624928501 / 1000000000000) (-19624927229 / 1000000000000), orderedInterval (30309792580 / 1000000000000) (30309793851 / 1000000000000)))) (orderedInterval (4423720660 / 1000000000000) (4423721011 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_chunkChecks0 :
    compactCertificate522.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate522.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate522_chunkChecks0_0
    compactCertificate522_chunkChecks0_1 compactCertificate522_chunkChecks0_2

theorem compactCertificate522_chunkChecks1_0 :
    compactCertificate522.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (787 / 2) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40217709384 / 1000000000000) (-40217709062 / 1000000000000), orderedInterval (662558702 / 1000000000000) (662559025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1159401275998087 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46831684585 / 1000000000000) (46831684803 / 1000000000000), orderedInterval (-1859629287 / 1000000000000) (-1859629068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (374926551255271 / 800000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-35929110539 / 1000000000000) (-35929110521 / 1000000000000), orderedInterval (-8176688533 / 1000000000000) (-8176688515 / 1000000000000)))) (orderedInterval (-321610917 / 1000000000000) (-321610755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (338310400748309 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44495050021 / 1000000000000) (-44495050020 / 1000000000000), orderedInterval (-74217180046 / 1000000000000) (-74217180045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (908749323704273 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51808618226 / 1000000000000) (51808619436 / 1000000000000), orderedInterval (-10978675465 / 1000000000000) (-10978674255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2467431190776141 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30494104240 / 1000000000000) (30494134283 / 1000000000000), orderedInterval (-10131408549 / 1000000000000) (-10131378505 / 1000000000000)))) (orderedInterval (1070691850 / 1000000000000) (1070695278 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1817498647409333 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (13575791133 / 1000000000000) (13575791251 / 1000000000000), orderedInterval (-34897434187 / 1000000000000) (-34897434069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3114314910608009 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7046429326 / 1000000000000) (7046429327 / 1000000000000), orderedInterval (27708596040 / 1000000000000) (27708596041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2293990267608731 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19594124788 / 1000000000000) (19594126230 / 1000000000000), orderedInterval (-26963989206 / 1000000000000) (-26963987764 / 1000000000000)))) (orderedInterval (-2640754062 / 1000000000000) (-2640753973 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_chunkChecks1_1 :
    compactCertificate522.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3519570996584213 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23088410978 / 1000000000000) (23088410981 / 1000000000000), orderedInterval (13787059780 / 1000000000000) (13787059784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2032025262309677 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5169072335 / 1000000000000) (-5169072332 / 1000000000000), orderedInterval (35025856022 / 1000000000000) (35025856025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3605864486605393 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15316968085 / 1000000000000) (-15316968084 / 1000000000000), orderedInterval (-21707751860 / 1000000000000) (-21707751859 / 1000000000000)))) (orderedInterval (-9197040555 / 1000000000000) (-9197040229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3369066343825717 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24563677199 / 1000000000000) (24563677208 / 1000000000000), orderedInterval (12333165491 / 1000000000000) (12333165499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2404324714619461 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-31521367425 / 1000000000000) (-31521352834 / 1000000000000), orderedInterval (8121148032 / 1000000000000) (8121162623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2726247971112819 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17797641761 / 1000000000000) (-17797641760 / 1000000000000), orderedInterval (-24832546639 / 1000000000000) (-24832546638 / 1000000000000)))) (orderedInterval (914163823 / 1000000000000) (914166008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2272861332675011 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12173948870 / 1000000000000) (-12173948869 / 1000000000000), orderedInterval (-31169088718 / 1000000000000) (-31169088717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2008141916387231 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5877265156 / 1000000000000) (5877265157 / 1000000000000), orderedInterval (35115872099 / 1000000000000) (35115872100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (582037798459869 / 800000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-14621561891 / 1000000000000) (-14621561760 / 1000000000000), orderedInterval (25724478870 / 1000000000000) (25724479000 / 1000000000000)))) (orderedInterval (-1865801728 / 1000000000000) (-1865801667 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_chunkChecks1_2 :
    compactCertificate522.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1609947181511143 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36269147217 / 1000000000000) (36269147218 / 1000000000000), orderedInterval (16272543813 / 1000000000000) (16272543814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1364770055443823 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (19023732160 / 1000000000000) (19023732912 / 1000000000000), orderedInterval (-38808873847 / 1000000000000) (-38808873096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (854009732391269 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33434166329 / 1000000000000) (33434166330 / 1000000000000), orderedInterval (43095190928 / 1000000000000) (43095190929 / 1000000000000)))) (orderedInterval (4529920 / 1000000000000) (4530049 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (459289274388123 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (44006159638 / 1000000000000) (44006176744 / 1000000000000), orderedInterval (-60257124865 / 1000000000000) (-60257107759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1247059724453369 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45154758558 / 1000000000000) (-45154758470 / 1000000000000), orderedInterval (-1668742536 / 1000000000000) (-1668742447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1702753439325913 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27283162699 / 1000000000000) (-27283146556 / 1000000000000), orderedInterval (27438900161 / 1000000000000) (27438916303 / 1000000000000)))) (orderedInterval (-1920239440 / 1000000000000) (-1920237965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (719990267608731 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58883460369 / 1000000000000) (-58883459965 / 1000000000000), orderedInterval (8503190043 / 1000000000000) (8503190447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2926720465165051 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13470622262 / 1000000000000) (-13470622261 / 1000000000000), orderedInterval (-26232399513 / 1000000000000) (-26232399512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1954913634610709 / 4000000000000) 1 (IntervalRat.scale (787 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19624928501 / 1000000000000) (-19624927229 / 1000000000000), orderedInterval (30309792580 / 1000000000000) (30309793851 / 1000000000000)))) (orderedInterval (-3069199600 / 1000000000000) (-3069199149 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_chunkChecks1 :
    compactCertificate522.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate522.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate522_chunkChecks1_0
    compactCertificate522_chunkChecks1_1 compactCertificate522_chunkChecks1_2

theorem compactCertificate522_chunkChecks2_0 :
    compactCertificate522.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (787 / 2) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40217709384 / 1000000000000) (-40217709062 / 1000000000000), orderedInterval (662558702 / 1000000000000) (662559025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1159401275998087 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46831684585 / 1000000000000) (46831684803 / 1000000000000), orderedInterval (-1859629287 / 1000000000000) (-1859629068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (374926551255271 / 800000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-35929110539 / 1000000000000) (-35929110521 / 1000000000000), orderedInterval (-8176688533 / 1000000000000) (-8176688515 / 1000000000000)))) (orderedInterval (18695607344 / 1000000000000) (18695607510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (338310400748309 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44495050021 / 1000000000000) (-44495050020 / 1000000000000), orderedInterval (-74217180046 / 1000000000000) (-74217180045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (908749323704273 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51808618226 / 1000000000000) (51808619436 / 1000000000000), orderedInterval (-10978675465 / 1000000000000) (-10978674255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2467431190776141 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30494104240 / 1000000000000) (30494134283 / 1000000000000), orderedInterval (-10131408549 / 1000000000000) (-10131378505 / 1000000000000)))) (orderedInterval (4671683603 / 1000000000000) (4671688949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1817498647409333 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (13575791133 / 1000000000000) (13575791251 / 1000000000000), orderedInterval (-34897434187 / 1000000000000) (-34897434069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3114314910608009 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7046429326 / 1000000000000) (7046429327 / 1000000000000), orderedInterval (27708596040 / 1000000000000) (27708596041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2293990267608731 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19594124788 / 1000000000000) (19594126230 / 1000000000000), orderedInterval (-26963989206 / 1000000000000) (-26963987764 / 1000000000000)))) (orderedInterval (-148301916 / 1000000000000) (-148301773 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_chunkChecks2_1 :
    compactCertificate522.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3519570996584213 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23088410978 / 1000000000000) (23088410981 / 1000000000000), orderedInterval (13787059780 / 1000000000000) (13787059784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2032025262309677 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5169072335 / 1000000000000) (-5169072332 / 1000000000000), orderedInterval (35025856022 / 1000000000000) (35025856025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3605864486605393 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15316968085 / 1000000000000) (-15316968084 / 1000000000000), orderedInterval (-21707751860 / 1000000000000) (-21707751859 / 1000000000000)))) (orderedInterval (32601730094 / 1000000000000) (32601730791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3369066343825717 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24563677199 / 1000000000000) (24563677208 / 1000000000000), orderedInterval (12333165491 / 1000000000000) (12333165499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2404324714619461 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-31521367425 / 1000000000000) (-31521352834 / 1000000000000), orderedInterval (8121148032 / 1000000000000) (8121162623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2726247971112819 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17797641761 / 1000000000000) (-17797641760 / 1000000000000), orderedInterval (-24832546639 / 1000000000000) (-24832546638 / 1000000000000)))) (orderedInterval (8714236143 / 1000000000000) (8714239495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2272861332675011 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12173948870 / 1000000000000) (-12173948869 / 1000000000000), orderedInterval (-31169088718 / 1000000000000) (-31169088717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2008141916387231 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5877265156 / 1000000000000) (5877265157 / 1000000000000), orderedInterval (35115872099 / 1000000000000) (35115872100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (582037798459869 / 800000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-14621561891 / 1000000000000) (-14621561760 / 1000000000000), orderedInterval (25724478870 / 1000000000000) (25724479000 / 1000000000000)))) (orderedInterval (2125108952 / 1000000000000) (2125109045 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_chunkChecks2_2 :
    compactCertificate522.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1609947181511143 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36269147217 / 1000000000000) (36269147218 / 1000000000000), orderedInterval (16272543813 / 1000000000000) (16272543814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1364770055443823 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (19023732160 / 1000000000000) (19023732912 / 1000000000000), orderedInterval (-38808873847 / 1000000000000) (-38808873096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (854009732391269 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33434166329 / 1000000000000) (33434166330 / 1000000000000), orderedInterval (43095190928 / 1000000000000) (43095190929 / 1000000000000)))) (orderedInterval (6556141642 / 1000000000000) (6556141762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (459289274388123 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (44006159638 / 1000000000000) (44006176744 / 1000000000000), orderedInterval (-60257124865 / 1000000000000) (-60257107759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1247059724453369 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45154758558 / 1000000000000) (-45154758470 / 1000000000000), orderedInterval (-1668742536 / 1000000000000) (-1668742447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1702753439325913 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27283162699 / 1000000000000) (-27283146556 / 1000000000000), orderedInterval (27438900161 / 1000000000000) (27438916303 / 1000000000000)))) (orderedInterval (-3016001932 / 1000000000000) (-3016000410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (719990267608731 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58883460369 / 1000000000000) (-58883459965 / 1000000000000), orderedInterval (8503190043 / 1000000000000) (8503190447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2926720465165051 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13470622262 / 1000000000000) (-13470622261 / 1000000000000), orderedInterval (-26232399513 / 1000000000000) (-26232399512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1954913634610709 / 4000000000000) 2 (IntervalRat.scale (787 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19624928501 / 1000000000000) (-19624927229 / 1000000000000), orderedInterval (30309792580 / 1000000000000) (30309793851 / 1000000000000)))) (orderedInterval (-9389104198 / 1000000000000) (-9389103602 / 1000000000000))) = true
  rfl'

theorem compactCertificate522_chunkChecks2 :
    compactCertificate522.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate522.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate522_chunkChecks2_0
    compactCertificate522_chunkChecks2_1 compactCertificate522_chunkChecks2_2

theorem compactCertificate522_chunkChecks3_0 :
    compactCertificate522.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (787 / 2) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40217709384 / 1000000000000) (-40217709062 / 1000000000000), orderedInterval (662558702 / 1000000000000) (662559025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1159401275998087 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46831684585 / 1000000000000) (46831684803 / 1000000000000), orderedInterval (-1859629287 / 1000000000000) (-1859629068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (374926551255271 / 800000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-35929110539 / 1000000000000) (-35929110521 / 1000000000000), orderedInterval (-8176688533 / 1000000000000) (-8176688515 / 1000000000000)))) (orderedInterval (507404055 / 1000000000000) (507404228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (338310400748309 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44495050021 / 1000000000000) (-44495050020 / 1000000000000), orderedInterval (-74217180046 / 1000000000000) (-74217180045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (908749323704273 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51808618226 / 1000000000000) (51808619436 / 1000000000000), orderedInterval (-10978675465 / 1000000000000) (-10978674255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2467431190776141 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30494104240 / 1000000000000) (30494134283 / 1000000000000), orderedInterval (-10131408549 / 1000000000000) (-10131378505 / 1000000000000)))) (orderedInterval (-2717296051 / 1000000000000) (-2717287690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1817498647409333 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (13575791133 / 1000000000000) (13575791251 / 1000000000000), orderedInterval (-34897434187 / 1000000000000) (-34897434069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3114314910608009 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7046429326 / 1000000000000) (7046429327 / 1000000000000), orderedInterval (27708596040 / 1000000000000) (27708596041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2293990267608731 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19594124788 / 1000000000000) (19594126230 / 1000000000000), orderedInterval (-26963989206 / 1000000000000) (-26963987764 / 1000000000000)))) (orderedInterval (8637740732 / 1000000000000) (8637740965 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate522_chunkChecks3_1 :
    compactCertificate522.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3519570996584213 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23088410978 / 1000000000000) (23088410981 / 1000000000000), orderedInterval (13787059780 / 1000000000000) (13787059784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2032025262309677 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5169072335 / 1000000000000) (-5169072332 / 1000000000000), orderedInterval (35025856022 / 1000000000000) (35025856025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3605864486605393 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15316968085 / 1000000000000) (-15316968084 / 1000000000000), orderedInterval (-21707751860 / 1000000000000) (-21707751859 / 1000000000000)))) (orderedInterval (58824487136 / 1000000000000) (58824488664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3369066343825717 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24563677199 / 1000000000000) (24563677208 / 1000000000000), orderedInterval (12333165491 / 1000000000000) (12333165499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2404324714619461 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-31521367425 / 1000000000000) (-31521352834 / 1000000000000), orderedInterval (8121148032 / 1000000000000) (8121162623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2726247971112819 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17797641761 / 1000000000000) (-17797641760 / 1000000000000), orderedInterval (-24832546639 / 1000000000000) (-24832546638 / 1000000000000)))) (orderedInterval (-1228872368 / 1000000000000) (-1228867227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2272861332675011 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12173948870 / 1000000000000) (-12173948869 / 1000000000000), orderedInterval (-31169088718 / 1000000000000) (-31169088717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2008141916387231 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5877265156 / 1000000000000) (5877265157 / 1000000000000), orderedInterval (35115872099 / 1000000000000) (35115872100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (582037798459869 / 800000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-14621561891 / 1000000000000) (-14621561760 / 1000000000000), orderedInterval (25724478870 / 1000000000000) (25724479000 / 1000000000000)))) (orderedInterval (1088572874 / 1000000000000) (1088573021 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate522_chunkChecks3_2 :
    compactCertificate522.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1609947181511143 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36269147217 / 1000000000000) (36269147218 / 1000000000000), orderedInterval (16272543813 / 1000000000000) (16272543814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1364770055443823 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (19023732160 / 1000000000000) (19023732912 / 1000000000000), orderedInterval (-38808873847 / 1000000000000) (-38808873096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (854009732391269 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33434166329 / 1000000000000) (33434166330 / 1000000000000), orderedInterval (43095190928 / 1000000000000) (43095190929 / 1000000000000)))) (orderedInterval (1111575569 / 1000000000000) (1111575682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (459289274388123 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (44006159638 / 1000000000000) (44006176744 / 1000000000000), orderedInterval (-60257124865 / 1000000000000) (-60257107759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1247059724453369 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45154758558 / 1000000000000) (-45154758470 / 1000000000000), orderedInterval (-1668742536 / 1000000000000) (-1668742447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1702753439325913 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27283162699 / 1000000000000) (-27283146556 / 1000000000000), orderedInterval (27438900161 / 1000000000000) (27438916303 / 1000000000000)))) (orderedInterval (2623479018 / 1000000000000) (2623480640 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (719990267608731 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58883460369 / 1000000000000) (-58883459965 / 1000000000000), orderedInterval (8503190043 / 1000000000000) (8503190447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2926720465165051 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13470622262 / 1000000000000) (-13470622261 / 1000000000000), orderedInterval (-26232399513 / 1000000000000) (-26232399512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1954913634610709 / 4000000000000) 3 (IntervalRat.scale (787 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19624928501 / 1000000000000) (-19624927229 / 1000000000000), orderedInterval (30309792580 / 1000000000000) (30309793851 / 1000000000000)))) (orderedInterval (-2813417371 / 1000000000000) (-2813416564 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate522_chunkChecks3 :
    compactCertificate522.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate522.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate522_chunkChecks3_0
    compactCertificate522_chunkChecks3_1 compactCertificate522_chunkChecks3_2

theorem compactCertificate522_chunkChecks4_0 :
    compactCertificate522.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (787 / 2) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40217709384 / 1000000000000) (-40217709062 / 1000000000000), orderedInterval (662558702 / 1000000000000) (662559025 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1159401275998087 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (46831684585 / 1000000000000) (46831684803 / 1000000000000), orderedInterval (-1859629287 / 1000000000000) (-1859629068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (374926551255271 / 800000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-35929110539 / 1000000000000) (-35929110521 / 1000000000000), orderedInterval (-8176688533 / 1000000000000) (-8176688515 / 1000000000000)))) (orderedInterval (-20057083974 / 1000000000000) (-20057083795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (338310400748309 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-44495050021 / 1000000000000) (-44495050020 / 1000000000000), orderedInterval (-74217180046 / 1000000000000) (-74217180045 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (908749323704273 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (51808618226 / 1000000000000) (51808619436 / 1000000000000), orderedInterval (-10978675465 / 1000000000000) (-10978674255 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2467431190776141 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30494104240 / 1000000000000) (30494134283 / 1000000000000), orderedInterval (-10131408549 / 1000000000000) (-10131378505 / 1000000000000)))) (orderedInterval (-12866282911 / 1000000000000) (-12866269795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1817498647409333 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (13575791133 / 1000000000000) (13575791251 / 1000000000000), orderedInterval (-34897434187 / 1000000000000) (-34897434069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3114314910608009 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7046429326 / 1000000000000) (7046429327 / 1000000000000), orderedInterval (27708596040 / 1000000000000) (27708596041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2293990267608731 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19594124788 / 1000000000000) (19594126230 / 1000000000000), orderedInterval (-26963989206 / 1000000000000) (-26963987764 / 1000000000000)))) (orderedInterval (-1238318478 / 1000000000000) (-1238318090 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate522_chunkChecks4_1 :
    compactCertificate522.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3519570996584213 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23088410978 / 1000000000000) (23088410981 / 1000000000000), orderedInterval (13787059780 / 1000000000000) (13787059784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2032025262309677 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-5169072335 / 1000000000000) (-5169072332 / 1000000000000), orderedInterval (35025856022 / 1000000000000) (35025856025 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3605864486605393 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-15316968085 / 1000000000000) (-15316968084 / 1000000000000), orderedInterval (-21707751860 / 1000000000000) (-21707751859 / 1000000000000)))) (orderedInterval (-163898999324 / 1000000000000) (-163898995935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3369066343825717 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24563677199 / 1000000000000) (24563677208 / 1000000000000), orderedInterval (12333165491 / 1000000000000) (12333165499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2404324714619461 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-31521367425 / 1000000000000) (-31521352834 / 1000000000000), orderedInterval (8121148032 / 1000000000000) (8121162623 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2726247971112819 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-17797641761 / 1000000000000) (-17797641760 / 1000000000000), orderedInterval (-24832546639 / 1000000000000) (-24832546638 / 1000000000000)))) (orderedInterval (-24719800744 / 1000000000000) (-24719792833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2272861332675011 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12173948870 / 1000000000000) (-12173948869 / 1000000000000), orderedInterval (-31169088718 / 1000000000000) (-31169088717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2008141916387231 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (5877265156 / 1000000000000) (5877265157 / 1000000000000), orderedInterval (35115872099 / 1000000000000) (35115872100 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (582037798459869 / 800000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-14621561891 / 1000000000000) (-14621561760 / 1000000000000), orderedInterval (25724478870 / 1000000000000) (25724479000 / 1000000000000)))) (orderedInterval (-5882737728 / 1000000000000) (-5882737491 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate522_chunkChecks4_2 :
    compactCertificate522.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1609947181511143 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36269147217 / 1000000000000) (36269147218 / 1000000000000), orderedInterval (16272543813 / 1000000000000) (16272543814 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1364770055443823 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (19023732160 / 1000000000000) (19023732912 / 1000000000000), orderedInterval (-38808873847 / 1000000000000) (-38808873096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (854009732391269 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (33434166329 / 1000000000000) (33434166330 / 1000000000000), orderedInterval (43095190928 / 1000000000000) (43095190929 / 1000000000000)))) (orderedInterval (-6867233430 / 1000000000000) (-6867233322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (459289274388123 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (44006159638 / 1000000000000) (44006176744 / 1000000000000), orderedInterval (-60257124865 / 1000000000000) (-60257107759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1247059724453369 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45154758558 / 1000000000000) (-45154758470 / 1000000000000), orderedInterval (-1668742536 / 1000000000000) (-1668742447 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1702753439325913 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-27283162699 / 1000000000000) (-27283146556 / 1000000000000), orderedInterval (27438900161 / 1000000000000) (27438916303 / 1000000000000)))) (orderedInterval (3248135861 / 1000000000000) (3248137612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (719990267608731 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-58883460369 / 1000000000000) (-58883459965 / 1000000000000), orderedInterval (8503190043 / 1000000000000) (8503190447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2926720465165051 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13470622262 / 1000000000000) (-13470622261 / 1000000000000), orderedInterval (-26232399513 / 1000000000000) (-26232399512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1954913634610709 / 4000000000000) 4 (IntervalRat.scale (787 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19624928501 / 1000000000000) (-19624927229 / 1000000000000), orderedInterval (30309792580 / 1000000000000) (30309793851 / 1000000000000)))) (orderedInterval (21868238364 / 1000000000000) (21868239495 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate522_chunkChecks4 :
    compactCertificate522.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate522.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate522_chunkChecks4_0
    compactCertificate522_chunkChecks4_1 compactCertificate522_chunkChecks4_2

theorem compactCertificate522_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate522.chunkCheck r b = true :=
  compactCertificate522.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate522_chunkChecks0
    · exact compactCertificate522_chunkChecks1
    · exact compactCertificate522_chunkChecks2
    · exact compactCertificate522_chunkChecks3
    · exact compactCertificate522_chunkChecks4)

theorem compactCertificate522_coefficient0 :
    compactCertificate522.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate522_coefficient1 :
    compactCertificate522.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate522_coefficient2 :
    compactCertificate522.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate522_coefficient3 :
    compactCertificate522.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate522_coefficient4 :
    compactCertificate522.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate522_coefficients : ∀ r : Fin 5,
    compactCertificate522.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate522_coefficient0
  · exact compactCertificate522_coefficient1
  · exact compactCertificate522_coefficient2
  · exact compactCertificate522_coefficient3
  · exact compactCertificate522_coefficient4

theorem compactCertificate522_lower : (1 : ℚ) ≤ compactCertificate522.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate522, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate522_proves {t : ℝ} (ht : t ∈ compactCertificate522.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate522.proves compactCertificate522_states compactCertificate522_chunks
    compactCertificate522_coefficients compactCertificate522_lower ht

end Erdos232
