/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate560 : CompactCertificate where
  left := 431
  right := 432
  center := 863 / 2
  grid := fun i =>
    match i.val with
    | 0 => 137
    | 1 => 101
    | 2 => 164
    | 3 => 30
    | 4 => 79
    | 5 => 215
    | 6 => 159
    | 7 => 272
    | 8 => 200
    | 9 => 307
    | 10 => 177
    | 11 => 315
    | 12 => 294
    | 13 => 210
    | 14 => 238
    | 15 => 198
    | 16 => 175
    | 17 => 254
    | 18 => 141
    | 19 => 119
    | 20 => 75
    | 21 => 40
    | 22 => 109
    | 23 => 149
    | 24 => 63
    | 25 => 256
    | _ => 171
  point := fun i =>
    match i.val with
    | 0 => 863 / 2
    | 1 => 1271363788038563 / 4000000000000
    | 2 => 411132927234179 / 800000000000
    | 3 => 370980782523241 / 4000000000000
    | 4 => 996506564621077 / 4000000000000
    | 5 => 2705709171079809 / 4000000000000
    | 6 => 1993013129243017 / 4000000000000
    | 7 => 3415061966778541 / 4000000000000
    | 8 => 2515519187987719 / 4000000000000
    | 9 => 3859453329164137 / 4000000000000
    | 10 => 2228256418517473 / 4000000000000
    | 11 => 3954080116823957 / 4000000000000
    | 12 => 3694414554919433 / 4000000000000
    | 13 => 2636508549830489 / 4000000000000
    | 14 => 2989519693863231 / 4000000000000
    | 15 => 2492349847647439 / 4000000000000
    | 16 => 2202066675784219 / 4000000000000
    | 17 => 638244752313681 / 800000000000
    | 18 => 1765418573880707 / 4000000000000
    | 19 => 1496564876554027 / 4000000000000
    | 20 => 936480812012281 / 4000000000000
    | 21 => 503642495294727 / 4000000000000
    | 22 => 1367487347145181 / 4000000000000
    | 23 => 1867187062437437 / 4000000000000
    | 24 => 789519187987719 / 4000000000000
    | 25 => 3209351666375399 / 4000000000000
    | _ => 2143698178740841 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-36507198156 / 1000000000000) (-36507186291 / 1000000000000), orderedInterval (11983342637 / 1000000000000) (11983354501 / 1000000000000))
    | 1 => (orderedInterval (-43410190950 / 1000000000000) (-43410190946 / 1000000000000), orderedInterval (-10817661377 / 1000000000000) (-10817661373 / 1000000000000))
    | 2 => (orderedInterval (-17484585914 / 1000000000000) (-17484585352 / 1000000000000), orderedInterval (30562902374 / 1000000000000) (30562902936 / 1000000000000))
    | 3 => (orderedInterval (-54538472276 / 1000000000000) (-54538430279 / 1000000000000), orderedInterval (62661861422 / 1000000000000) (62661903419 / 1000000000000))
    | 4 => (orderedInterval (-49945558317 / 1000000000000) (-49945557573 / 1000000000000), orderedInterval (7900405561 / 1000000000000) (7900406305 / 1000000000000))
    | 5 => (orderedInterval (-30070978734 / 1000000000000) (-30070965988 / 1000000000000), orderedInterval (6095664158 / 1000000000000) (6095676904 / 1000000000000))
    | 6 => (orderedInterval (16341262259 / 1000000000000) (16341262610 / 1000000000000), orderedInterval (-31807382244 / 1000000000000) (-31807381892 / 1000000000000))
    | 7 => (orderedInterval (1024901932 / 1000000000000) (1024901933 / 1000000000000), orderedInterval (27286958661 / 1000000000000) (27286958662 / 1000000000000))
    | 8 => (orderedInterval (31019550232 / 1000000000000) (31019550294 / 1000000000000), orderedInterval (7053103502 / 1000000000000) (7053103564 / 1000000000000))
    | 9 => (orderedInterval (-23746647753 / 1000000000000) (-23746647688 / 1000000000000), orderedInterval (-9780534173 / 1000000000000) (-9780534108 / 1000000000000))
    | 10 => (orderedInterval (-33015727217 / 1000000000000) (-33015718926 / 1000000000000), orderedInterval (7294202060 / 1000000000000) (7294210351 / 1000000000000))
    | 11 => (orderedInterval (7411845814 / 1000000000000) (7411845816 / 1000000000000), orderedInterval (-24274670513 / 1000000000000) (-24274670512 / 1000000000000))
    | 12 => (orderedInterval (18099598120 / 1000000000000) (18099598121 / 1000000000000), orderedInterval (19008158026 / 1000000000000) (19008158027 / 1000000000000))
    | 13 => (orderedInterval (5499344171 / 1000000000000) (5499344172 / 1000000000000), orderedInterval (30583574971 / 1000000000000) (30583574972 / 1000000000000))
    | 14 => (orderedInterval (13116269941 / 1000000000000) (13116269942 / 1000000000000), orderedInterval (26063541045 / 1000000000000) (26063541046 / 1000000000000))
    | 15 => (orderedInterval (30835775465 / 1000000000000) (30835794243 / 1000000000000), orderedInterval (-8443318118 / 1000000000000) (-8443299339 / 1000000000000))
    | 16 => (orderedInterval (-33967304578 / 1000000000000) (-33967304178 / 1000000000000), orderedInterval (-1589621833 / 1000000000000) (-1589621434 / 1000000000000))
    | 17 => (orderedInterval (16565695145 / 1000000000000) (16565695146 / 1000000000000), orderedInterval (22870635916 / 1000000000000) (22870635917 / 1000000000000))
    | 18 => (orderedInterval (27892535524 / 1000000000000) (27892557761 / 1000000000000), orderedInterval (-25808111203 / 1000000000000) (-25808088966 / 1000000000000))
    | 19 => (orderedInterval (-36317369474 / 1000000000000) (-36317369473 / 1000000000000), orderedInterval (-19511559156 / 1000000000000) (-19511559155 / 1000000000000))
    | 20 => (orderedInterval (34163395849 / 1000000000000) (34163416953 / 1000000000000), orderedInterval (-39469202038 / 1000000000000) (-39469180934 / 1000000000000))
    | 21 => (orderedInterval (61007611477 / 1000000000000) (61007611478 / 1000000000000), orderedInterval (36284124320 / 1000000000000) (36284124321 / 1000000000000))
    | 22 => (orderedInterval (-9554862528 / 1000000000000) (-9554862527 / 1000000000000), orderedInterval (-42067679160 / 1000000000000) (-42067679159 / 1000000000000))
    | 23 => (orderedInterval (18202330082 / 1000000000000) (18202330796 / 1000000000000), orderedInterval (-32151733363 / 1000000000000) (-32151732649 / 1000000000000))
    | 24 => (orderedInterval (-13732565433 / 1000000000000) (-13732565432 / 1000000000000), orderedInterval (-55072200473 / 1000000000000) (-55072200472 / 1000000000000))
    | 25 => (orderedInterval (-25410075426 / 1000000000000) (-25410011779 / 1000000000000), orderedInterval (12172507543 / 1000000000000) (12172571190 / 1000000000000))
    | _ => (orderedInterval (16603392923 / 1000000000000) (16603393316 / 1000000000000), orderedInterval (-30218442357 / 1000000000000) (-30218441964 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15900689554 / 1000000000000) (-15900684788 / 1000000000000)
      | 1 => orderedInterval (905837912 / 1000000000000) (905839353 / 1000000000000)
      | 2 => orderedInterval (718069239 / 1000000000000) (718069265 / 1000000000000)
      | 3 => orderedInterval (2826936344 / 1000000000000) (2826937141 / 1000000000000)
      | 4 => orderedInterval (126904238 / 1000000000000) (126904290 / 1000000000000)
      | 5 => orderedInterval (2724064513 / 1000000000000) (2724064795 / 1000000000000)
      | 6 => orderedInterval (-1292049104 / 1000000000000) (-1292044753 / 1000000000000)
      | 7 => orderedInterval (-2304748926 / 1000000000000) (-2304748819 / 1000000000000)
      | _ => orderedInterval (-1129601380 / 1000000000000) (-1129596006 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (6811545494 / 1000000000000) (6811550270 / 1000000000000)
      | 1 => orderedInterval (-658891840 / 1000000000000) (-658890247 / 1000000000000)
      | 2 => orderedInterval (-1416833675 / 1000000000000) (-1416833631 / 1000000000000)
      | 3 => orderedInterval (-3321652952 / 1000000000000) (-3321651778 / 1000000000000)
      | 4 => orderedInterval (3454751485 / 1000000000000) (3454751569 / 1000000000000)
      | 5 => orderedInterval (1057952418 / 1000000000000) (1057952821 / 1000000000000)
      | 6 => orderedInterval (4481144703 / 1000000000000) (4481148813 / 1000000000000)
      | 7 => orderedInterval (3226278087 / 1000000000000) (3226278193 / 1000000000000)
      | _ => orderedInterval (5047588546 / 1000000000000) (5047598439 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16129236356 / 1000000000000) (16129241156 / 1000000000000)
      | 1 => orderedInterval (-4671270111 / 1000000000000) (-4671267768 / 1000000000000)
      | 2 => orderedInterval (-1465353304 / 1000000000000) (-1465353225 / 1000000000000)
      | 3 => orderedInterval (-22542464416 / 1000000000000) (-22542462572 / 1000000000000)
      | 4 => orderedInterval (474737571 / 1000000000000) (474737710 / 1000000000000)
      | 5 => orderedInterval (-5358890403 / 1000000000000) (-5358889823 / 1000000000000)
      | 6 => orderedInterval (2782641793 / 1000000000000) (2782645820 / 1000000000000)
      | 7 => orderedInterval (1584934182 / 1000000000000) (1584934292 / 1000000000000)
      | _ => orderedInterval (-2340325752 / 1000000000000) (-2340307455 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-7776734788 / 1000000000000) (-7776729974 / 1000000000000)
      | 1 => orderedInterval (1631412391 / 1000000000000) (1631416019 / 1000000000000)
      | 2 => orderedInterval (5994968451 / 1000000000000) (5994968593 / 1000000000000)
      | 3 => orderedInterval (20948188285 / 1000000000000) (20948191404 / 1000000000000)
      | 4 => orderedInterval (-6258556727 / 1000000000000) (-6258556492 / 1000000000000)
      | 5 => orderedInterval (-3584050579 / 1000000000000) (-3584049740 / 1000000000000)
      | 6 => orderedInterval (-4936842809 / 1000000000000) (-4936838792 / 1000000000000)
      | 7 => orderedInterval (-3581225461 / 1000000000000) (-3581225344 / 1000000000000)
      | _ => orderedInterval (-4455341010 / 1000000000000) (-4455307138 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16617550455 / 1000000000000) (-16617545611 / 1000000000000)
      | 1 => orderedInterval (12700719395 / 1000000000000) (12700725075 / 1000000000000)
      | 2 => orderedInterval (2870109050 / 1000000000000) (2870109309 / 1000000000000)
      | 3 => orderedInterval (127615951326 / 1000000000000) (127615957032 / 1000000000000)
      | 4 => orderedInterval (-4595744509 / 1000000000000) (-4595744102 / 1000000000000)
      | 5 => orderedInterval (11671481031 / 1000000000000) (11671482255 / 1000000000000)
      | 6 => orderedInterval (-3600262414 / 1000000000000) (-3600258353 / 1000000000000)
      | 7 => orderedInterval (-1816721300 / 1000000000000) (-1816721174 / 1000000000000)
      | _ => orderedInterval (17329694416 / 1000000000000) (17329757292 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13325276718 / 1000000000000) (-13325259522 / 1000000000000)
    | 1 => orderedInterval (18681882266 / 1000000000000) (18681904449 / 1000000000000)
    | 2 => orderedInterval (-15406754084 / 1000000000000) (-15406721865 / 1000000000000)
    | 3 => orderedInterval (-2018182247 / 1000000000000) (-2018131464 / 1000000000000)
    | _ => orderedInterval (145557676540 / 1000000000000) (145557761723 / 1000000000000)

theorem compactCertificate560_stateChecks0 :
    compactCertificate560.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (863 / 2)) (orderedInterval (-36507198156 / 1000000000000) (-36507186291 / 1000000000000), orderedInterval (11983342637 / 1000000000000) (11983354501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1271363788038563 / 4000000000000)) (orderedInterval (-43410190950 / 1000000000000) (-43410190946 / 1000000000000), orderedInterval (-10817661377 / 1000000000000) (-10817661373 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (411132927234179 / 800000000000)) (orderedInterval (-17484585914 / 1000000000000) (-17484585352 / 1000000000000), orderedInterval (30562902374 / 1000000000000) (30562902936 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_stateChecks1 :
    compactCertificate560.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (370980782523241 / 4000000000000)) (orderedInterval (-54538472276 / 1000000000000) (-54538430279 / 1000000000000), orderedInterval (62661861422 / 1000000000000) (62661903419 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (996506564621077 / 4000000000000)) (orderedInterval (-49945558317 / 1000000000000) (-49945557573 / 1000000000000), orderedInterval (7900405561 / 1000000000000) (7900406305 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2705709171079809 / 4000000000000)) (orderedInterval (-30070978734 / 1000000000000) (-30070965988 / 1000000000000), orderedInterval (6095664158 / 1000000000000) (6095676904 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_stateChecks2 :
    compactCertificate560.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (1993013129243017 / 4000000000000)) (orderedInterval (16341262259 / 1000000000000) (16341262610 / 1000000000000), orderedInterval (-31807382244 / 1000000000000) (-31807381892 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (3415061966778541 / 4000000000000)) (orderedInterval (1024901932 / 1000000000000) (1024901933 / 1000000000000), orderedInterval (27286958661 / 1000000000000) (27286958662 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2515519187987719 / 4000000000000)) (orderedInterval (31019550232 / 1000000000000) (31019550294 / 1000000000000), orderedInterval (7053103502 / 1000000000000) (7053103564 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_stateChecks3 :
    compactCertificate560.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 307 12 (3859453329164137 / 4000000000000)) (orderedInterval (-23746647753 / 1000000000000) (-23746647688 / 1000000000000), orderedInterval (-9780534173 / 1000000000000) (-9780534108 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2228256418517473 / 4000000000000)) (orderedInterval (-33015727217 / 1000000000000) (-33015718926 / 1000000000000), orderedInterval (7294202060 / 1000000000000) (7294210351 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 315 12 (3954080116823957 / 4000000000000)) (orderedInterval (7411845814 / 1000000000000) (7411845816 / 1000000000000), orderedInterval (-24274670513 / 1000000000000) (-24274670512 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_stateChecks4 :
    compactCertificate560.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 294 12 (3694414554919433 / 4000000000000)) (orderedInterval (18099598120 / 1000000000000) (18099598121 / 1000000000000), orderedInterval (19008158026 / 1000000000000) (19008158027 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (2636508549830489 / 4000000000000)) (orderedInterval (5499344171 / 1000000000000) (5499344172 / 1000000000000), orderedInterval (30583574971 / 1000000000000) (30583574972 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (2989519693863231 / 4000000000000)) (orderedInterval (13116269941 / 1000000000000) (13116269942 / 1000000000000), orderedInterval (26063541045 / 1000000000000) (26063541046 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_stateChecks5 :
    compactCertificate560.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2492349847647439 / 4000000000000)) (orderedInterval (30835775465 / 1000000000000) (30835794243 / 1000000000000), orderedInterval (-8443318118 / 1000000000000) (-8443299339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2202066675784219 / 4000000000000)) (orderedInterval (-33967304578 / 1000000000000) (-33967304178 / 1000000000000), orderedInterval (-1589621833 / 1000000000000) (-1589621434 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 254 12 (638244752313681 / 800000000000)) (orderedInterval (16565695145 / 1000000000000) (16565695146 / 1000000000000), orderedInterval (22870635916 / 1000000000000) (22870635917 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_stateChecks6 :
    compactCertificate560.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1765418573880707 / 4000000000000)) (orderedInterval (27892535524 / 1000000000000) (27892557761 / 1000000000000), orderedInterval (-25808111203 / 1000000000000) (-25808088966 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1496564876554027 / 4000000000000)) (orderedInterval (-36317369474 / 1000000000000) (-36317369473 / 1000000000000), orderedInterval (-19511559156 / 1000000000000) (-19511559155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (936480812012281 / 4000000000000)) (orderedInterval (34163395849 / 1000000000000) (34163416953 / 1000000000000), orderedInterval (-39469202038 / 1000000000000) (-39469180934 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_stateChecks7 :
    compactCertificate560.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (503642495294727 / 4000000000000)) (orderedInterval (61007611477 / 1000000000000) (61007611478 / 1000000000000), orderedInterval (36284124320 / 1000000000000) (36284124321 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1367487347145181 / 4000000000000)) (orderedInterval (-9554862528 / 1000000000000) (-9554862527 / 1000000000000), orderedInterval (-42067679160 / 1000000000000) (-42067679159 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1867187062437437 / 4000000000000)) (orderedInterval (18202330082 / 1000000000000) (18202330796 / 1000000000000), orderedInterval (-32151733363 / 1000000000000) (-32151732649 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_stateChecks8 :
    compactCertificate560.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (789519187987719 / 4000000000000)) (orderedInterval (-13732565433 / 1000000000000) (-13732565432 / 1000000000000), orderedInterval (-55072200473 / 1000000000000) (-55072200472 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (3209351666375399 / 4000000000000)) (orderedInterval (-25410075426 / 1000000000000) (-25410011779 / 1000000000000), orderedInterval (12172507543 / 1000000000000) (12172571190 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2143698178740841 / 4000000000000)) (orderedInterval (16603392923 / 1000000000000) (16603393316 / 1000000000000), orderedInterval (-30218442357 / 1000000000000) (-30218441964 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_states : ∀ j,
    BesselStateValid (compactCertificate560.point j) (compactCertificate560.state j) :=
  compactCertificate560.statesValid_of_checks3 compactCertificate560_stateChecks0
    compactCertificate560_stateChecks1 compactCertificate560_stateChecks2
    compactCertificate560_stateChecks3 compactCertificate560_stateChecks4
    compactCertificate560_stateChecks5 compactCertificate560_stateChecks6
    compactCertificate560_stateChecks7 compactCertificate560_stateChecks8

theorem compactCertificate560_chunkChecks0_0 :
    compactCertificate560.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (863 / 2) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36507198156 / 1000000000000) (-36507186291 / 1000000000000), orderedInterval (11983342637 / 1000000000000) (11983354501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1271363788038563 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43410190950 / 1000000000000) (-43410190946 / 1000000000000), orderedInterval (-10817661377 / 1000000000000) (-10817661373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (411132927234179 / 800000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17484585914 / 1000000000000) (-17484585352 / 1000000000000), orderedInterval (30562902374 / 1000000000000) (30562902936 / 1000000000000)))) (orderedInterval (-15900689554 / 1000000000000) (-15900684788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (370980782523241 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-54538472276 / 1000000000000) (-54538430279 / 1000000000000), orderedInterval (62661861422 / 1000000000000) (62661903419 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (996506564621077 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49945558317 / 1000000000000) (-49945557573 / 1000000000000), orderedInterval (7900405561 / 1000000000000) (7900406305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2705709171079809 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30070978734 / 1000000000000) (-30070965988 / 1000000000000), orderedInterval (6095664158 / 1000000000000) (6095676904 / 1000000000000)))) (orderedInterval (905837912 / 1000000000000) (905839353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1993013129243017 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16341262259 / 1000000000000) (16341262610 / 1000000000000), orderedInterval (-31807382244 / 1000000000000) (-31807381892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3415061966778541 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1024901932 / 1000000000000) (1024901933 / 1000000000000), orderedInterval (27286958661 / 1000000000000) (27286958662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2515519187987719 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31019550232 / 1000000000000) (31019550294 / 1000000000000), orderedInterval (7053103502 / 1000000000000) (7053103564 / 1000000000000)))) (orderedInterval (718069239 / 1000000000000) (718069265 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_chunkChecks0_1 :
    compactCertificate560.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3859453329164137 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23746647753 / 1000000000000) (-23746647688 / 1000000000000), orderedInterval (-9780534173 / 1000000000000) (-9780534108 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2228256418517473 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33015727217 / 1000000000000) (-33015718926 / 1000000000000), orderedInterval (7294202060 / 1000000000000) (7294210351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3954080116823957 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7411845814 / 1000000000000) (7411845816 / 1000000000000), orderedInterval (-24274670513 / 1000000000000) (-24274670512 / 1000000000000)))) (orderedInterval (2826936344 / 1000000000000) (2826937141 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3694414554919433 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18099598120 / 1000000000000) (18099598121 / 1000000000000), orderedInterval (19008158026 / 1000000000000) (19008158027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2636508549830489 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5499344171 / 1000000000000) (5499344172 / 1000000000000), orderedInterval (30583574971 / 1000000000000) (30583574972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2989519693863231 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13116269941 / 1000000000000) (13116269942 / 1000000000000), orderedInterval (26063541045 / 1000000000000) (26063541046 / 1000000000000)))) (orderedInterval (126904238 / 1000000000000) (126904290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2492349847647439 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30835775465 / 1000000000000) (30835794243 / 1000000000000), orderedInterval (-8443318118 / 1000000000000) (-8443299339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2202066675784219 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33967304578 / 1000000000000) (-33967304178 / 1000000000000), orderedInterval (-1589621833 / 1000000000000) (-1589621434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (638244752313681 / 800000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16565695145 / 1000000000000) (16565695146 / 1000000000000), orderedInterval (22870635916 / 1000000000000) (22870635917 / 1000000000000)))) (orderedInterval (2724064513 / 1000000000000) (2724064795 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_chunkChecks0_2 :
    compactCertificate560.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1765418573880707 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27892535524 / 1000000000000) (27892557761 / 1000000000000), orderedInterval (-25808111203 / 1000000000000) (-25808088966 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1496564876554027 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36317369474 / 1000000000000) (-36317369473 / 1000000000000), orderedInterval (-19511559156 / 1000000000000) (-19511559155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (936480812012281 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34163395849 / 1000000000000) (34163416953 / 1000000000000), orderedInterval (-39469202038 / 1000000000000) (-39469180934 / 1000000000000)))) (orderedInterval (-1292049104 / 1000000000000) (-1292044753 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (503642495294727 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61007611477 / 1000000000000) (61007611478 / 1000000000000), orderedInterval (36284124320 / 1000000000000) (36284124321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1367487347145181 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9554862528 / 1000000000000) (-9554862527 / 1000000000000), orderedInterval (-42067679160 / 1000000000000) (-42067679159 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1867187062437437 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18202330082 / 1000000000000) (18202330796 / 1000000000000), orderedInterval (-32151733363 / 1000000000000) (-32151732649 / 1000000000000)))) (orderedInterval (-2304748926 / 1000000000000) (-2304748819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (789519187987719 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13732565433 / 1000000000000) (-13732565432 / 1000000000000), orderedInterval (-55072200473 / 1000000000000) (-55072200472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3209351666375399 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25410075426 / 1000000000000) (-25410011779 / 1000000000000), orderedInterval (12172507543 / 1000000000000) (12172571190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2143698178740841 / 4000000000000) 0 (IntervalRat.scale (863 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16603392923 / 1000000000000) (16603393316 / 1000000000000), orderedInterval (-30218442357 / 1000000000000) (-30218441964 / 1000000000000)))) (orderedInterval (-1129601380 / 1000000000000) (-1129596006 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_chunkChecks0 :
    compactCertificate560.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate560.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate560_chunkChecks0_0
    compactCertificate560_chunkChecks0_1 compactCertificate560_chunkChecks0_2

theorem compactCertificate560_chunkChecks1_0 :
    compactCertificate560.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (863 / 2) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36507198156 / 1000000000000) (-36507186291 / 1000000000000), orderedInterval (11983342637 / 1000000000000) (11983354501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1271363788038563 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43410190950 / 1000000000000) (-43410190946 / 1000000000000), orderedInterval (-10817661377 / 1000000000000) (-10817661373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (411132927234179 / 800000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17484585914 / 1000000000000) (-17484585352 / 1000000000000), orderedInterval (30562902374 / 1000000000000) (30562902936 / 1000000000000)))) (orderedInterval (6811545494 / 1000000000000) (6811550270 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (370980782523241 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-54538472276 / 1000000000000) (-54538430279 / 1000000000000), orderedInterval (62661861422 / 1000000000000) (62661903419 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (996506564621077 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49945558317 / 1000000000000) (-49945557573 / 1000000000000), orderedInterval (7900405561 / 1000000000000) (7900406305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2705709171079809 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30070978734 / 1000000000000) (-30070965988 / 1000000000000), orderedInterval (6095664158 / 1000000000000) (6095676904 / 1000000000000)))) (orderedInterval (-658891840 / 1000000000000) (-658890247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1993013129243017 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16341262259 / 1000000000000) (16341262610 / 1000000000000), orderedInterval (-31807382244 / 1000000000000) (-31807381892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3415061966778541 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1024901932 / 1000000000000) (1024901933 / 1000000000000), orderedInterval (27286958661 / 1000000000000) (27286958662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2515519187987719 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31019550232 / 1000000000000) (31019550294 / 1000000000000), orderedInterval (7053103502 / 1000000000000) (7053103564 / 1000000000000)))) (orderedInterval (-1416833675 / 1000000000000) (-1416833631 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_chunkChecks1_1 :
    compactCertificate560.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3859453329164137 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23746647753 / 1000000000000) (-23746647688 / 1000000000000), orderedInterval (-9780534173 / 1000000000000) (-9780534108 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2228256418517473 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33015727217 / 1000000000000) (-33015718926 / 1000000000000), orderedInterval (7294202060 / 1000000000000) (7294210351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3954080116823957 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7411845814 / 1000000000000) (7411845816 / 1000000000000), orderedInterval (-24274670513 / 1000000000000) (-24274670512 / 1000000000000)))) (orderedInterval (-3321652952 / 1000000000000) (-3321651778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3694414554919433 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18099598120 / 1000000000000) (18099598121 / 1000000000000), orderedInterval (19008158026 / 1000000000000) (19008158027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2636508549830489 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5499344171 / 1000000000000) (5499344172 / 1000000000000), orderedInterval (30583574971 / 1000000000000) (30583574972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2989519693863231 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13116269941 / 1000000000000) (13116269942 / 1000000000000), orderedInterval (26063541045 / 1000000000000) (26063541046 / 1000000000000)))) (orderedInterval (3454751485 / 1000000000000) (3454751569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2492349847647439 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30835775465 / 1000000000000) (30835794243 / 1000000000000), orderedInterval (-8443318118 / 1000000000000) (-8443299339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2202066675784219 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33967304578 / 1000000000000) (-33967304178 / 1000000000000), orderedInterval (-1589621833 / 1000000000000) (-1589621434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (638244752313681 / 800000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16565695145 / 1000000000000) (16565695146 / 1000000000000), orderedInterval (22870635916 / 1000000000000) (22870635917 / 1000000000000)))) (orderedInterval (1057952418 / 1000000000000) (1057952821 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_chunkChecks1_2 :
    compactCertificate560.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1765418573880707 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27892535524 / 1000000000000) (27892557761 / 1000000000000), orderedInterval (-25808111203 / 1000000000000) (-25808088966 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1496564876554027 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36317369474 / 1000000000000) (-36317369473 / 1000000000000), orderedInterval (-19511559156 / 1000000000000) (-19511559155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (936480812012281 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34163395849 / 1000000000000) (34163416953 / 1000000000000), orderedInterval (-39469202038 / 1000000000000) (-39469180934 / 1000000000000)))) (orderedInterval (4481144703 / 1000000000000) (4481148813 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (503642495294727 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61007611477 / 1000000000000) (61007611478 / 1000000000000), orderedInterval (36284124320 / 1000000000000) (36284124321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1367487347145181 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9554862528 / 1000000000000) (-9554862527 / 1000000000000), orderedInterval (-42067679160 / 1000000000000) (-42067679159 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1867187062437437 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18202330082 / 1000000000000) (18202330796 / 1000000000000), orderedInterval (-32151733363 / 1000000000000) (-32151732649 / 1000000000000)))) (orderedInterval (3226278087 / 1000000000000) (3226278193 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (789519187987719 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13732565433 / 1000000000000) (-13732565432 / 1000000000000), orderedInterval (-55072200473 / 1000000000000) (-55072200472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3209351666375399 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25410075426 / 1000000000000) (-25410011779 / 1000000000000), orderedInterval (12172507543 / 1000000000000) (12172571190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2143698178740841 / 4000000000000) 1 (IntervalRat.scale (863 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16603392923 / 1000000000000) (16603393316 / 1000000000000), orderedInterval (-30218442357 / 1000000000000) (-30218441964 / 1000000000000)))) (orderedInterval (5047588546 / 1000000000000) (5047598439 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_chunkChecks1 :
    compactCertificate560.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate560.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate560_chunkChecks1_0
    compactCertificate560_chunkChecks1_1 compactCertificate560_chunkChecks1_2

theorem compactCertificate560_chunkChecks2_0 :
    compactCertificate560.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (863 / 2) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36507198156 / 1000000000000) (-36507186291 / 1000000000000), orderedInterval (11983342637 / 1000000000000) (11983354501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1271363788038563 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43410190950 / 1000000000000) (-43410190946 / 1000000000000), orderedInterval (-10817661377 / 1000000000000) (-10817661373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (411132927234179 / 800000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17484585914 / 1000000000000) (-17484585352 / 1000000000000), orderedInterval (30562902374 / 1000000000000) (30562902936 / 1000000000000)))) (orderedInterval (16129236356 / 1000000000000) (16129241156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (370980782523241 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-54538472276 / 1000000000000) (-54538430279 / 1000000000000), orderedInterval (62661861422 / 1000000000000) (62661903419 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (996506564621077 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49945558317 / 1000000000000) (-49945557573 / 1000000000000), orderedInterval (7900405561 / 1000000000000) (7900406305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2705709171079809 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30070978734 / 1000000000000) (-30070965988 / 1000000000000), orderedInterval (6095664158 / 1000000000000) (6095676904 / 1000000000000)))) (orderedInterval (-4671270111 / 1000000000000) (-4671267768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1993013129243017 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16341262259 / 1000000000000) (16341262610 / 1000000000000), orderedInterval (-31807382244 / 1000000000000) (-31807381892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3415061966778541 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1024901932 / 1000000000000) (1024901933 / 1000000000000), orderedInterval (27286958661 / 1000000000000) (27286958662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2515519187987719 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31019550232 / 1000000000000) (31019550294 / 1000000000000), orderedInterval (7053103502 / 1000000000000) (7053103564 / 1000000000000)))) (orderedInterval (-1465353304 / 1000000000000) (-1465353225 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_chunkChecks2_1 :
    compactCertificate560.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3859453329164137 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23746647753 / 1000000000000) (-23746647688 / 1000000000000), orderedInterval (-9780534173 / 1000000000000) (-9780534108 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2228256418517473 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33015727217 / 1000000000000) (-33015718926 / 1000000000000), orderedInterval (7294202060 / 1000000000000) (7294210351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3954080116823957 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7411845814 / 1000000000000) (7411845816 / 1000000000000), orderedInterval (-24274670513 / 1000000000000) (-24274670512 / 1000000000000)))) (orderedInterval (-22542464416 / 1000000000000) (-22542462572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3694414554919433 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18099598120 / 1000000000000) (18099598121 / 1000000000000), orderedInterval (19008158026 / 1000000000000) (19008158027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2636508549830489 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5499344171 / 1000000000000) (5499344172 / 1000000000000), orderedInterval (30583574971 / 1000000000000) (30583574972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2989519693863231 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13116269941 / 1000000000000) (13116269942 / 1000000000000), orderedInterval (26063541045 / 1000000000000) (26063541046 / 1000000000000)))) (orderedInterval (474737571 / 1000000000000) (474737710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2492349847647439 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30835775465 / 1000000000000) (30835794243 / 1000000000000), orderedInterval (-8443318118 / 1000000000000) (-8443299339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2202066675784219 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33967304578 / 1000000000000) (-33967304178 / 1000000000000), orderedInterval (-1589621833 / 1000000000000) (-1589621434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (638244752313681 / 800000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16565695145 / 1000000000000) (16565695146 / 1000000000000), orderedInterval (22870635916 / 1000000000000) (22870635917 / 1000000000000)))) (orderedInterval (-5358890403 / 1000000000000) (-5358889823 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_chunkChecks2_2 :
    compactCertificate560.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1765418573880707 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27892535524 / 1000000000000) (27892557761 / 1000000000000), orderedInterval (-25808111203 / 1000000000000) (-25808088966 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1496564876554027 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36317369474 / 1000000000000) (-36317369473 / 1000000000000), orderedInterval (-19511559156 / 1000000000000) (-19511559155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (936480812012281 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34163395849 / 1000000000000) (34163416953 / 1000000000000), orderedInterval (-39469202038 / 1000000000000) (-39469180934 / 1000000000000)))) (orderedInterval (2782641793 / 1000000000000) (2782645820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (503642495294727 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61007611477 / 1000000000000) (61007611478 / 1000000000000), orderedInterval (36284124320 / 1000000000000) (36284124321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1367487347145181 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9554862528 / 1000000000000) (-9554862527 / 1000000000000), orderedInterval (-42067679160 / 1000000000000) (-42067679159 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1867187062437437 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18202330082 / 1000000000000) (18202330796 / 1000000000000), orderedInterval (-32151733363 / 1000000000000) (-32151732649 / 1000000000000)))) (orderedInterval (1584934182 / 1000000000000) (1584934292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (789519187987719 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13732565433 / 1000000000000) (-13732565432 / 1000000000000), orderedInterval (-55072200473 / 1000000000000) (-55072200472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3209351666375399 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25410075426 / 1000000000000) (-25410011779 / 1000000000000), orderedInterval (12172507543 / 1000000000000) (12172571190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2143698178740841 / 4000000000000) 2 (IntervalRat.scale (863 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16603392923 / 1000000000000) (16603393316 / 1000000000000), orderedInterval (-30218442357 / 1000000000000) (-30218441964 / 1000000000000)))) (orderedInterval (-2340325752 / 1000000000000) (-2340307455 / 1000000000000))) = true
  rfl'

theorem compactCertificate560_chunkChecks2 :
    compactCertificate560.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate560.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate560_chunkChecks2_0
    compactCertificate560_chunkChecks2_1 compactCertificate560_chunkChecks2_2

theorem compactCertificate560_chunkChecks3_0 :
    compactCertificate560.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (863 / 2) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36507198156 / 1000000000000) (-36507186291 / 1000000000000), orderedInterval (11983342637 / 1000000000000) (11983354501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1271363788038563 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43410190950 / 1000000000000) (-43410190946 / 1000000000000), orderedInterval (-10817661377 / 1000000000000) (-10817661373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (411132927234179 / 800000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17484585914 / 1000000000000) (-17484585352 / 1000000000000), orderedInterval (30562902374 / 1000000000000) (30562902936 / 1000000000000)))) (orderedInterval (-7776734788 / 1000000000000) (-7776729974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (370980782523241 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-54538472276 / 1000000000000) (-54538430279 / 1000000000000), orderedInterval (62661861422 / 1000000000000) (62661903419 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (996506564621077 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49945558317 / 1000000000000) (-49945557573 / 1000000000000), orderedInterval (7900405561 / 1000000000000) (7900406305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2705709171079809 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30070978734 / 1000000000000) (-30070965988 / 1000000000000), orderedInterval (6095664158 / 1000000000000) (6095676904 / 1000000000000)))) (orderedInterval (1631412391 / 1000000000000) (1631416019 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1993013129243017 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16341262259 / 1000000000000) (16341262610 / 1000000000000), orderedInterval (-31807382244 / 1000000000000) (-31807381892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3415061966778541 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1024901932 / 1000000000000) (1024901933 / 1000000000000), orderedInterval (27286958661 / 1000000000000) (27286958662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2515519187987719 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31019550232 / 1000000000000) (31019550294 / 1000000000000), orderedInterval (7053103502 / 1000000000000) (7053103564 / 1000000000000)))) (orderedInterval (5994968451 / 1000000000000) (5994968593 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate560_chunkChecks3_1 :
    compactCertificate560.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3859453329164137 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23746647753 / 1000000000000) (-23746647688 / 1000000000000), orderedInterval (-9780534173 / 1000000000000) (-9780534108 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2228256418517473 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33015727217 / 1000000000000) (-33015718926 / 1000000000000), orderedInterval (7294202060 / 1000000000000) (7294210351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3954080116823957 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7411845814 / 1000000000000) (7411845816 / 1000000000000), orderedInterval (-24274670513 / 1000000000000) (-24274670512 / 1000000000000)))) (orderedInterval (20948188285 / 1000000000000) (20948191404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3694414554919433 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18099598120 / 1000000000000) (18099598121 / 1000000000000), orderedInterval (19008158026 / 1000000000000) (19008158027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2636508549830489 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5499344171 / 1000000000000) (5499344172 / 1000000000000), orderedInterval (30583574971 / 1000000000000) (30583574972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2989519693863231 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13116269941 / 1000000000000) (13116269942 / 1000000000000), orderedInterval (26063541045 / 1000000000000) (26063541046 / 1000000000000)))) (orderedInterval (-6258556727 / 1000000000000) (-6258556492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2492349847647439 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30835775465 / 1000000000000) (30835794243 / 1000000000000), orderedInterval (-8443318118 / 1000000000000) (-8443299339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2202066675784219 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33967304578 / 1000000000000) (-33967304178 / 1000000000000), orderedInterval (-1589621833 / 1000000000000) (-1589621434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (638244752313681 / 800000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16565695145 / 1000000000000) (16565695146 / 1000000000000), orderedInterval (22870635916 / 1000000000000) (22870635917 / 1000000000000)))) (orderedInterval (-3584050579 / 1000000000000) (-3584049740 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate560_chunkChecks3_2 :
    compactCertificate560.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1765418573880707 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27892535524 / 1000000000000) (27892557761 / 1000000000000), orderedInterval (-25808111203 / 1000000000000) (-25808088966 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1496564876554027 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36317369474 / 1000000000000) (-36317369473 / 1000000000000), orderedInterval (-19511559156 / 1000000000000) (-19511559155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (936480812012281 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34163395849 / 1000000000000) (34163416953 / 1000000000000), orderedInterval (-39469202038 / 1000000000000) (-39469180934 / 1000000000000)))) (orderedInterval (-4936842809 / 1000000000000) (-4936838792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (503642495294727 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61007611477 / 1000000000000) (61007611478 / 1000000000000), orderedInterval (36284124320 / 1000000000000) (36284124321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1367487347145181 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9554862528 / 1000000000000) (-9554862527 / 1000000000000), orderedInterval (-42067679160 / 1000000000000) (-42067679159 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1867187062437437 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18202330082 / 1000000000000) (18202330796 / 1000000000000), orderedInterval (-32151733363 / 1000000000000) (-32151732649 / 1000000000000)))) (orderedInterval (-3581225461 / 1000000000000) (-3581225344 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (789519187987719 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13732565433 / 1000000000000) (-13732565432 / 1000000000000), orderedInterval (-55072200473 / 1000000000000) (-55072200472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3209351666375399 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25410075426 / 1000000000000) (-25410011779 / 1000000000000), orderedInterval (12172507543 / 1000000000000) (12172571190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2143698178740841 / 4000000000000) 3 (IntervalRat.scale (863 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16603392923 / 1000000000000) (16603393316 / 1000000000000), orderedInterval (-30218442357 / 1000000000000) (-30218441964 / 1000000000000)))) (orderedInterval (-4455341010 / 1000000000000) (-4455307138 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate560_chunkChecks3 :
    compactCertificate560.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate560.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate560_chunkChecks3_0
    compactCertificate560_chunkChecks3_1 compactCertificate560_chunkChecks3_2

theorem compactCertificate560_chunkChecks4_0 :
    compactCertificate560.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (863 / 2) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-36507198156 / 1000000000000) (-36507186291 / 1000000000000), orderedInterval (11983342637 / 1000000000000) (11983354501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1271363788038563 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-43410190950 / 1000000000000) (-43410190946 / 1000000000000), orderedInterval (-10817661377 / 1000000000000) (-10817661373 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (411132927234179 / 800000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17484585914 / 1000000000000) (-17484585352 / 1000000000000), orderedInterval (30562902374 / 1000000000000) (30562902936 / 1000000000000)))) (orderedInterval (-16617550455 / 1000000000000) (-16617545611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (370980782523241 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-54538472276 / 1000000000000) (-54538430279 / 1000000000000), orderedInterval (62661861422 / 1000000000000) (62661903419 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (996506564621077 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-49945558317 / 1000000000000) (-49945557573 / 1000000000000), orderedInterval (7900405561 / 1000000000000) (7900406305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2705709171079809 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30070978734 / 1000000000000) (-30070965988 / 1000000000000), orderedInterval (6095664158 / 1000000000000) (6095676904 / 1000000000000)))) (orderedInterval (12700719395 / 1000000000000) (12700725075 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1993013129243017 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16341262259 / 1000000000000) (16341262610 / 1000000000000), orderedInterval (-31807382244 / 1000000000000) (-31807381892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3415061966778541 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (1024901932 / 1000000000000) (1024901933 / 1000000000000), orderedInterval (27286958661 / 1000000000000) (27286958662 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2515519187987719 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31019550232 / 1000000000000) (31019550294 / 1000000000000), orderedInterval (7053103502 / 1000000000000) (7053103564 / 1000000000000)))) (orderedInterval (2870109050 / 1000000000000) (2870109309 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate560_chunkChecks4_1 :
    compactCertificate560.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3859453329164137 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23746647753 / 1000000000000) (-23746647688 / 1000000000000), orderedInterval (-9780534173 / 1000000000000) (-9780534108 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2228256418517473 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-33015727217 / 1000000000000) (-33015718926 / 1000000000000), orderedInterval (7294202060 / 1000000000000) (7294210351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3954080116823957 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (7411845814 / 1000000000000) (7411845816 / 1000000000000), orderedInterval (-24274670513 / 1000000000000) (-24274670512 / 1000000000000)))) (orderedInterval (127615951326 / 1000000000000) (127615957032 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3694414554919433 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (18099598120 / 1000000000000) (18099598121 / 1000000000000), orderedInterval (19008158026 / 1000000000000) (19008158027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2636508549830489 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5499344171 / 1000000000000) (5499344172 / 1000000000000), orderedInterval (30583574971 / 1000000000000) (30583574972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2989519693863231 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (13116269941 / 1000000000000) (13116269942 / 1000000000000), orderedInterval (26063541045 / 1000000000000) (26063541046 / 1000000000000)))) (orderedInterval (-4595744509 / 1000000000000) (-4595744102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2492349847647439 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30835775465 / 1000000000000) (30835794243 / 1000000000000), orderedInterval (-8443318118 / 1000000000000) (-8443299339 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2202066675784219 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-33967304578 / 1000000000000) (-33967304178 / 1000000000000), orderedInterval (-1589621833 / 1000000000000) (-1589621434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (638244752313681 / 800000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16565695145 / 1000000000000) (16565695146 / 1000000000000), orderedInterval (22870635916 / 1000000000000) (22870635917 / 1000000000000)))) (orderedInterval (11671481031 / 1000000000000) (11671482255 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate560_chunkChecks4_2 :
    compactCertificate560.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1765418573880707 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (27892535524 / 1000000000000) (27892557761 / 1000000000000), orderedInterval (-25808111203 / 1000000000000) (-25808088966 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1496564876554027 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-36317369474 / 1000000000000) (-36317369473 / 1000000000000), orderedInterval (-19511559156 / 1000000000000) (-19511559155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (936480812012281 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34163395849 / 1000000000000) (34163416953 / 1000000000000), orderedInterval (-39469202038 / 1000000000000) (-39469180934 / 1000000000000)))) (orderedInterval (-3600262414 / 1000000000000) (-3600258353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (503642495294727 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (61007611477 / 1000000000000) (61007611478 / 1000000000000), orderedInterval (36284124320 / 1000000000000) (36284124321 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1367487347145181 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-9554862528 / 1000000000000) (-9554862527 / 1000000000000), orderedInterval (-42067679160 / 1000000000000) (-42067679159 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1867187062437437 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (18202330082 / 1000000000000) (18202330796 / 1000000000000), orderedInterval (-32151733363 / 1000000000000) (-32151732649 / 1000000000000)))) (orderedInterval (-1816721300 / 1000000000000) (-1816721174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (789519187987719 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-13732565433 / 1000000000000) (-13732565432 / 1000000000000), orderedInterval (-55072200473 / 1000000000000) (-55072200472 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3209351666375399 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25410075426 / 1000000000000) (-25410011779 / 1000000000000), orderedInterval (12172507543 / 1000000000000) (12172571190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2143698178740841 / 4000000000000) 4 (IntervalRat.scale (863 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16603392923 / 1000000000000) (16603393316 / 1000000000000), orderedInterval (-30218442357 / 1000000000000) (-30218441964 / 1000000000000)))) (orderedInterval (17329694416 / 1000000000000) (17329757292 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate560_chunkChecks4 :
    compactCertificate560.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate560.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate560_chunkChecks4_0
    compactCertificate560_chunkChecks4_1 compactCertificate560_chunkChecks4_2

theorem compactCertificate560_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate560.chunkCheck r b = true :=
  compactCertificate560.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate560_chunkChecks0
    · exact compactCertificate560_chunkChecks1
    · exact compactCertificate560_chunkChecks2
    · exact compactCertificate560_chunkChecks3
    · exact compactCertificate560_chunkChecks4)

theorem compactCertificate560_coefficient0 :
    compactCertificate560.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate560_coefficient1 :
    compactCertificate560.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate560_coefficient2 :
    compactCertificate560.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate560_coefficient3 :
    compactCertificate560.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate560_coefficient4 :
    compactCertificate560.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate560_coefficients : ∀ r : Fin 5,
    compactCertificate560.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate560_coefficient0
  · exact compactCertificate560_coefficient1
  · exact compactCertificate560_coefficient2
  · exact compactCertificate560_coefficient3
  · exact compactCertificate560_coefficient4

theorem compactCertificate560_lower : (1 : ℚ) ≤ compactCertificate560.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate560, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate560_proves {t : ℝ} (ht : t ∈ compactCertificate560.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate560.proves compactCertificate560_states compactCertificate560_chunks
    compactCertificate560_coefficients compactCertificate560_lower ht

end Erdos232
